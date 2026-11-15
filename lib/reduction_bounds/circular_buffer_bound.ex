defmodule ReductionBounds.CircularBufferBound do
  @moduledoc false
  # cspell:words cerl cons

  alias ReductionBounds.{ComposedBound, CoreFragment, Normalize, SearchBound}

  @target {CircularBuffer, :insert, 2}
  @paths [:consume, :fill, :rotate, :zero]
  @fields [:a, :b, :count, :max_size]
  @field_names Map.new(@fields, &{Atom.to_string(&1), &1})
  @proof_path Path.expand("../../priv/lean/reduction_bounds/CircularBuffer.lean", __DIR__)
  @external_resource @proof_path
  @proof_source File.read!(@proof_path)

  @spec infer([binary()]) :: {:ok, map()} | {:error, term()}
  @spec infer([binary()], :n | :m) :: {:ok, map()} | {:error, term()}
  def infer(beams, capacity \\ :n) do
    with {:ok, core} <- SearchBound.core_function(@target, beams),
         true <- supported?(core),
         :ok <- check_enum_reverse(beams) do
      {:ok, candidate(capacity)}
    else
      false -> {:error, {:unsupported_circular_buffer_shape, @target}}
      {:error, _} = error -> error
    end
  end

  defp check_enum_reverse(beams) do
    target = {Enum, :reverse, 1}

    with {:ok, core} <- SearchBound.core_function(target, beams) do
      if list_reverse?(core), do: :ok, else: {:error, {:unsupported_list_reverse, target}}
    end
  end

  defp list_reverse?({:c_fun, _, [{:c_var, _, input}], {:c_case, _, {:c_var, _, input}, clauses}}) do
    case :cerl_trees.map(&:cerl.set_ann(&1, []), {:c_values, [], clauses}) do
      {:c_values, [],
       [
         {:c_clause, [], [{:c_literal, [], []}], {:c_literal, [], true}, {:c_literal, [], []}},
         {:c_clause, [],
          [
            {:c_alias, [], {:c_var, [], singleton},
             {:c_cons, [], {:c_var, [], _}, {:c_literal, [], []}}}
          ], {:c_literal, [], true}, {:c_var, [], singleton}},
         pair,
         longer | _
       ]} ->
        reverse_pair?(pair) and reverse_tail?(longer)

      _ ->
        false
    end
  end

  defp list_reverse?(_), do: false

  defp reverse_pair?(
         {:c_clause, [],
          [
            {:c_cons, [], {:c_var, [], first},
             {:c_cons, [], {:c_var, [], second}, {:c_literal, [], []}}}
          ], {:c_literal, [], true}, result}
       ),
       do: swapped_pair(result, first, second)

  defp reverse_pair?(_), do: false

  defp reverse_tail?(
         {:c_clause, [],
          [
            {:c_cons, [], {:c_var, [], first},
             {:c_cons, [], {:c_var, [], second}, {:c_var, [], rest}}}
          ], {:c_literal, [], true},
          {:c_call, [], {:c_literal, [], :lists}, {:c_literal, [], :reverse},
           [{:c_var, [], rest}, acc]}}
       ),
       do: swapped_pair(acc, first, second)

  defp reverse_tail?(_), do: false

  defp swapped_pair(result, first, second) do
    result ==
      {:c_cons, [], {:c_var, [], second},
       {:c_cons, [], {:c_var, [], first}, {:c_literal, [], []}}}
  end

  defp candidate(capacity) do
    capacity
    |> path_costs()
    |> ComposedBound.compose_paths()
    |> Map.merge(%{
      target: @target,
      metric: :symbolic_cost,
      domain: :valid_integer_circular_buffer,
      value_model: :circular_buffer_model,
      size_measure: :capacity,
      source: :circular_buffer_model
    })
  end

  defp path_costs(capacity), do: Enum.map(@paths, &{&1, path_cost(&1, capacity)})

  defp path_cost(:rotate, capacity),
    do: {:add, {:buffer_charge, :rotate}, {:enum_reverse, "a", capacity}}

  defp path_cost(path, _capacity), do: {:buffer_charge, path}

  defp supported?({:c_fun, _, params, {:c_case, _, {:c_values, _, args}, clauses}}) do
    Enum.map(params, &:cerl.var_name/1) == Enum.map(args, &variable/1) and
      Enum.map(clauses, &normalize_clause/1) == expected_clauses()
  end

  defp supported?(_core), do: false

  defp expected_clauses() do
    [
      {[{:nonempty, :b}], true, {:update, %{a: {:cons, :item, :a}, b: {:tail, :b}}}},
      {[], {:less, :count, :max_size},
       {:update, %{a: {:cons, :item, :a}, count: {:add, :count, 1}}}},
      {[{:empty, :b}], {:nonempty, :a},
       {:update, %{a: {:cons, :item, []}, b: {:tail, {:reverse, :a}}}}},
      {[], true, :buffer}
    ]
  end

  defp normalize_clause({:c_clause, _, [buffer, {:c_var, _, item}], guard, body}) do
    with {:ok, env, tests} <- buffer_pattern(buffer, %{item => :item}),
         {:ok, guard} <- expression(guard, env),
         {:ok, body} <- expression(body, env) do
      {tests, guard, body}
    end
  end

  defp normalize_clause(_), do: :unsupported

  defp buffer_pattern({:c_var, _, name}, env), do: {:ok, Map.put(env, name, :buffer), []}

  defp buffer_pattern({:c_alias, _, {:c_var, _, name}, {:c_map, _, _, fields, true}}, env) do
    case Enum.split_with(fields, &struct_tag?/1) do
      {[_tag], fields} ->
        field_patterns(fields, Map.put(env, name, :buffer), [])

      _ ->
        :unsupported
    end
  end

  defp buffer_pattern(_, _), do: :unsupported

  defp struct_tag?(
         {:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, :__struct__},
          {:c_literal, _, CircularBuffer}}
       ),
       do: true

  defp struct_tag?(_), do: false

  defp field_patterns([], env, tests), do: {:ok, env, Enum.sort(tests)}

  defp field_patterns(
         [{:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, field}, pattern} | rest],
         env,
         tests
       )
       when field in @fields do
    case pattern do
      {:c_var, _, name} ->
        field_patterns(rest, Map.put(env, name, field), tests)

      {:c_literal, _, []} when field in [:a, :b] ->
        field_patterns(rest, env, [{:empty, field} | tests])

      {:c_cons, _, {:c_var, _, _}, {:c_var, _, tail}} when field in [:a, :b] ->
        field_patterns(rest, Map.put(env, tail, {:tail, field}), [{:nonempty, field} | tests])

      _ ->
        :unsupported
    end
  end

  defp field_patterns(_, _, _), do: :unsupported

  defp expression({:c_var, _, name}, env), do: Map.fetch(env, name)
  defp expression({:c_literal, _, value}, _env), do: {:ok, value}

  defp expression({:c_cons, _, head, tail}, env) do
    with {:ok, head} <- expression(head, env), {:ok, tail} <- expression(tail, env) do
      {:ok, {:cons, head, tail}}
    end
  end

  defp expression({:c_let, _, [{:c_var, _, name}], value, body}, env) do
    with {:ok, value} <- expression(value, env), do: expression(body, Map.put(env, name, value))
  end

  defp expression({:c_call, _, {:c_literal, _, module}, {:c_literal, _, name}, args}, env) do
    operation(module, name, Enum.map(args, &expression(&1, env)))
  end

  # The valid-buffer domain supplies the field facts to the common rewrite rule.
  defp expression({:c_case, _, {:c_var, _, _} = buffer, _} = core, env) do
    with {:ok, :buffer} <- expression(buffer, env),
         {:ok, %{parameters: [subject]} = program} <-
           CoreFragment.decode({:c_fun, [], [buffer], core}),
         facts = Enum.map(Map.keys(@field_names), &{subject, &1}),
         %{program: %{expression: {:field, {:var, ^subject}, key}}} <-
           Normalize.normalize(program, facts) do
      Map.fetch(@field_names, key)
    else
      _ -> :unsupported
    end
  end

  # The compiler guards map updates with is_map/1.
  defp expression(
         {:c_case, _, {:c_values, _, []},
          [
            {:c_clause, _, [],
             {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :is_map}, [buffer]}, updated}
            | _
          ]},
         env
       ) do
    with {:ok, :buffer} <- expression(buffer, env), do: expression(updated, env)
  end

  defp expression({:c_map, _, base, fields, false}, env) do
    with {:ok, :buffer} <- expression(base, env),
         {:ok, updates} <- updates(fields, env, %{}) do
      {:ok, {:update, updates}}
    end
  end

  defp expression(_, _), do: :unsupported

  defp operation(Enum, :reverse, [{:ok, arg}]), do: {:ok, {:reverse, arg}}
  defp operation(:erlang, :tl, [{:ok, arg}]), do: {:ok, {:tail, arg}}
  defp operation(:erlang, :"/=", [{:ok, field}, {:ok, []}]), do: {:ok, {:nonempty, field}}
  defp operation(:erlang, :<, [{:ok, left}, {:ok, right}]), do: {:ok, {:less, left, right}}
  defp operation(:erlang, :+, [{:ok, left}, {:ok, right}]), do: {:ok, {:add, left, right}}
  defp operation(_module, _name, _args), do: :unsupported

  defp updates([], _env, result), do: {:ok, result}

  defp updates(
         [{:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, field}, value} | rest],
         env,
         result
       ) do
    with {:ok, value} <- expression(value, env),
         false <- Map.has_key?(result, field) do
      updates(rest, env, Map.put(result, field, value))
    end
  end

  defp updates(_, _, _), do: :unsupported

  defp variable({:c_var, _, name}), do: name
  defp variable(_), do: nil

  @spec proof() :: Lynx.Lean.t()
  def proof() do
    %Lynx.Lean{
      file: "generated_circular_buffer_bound.lean",
      span: {1, 1},
      indentation: 0,
      source: ComposedBound.buffer_cost_proof(path_costs(:n)) <> @proof_source
    }
  end
end
