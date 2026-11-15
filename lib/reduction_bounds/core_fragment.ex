defmodule ReductionBounds.CoreFragment do
  @moduledoc false
  # cspell:words badarg

  @type name :: String.t()
  @type map_pattern :: %{tag: name() | nil, fields: [{name(), name()}]}
  @type expr ::
          {:var, name()}
          | {:int, integer()}
          | {:atom, name()}
          | {:let_in, name(), expr(), expr()}
          | {:case_map, expr(), map_pattern(), expr(), expr()}
          | {:case_map_guarded, expr(), map_pattern(), expr(), expr(), expr()}
          | {:guarded, expr(), expr(), expr()}
          | {:is_integer, expr()}
          | {:is_map, expr()}
          | {:field, expr(), name()}
          | {:update, expr(), name(), expr()}
          | {:ge, expr(), expr()}
          | {:sub, expr(), expr()}
          | {:opaque, String.t()}

  @type t :: %{
          parameters: [name()],
          expression: expr(),
          opaque: %{String.t() => tuple()}
        }

  @type decode_error :: {:unsupported_core, term()}

  @spec decode(tuple()) :: {:ok, t()} | {:error, decode_error()}
  def decode({:c_fun, _, parameters, body}) do
    with {:ok, names} <- map_ok(parameters, &name/1),
         {:ok, expression, opaque} <- decode_expression(body, %{}) do
      {:ok, %{parameters: names, expression: expression, opaque: opaque}}
    end
  end

  def decode(other), do: unsupported(other)

  defp decode_expression({:c_var, _, _} = var, opaque) do
    with {:ok, name} <- name(var), do: {:ok, {:var, name}, opaque}
  end

  defp decode_expression({:c_literal, _, value}, opaque) when is_integer(value),
    do: {:ok, {:int, value}, opaque}

  defp decode_expression({:c_literal, _, value}, opaque) when is_atom(value),
    do: {:ok, {:atom, Atom.to_string(value)}, opaque}

  defp decode_expression({:c_let, _, [var], rhs, body}, opaque) do
    with {:ok, name} <- name(var),
         {:ok, rhs, opaque} <- decode_expression(rhs, opaque),
         {:ok, body, opaque} <- decode_expression(body, opaque) do
      {:ok, {:let_in, name, rhs, body}, opaque}
    end
  end

  defp decode_expression({:c_case, _, {:c_var, _, _} = subject, _} = core, opaque) do
    with {:ok, subject, opaque} <- decode_expression(subject, opaque) do
      decode_case(core, subject, opaque)
    end
  end

  defp decode_expression({:c_case, _, {:c_values, _, [_, _ | _] = subjects}, _} = core, opaque) do
    with {:ok, names} <- map_ok(subjects, &name/1) do
      decode_multi_case(core, names, opaque)
    end
  end

  defp decode_expression(
         {:c_case, annotations, {:c_values, _, []} = inputs,
          [{:c_clause, _, [], guard, body}, fallback]},
         opaque
       ) do
    with {:ok, condition, opaque} <- decode_test(guard, opaque),
         {:ok, success, opaque} <- decode_expression(body, opaque) do
      {failure, opaque} = preserve({:c_case, annotations, inputs, [fallback]}, opaque)
      {:ok, {:guarded, condition, success, failure}, opaque}
    end
  end

  defp decode_expression(
         {:c_map, _, base,
          [{:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, key}, value}], false},
         opaque
       )
       when is_atom(key),
       do: decode_update(base, key, value, opaque)

  defp decode_expression(
         {:c_call, _, {:c_literal, _, :maps}, {:c_literal, _, :get},
          [{:c_literal, _, key}, subject]},
         opaque
       )
       when is_atom(key) do
    with {:ok, subject, opaque} <- decode_expression(subject, opaque) do
      {:ok, {:field, subject, Atom.to_string(key)}, opaque}
    end
  end

  defp decode_expression(
         {:c_call, _, {:c_literal, _, :maps}, {:c_literal, _, :update},
          [{:c_literal, _, key}, value, subject]},
         opaque
       )
       when is_atom(key) do
    decode_update(subject, key, value, opaque)
  end

  defp decode_expression(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, operation}, [left, right]},
         opaque
       )
       when operation in [:>=, :-] do
    with {:ok, left, opaque} <- decode_expression(left, opaque),
         {:ok, right, opaque} <- decode_expression(right, opaque) do
      op = if operation == :>=, do: :ge, else: :sub
      {:ok, {op, left, right}, opaque}
    end
  end

  defp decode_expression(other, _opaque), do: unsupported(other)

  defp decode_update(subject, key, rhs, opaque) do
    # These operands are already values, including when lowered from a call.
    with :ok <- require_value(subject),
         :ok <- require_value(rhs),
         {:ok, subject, opaque} <- decode_expression(subject, opaque),
         {:ok, rhs, opaque} <- decode_expression(rhs, opaque) do
      {:ok, {:update, subject, Atom.to_string(key), rhs}, opaque}
    end
  end

  defp require_value({:c_var, _, _}), do: :ok
  defp require_value({:c_literal, _, _}), do: :ok
  defp require_value(other), do: unsupported(other)

  defp decode_case(
         {:c_case, annotations, source, [first | rest]} = original,
         {:var, subject_name} = subject,
         opaque
       ) do
    with {:c_clause, _, [pattern], {:c_literal, _, true}, body} <- first,
         {:ok, pattern, alias_name} <- decode_map_pattern(pattern),
         :ok <- check_alias_subject(alias_name, subject_name, pattern),
         {:ok, matched, opaque} <- decode_expression(body, opaque) do
      # The original case tail remains available, with its patterns and bindings.
      {fallback, opaque} = preserve({:c_case, annotations, source, rest}, opaque)
      matched = bind_alias(matched, alias_name, subject)
      {:ok, {:case_map, subject, pattern, matched, fallback}, opaque}
    else
      {:error, _reason} = error -> error
      _ -> unsupported(original)
    end
  end

  defp decode_case(other, _subject, _opaque), do: unsupported(other)

  defp decode_multi_case({:c_case, annotations, inputs, [first | rest]}, subjects, opaque) do
    case decode_multi_clause(first, subjects, opaque) do
      {:ok, pattern, guard, body, opaque} ->
        remainder = {:c_case, annotations, inputs, rest}
        {:ok, fallback, opaque} = decode_multi_fallback(remainder, subjects, opaque)

        [subject | _] = subjects
        expression = map_clause({:var, subject}, pattern, guard, body, fallback)
        {:ok, expression, opaque}

      {:error, _reason} = error ->
        error
    end
  end

  defp decode_multi_case(other, _subjects, _opaque), do: unsupported(other)

  defp decode_multi_fallback(core, subjects, opaque) do
    case decode_multi_case(core, subjects, opaque) do
      {:ok, _, _} = decoded ->
        decoded

      {:error, _reason} ->
        {fallback, opaque} = preserve(core, opaque)
        {:ok, fallback, opaque}
    end
  end

  defp decode_multi_clause({:c_clause, _, [first | rest], guard, body}, subjects, opaque) do
    with {:ok, pattern, alias_name} <- decode_map_pattern(first),
         {:ok, names} <- map_ok(rest, &name/1),
         {:ok, bindings} <- argument_bindings(subjects, alias_name, names, pattern),
         {:ok, condition, opaque} <- decode_guard(guard, opaque),
         {:ok, body, opaque} <- decode_expression(body, opaque) do
      {:ok, pattern, bind_arguments(condition, bindings), bind_arguments(body, bindings), opaque}
    end
  end

  defp decode_multi_clause(other, _subjects, _opaque), do: unsupported(other)

  defp argument_bindings([subject | rest] = subjects, alias_name, names, pattern) do
    fields = Enum.map(pattern.fields, &elem(&1, 1))
    binders = if alias_name, do: [alias_name | names ++ fields], else: names ++ fields

    if length(rest) == length(names) and Enum.uniq(binders) == binders and
         Enum.all?(binders, &(&1 not in subjects)) do
      arguments = Enum.zip(names, rest)
      {:ok, if(alias_name, do: [{alias_name, subject} | arguments], else: arguments)}
    else
      unsupported(pattern)
    end
  end

  defp bind_arguments(nil, _bindings), do: nil

  defp bind_arguments(expression, bindings) do
    Enum.reduce(Enum.reverse(bindings), expression, fn {name, subject}, body ->
      {:let_in, name, {:var, subject}, body}
    end)
  end

  defp map_clause(subject, pattern, nil, body, fallback),
    do: {:case_map, subject, pattern, body, fallback}

  defp map_clause(subject, pattern, condition, body, fallback),
    do: {:case_map_guarded, subject, pattern, condition, body, fallback}

  defp decode_guard({:c_literal, _, true}, opaque), do: {:ok, nil, opaque}

  defp decode_guard(
         {:c_try, _,
          {:c_let, _, [{:c_var, _, result}], condition,
           {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :"=:="},
            [{:c_var, _, result}, {:c_literal, _, true}]}}, [{:c_var, _, success}],
          {:c_var, _, success}, _exceptions, {:c_literal, _, false}},
         opaque
       ),
       do: decode_test(condition, opaque)

  defp decode_guard(other, opaque), do: decode_test(other, opaque)

  defp decode_test(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, test}, [operand]},
         opaque
       )
       when test in [:is_integer, :is_map] do
    with :ok <- require_value(operand),
         {:ok, value, opaque} <- decode_expression(operand, opaque) do
      {:ok, {test, value}, opaque}
    end
  end

  defp decode_test(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :>=}, [left, right]} = core,
         opaque
       ) do
    with :ok <- require_value(left),
         :ok <- require_value(right),
         do: decode_expression(core, opaque)
  end

  # Core lowers a Boolean conjunction to a case with an unreachable badarg arm.
  defp decode_test(
         {:c_case, _, test,
          [
            {:c_clause, _, [{:c_literal, _, true}], {:c_literal, _, true}, next},
            {:c_clause, _, [{:c_literal, _, false}], {:c_literal, _, true},
             {:c_literal, _, false}},
            {:c_clause, _, [{:c_var, _, bad}], {:c_literal, _, true},
             {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :error},
              [{:c_tuple, _, [{:c_literal, _, :badarg}, {:c_var, _, bad}]}]}}
          ]},
         opaque
       ) do
    with {:ok, condition, opaque} <- decode_test(test, opaque),
         {:ok, success, opaque} <- decode_test(next, opaque) do
      {:ok, {:guarded, condition, success, {:atom, "false"}}, opaque}
    end
  end

  defp decode_test(other, _opaque), do: unsupported(other)

  defp preserve(core, opaque) do
    id = "fallback:#{map_size(opaque)}"
    {{:opaque, id}, Map.put(opaque, id, core)}
  end

  defp bind_alias(body, nil, _subject), do: body
  defp bind_alias(body, name, subject), do: {:let_in, name, subject, body}

  defp check_alias_subject(nil, _subject, _pattern), do: :ok

  defp check_alias_subject(_alias, subject, pattern) do
    if Enum.any?(pattern.fields, fn {_key, binder} -> binder == subject end),
      do: unsupported(pattern),
      else: :ok
  end

  defp decode_map_pattern({:c_alias, _, alias_var, pattern}) do
    with {:ok, name} <- name(alias_var),
         {:ok, decoded, nil} <- decode_map_pattern(pattern),
         false <- Enum.any?(decoded.fields, fn {_key, binder} -> binder == name end) do
      {:ok, decoded, name}
    else
      _ -> unsupported(pattern)
    end
  end

  defp decode_map_pattern({:c_map, _, {:c_literal, _, base}, pairs, true} = pattern)
       when base == %{} do
    with {:ok, entries} <- map_ok(pairs, &decode_pattern_pair/1),
         {tags, fields} = Enum.split_with(entries, &(elem(&1, 0) == "__struct__")),
         {:ok, tag} <- decode_tag(tags),
         true <- distinct?(fields, 0) and distinct?(fields, 1),
         true <- Enum.all?(fields, &(elem(&1, 2) == :binder)) do
      {:ok, %{tag: tag, fields: Enum.map(fields, fn {key, name, _} -> {key, name} end)}, nil}
    else
      _ -> unsupported(pattern)
    end
  end

  defp decode_map_pattern(other), do: unsupported(other)

  defp decode_pattern_pair(
         {:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, key}, {:c_var, _, _} = var}
       )
       when is_atom(key) do
    with {:ok, name} <- name(var), do: {:ok, {Atom.to_string(key), name, :binder}}
  end

  defp decode_pattern_pair(
         {:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, :__struct__},
          {:c_literal, _, tag}}
       )
       when is_atom(tag),
       do: {:ok, {"__struct__", Atom.to_string(tag), :tag}}

  defp decode_pattern_pair(other), do: unsupported(other)

  defp decode_tag([]), do: {:ok, nil}
  defp decode_tag([{"__struct__", tag, :tag}]), do: {:ok, tag}
  defp decode_tag(other), do: unsupported(other)

  defp distinct?(entries, index) do
    Enum.uniq_by(entries, &elem(&1, index)) == entries
  end

  defp name({:c_var, _, id}) when is_integer(id), do: {:ok, "integer:#{id}"}
  defp name({:c_var, _, id}) when is_atom(id), do: {:ok, "atom:#{id}"}
  defp name(other), do: unsupported(other)

  defp map_ok([], _function), do: {:ok, []}

  defp map_ok([first | rest], function) do
    with {:ok, value} <- function.(first),
         {:ok, values} <- map_ok(rest, function) do
      {:ok, [value | values]}
    end
  end

  defp unsupported(core), do: {:error, {:unsupported_core, core}}
end
