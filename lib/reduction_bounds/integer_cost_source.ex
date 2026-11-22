defmodule ReductionBounds.IntegerCostSource do
  @moduledoc false
  # cspell:words rhs bxor bsl bsr band

  alias ReductionBounds.IntegerSize

  @binary %{+: :add, -: :subtract, *: :multiply, bxor: :bit_xor}
  @comparisons %{<: :lt, "=<": :le, "=:=": :eq, ==: :eq, "/=": :ne, "=/=": :ne, >=: :ge, >: :gt}

  @spec decode(tuple(), ReductionBounds.target(), map()) :: {:ok, map()} | {:error, term()}
  def decode({:c_fun, _, args, body}, target, contracts) do
    variables = args |> Enum.with_index() |> Map.new(fn {{:c_var, _, name}, id} -> {name, id} end)
    context = %{variables: variables, next: length(args), target: target, contracts: contracts}
    {:ok, lower(body, context, [])}
  catch
    {:integer_cost_source, reason} -> {:error, {:integer_cost_source, target, reason}}
  end

  def decode(_core, target, _contracts), do: {:error, {:unsupported_integer_function, target}}

  defp lower({:c_literal, _, value}, _context, _path) when is_integer(value),
    do: node({:int, value}, {:integer, value}, "(.integer)")

  defp lower({:c_var, _, name}, context, path) do
    case Map.fetch(context.variables, name) do
      {:ok, id} -> node({:var, id}, {:variable, id}, "(.variable)")
      :error -> fail({:unbound_variable, path, name})
    end
  end

  defp lower({:c_let, _, [{:c_var, _, name}], rhs, body}, context, path) do
    id = context.next
    bound = %{context | variables: Map.put(context.variables, name, id), next: id + 1}
    a = lower(rhs, context, path ++ [:binding])
    b = lower(body, bound, path ++ [:body])

    node(
      {:let, id, a.expr, b.expr},
      {:letOne, id, a.source, b.source},
      "(.letOne #{a.proof} #{b.proof})"
    )
  end

  defp lower({:c_call, _, {:c_literal, _, module}, {:c_literal, _, name}, args}, context, path),
    do: lower_call(module, name, args, context, path)

  defp lower({:c_apply, _, {:c_var, _, {name, 1}}, [argument]}, context, path) do
    {module, current, arity} = context.target
    if name == current and arity == 1, do: fail({:unsupported_self_arity, path, 1})
    target = {module, name, 1}

    case Map.fetch(context.contracts, target) do
      {:ok, key} ->
        a = lower(argument, context, path ++ [:argument])

        node(
          {:call, key, a.expr},
          {:apply1, Atom.to_string(module), Atom.to_string(name), a.source},
          "(.localCall (by decide) (by decide) #{a.proof})"
        )

      :error ->
        fail({:missing_call_contract, path, target})
    end
  end

  defp lower({:c_apply, _, {:c_var, _, {name, 2}}, [counter, accumulator]}, context, path) do
    {_, current, arity} = context.target
    if name != current or arity != 2, do: fail({:unsupported_local_call, path, {name, 2}})
    a = lower(counter, context, path ++ [:counter])
    b = lower(accumulator, context, path ++ [:accumulator])

    node(
      {:recur, a.expr, b.expr},
      {:apply2, Atom.to_string(name), a.source, b.source},
      "(.recur (by decide) #{a.proof} #{b.proof})"
    )
  end

  defp lower({:c_case, _, condition, clauses}, context, path) do
    {op, id, constant, source} = test(condition, context, path)
    {first_truth, first_body, second_truth, second_body} = clauses(clauses, path)
    first = lower(first_body, context, path ++ [if(first_truth, do: :then, else: :else)])
    second = lower(second_body, context, path ++ [if(second_truth, do: :then, else: :else)])

    {yes, no, rule} =
      if first_truth, do: {first, second, :branchTrue}, else: {second, first, :branchFalse}

    node(
      {:if, op, id, constant, yes.expr, no.expr},
      {:case2, source, first_truth, first.source, second_truth, second.source},
      "(.#{rule} (by decide) #{yes.proof} #{no.proof})"
    )
  end

  defp lower(core, _context, path), do: fail({:unsupported_expression, path, kind(core)})

  defp lower_call(:erlang, name, [left, right], context, path) when is_map_key(@binary, name) do
    a = lower(left, context, path ++ [:left])
    b = lower(right, context, path ++ [:right])

    node(
      {:binary, Map.fetch!(@binary, name), a.expr, b.expr},
      {:call2, "erlang", Atom.to_string(name), a.source, b.source},
      "(.binary (by decide) #{a.proof} #{b.proof})"
    )
  end

  defp lower_call(:erlang, name, [value], context, path) when name in [:+, :-] do
    a = lower(value, context, path ++ [:operand])
    op = if name == :+, do: :add, else: :subtract
    rule = if name == :+, do: :positive, else: :negative

    node(
      {:binary, op, {:int, 0}, a.expr},
      {:call1, "erlang", Atom.to_string(name), a.source},
      "(.#{rule} (by decide) #{a.proof})"
    )
  end

  defp lower_call(:erlang, name, [value, {:c_literal, _, amount}], context, path)
       when name in [:bsl, :bsr] and is_integer(amount) and amount >= 0 do
    a = lower(value, context, path ++ [:operand])
    op = if name == :bsl, do: :shift_left, else: :shift_right

    node(
      {:unary, op, amount, a.expr},
      {:call2, "erlang", Atom.to_string(name), a.source, {:integer, amount}},
      "(.unary (by decide) (by decide) #{a.proof})"
    )
  end

  defp lower_call(:erlang, :band, [value, {:c_literal, _, mask}], context, path)
       when is_integer(mask) and mask >= 0 do
    width = mask_width(mask, path)
    a = lower(value, context, path ++ [:operand])

    node(
      {:unary, :mask, width, a.expr},
      {:call2, "erlang", "band", a.source, {:integer, mask}},
      "(.unary (by decide) (by decide) #{a.proof})"
    )
  end

  defp lower_call(:erlang, :band, [{:c_literal, _, mask}, value], context, path)
       when is_integer(mask) and mask >= 0 do
    width = mask_width(mask, path)
    a = lower(value, context, path ++ [:operand])

    node(
      {:unary, :mask, width, a.expr},
      {:call2, "erlang", "band", {:integer, mask}, a.source},
      "(.maskLeft (by decide) (by decide) (by decide) #{a.proof})"
    )
  end

  defp lower_call(module, name, [argument], context, path) do
    target = {module, name, 1}

    case Map.fetch(context.contracts, target) do
      {:ok, key} ->
        a = lower(argument, context, path ++ [:argument])

        node(
          {:call, key, a.expr},
          {:call1, Atom.to_string(module), Atom.to_string(name), a.source},
          "(.call (by decide) (by decide) #{a.proof})"
        )

      :error ->
        fail({:missing_call_contract, path, target})
    end
  end

  defp lower_call(module, name, args, _context, path),
    do: fail({:unsupported_call, path, {module, name, length(args)}})

  defp test(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, name},
          [{:c_var, _, variable}, {:c_literal, _, constant}]},
         context,
         path
       )
       when is_map_key(@comparisons, name) and is_integer(constant) do
    a = lower({:c_var, [], variable}, context, path)
    {:var, id} = a.expr

    {Map.fetch!(@comparisons, name), id, constant,
     {:call2, "erlang", Atom.to_string(name), a.source, {:integer, constant}}}
  end

  defp test(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, name},
          [{:c_literal, _, constant}, {:c_var, _, variable}]},
         context,
         path
       )
       when is_map_key(@comparisons, name) and is_integer(constant) do
    a = lower({:c_var, [], variable}, context, path)
    {:var, id} = a.expr
    reverse = %{lt: :gt, le: :ge, eq: :eq, ne: :ne, ge: :le, gt: :lt}

    {Map.fetch!(reverse, Map.fetch!(@comparisons, name)), id, constant,
     {:call2, "erlang", Atom.to_string(name), {:integer, constant}, a.source}}
  end

  defp test(_condition, _context, path), do: fail({:unsupported_condition, path})

  defp clauses(
         [
           {:c_clause, _, [{:c_literal, _, first}], {:c_literal, _, true}, first_body},
           {:c_clause, _, [{:c_literal, _, second}], {:c_literal, _, true}, second_body}
         ],
         _path
       )
       when is_boolean(first) and is_boolean(second) and first != second,
       do: {first, first_body, second, second_body}

  defp clauses(_clauses, path), do: fail({:unsupported_boolean_clauses, path})

  defp mask_width(mask, path) do
    width = IntegerSize.from_integer(mask + 1).magnitude_bits - 1
    if Integer.pow(2, width) != mask + 1, do: fail({:unsupported_mask, path, mask})
    width
  end

  defp node(expr, source, proof), do: %{expr: expr, source: source, proof: proof}
  defp kind(core) when is_tuple(core), do: elem(core, 0)
  defp kind(_core), do: :unknown
  defp fail(reason), do: throw({:integer_cost_source, reason})

  @spec lean(term()) :: String.t()
  def lean({:integer, value}), do: "(.integer (#{value}))"
  def lean({:variable, id}), do: "(.variable #{id})"
  def lean({:letOne, id, a, b}), do: "(.letOne #{id} #{lean(a)} #{lean(b)})"

  def lean({:call1, module, name, arg}),
    do: "(.call1 #{string(module)} #{string(name)} #{lean(arg)})"

  def lean({:call2, module, name, a, b}),
    do: "(.call2 #{string(module)} #{string(name)} #{lean(a)} #{lean(b)})"

  def lean({:case2, condition, first, a, second, b}),
    do: "(.case2 #{lean(condition)} #{first} #{lean(a)} #{second} #{lean(b)})"

  def lean({:apply1, module, name, argument}),
    do: "(.apply1 #{string(module)} #{string(name)} #{lean(argument)})"

  def lean({:apply2, name, a, b}), do: "(.apply2 #{string(name)} #{lean(a)} #{lean(b)})"
  @spec string(String.t()) :: String.t()
  def string(value), do: ReductionBounds.ProofInput.string(value)
end
