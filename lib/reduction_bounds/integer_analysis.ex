defmodule ReductionBounds.IntegerAnalysis do
  @moduledoc false
  # cspell:words cerl bxor bsl bsr band rhs

  alias ReductionBounds.{IntegerSize, SearchBound}

  @binary %{+: :add, -: :subtract, *: :multiply, bxor: :bit_xor}
  @comparisons %{<: :lt, "=<": :le, "=:=": :eq, ==: :eq, "/=": :ne, "=/=": :ne, >=: :ge, >: :gt}

  @spec infer(ReductionBounds.target(), [binary()], [IntegerSize.t()] | nil) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer(target, beams, inputs) do
    with {:ok, core} <- SearchBound.core_function(target, beams) do
      infer_core(core, target, inputs)
    end
  end

  @spec infer_core(tuple(), ReductionBounds.target(), [IntegerSize.t()] | nil) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer_core({:c_fun, _, arguments, body}, {_, _, arity} = target, inputs) do
    sizes = input_sizes(inputs, arity, target)

    variables =
      arguments |> Enum.with_index() |> Map.new(fn {{:c_var, _, name}, id} -> {name, id} end)

    expression = decode(body, %{variables: variables, next: arity}, [])

    environment =
      if :unreachable in sizes,
        do: :unreachable,
        else: sizes |> Enum.with_index() |> Map.new(fn {size, id} -> {id, size} end)

    {size, intermediates} = analyze(expression, environment, [])

    unresolved =
      for row <- intermediates,
          unknown?(row.size),
          do: %{path: row.path, operation: row.operation, reason: :unknown_magnitude}

    candidate = %{
      target: target,
      source: :integer_fragment,
      metric: :integer_size,
      expression: expression,
      input_sizes: sizes,
      result_size: size,
      intermediates: intermediates,
      unresolved_sizes: unresolved,
      assumptions: %{arguments: :integers, arithmetic: :mathematical_integers},
      proof_scope: :reified_integer_fragment,
      termination: :structural_model,
      cost_model: :not_analyzed,
      value_agreement: :not_checked
    }

    {:ok, candidate, proof(candidate)}
  catch
    {:integer_analysis, reason} -> {:error, {:integer_analysis, target, reason}}
  end

  def infer_core(_core, target, _inputs), do: {:error, {:unsupported_integer_function, target}}

  defp input_sizes(nil, arity, _target), do: List.duplicate(IntegerSize.unknown(), arity)

  defp input_sizes(inputs, arity, target) do
    if is_list(inputs) and length(inputs) == arity and Enum.all?(inputs, &IntegerSize.valid?/1) do
      Enum.map(inputs, &IntegerSize.normalize/1)
    else
      fail({:invalid_input_sizes, target, arity, inputs})
    end
  end

  defp decode({:c_literal, _, value}, _context, _path) when is_integer(value), do: {:int, value}

  defp decode({:c_var, _, name}, context, path) do
    case Map.fetch(context.variables, name) do
      {:ok, id} -> {:var, id}
      :error -> fail({:unbound_integer_variable, path, name})
    end
  end

  defp decode({:c_values, _, [value]}, context, path), do: decode(value, context, path)

  defp decode({:c_let, _, [{:c_var, _, name}], rhs, body}, context, path) do
    id = context.next
    bound = %{context | variables: Map.put(context.variables, name, id), next: id + 1}
    {:let, id, decode(rhs, context, path ++ [:binding]), decode(body, bound, path ++ [:body])}
  end

  defp decode({:c_seq, _, first, second}, context, path) do
    {:let, context.next, decode(first, context, path ++ [:first]),
     decode(second, %{context | next: context.next + 1}, path ++ [:second])}
  end

  defp decode({:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, name}, args}, context, path) do
    decode_call(name, args, context, path)
  end

  defp decode({:c_call, _, {:c_literal, _, module}, {:c_literal, _, name}, args}, _context, path),
    do: fail({:unsupported_integer_call, path, {module, name, length(args)}})

  defp decode({:c_apply, _, {:c_var, _, {name, arity}}, _args}, _context, path),
    do: fail({:unsupported_integer_call, path, {:local, name, arity}})

  defp decode({:c_case, _, condition, clauses}, context, path) do
    {comparison, operand, constant} = condition(condition, path)
    yes = boolean_clause(clauses, true, path)
    no = boolean_clause(clauses, false, path)
    if length(clauses) != 2, do: fail({:unsupported_integer_case, path})
    conditional(comparison, operand, constant, yes, no, context, path)
  end

  defp decode(node, _context, path),
    do: fail({:unsupported_integer_expression, path, node_kind(node)})

  defp decode_call(:-, [operand], context, path),
    do: {:binary, :subtract, {:int, 0}, decode(operand, context, path ++ [:operand])}

  defp decode_call(:+, [operand], context, path), do: decode(operand, context, path)

  defp decode_call(name, [left, right], context, path) when is_map_key(@binary, name) do
    {:binary, Map.fetch!(@binary, name), decode(left, context, path ++ [:left]),
     decode(right, context, path ++ [:right])}
  end

  defp decode_call(name, [value, {:c_literal, _, amount}], context, path)
       when name in [:bsl, :bsr] and is_integer(amount) and amount >= 0 do
    operation = if name == :bsl, do: :shift_left, else: :shift_right
    {:unary, operation, amount, decode(value, context, path ++ [:operand])}
  end

  defp decode_call(:band, [value, {:c_literal, _, mask}], context, path)
       when is_integer(mask) and mask >= 0 do
    width = IntegerSize.from_integer(mask + 1).magnitude_bits - 1
    if Integer.pow(2, width) != mask + 1, do: fail({:unsupported_integer_mask, path, mask})
    {:unary, :mask, width, decode(value, context, path ++ [:operand])}
  end

  defp decode_call(:band, [{:c_literal, _, mask}, value], context, path)
       when is_integer(mask) and mask >= 0 do
    decode_call(:band, [value, {:c_literal, [], mask}], context, path)
  end

  defp decode_call(name, args, _context, path),
    do: fail({:unsupported_integer_call, path, {:erlang, name, length(args)}})

  defp condition(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, name},
          [operand, {:c_literal, _, constant}]},
         _path
       )
       when is_map_key(@comparisons, name) and is_integer(constant),
       do: {Map.fetch!(@comparisons, name), operand, constant}

  defp condition(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, name},
          [{:c_literal, _, constant}, operand]},
         _path
       )
       when is_map_key(@comparisons, name) and is_integer(constant) do
    comparison = Map.fetch!(@comparisons, name)
    reverse = %{lt: :gt, le: :ge, eq: :eq, ne: :ne, ge: :le, gt: :lt}
    {Map.fetch!(reverse, comparison), operand, constant}
  end

  defp condition(_node, path), do: fail({:unsupported_integer_condition, path})

  defp boolean_clause(clauses, truth, path) do
    case Enum.find(clauses, fn
           {:c_clause, _, [{:c_literal, _, ^truth}], {:c_literal, _, true}, _} -> true
           _ -> false
         end) do
      {:c_clause, _, _, _, body} -> body
      nil -> fail({:unsupported_integer_case, path})
    end
  end

  defp conditional(comparison, {:c_var, _, name}, constant, yes, no, context, path) do
    {:var, id} = decode({:c_var, [], name}, context, path)

    {:if, comparison, id, constant, decode(yes, context, path ++ [:then]),
     decode(no, context, path ++ [:else])}
  end

  defp conditional(comparison, operand, constant, yes, no, context, path) do
    id = context.next
    branch_context = %{context | next: id + 1}

    {:let, id, decode(operand, context, path ++ [:test]),
     {:if, comparison, id, constant, decode(yes, branch_context, path ++ [:then]),
      decode(no, branch_context, path ++ [:else])}}
  end

  defp analyze(expression, :unreachable, path),
    do: {:unreachable, [row(path, kind(expression), :unreachable)]}

  defp analyze({:int, value}, _environment, path) do
    size = IntegerSize.from_integer(value)
    {size, [row(path, :constant, size)]}
  end

  defp analyze({:var, id}, environment, path) do
    size = Map.fetch!(environment, id)
    {size, [Map.put(row(path, :variable, size), :variable, id)]}
  end

  defp analyze({:let, id, rhs, body}, environment, path) do
    {value, first} = analyze(rhs, environment, path ++ [:binding])
    bound = bind(environment, id, value)
    {result, second} = analyze(body, bound, path ++ [:body])
    {result, first ++ second ++ [Map.put(row(path, :binding, result), :variable, id)]}
  end

  defp analyze({:binary, operation, left, right}, environment, path) do
    {a, first} = analyze(left, environment, path ++ [:left])
    {b, second} = analyze(right, environment, path ++ [:right])
    size = apply(IntegerSize, operation, [a, b])
    {size, first ++ second ++ [Map.put(row(path, operation, size), :operand_sizes, [a, b])]}
  end

  defp analyze({:unary, operation, amount, operand}, environment, path) do
    {value, first} = analyze(operand, environment, path ++ [:operand])
    size = apply(IntegerSize, operation, [value, amount])
    {size, first ++ [Map.put(row(path, operation, size), :operand_sizes, [value])]}
  end

  defp analyze({:if, comparison, id, constant, yes, no}, environment, path) do
    branches =
      for {truth, branch, label} <- [{true, yes, :then}, {false, no, :else}] do
        narrowed = IntegerSize.assume(Map.fetch!(environment, id), comparison, constant, truth)
        state = bind(environment, id, narrowed)
        {size, rows} = analyze(branch, state, path ++ [label])

        condition = %{
          variable: id,
          comparison: comparison,
          constant: constant,
          truth: truth,
          size: narrowed
        }

        {size,
         Enum.map(
           rows,
           &prepend_condition(&1, condition)
         )}
      end

    [{a, first}, {b, second}] = branches
    result = IntegerSize.join(a, b)
    {result, first ++ second ++ [row(path, :join, result)]}
  end

  defp bind(_environment, _id, :unreachable), do: :unreachable
  defp bind(environment, id, size), do: Map.put(environment, id, size)

  defp prepend_condition(row, condition) do
    Map.update(row, :conditions, [condition], fn existing -> [condition | existing] end)
  end

  defp row(path, operation, size), do: %{path: path, operation: operation, size: size}
  defp kind(expression), do: elem(expression, 0)
  defp node_kind(node) when is_tuple(node), do: elem(node, 0)
  defp node_kind(_node), do: :unknown
  defp unknown?(:unreachable), do: false
  defp unknown?(size), do: size.magnitude_bits == :unknown
  defp fail(reason), do: throw({:integer_analysis, reason})

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(candidate) do
    source = """
    open ReductionBounds.IntegerSize ReductionBounds.IntegerAnalysis
    def targetIntegerProgram : Expr := #{expression(candidate.expression)}
    def targetIntegerInputs : State := #{state(candidate.input_sizes)}
    def targetIntegerResult : Domain := #{size(candidate.result_size)}
    theorem targetIntegerSizeCorrect : targetIntegerProgram.infer targetIntegerInputs = targetIntegerResult := by decide
    theorem targetIntegerTraceCorrect : targetIntegerProgram.trace targetIntegerInputs = #{trace(candidate.intermediates)} := by decide
    theorem targetIntegerSizeBound (environment : Env) (precondition : Covers targetIntegerInputs environment) :
        targetIntegerResult.Holds (targetIntegerProgram.eval environment) := by
      rw [← targetIntegerSizeCorrect]
      exact inferSound targetIntegerProgram targetIntegerInputs environment precondition
    """

    %Lynx.Lean{file: "generated_integer_sizes.lean", span: {1, 1}, indentation: 0, source: source}
  end

  defp trace(rows) do
    encoded =
      Enum.map_join(rows, ",\n", fn row ->
        path = Enum.map_join(row.path, ", ", &Integer.to_string(path_index(&1)))
        "([#{path}], #{size(row.size)})"
      end)

    "[#{encoded}]"
  end

  defp path_index(label) when label in [:binding, :left, :operand, :then], do: 0
  defp path_index(label) when label in [:body, :right, :else], do: 1

  defp state(sizes) do
    if :unreachable in sizes do
      "none"
    else
      cases =
        sizes
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {bound, id} -> "| #{id} => #{size(bound)}" end)

      "some (fun index => match index with\n#{cases}\n| _ => .bounded {})"
    end
  end

  @spec size(IntegerSize.t()) :: String.t()
  def size(:unreachable), do: "(.unreachable : Domain)"

  def size(bound),
    do:
      "(.bounded { lower := #{endpoint(bound.lower)}, upper := #{endpoint(bound.upper)}, magnitudeBits := #{bits(bound.magnitude_bits)} } : Domain)"

  defp endpoint(:unbounded), do: "none"
  defp endpoint(value), do: "some (#{value})"
  defp bits(:unknown), do: "none"
  defp bits(value), do: "some #{value}"

  defp expression({:int, value}), do: "(.literal (#{value}))"
  defp expression({:var, id}), do: "(.variable #{id})"

  defp expression({:let, id, rhs, body}),
    do: "(.bind #{id} #{expression(rhs)} #{expression(body)})"

  defp expression({:binary, op, left, right}),
    do: "(.binary .#{binary_name(op)} #{expression(left)} #{expression(right)})"

  defp expression({:unary, op, amount, value}),
    do: "(.unary .#{unary_name(op)} #{amount} #{expression(value)})"

  defp expression({:if, comparison, id, constant, yes, no}),
    do: "(.branch .#{comparison} #{id} (#{constant}) #{expression(yes)} #{expression(no)})"

  defp binary_name(:bit_xor), do: "bitXor"
  defp binary_name(op), do: Atom.to_string(op)
  defp unary_name(:shift_left), do: "shiftLeft"
  defp unary_name(:shift_right), do: "shiftRight"
  defp unary_name(:mask), do: "mask"
end
