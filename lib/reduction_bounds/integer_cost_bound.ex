defmodule ReductionBounds.IntegerCostBound do
  @moduledoc false
  alias ReductionBounds.{IntegerCostSource, IntegerSize, SearchBound}

  @operations [
    :value,
    :variable,
    :binding,
    :comparison,
    :recursive_call,
    :addition,
    :subtraction,
    :multiplication,
    :xor,
    :shift_left,
    :shift_right,
    :mask,
    :static_call
  ]
  @binary %{add: :addition, subtract: :subtraction, multiply: :multiplication, bit_xor: :xor}

  @spec infer(ReductionBounds.target(), keyword()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer(target, options) do
    with {:ok, core} <- SearchBound.core_function(target, options[:beam_binaries]),
         {:ok, candidate} <- infer_core(core, target, options) do
      {:ok, candidate, proof(candidate)}
    end
  end

  @spec infer_core(tuple(), ReductionBounds.target(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def infer_core(core, {_, _, arity} = target, options) do
    inputs = inputs(options[:input_sizes], arity)
    contracts = contracts(options[:call_contracts] || %{})
    keys = Map.new(contracts, fn {key, contract} -> {contract.target, key} end)

    with {:ok, lowered} <- IntegerCostSource.decode(core, target, keys) do
      context = %{
        program: lowered.expr,
        contracts: contracts,
        remaining: options[:max_unfolding] || 32,
        limit: options[:max_nodes] || 10_000,
        nodes: :counters.new(1, []),
        invariant: invariant(options[:recursive_invariant], arity)
      }

      state = state(inputs)
      check_invariant(inputs, context.invariant, [])
      tree = analyze(lowered.expr, state, context, [])
      rows = rows(tree)

      {:ok,
       %{
         target: target,
         source: :integer_cost_fragment,
         metric: :symbolic_size_cost,
         input_sizes: inputs,
         result_size: tree.size,
         upper_bound: tree.budget,
         expression: lowered.expr,
         core_source: lowered.source,
         translation_certificate: lowered.proof,
         derivation: tree,
         call_contracts: contracts,
         intermediates: rows,
         conditions: %{
           input_sizes: inputs,
           recursive_invariant: context.invariant,
           inferred_recursive_inputs:
             for(row <- rows, row.operation == :recursive_call, do: row.argument_sizes),
           cost_functions: :nondecreasing_in_operand_sizes,
           calls: Enum.map(contracts, fn {_key, c} -> Map.drop(c, [:checked_bound]) end)
         },
         unresolved_sizes: Enum.filter(rows, &unknown_size?/1),
         unresolved_contracts: [],
         proof_scope: :reified_core_integer_cost_fragment,
         value_agreement: :checked,
         termination: :finite_derivation_under_call_contracts,
         runtime_correspondence: :not_checked
       }}
    end
  catch
    {:integer_cost, reason} -> {:error, {:integer_cost, target, reason}}
  end

  defp inputs(nil, arity), do: List.duplicate(IntegerSize.unknown(), arity)

  defp inputs(sizes, arity) when is_list(sizes) and length(sizes) == arity,
    do: Enum.map(sizes, &normalize_size/1)

  defp inputs(sizes, arity), do: fail({:invalid_input_sizes, arity, sizes})

  defp normalize_size(size) do
    if IntegerSize.valid?(size),
      do: IntegerSize.normalize(size),
      else: fail({:invalid_integer_size, size})
  end

  defp invariant(nil, _arity), do: nil
  defp invariant(sizes, 2), do: inputs(sizes, 2)
  defp invariant(_sizes, _arity), do: fail(:recursive_invariant_requires_two_arguments)

  defp contracts(values) when is_map(values) do
    values
    |> Enum.sort()
    |> Enum.with_index()
    |> Map.new(fn {{target, value}, key} ->
      {key, contract(target, value)}
    end)
  end

  defp contracts(_values), do: fail(:invalid_call_contracts)

  defp contract(
         {module, name, 1} = target,
         %{source: :integer_cost_fragment, input_sizes: [input]} = checked
       )
       when is_atom(module) and is_atom(name) do
    required = [
      :target,
      :expression,
      :core_source,
      :translation_certificate,
      :derivation,
      :conditions,
      :upper_bound,
      :result_size,
      :call_contracts
    ]

    if !Enum.all?(required, &Map.has_key?(checked, &1)),
      do: fail({:invalid_checked_contract, target})

    if checked.target != target, do: fail({:callee_target_mismatch, target, checked.target})

    %{
      target: target,
      input_size: normalize_size(input),
      result_size: normalize_size(checked.result_size),
      upper_bound: validate_budget(checked.upper_bound),
      origin: :checked_model_bound,
      model_conditions: checked.conditions,
      checked_bound: checked
    }
  end

  defp contract(
         {module, name, 1} = target,
         %{input_size: input, result_size: output, upper_bound: budget}
       )
       when is_atom(module) and is_atom(name) do
    %{
      target: target,
      input_size: normalize_size(input),
      result_size: normalize_size(output),
      upper_bound: validate_budget(budget),
      origin: :user_contract
    }
  end

  defp contract(target, _value), do: fail({:invalid_call_contract, target})

  defp validate_budget(0), do: 0

  defp validate_budget({:cost, name, [a, b]} = budget)
       when is_atom(name) and is_integer(a) and a >= 0 and is_integer(b) and b >= 0,
       do: budget

  defp validate_budget({op, a, b}) when op in [:add, :max],
    do: {op, validate_budget(a), validate_budget(b)}

  defp validate_budget(value), do: fail({:invalid_cost_formula, value})

  defp state(sizes) do
    if :unreachable in sizes,
      do: :unreachable,
      else: sizes |> Enum.with_index() |> Map.new(fn {size, index} -> {index, size} end)
  end

  defp analyze(expr, environment, context, path) do
    :counters.add(context.nodes, 1, 1)

    if :counters.get(context.nodes, 1) > context.limit,
      do: fail({:analysis_node_limit, path, context.limit})

    derive(expr, environment, context, path)
  end

  defp derive(expr, :unreachable, _context, path),
    do: leaf(expr, :unreachable, 0, path, :unreachable)

  defp derive({:int, value} = expr, _environment, _context, path),
    do: leaf(expr, IntegerSize.from_integer(value), cost(:value), path, :value)

  defp derive({:var, id} = expr, environment, _context, path),
    do: leaf(expr, Map.fetch!(environment, id), cost(:variable), path, :variable)

  defp derive({:let, id, rhs, body} = expr, environment, context, path) do
    a = analyze(rhs, environment, context, path ++ [:binding])
    b = analyze(body, bind(environment, id, a.size), context, path ++ [:body])
    branch(expr, b.size, add(add(a.budget, b.budget), cost(:binding)), path, :binding, [a, b])
  end

  defp derive({:binary, op, left, right} = expr, environment, context, path) do
    a = analyze(left, environment, context, path ++ [:left])
    b = analyze(right, environment, context, path ++ [:right])
    widths = [width(a.size, path), width(b.size, path)]
    local = {:cost, Map.fetch!(@binary, op), widths}
    size = apply(IntegerSize, op, [a.size, b.size])
    branch(expr, size, add(add(a.budget, b.budget), local), path, op, [a, b])
  end

  defp derive({:unary, op, amount, argument} = expr, environment, context, path) do
    a = analyze(argument, environment, context, path ++ [:operand])
    local = {:cost, op, [width(a.size, path), amount]}
    size = apply(IntegerSize, op, [a.size, amount])
    branch(expr, size, add(a.budget, local), path, op, [a])
  end

  defp derive({:if, op, id, constant, yes, no} = expr, environment, context, path) do
    original = Map.fetch!(environment, id)
    a_state = bind(environment, id, IntegerSize.assume(original, op, constant, true))
    b_state = bind(environment, id, IntegerSize.assume(original, op, constant, false))
    a = analyze(yes, a_state, context, path ++ [:then])
    b = analyze(no, b_state, context, path ++ [:else])

    local =
      {:cost, :comparison,
       [width(original, path), IntegerSize.from_integer(constant).magnitude_bits]}

    branch(
      expr,
      IntegerSize.join(a.size, b.size),
      add({:max, a.budget, b.budget}, local),
      path,
      :branch,
      [a, b]
    )
    |> Map.put(:test_size, original)
  end

  defp derive({:call, key, argument} = expr, environment, context, path) do
    a = analyze(argument, environment, context, path ++ [:argument])
    contract = Map.fetch!(context.contracts, key)

    if !included?(a.size, contract.input_size),
      do: fail({:call_precondition, path, contract.target, a.size, contract.input_size})

    branch(
      expr,
      contract.result_size,
      add(add(a.budget, contract.upper_bound), cost(:static_call)),
      path,
      :static_call,
      [
        a
      ]
    )
    |> Map.put(:contract_key, key)
  end

  defp derive({:recur, counter, accumulator} = expr, environment, context, path) do
    if context.remaining == 0, do: fail({:unresolved_recursion, path, environment})
    a = analyze(counter, environment, context, path ++ [:counter])
    b = analyze(accumulator, environment, context, path ++ [:accumulator])
    check_invariant([a.size, b.size], context.invariant, path)
    body_context = %{context | remaining: context.remaining - 1}

    body =
      analyze(context.program, state([a.size, b.size]), body_context, path ++ [:recursive_body])

    budget = add(add(add(a.budget, b.budget), body.budget), cost(:recursive_call))

    branch(expr, body.size, budget, path, :recursive_call, [a, b, body])
    |> Map.put(:argument_sizes, [a.size, b.size])
  end

  defp check_invariant(_sizes, nil, _path), do: :ok

  defp check_invariant(sizes, invariant, path) do
    if !(Enum.zip(sizes, invariant) |> Enum.all?(fn {a, b} -> included?(a, b) end)),
      do: fail({:recursive_invariant, path, sizes, invariant})
  end

  @spec included?(IntegerSize.t(), IntegerSize.t()) :: boolean()
  def included?(a, b) do
    case {IntegerSize.normalize(a), IntegerSize.normalize(b)} do
      {:unreachable, _} ->
        true

      {_, :unreachable} ->
        false

      {a, b} ->
        lower_includes?(a.lower, b.lower) and upper_includes?(a.upper, b.upper) and
          bits_include?(a.magnitude_bits, b.magnitude_bits)
    end
  end

  defp lower_includes?(_a, :unbounded), do: true
  defp lower_includes?(:unbounded, _b), do: false
  defp lower_includes?(a, b), do: a >= b
  defp upper_includes?(_a, :unbounded), do: true
  defp upper_includes?(:unbounded, _b), do: false
  defp upper_includes?(a, b), do: a <= b
  defp bits_include?(_a, :unknown), do: true
  defp bits_include?(:unknown, _b), do: false
  defp bits_include?(a, b), do: a <= b

  defp bind(_environment, _id, :unreachable), do: :unreachable
  defp bind(environment, id, size), do: Map.put(environment, id, size)
  defp width(:unreachable, _path), do: 0
  defp width(%IntegerSize{magnitude_bits: width}, _path) when is_integer(width), do: width
  defp width(size, path), do: fail({:unknown_operand_width, path, size})
  defp cost(name), do: {:cost, name, [0, 0]}
  defp add(a, b), do: {:add, a, b}
  defp fail(reason), do: throw({:integer_cost, reason})
  defp leaf(expr, size, budget, path, op), do: branch(expr, size, budget, path, op, [])

  defp branch(expr, size, budget, path, operation, children),
    do: %{
      expr: expr,
      size: size,
      budget: budget,
      path: path,
      operation: operation,
      children: children
    }

  defp unknown_size?(%{size: :unreachable}), do: false
  defp unknown_size?(%{size: %IntegerSize{magnitude_bits: :unknown}}), do: true
  defp unknown_size?(_row), do: false

  defp rows(tree),
    do: Enum.flat_map(tree.children, &rows/1) ++ [Map.drop(tree, [:children, :expr])]

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(candidate) do
    registry = candidate |> cost_names() |> Enum.with_index() |> Map.new()

    %Lynx.Lean{
      file: "generated_integer_cost.lean",
      span: {1, 1},
      indentation: 0,
      source: proof_source(candidate, registry)
    }
  end

  defp proof_source(candidate, registry) do
    contracts = candidate.call_contracts |> Enum.sort()

    contract_code =
      Enum.map_join(contracts, "\n", fn {key, c} ->
        "| #{key} => ⟨#{size(c.input_size)}, #{size(c.result_size)}, #{budget(c.upper_bound, registry)}⟩"
      end)

    call_names =
      Enum.map_join(contracts, "\n", fn {key, c} ->
        {module, name, 1} = c.target

        "| #{key} => some (#{IntegerCostSource.string(Atom.to_string(module))}, #{IntegerCostSource.string(Atom.to_string(name))})"
      end)

    {_, function, _} = candidate.target
    reused = Enum.map_join(contracts, "\n", &reused_proof(&1, registry))
    invariants = invariant_proofs(candidate)

    """
    open ReductionBounds.IntegerSize ReductionBounds.IntegerCost
    open ReductionBounds.IntegerAnalysis (State Env Covers)
    open ReductionBounds.IntegerCostSource (Core Translates Evaluates)
    #{reused}
    def costProgram : Expr := #{expression(candidate.expression)}
    def costInputs : State := #{lean_state(candidate.input_sizes)}
    def costContracts : Contracts := fun key => match key with
    #{contract_code}
    | _ => ⟨.unreachable, .unreachable, .zero⟩
    def costNames : ReductionBounds.IntegerCostSource.Names := fun key => match key with
    #{call_names}
    | _ => none
    theorem costUniqueNames : ReductionBounds.IntegerCostSource.UniqueNames costNames := by
      #{unique_names_proof(length(contracts))}
    def costSource : Core := #{IntegerCostSource.lean(candidate.core_source)}
    def costInvariant : Int → Int → Prop := #{invariant_condition(candidate.conditions.recursive_invariant)}
    def costSummary : Summary := #{summary(candidate.derivation, registry)}
    theorem costTranslation : Translates costNames #{IntegerCostSource.string(Atom.to_string(function))} costSource costProgram :=
      #{candidate.translation_certificate}
    theorem costDerivation : Derives costProgram costContracts costInvariant costInputs costProgram costSummary :=
      #{certificate(candidate.derivation, {registry, candidate.conditions.recursive_invariant})}
    theorem costCandidate : costSummary.size = #{size(candidate.result_size)} ∧
        costSummary.budget = #{budget(candidate.upper_bound, registry)} := by decide
    #{invariants}
    #{reuse_links(contracts)}
    theorem integerCostValueAgreement (charge : Charges) (external : External) (env : Env) (value : Int) :
        Evaluates costSource #{IntegerCostSource.string(Atom.to_string(function))} costNames external costSource env value ↔
          ∃ cost, Runs costProgram charge external costProgram env value cost := by
      constructor
      · intro run
        exact ReductionBounds.IntegerCostSource.sourceComplete costTranslation costUniqueNames costTranslation run charge
      · rintro ⟨cost, run⟩
        exact ReductionBounds.IntegerCostSource.sourceAgreement costTranslation costTranslation run
    theorem integerCostSound (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
        (calls : ContractsHold charge costContracts external) (env : Env) (pre : Covers costInputs env)
        (value : Int) (cost : Nat) (run : Runs costProgram charge external costProgram env value cost) :
        costSummary.size.Holds value ∧ cost ≤ costSummary.budget.eval charge :=
      derivationSound charge external monotone calls costDerivation pre run
    theorem integerCostInvariant (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
        (calls : ContractsHold charge costContracts external) (env : Env) (pre : Covers costInputs env)
        (value : Int) (cost : Nat) (run : Runs costProgram charge external costProgram env value cost) :
        RunInvariant costInvariant run :=
      derivationInvariant charge external monotone calls costDerivation pre run
    theorem integerCostSourceBound (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
        (calls : ContractsHold charge costContracts external) (env : Env) (pre : Covers costInputs env)
        (value : Int) (run : Evaluates costSource #{IntegerCostSource.string(Atom.to_string(function))} costNames external costSource env value) :
        ∃ cost, Runs costProgram charge external costProgram env value cost ∧
          costSummary.size.Holds value ∧ cost ≤ costSummary.budget.eval charge := by
      obtain ⟨cost, execution⟩ := (integerCostValueAgreement charge external env value).mp run
      exact ⟨cost, execution, integerCostSound charge external monotone calls env pre value cost execution⟩
    theorem integerCostTotal (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
        (calls : ContractsHold charge costContracts external) (env : Env) (pre : Covers costInputs env) :
        ∃ value cost, Runs costProgram charge external costProgram env value cost ∧
          Evaluates costSource #{IntegerCostSource.string(Atom.to_string(function))} costNames external costSource env value ∧
          costSummary.size.Holds value ∧ cost ≤ costSummary.budget.eval charge := by
      obtain ⟨value, cost, run⟩ := derivationTerminates charge external monotone calls costDerivation pre
      exact ⟨value, cost, run,
        ReductionBounds.IntegerCostSource.sourceAgreement costTranslation costTranslation run,
        integerCostSound charge external monotone calls env pre value cost run⟩
    """
  end

  defp unique_names_proof(0), do: "intro a b pair ha hb; simp [costNames] at ha"

  defp unique_names_proof(count) do
    "intro a b pair ha hb\n  rcases a with #{natural_cases(count, "a")}\n" <>
      "  all_goals rcases b with #{natural_cases(count, "b")}\n" <>
      "  all_goals simp_all [costNames]\n  all_goals have same := ha.trans hb.symm\n" <>
      "  all_goals exact absurd same (by decide)"
  end

  defp natural_cases(0, rest), do: rest
  defp natural_cases(count, rest), do: "_ | (#{natural_cases(count - 1, rest)})"

  defp reused_proof({key, %{origin: :checked_model_bound, checked_bound: checked}}, registry) do
    "namespace Callee#{key}\n" <> proof_source(checked, registry) <> "\nend Callee#{key}\n"
  end

  defp reused_proof(_contract, _registry), do: ""

  defp reuse_links(contracts) do
    Enum.map_join(contracts, "\n", fn
      {key, %{origin: :checked_model_bound}} ->
        "theorem costReuse#{key} : (costContracts #{key}).output = Callee#{key}.costSummary.size ∧ " <>
          "(costContracts #{key}).budget = Callee#{key}.costSummary.budget := by decide\n"

      _ ->
        ""
    end)
  end

  defp invariant_condition(nil), do: "fun _ _ => True"
  defp invariant_condition([a, b]), do: "fun x y => #{size(a)}.Holds x ∧ #{size(b)}.Holds y"
  defp invariant_call_proof(nil, _a, _b), do: "(by intros; trivial)"

  defp invariant_call_proof([ia, ib], a, b) do
    "(by intro x y hx hy; exact ⟨inclusionSound #{size(a)} #{size(ia)} (by decide) x hx, " <>
      "inclusionSound #{size(b)} #{size(ib)} (by decide) y hy⟩)"
  end

  defp invariant_proofs(%{conditions: %{recursive_invariant: nil}}), do: ""

  defp invariant_proofs(candidate) do
    invariant = candidate.conditions.recursive_invariant
    sets = [candidate.input_sizes | candidate.conditions.inferred_recursive_inputs]

    checks =
      for sizes <- sets,
          {a, b} <- Enum.zip(sizes, invariant),
          do: "included #{size(a)} #{size(b)} = true"

    "theorem costInvariants : #{Enum.join(checks, " ∧ ")} := by decide\n"
  end

  @spec cost_names(map()) :: [atom()]
  def cost_names(candidate) do
    contract_names =
      Enum.flat_map(candidate.call_contracts, fn
        {_key, %{checked_bound: checked} = c} -> names(c.upper_bound) ++ cost_names(checked)
        {_key, c} -> names(c.upper_bound)
      end)

    extras =
      (names(candidate.upper_bound) ++ contract_names)
      |> Enum.uniq()
      |> Enum.reject(&(&1 in @operations))
      |> Enum.sort()

    @operations ++ extras
  end

  defp names(0), do: []
  defp names({:cost, name, _widths}), do: [name]
  defp names({_op, a, b}), do: names(a) ++ names(b)

  @spec evaluate(term(), map()) :: non_neg_integer()
  def evaluate(0, _charges), do: 0
  def evaluate({:cost, name, [a, b]}, charges), do: Map.fetch!(charges, name).(a, b)
  def evaluate({:add, a, b}, charges), do: evaluate(a, charges) + evaluate(b, charges)
  def evaluate({:max, a, b}, charges), do: max(evaluate(a, charges), evaluate(b, charges))

  defp certificate(tree, {registry, _invariant} = context, state \\ "costInputs") do
    "(show Derives costProgram costContracts costInvariant (#{state}) #{expression(tree.expr)} #{summary(tree, registry)} from #{rule(tree, context, state)})"
  end

  defp rule(%{operation: :unreachable}, _registry, _state), do: "(.dead)"
  defp rule(%{expr: {:int, _}}, _registry, _state), do: "(.literal)"
  defp rule(%{expr: {:var, _}}, _registry, _state), do: "(.variable)"

  defp rule(%{expr: {:let, id, _, _}, children: [a, b]}, registry, state) do
    bound = "ReductionBounds.IntegerAnalysis.bindState (#{state}) #{id} #{size(a.size)}"
    "(.bind #{certificate(a, registry, state)} #{certificate(b, registry, bound)})"
  end

  defp rule(%{expr: {:binary, _, _, _}, children: [a, b]}, registry, state),
    do:
      "(.binary #{certificate(a, registry, state)} #{certificate(b, registry, state)} #{width_proof(a.size)} #{width_proof(b.size)})"

  defp rule(%{expr: {:unary, _, _, _}, children: [a]}, registry, state),
    do: "(.unary #{certificate(a, registry, state)} #{width_proof(a.size)})"

  defp rule(
         %{expr: {:if, op, id, constant, _, _}, children: [a, b], test_size: size},
         registry,
         state
       ) do
    left =
      "ReductionBounds.IntegerAnalysis.refineState (#{state}) .#{op} #{id} (#{constant}) true"

    right =
      "ReductionBounds.IntegerAnalysis.refineState (#{state}) .#{op} #{id} (#{constant}) false"

    "(.branch (state := (#{state})) (index := #{id}) (width := #{width(size, [])}) #{width_proof(size)} #{certificate(a, registry, left)} #{certificate(b, registry, right)})"
  end

  defp rule(%{expr: {:call, _, _}, children: [a]}, registry, state),
    do: "(.call #{certificate(a, registry, state)} (inclusionSound _ _ (by decide)))"

  defp rule(
         %{expr: {:recur, _, _}, children: [a, b, body]},
         {_registry, invariant} = context,
         state
       ) do
    arguments = "argumentState #{size(a.size)} #{size(b.size)}"

    "(.recur #{certificate(a, context, state)} #{certificate(b, context, state)} #{certificate(body, context, arguments)} #{invariant_call_proof(invariant, a.size, b.size)})"
  end

  defp width_proof(:unreachable), do: "(by intro value held; exact False.elim held)"

  defp width_proof(%IntegerSize{} = size),
    do: "(knownWidth #{bounds(size)} #{size.magnitude_bits} rfl)"

  defp summary(tree, registry), do: "⟨#{size(tree.size)}, #{budget(tree.budget, registry)}⟩"
  defp budget(0, _registry), do: ".zero"

  defp budget({:cost, name, [a, b]}, registry),
    do: "(.item #{Map.fetch!(registry, name)} #{a} #{b})"

  defp budget({:add, a, b}, registry), do: "(.add #{budget(a, registry)} #{budget(b, registry)})"
  defp budget({:max, a, b}, registry), do: "(.max #{budget(a, registry)} #{budget(b, registry)})"
  defp size(size), do: ReductionBounds.IntegerAnalysis.size(size)

  defp bounds(size),
    do:
      "{ lower := #{endpoint(size.lower)}, upper := #{endpoint(size.upper)}, magnitudeBits := #{bits(size.magnitude_bits)} }"

  defp endpoint(:unbounded), do: "none"
  defp endpoint(value), do: "some (#{value})"
  defp bits(:unknown), do: "none"
  defp bits(value), do: "some #{value}"

  defp lean_state(sizes) do
    if :unreachable in sizes do
      "none"
    else
      cases =
        sizes
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {size, index} -> "| #{index} => #{size(size)}" end)

      "some (fun index => match index with\n#{cases}\n| _ => .bounded {})"
    end
  end

  defp expression({:int, value}), do: "(.literal (#{value}))"
  defp expression({:var, id}), do: "(.variable #{id})"
  defp expression({:let, id, a, b}), do: "(.bind #{id} #{expression(a)} #{expression(b)})"

  defp expression({:binary, op, a, b}),
    do: "(.binary .#{binary(op)} #{expression(a)} #{expression(b)})"

  defp expression({:unary, op, amount, a}),
    do: "(.unary .#{unary(op)} #{amount} #{expression(a)})"

  defp expression({:if, op, id, constant, yes, no}),
    do: "(.branch .#{op} #{id} (#{constant}) #{expression(yes)} #{expression(no)})"

  defp expression({:call, key, a}), do: "(.call #{key} #{expression(a)})"
  defp expression({:recur, a, b}), do: "(.recur #{expression(a)} #{expression(b)})"
  defp binary(:bit_xor), do: "bitXor"
  defp binary(op), do: Atom.to_string(op)
  defp unary(:shift_left), do: "shiftLeft"
  defp unary(:shift_right), do: "shiftRight"
  defp unary(:mask), do: "mask"
end
