defmodule ReductionBounds.ContractComparison do
  @moduledoc false

  alias ReductionBounds.CostContract

  @spec infer(term(), term(), term()) :: {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer(smaller, larger, budget \\ nil) do
    with :ok <- validate(smaller, :smaller),
         :ok <- validate(larger, :larger),
         :ok <- compatible(smaller, larger),
         {:ok, derivations} <- derivations(smaller.functions, larger.functions),
         :ok <- validate_budget(budget, smaller) do
      core = CostContract.execution_operations()
      auxiliary = smaller |> CostContract.parameters() |> Map.keys() |> Enum.reject(&(&1 in core))
      operations = core ++ Enum.sort(auxiliary)

      candidate = %{
        source: :cost_contract_comparison,
        smaller: smaller,
        larger: larger,
        operations: operations,
        derivations: derivations,
        parameter_domain: :all_natural_pairs,
        cost_unit: smaller.cost_unit,
        parameters: CostContract.parameters(smaller),
        budget: budget,
        budget_values: budget_values(budget, smaller, larger),
        proof_scope: :cost_functions_budgets_and_executions,
        compatibility_check: :elixir_validation,
        size_monotonicity: :checked,
        cost_function_order: :checked,
        budget_order: :checked,
        execution_cost_order: :checked,
        execution_applicability: :not_checked,
        callee_correspondence: :assumed,
        execution_conditions: [
          :same_program_and_input,
          :corresponding_charge_events,
          :admitted_call_arguments,
          :callee_value_agreement,
          :callee_actual_cost_order,
          :finite_execution
        ],
        bound_transfer: :not_checked,
        runtime_correspondence: :not_checked
      }

      {:ok, candidate, proof(candidate)}
    end
  end

  defp validate(contract, side) do
    case CostContract.validate(contract) do
      :ok -> :ok
      {:error, reason} -> {:error, {:invalid_cost_contract, side, reason}}
    end
  end

  defp compatible(smaller, larger) do
    fields = [:cost_unit, :semantics, :events, :parameter_domain]

    case Enum.find(fields, &(Map.fetch!(smaller, &1) != Map.fetch!(larger, &1))) do
      nil -> compatible_parameters(smaller, larger)
      field -> {:error, {:incompatible_cost_contracts, field}}
    end
  end

  defp compatible_parameters(smaller, larger) do
    if CostContract.parameters(smaller) == CostContract.parameters(larger),
      do: :ok,
      else: {:error, {:incompatible_cost_contracts, :parameters}}
  end

  defp derivations(:symbolic, _larger), do: {:error, {:unresolved_cost_functions, :smaller}}
  defp derivations(_smaller, :symbolic), do: {:error, {:unresolved_cost_functions, :larger}}

  defp derivations(smaller, larger) do
    smaller
    |> Enum.sort()
    |> Enum.reduce_while({:ok, %{}}, fn {name, expr}, {:ok, proofs} ->
      compare_operation(name, expr, Map.fetch!(larger, name), proofs)
    end)
  end

  defp compare_operation(name, left, right, proofs) do
    case derive(left, right) do
      nil -> {:halt, {:error, {:unresolved_cost_order, name, left, right}}}
      proof -> {:cont, {:ok, Map.put(proofs, name, proof)}}
    end
  end

  defp derive(left, right),
    do: direct(left, right) || through_right(left, right) || through_left(left, right)

  defp direct(expr, expr), do: :refl
  defp direct(0, _expr), do: :zero

  defp direct(left, right) when is_integer(left) and is_integer(right),
    do: if(left <= right, do: :constant)

  defp direct({op, a, b}, {op, c, d}) when op in [:add, :mul, :max],
    do: pair(op, derive(a, c), derive(b, d))

  defp direct(_left, _right), do: nil

  defp through_right(left, {:add, a, b}),
    do: wrap(:add_left, derive(left, a)) || wrap(:add_right, derive(left, b))

  defp through_right(left, {:max, a, b}),
    do: wrap(:max_left, derive(left, a)) || wrap(:max_right, derive(left, b))

  defp through_right(_left, _right), do: nil

  defp through_left({:max, a, b}, right),
    do: pair(:max_cases, derive(a, right), derive(b, right))

  defp through_left(_left, _right), do: nil

  defp pair(_kind, nil, _right), do: nil
  defp pair(_kind, _left, nil), do: nil
  defp pair(kind, left, right), do: {kind, left, right}
  defp wrap(_kind, nil), do: nil
  defp wrap(kind, proof), do: {kind, proof}

  defp validate_budget(nil, _contract), do: :ok
  defp validate_budget(0, _contract), do: :ok

  defp validate_budget({:cost, name, [a, b]} = budget, contract)
       when is_atom(name) and is_integer(a) and a >= 0 and is_integer(b) and b >= 0 do
    if Map.has_key?(CostContract.parameters(contract), name),
      do: :ok,
      else: {:error, {:unknown_budget_operation, name, budget}}
  end

  defp validate_budget({kind, left, right}, contract) when kind in [:add, :max] do
    with :ok <- validate_budget_child(left, contract) do
      validate_budget_child(right, contract)
    end
  end

  defp validate_budget(value, _contract), do: {:error, {:unsupported_cost_budget, value}}

  defp validate_budget_child(nil, _contract), do: {:error, {:unsupported_cost_budget, nil}}
  defp validate_budget_child(value, contract), do: validate_budget(value, contract)

  defp budget_values(nil, _smaller, _larger), do: nil

  defp budget_values(budget, smaller, larger),
    do: %{smaller: evaluate_budget(budget, smaller), larger: evaluate_budget(budget, larger)}

  defp evaluate_budget(0, _contract), do: 0

  defp evaluate_budget({:cost, name, args}, contract) do
    {:ok, value} = CostContract.evaluate(contract, name, args)
    value
  end

  defp evaluate_budget({:add, left, right}, contract),
    do: evaluate_budget(left, contract) + evaluate_budget(right, contract)

  defp evaluate_budget({:max, left, right}, contract),
    do: max(evaluate_budget(left, contract), evaluate_budget(right, contract))

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(candidate) do
    names = candidate.operations
    registry = names |> Enum.with_index() |> Map.new()
    smaller = Enum.map_join(names, ", ", &expression(Map.fetch!(candidate.smaller.functions, &1)))
    larger = Enum.map_join(names, ", ", &expression(Map.fetch!(candidate.larger.functions, &1)))
    certificate = function_certificate(names, candidate.derivations)

    source = """
    open ReductionBounds.CostContract
    def smallerFunctions : List Expr := [#{smaller}]
    def largerFunctions : List Expr := [#{larger}]
    def smallerCharges := charges smallerFunctions
    def largerCharges := charges largerFunctions

    theorem smallerMonotone : ReductionBounds.IntegerCost.MonotoneCharges smallerCharges :=
      functionsMonotone smallerFunctions
    theorem largerMonotone : ReductionBounds.IntegerCost.MonotoneCharges largerCharges :=
      functionsMonotone largerFunctions
    theorem functionCertificate : FunctionsLe smallerFunctions largerFunctions :=
      #{certificate}
    theorem operationOrdering : ChargesLe smallerCharges largerCharges :=
      functionCertificate.sound
    theorem allBudgetOrdering (budget : ReductionBounds.IntegerCost.Budget) :
        budget.eval smallerCharges ≤ budget.eval largerCharges :=
      budgetMonotone budget operationOrdering
    """

    %Lynx.Lean{
      file: "generated_cost_contract_comparison.lean",
      span: {1, 1},
      indentation: 0,
      source: source <> execution_proof() <> budget_proof(candidate, registry)
    }
  end

  defp execution_proof() do
    """
    theorem executionCostOrdering
        {program expr : ReductionBounds.IntegerCost.Expr}
        {externalA externalB : ReductionBounds.IntegerCost.External}
        {admitted : Nat → Int → Prop} {env : ReductionBounds.IntegerAnalysis.Env}
        {valueA valueB : Int} {costA costB : Nat}
        (callees : ReductionBounds.BoundTransfer.ExternalAgreement admitted externalA externalB)
        (runA : ReductionBounds.IntegerCost.Runs program smallerCharges externalA expr env valueA costA)
        (covered : ReductionBounds.BoundTransfer.CallsWithin admitted runA)
        (runB : ReductionBounds.IntegerCost.Runs program largerCharges externalB expr env valueB costB) :
        valueA = valueB ∧ costA ≤ costB :=
      ReductionBounds.BoundTransfer.executionCostLe operationOrdering callees runA covered runB

    theorem executionOrderingUnderContracts
        {program expr : ReductionBounds.IntegerCost.Expr}
        {externalA externalB : ReductionBounds.IntegerCost.External}
        {contracts : ReductionBounds.IntegerCost.Contracts}
        {invariant : Int → Int → Prop} {state : ReductionBounds.IntegerAnalysis.State}
        {summary : ReductionBounds.IntegerCost.Summary}
        {env : ReductionBounds.IntegerAnalysis.Env} {value : Int} {cost : Nat}
        (calls : ReductionBounds.IntegerCost.ContractsHold smallerCharges contracts externalA)
        (callees : ReductionBounds.BoundTransfer.ExternalAgreement
          (fun key argument => (contracts key).input.Holds argument) externalA externalB)
        (derivation : ReductionBounds.IntegerCost.Derives program contracts invariant state expr summary)
        (covered : ReductionBounds.IntegerAnalysis.Covers state env)
        (run : ReductionBounds.IntegerCost.Runs program smallerCharges externalA expr env value cost) :
        ∃ largerCost, ReductionBounds.IntegerCost.Runs program largerCharges externalB expr env value largerCost ∧
          cost ≤ largerCost :=
      ReductionBounds.BoundTransfer.compareUnderContracts operationOrdering smallerMonotone
        calls callees derivation covered run
    """
  end

  defp expression(value) when is_integer(value), do: "(.constant #{value})"
  defp expression(:left), do: ".left"
  defp expression(:right), do: ".right"

  defp expression({op, left, right}),
    do: "(.#{op} #{expression(left)} #{expression(right)})"

  defp function_certificate([], _derivations), do: ".nil"

  defp function_certificate([name | rest], derivations),
    do:
      "(.cons #{certificate(Map.fetch!(derivations, name))} " <>
        "#{function_certificate(rest, derivations)})"

  defp certificate(:refl), do: ".refl"
  defp certificate(:zero), do: ".zero"
  defp certificate(:constant), do: "(.constant (by decide))"

  defp certificate({kind, a, b}) when kind in [:add, :mul, :max],
    do: "(.#{kind} #{certificate(a)} #{certificate(b)})"

  defp certificate({:max_cases, a, b}),
    do: "(.maxCases #{certificate(a)} #{certificate(b)})"

  defp certificate({kind, inner}) do
    constructor = %{
      add_left: "addLeft",
      add_right: "addRight",
      max_left: "maxLeft",
      max_right: "maxRight"
    }

    "(.#{Map.fetch!(constructor, kind)} #{certificate(inner)})"
  end

  defp budget_proof(%{budget: nil}, _registry), do: ""

  defp budget_proof(candidate, registry) do
    """
    def suppliedBudget : ReductionBounds.IntegerCost.Budget :=
      #{budget(candidate.budget, registry)}
    theorem suppliedBudgetValues :
        suppliedBudget.eval smallerCharges = #{candidate.budget_values.smaller} ∧
        suppliedBudget.eval largerCharges = #{candidate.budget_values.larger} := by decide
    theorem suppliedBudgetOrdering :
        suppliedBudget.eval smallerCharges ≤ suppliedBudget.eval largerCharges :=
      allBudgetOrdering suppliedBudget
    """
  end

  defp budget(0, _registry), do: ".zero"

  defp budget({:cost, name, [a, b]}, registry),
    do: "(.item #{Map.fetch!(registry, name)} #{a} #{b})"

  defp budget({kind, a, b}, registry),
    do: "(.#{kind} #{budget(a, registry)} #{budget(b, registry)})"
end
