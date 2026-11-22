defmodule ReductionBounds.ContractComparisonTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{ContractComparison, CostContract, ProofInput}

  @moduletag timeout: 120_000

  test "Lean checks monotone functions and every composed budget" do
    smaller = contract(:smaller, {:add, 1, {:max, :left, :right}})
    larger = contract(:larger, {:add, 2, {:max, :left, :right}})

    budget =
      {:add, {:cost, :addition, [8, 9]},
       {:max, {:cost, :binding, [0, 0]}, {:cost, :mask, [100, 64]}}}

    assert {:ok, result} = ReductionBounds.compare_cost_contracts(smaller, larger, budget: budget)
    assert result.budget_values == %{smaller: 111, larger: 113}
    assert result.proof_scope == :cost_functions_budgets_and_executions
    assert result.parameter_domain == :all_natural_pairs
    assert result.execution_cost_order == :checked
    assert result.execution_applicability == :not_checked
    assert result.callee_correspondence == :assumed
    assert :callee_actual_cost_order in result.execution_conditions
    assert "executionCostOrdering" in result.checked_theorems
    assert "executionOrderingUnderContracts" in result.checked_theorems
    assert result.bound_transfer == :not_checked
    assert result.runtime_correspondence == :not_checked
    assert "operationOrdering" in result.checked_theorems
    assert "allBudgetOrdering" in result.checked_theorems
    assert "suppliedBudgetValues" in result.checked_theorems
    assert result.reports != []
    assert Enum.all?(result.reports, &(&1.status == :ok))
  end

  test "ordering certificates cover multiplication and structural padding" do
    examples = [
      {0, {:mul, :left, :right}},
      {{:mul, {:add, 1, :left}, :right}, {:mul, {:add, 2, :left}, {:add, 1, :right}}},
      {:left, {:add, 1, :left}},
      {:left, {:max, :left, :right}},
      {:right, {:max, :left, :right}},
      {{:max, 1, :left}, {:max, 2, :left}},
      {{:max, :left, :right}, {:add, {:add, :left, :right}, 1}}
    ]

    for {a, b} <- examples do
      assert {:ok, result} =
               ReductionBounds.compare_cost_contracts(contract(:a, a), contract(:b, b))

      assert result.budget_values == nil
      assert "smallerMonotone" in result.checked_theorems
      assert "largerMonotone" in result.checked_theorems
      assert "allBudgetOrdering" in result.checked_theorems
    end
  end

  test "reflexive comparison and an empty budget are checked" do
    costs = contract(:same, {:add, 1, {:mul, :left, :right}})
    assert {:ok, result} = ReductionBounds.compare_cost_contracts(costs, costs, budget: 0)
    assert result.budget_values == %{smaller: 0, larger: 0}
  end

  test "auxiliary callee budget items use the same declared registry" do
    a = contract(:a, 1, %{absolute: {:argument_bits, :unused}})
    b = contract(:b, 2, %{absolute: {:argument_bits, :unused}})

    assert {:ok, result} =
             ReductionBounds.compare_cost_contracts(a, b, budget: {:cost, :absolute, [200, 0]})

    assert result.budget_values == %{smaller: 1, larger: 2}
    assert :absolute in result.operations
  end

  test "a contract label is not runtime evidence or evidence of equality" do
    a = contract(:jit, 1)
    b = contract(:interpreter, 2)
    assert {:ok, result} = ReductionBounds.compare_cost_contracts(a, b)
    assert result.runtime_correspondence == :not_checked

    assert {:error, {:unresolved_cost_order, _operation, 2, 1}} =
             ReductionBounds.compare_cost_contracts(contract(:same, 2), contract(:same, 1))
  end

  test "an ordering does not authorize its reverse" do
    a = contract(:a, 1)
    b = contract(:b, 2)
    assert {:ok, _result} = ReductionBounds.compare_cost_contracts(a, b)

    assert {:error, {:unresolved_cost_order, _operation, 2, 1}} =
             ReductionBounds.compare_cost_contracts(b, a)
  end

  test "sampled success is insufficient for a universal comparison" do
    a = contract(:a, :left)
    b = contract(:b, 100)
    assert CostContract.evaluate(a, :addition, [100, 0]) == {:ok, 100}
    assert CostContract.evaluate(a, :addition, [101, 0]) == {:ok, 101}

    assert {:error, {:unresolved_cost_order, _operation, :left, 100}} =
             ReductionBounds.compare_cost_contracts(a, b)
  end

  test "unsupported true comparisons remain unresolved rather than declared false" do
    a = contract(:a, {:add, :left, :right})
    b = contract(:b, {:add, :right, :left})

    assert {:error, {:unresolved_cost_order, _, _, _}} =
             ReductionBounds.compare_cost_contracts(a, b)
  end

  test "units, parameter meanings, and unsupported domains are checked" do
    a = contract(:a, 1)
    b = %{contract(:b, 2) | cost_unit: :processor_time}

    assert {:error, {:incompatible_cost_contracts, :cost_unit}} =
             ReductionBounds.compare_cost_contracts(a, b)

    a = contract(:a, 1, %{absolute: {:argument_bits, :unused}})
    b = contract(:b, 2, %{absolute: {:other_meaning, :unused}})

    assert {:error, {:incompatible_cost_contracts, :parameters}} =
             ReductionBounds.compare_cost_contracts(a, b)

    assert {:error, {:invalid_cost_contract, :smaller, {:unsupported_cost_profile, _}}} =
             ReductionBounds.compare_cost_contracts(%{a | parameter_domain: :bounded}, b)
  end

  test "symbolic functions and unsupported budget items are reported" do
    a = contract(:a, 1)

    assert {:error, {:unresolved_cost_functions, :smaller}} =
             ReductionBounds.compare_cost_contracts(%CostContract{}, a)

    assert {:error, {:unresolved_cost_functions, :larger}} =
             ReductionBounds.compare_cost_contracts(a, %CostContract{})

    assert {:error, {:unknown_budget_operation, :missing, _}} =
             ReductionBounds.compare_cost_contracts(a, a, budget: {:cost, :missing, [1, 2]})

    for budget <- [1, :n, {:cost, :addition, [-1, 2]}, {:add, 0, nil}] do
      assert {:error, {:unsupported_cost_budget, _}} =
               ReductionBounds.compare_cost_contracts(a, a, budget: budget)
    end
  end

  test "Lean rejects changed functions or forged ordering certificates" do
    a = contract(:a, 1)
    b = contract(:b, 2)
    assert {:ok, candidate, _proof} = ContractComparison.infer(a, b)
    wrong_functions = %{b | functions: Map.new(b.functions, fn {name, _} -> {name, 0} end)}
    wrong_certificates = Map.new(candidate.derivations, fn {name, _} -> {name, :refl} end)

    for changed <- [
          %{candidate | larger: wrong_functions},
          %{candidate | derivations: wrong_certificates}
        ] do
      assert Enum.any?(verify(changed), &(&1.status == :error))
    end
  end

  test "Lean checks supplied budget evaluations rather than trusting Elixir values" do
    a = contract(:a, {:add, 1, {:mul, :left, :right}})
    b = contract(:b, {:add, 2, {:mul, :left, :right}})
    budget = {:cost, :multiplication, [200, 201]}
    assert {:ok, candidate, _proof} = ContractComparison.infer(a, b, budget)
    assert candidate.budget_values == %{smaller: 40_201, larger: 40_202}
    changed = %{candidate | budget_values: %{smaller: 0, larger: 0}}
    assert Enum.any?(verify(changed), &(&1.status == :error))
  end

  defp contract(id, expression, auxiliary \\ %{}) do
    names = CostContract.operations() ++ Map.keys(auxiliary)
    functions = Map.new(names, &{&1, expression})

    {:ok, contract} =
      CostContract.new(id: id, functions: functions, auxiliary_parameters: auxiliary)

    contract
  end

  defp verify(candidate) do
    {proof, _evidence} = ProofInput.audit_bound(ContractComparison.proof(candidate), candidate)
    {:ok, postludes} = ProofInput.contract_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    Lynx.Commands.verify!(project, Lynx.Translation.assemble(translation, cache: false))
  end
end
