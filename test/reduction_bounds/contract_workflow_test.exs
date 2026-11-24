defmodule ReductionBounds.ContractWorkflowSupport do
  import ExUnit.Assertions
  alias ReductionBounds.{CostContract, IntegerSize}
  alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Programs
  alias ReductionBounds.Fixtures.IntegerCostCases, as: Cases

  def examples do
    [
      {Programs, :product, [size(-4, 4, 3)]},
      {Programs, :guarded, [size(-4, 4, 3)]},
      {Programs, :sum, [size(0, 3, 2), IntegerSize.from_integer(0)]},
      {Cases, :variance_numerator, [size(0, 3, 2), size(0, 9, 4), size(0, 3, 2)]},
      {Cases, :crc64_update, [size(0, 255, 8), size(0, 255, 8)]},
      {Cases, :crc64_reflected_index, [size(0, Integer.pow(2, 64) - 1, 64), size(0, 255, 8)]}
    ]
  end

  def assert_workflow(program, beams) do
    source = contract(:source, 2)
    destination = contract(:destination, 1)
    {module, name, inputs} = Enum.find(examples(), fn {_, name, _} -> name == program end)
    target = {module, name, length(inputs)}

    assert {:ok, original} =
             ReductionBounds.infer_integer_cost_bound(target,
               input_sizes: inputs,
               cost_contract: source,
               beam_binaries: beams
             )

    assert {:ok, comparison} =
             ReductionBounds.compare_cost_contracts(destination, source,
               budget: original.upper_bound
             )

    assert comparison.verification_scope.contracts == %{smaller: :destination, larger: :source}
    assert :conditional_execution_order in comparison.verification_scope.checked
    assert :target_applicability in comparison.verification_scope.unverified
    conditions = comparison.verification_scope.assumptions.execution_conditions
    assert :callee_value_agreement in conditions
    assert comparison.bound_transfer == :not_checked

    assert {:ok, transferred} =
             ReductionBounds.transfer_integer_bound(original, destination, beam_binaries: beams)

    scope = transferred.verification_scope
    assert scope.contracts == %{from: :source, to: :destination}
    assert :bound_transfer in scope.checked
    assert :termination_under_source_call_contracts in scope.checked
    assert :wall_clock_time in scope.unverified
    assert :runtime_correspondence in scope.unverified
    assert scope.assumptions.source_call_contracts == []
    assert transferred.upper_bound_value == comparison.budget_values.larger
    assert transferred.upper_bound_value >= comparison.budget_values.smaller
    assert transferred.upper_bound == original.upper_bound
    assert transferred.upper_bound_contract == :source
    assert transferred.runtime_correspondence == :not_checked
    assert "transferredCostChain" in transferred.checked_theorems
    assert "transferredTotal" in transferred.checked_theorems
    report(name, transferred)
  end

  def contract(id, base) do
    expression = {:add, base, {:mul, :left, :right}}
    functions = Map.new(CostContract.operations(), &{&1, expression})
    {:ok, result} = CostContract.new(id: id, functions: functions)
    result
  end

  def size(lower, upper, bits),
    do: %IntegerSize{lower: lower, upper: upper, magnitude_bits: bits}

  def report(name, result) do
    if System.get_env("REDUCTION_BOUNDS_REPORT") == "1" do
      snapshot =
        Map.take(result, [
          :target,
          :input_sizes,
          :source_contract,
          :destination_contract,
          :upper_bound,
          :upper_bound_contract,
          :upper_bound_value,
          :verification_scope,
          :checked_theorems
        ])

      IO.inspect(snapshot,
        label: "#{name}",
        pretty: true,
        limit: :infinity,
        printable_limit: :infinity
      )
    end
  end
end

defmodule ReductionBounds.ContractWorkflowTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.CostContract
  alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Programs
  import ReductionBounds.ContractWorkflowSupport, only: [contract: 2, size: 3, report: 2]

  @moduletag :cost_contract_workflow
  @moduletag timeout: 300_000

  setup_all do
    %{beams: ReductionBounds.TestFixtures.integer_cost_beams()}
  end

  test "call contracts remain visible in the public transfer report", %{beams: beams} do
    source = contract(:source, 2)
    destination = contract(:destination, 1)
    inputs = [size(0, 4, 3)]

    assert {:ok, helper} =
             ReductionBounds.infer_integer_cost_bound({Programs, :helper, 1},
               input_sizes: inputs,
               cost_contract: source,
               beam_binaries: beams
             )

    assert {:ok, original} =
             ReductionBounds.infer_integer_cost_bound({Programs, :caller, 1},
               input_sizes: inputs,
               cost_contract: source,
               call_contracts: %{{Programs, :helper, 1} => helper},
               beam_binaries: beams
             )

    assert {:error, {:unresolved_callee_correspondence, [{Programs, :helper, 1}]}} =
             ReductionBounds.transfer_integer_bound(original, destination, beam_binaries: beams)

    assert {:ok, transferred} =
             ReductionBounds.transfer_integer_bound(original, destination,
               callee_correspondence: :shared,
               beam_binaries: beams
             )

    assert transferred.verification_scope.assumptions.callee_models == :shared_external_model
    assert [_call] = transferred.verification_scope.assumptions.source_call_contracts
    assert "SourceBound.Callee0.integerCostSound" in transferred.checked_theorems
    report(:contracted_call, transferred)
  end

  test "unknown and invalid public options are reported before proof generation" do
    source = contract(:source, 2)
    destination = contract(:destination, 1)

    assert {:error, {:unknown_options, [:unexpected]}} =
             ReductionBounds.compare_cost_contracts(destination, source, unexpected: true)

    assert {:error, {:unknown_options, [:beam_binaries]}} =
             ReductionBounds.compare_cost_contracts(destination, source, beam_binaries: [])

    assert {:error, {:unknown_options, [:unexpected]}} =
             ReductionBounds.transfer_integer_bound(%{}, destination, unexpected: true)

    assert {:error, {:invalid_option, :timeout, -1}} =
             ReductionBounds.compare_cost_contracts(destination, source, timeout: -1)

    assert {:error, {:invalid_option, :max_nodes, 0}} =
             ReductionBounds.transfer_integer_bound(%{}, destination, max_nodes: 0)

    assert {:error, {:invalid_option, :callee_correspondence, :assumed}} =
             ReductionBounds.transfer_integer_bound(%{}, destination,
               callee_correspondence: :assumed
             )

    assert {:error, :invalid_options} =
             ReductionBounds.compare_cost_contracts(destination, source, :invalid)
  end

  test "missing callee contracts and insufficient call inputs remain errors", %{beams: beams} do
    target = {Programs, :caller, 1}
    callee = {Programs, :helper, 1}

    options = [
      input_sizes: [size(0, 4, 3)],
      cost_contract: contract(:source, 2),
      beam_binaries: beams
    ]

    assert {:error, {:integer_cost_source, ^target, {:missing_call_contract, _path, ^callee}}} =
             ReductionBounds.infer_integer_cost_bound(target, options)

    call = %{
      input_size: size(0, 1, 1),
      result_size: size(0, 3, 2),
      upper_bound: {:cost, :value, [0, 0]}
    }

    assert {:error,
            {:integer_cost, ^target, {:call_precondition, _path, ^callee, _actual, _required}}} =
             ReductionBounds.infer_integer_cost_bound(
               target,
               options ++ [call_contracts: %{callee => call}]
             )
  end

  test "unsupported profiles, registries, and unproved orderings have explicit diagnostics" do
    source = contract(:source, 2)
    destination = contract(:destination, 1)

    for field <- [:semantics, :events, :parameter_domain] do
      invalid = Map.put(source, field, :unsupported)

      assert {:error, {:invalid_cost_contract, :larger, _reason}} =
               ReductionBounds.compare_cost_contracts(destination, invalid)
    end

    assert {:error, {:incompatible_cost_contracts, :cost_unit}} =
             ReductionBounds.compare_cost_contracts(destination, %{source | cost_unit: :other})

    assert {:error, {:unresolved_cost_order, _operation, _left, _right}} =
             ReductionBounds.compare_cost_contracts(source, destination)

    assert {:error, {:unresolved_cost_functions, :larger}} =
             ReductionBounds.compare_cost_contracts(destination, %CostContract{})

    assert {:error, {:invalid_cost_contract, :larger, _reason}} =
             ReductionBounds.compare_cost_contracts(destination, %{
               source
               | functions: Map.delete(source.functions, :addition)
             })
  end
end

defmodule ReductionBounds.ContractWorkflowScenarioTest do
  use ExUnit.Case,
    async: true,
    parameterize:
      for(
        {_module, name, _inputs} <- ReductionBounds.ContractWorkflowSupport.examples(),
        do: %{program: name}
      )

  @moduletag :cost_contract_workflow
  @moduletag timeout: 300_000
  setup :label_scenario

  defp label_scenario(context), do: ReductionBounds.TestFixtures.label_scenario(context)

  test "public workflows report checked bounds and their assumptions", %{program: program} do
    ReductionBounds.ContractWorkflowSupport.assert_workflow(
      program,
      ReductionBounds.TestFixtures.integer_cost_beams()
    )
  end
end
