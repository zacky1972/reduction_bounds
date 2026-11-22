defmodule ReductionBounds.CostContractTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.CostContract

  doctest CostContract

  test "the default declaration identifies symbolic costs and the supported profile" do
    assert {:ok, contract} = CostContract.new()
    assert contract.id == :symbolic_integer
    assert contract.cost_unit == :symbolic_work
    assert contract.semantics == :core_integer_v1
    assert contract.events == :integer_cost_v1
    assert contract.parameter_domain == :all_natural_pairs
    assert contract.functions == :symbolic

    assert {:error, {:unresolved_cost_function, :addition}} =
             CostContract.evaluate(contract, :addition, [8, 8])
  end

  test "parameter meanings distinguish widths, constant amounts, and local events" do
    {:ok, contract} = CostContract.new()
    parameters = CostContract.parameters(contract)
    assert parameters.addition == {:left_magnitude_bits, :right_magnitude_bits}
    assert parameters.shift_left == {:input_magnitude_bits, :shift_amount}
    assert parameters.shift_right == {:input_magnitude_bits, :shift_amount}
    assert parameters.mask == {:input_magnitude_bits, :mask_width}
    assert parameters.binding == {:unused, :unused}
  end

  test "declarative expressions evaluate on arbitrary precision natural parameters" do
    expr = {:max, {:add, 1, :left}, {:mul, :left, :right}}
    {:ok, contract} = CostContract.new(id: "example", functions: functions(expr))

    for left <- [0, 1, 8, Integer.pow(2, 200)], right <- [0, 1, 9] do
      assert CostContract.evaluate(contract, :multiplication, [left, right]) ==
               {:ok, max(1 + left, left * right)}
    end
  end

  test "negative values, unsupported expressions, and executable functions are rejected" do
    for expr <- [-1, 1.0, :unknown, {:sub, :left, 1}, {:add, 0, -1}, fn x -> x end] do
      assert {:error, {:invalid_cost_function, _name, ^expr}} =
               CostContract.new(functions: functions(expr))
    end
  end

  test "missing or additional function names cannot silently change the registry" do
    registries = [
      %{},
      Map.delete(functions(1), :addition),
      Map.put(functions(1), :other, 1)
    ]

    for declarations <- registries do
      assert {:error, :cost_function_registry_mismatch} =
               CostContract.new(functions: declarations)
    end
  end

  test "auxiliary callee cost names have explicit parameter meanings" do
    declarations = Map.put(functions(1), :absolute, :left)

    assert {:ok, contract} =
             CostContract.new(
               functions: declarations,
               auxiliary_parameters: %{absolute: {:argument_bits, :unused}}
             )

    assert CostContract.parameters(contract).absolute == {:argument_bits, :unused}
    assert CostContract.evaluate(contract, :absolute, [200, 0]) == {:ok, 200}

    assert {:error, {:invalid_auxiliary_parameters, _entry}} =
             CostContract.new(auxiliary_parameters: %{addition: {:other, :other}})

    assert {:error, {:undeclared_cost_operations, [:absolute]}} =
             CostContract.prepare(%CostContract{}, [:addition, :absolute])
  end

  test "default preparation preserves symbolic callee cost names" do
    assert {:ok, contract} = CostContract.prepare(nil, [:value, :absolute])
    assert contract.functions == :symbolic

    assert CostContract.parameters(contract).absolute ==
             {:callee_parameter_1, :callee_parameter_2}
  end

  test "unsupported profiles and invalid labels are rejected even on forged structs" do
    for contract <- [
          %CostContract{semantics: :other},
          %CostContract{events: :other},
          %CostContract{parameter_domain: :bounded},
          %CostContract{id: nil},
          %CostContract{cost_unit: " "},
          %CostContract{auxiliary_parameters: %{other: {"not an atom", :unused}}}
        ] do
      assert {:error, _reason} = CostContract.validate(contract)
    end

    assert {:error, :invalid_contract_options} =
             CostContract.new(runtime_correspondence: :checked)

    assert {:ok, _contract} = CostContract.new(id: :jit)
  end

  test "evaluation validates arguments and operation membership" do
    {:ok, contract} = CostContract.new(functions: functions(1))

    for arguments <- [[-1, 2], [1, -2], [1.0, 2], [1], [1, 2, 3], :unknown] do
      assert {:error, {:invalid_cost_arguments, ^arguments}} =
               CostContract.evaluate(contract, :addition, arguments)
    end

    assert {:error, {:unknown_operation, :missing}} =
             CostContract.evaluate(contract, :missing, [1, 2])
  end

  defp functions(expr), do: Map.new(CostContract.operations(), &{&1, expr})
end
