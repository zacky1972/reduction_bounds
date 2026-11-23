defmodule ReductionBounds.IntegerCostBoundTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.{CostContract, IntegerCostBound, IntegerSize, ProofInput, SearchBound}
  alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Fixture
  @moduletag timeout: 120_000

  setup_all do
    [{Fixture, beam}] =
      Code.compile_file(Path.expand("../fixtures/integer_cost_programs.ex", __DIR__))

    on_exit(fn ->
      :code.purge(Fixture)
      :code.delete(Fixture)
      :code.purge(Fixture)
    end)

    %{beam: beam}
  end

  test "checks size-dependent costs and source agreement for compiled arithmetic", %{beam: beam} do
    assert {:ok, result} = infer(:product, [size(-4, 4, 3)], beam)
    assert result.metric == :symbolic_size_cost
    assert result.value_agreement == :checked
    assert result.runtime_correspondence == :not_checked
    assert result.termination == :finite_derivation_under_call_contracts
    assert "integerCostValueAgreement" in result.checked_theorems
    assert "integerCostSourceBound" in result.checked_theorems

    assert Enum.any?(
             result.intermediates,
             &(&1.operation == :multiply and &1.size.magnitude_bits == 6)
           )

    for x <- -4..4,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :product, [x])))

    assert IntegerCostBound.evaluate(result.upper_bound, charges()) > 0
  end

  test "records the default operation contract without changing symbolic inference", %{beam: beam} do
    assert {:ok, result} = infer(:product, [size(-4, 4, 3)], beam)
    assert result.cost_contract.id == :symbolic_integer
    assert result.cost_contract.functions == :symbolic
    assert result.conditions.operation_cost_contract == :symbolic_integer
    assert result.applicability.input_sizes == result.input_sizes
    assert result.applicability.cost_unit == :symbolic_work
    assert result.applicability.parameters.mask == {:input_magnitude_bits, :mask_width}
    assert result.applicability.contract_instantiation == :not_checked
    assert result.applicability.runtime_correspondence == :not_checked
    assert "integerCostSourceBound" in result.checked_theorems
  end

  test "records a declaration without claiming a checked concrete instance", %{beam: beam} do
    functions = Map.new(CostContract.operations(), &{&1, {:add, 1, {:max, :left, :right}}})
    assert {:ok, contract} = CostContract.new(id: :jit, functions: functions)
    inputs = [size(-4, 4, 3)]
    assert {:ok, original} = infer(:product, inputs, beam)
    assert {:ok, declared} = infer(:product, inputs, beam, cost_contract: contract)
    assert declared.upper_bound == original.upper_bound
    assert declared.result_size == original.result_size
    assert declared.cost_contract == contract
    assert declared.applicability.size_monotonicity == :assumed
    assert declared.applicability.contract_instantiation == :not_checked
    assert declared.runtime_correspondence == :not_checked
    assert "integerCostSourceBound" in declared.checked_theorems
  end

  test "invalid operation declarations report the target and contract diagnostic", %{beam: beam} do
    contract = %ReductionBounds.CostContract{semantics: :other}
    target = {Fixture, :product, 1}

    assert {:error, {:integer_cost, ^target, {:cost_contract, {:unsupported_cost_profile, _}}}} =
             infer(:product, [size(-4, 4, 3)], beam, cost_contract: contract)
  end

  test "retains large CRC intermediates before masking", %{beam: beam} do
    assert {:ok, result} = infer(:crc_step, [size(0, 255, 8)], beam)
    assert result.result_size == size(0, 255, 8)

    assert Enum.any?(
             result.intermediates,
             &(&1.operation == :shift_left and &1.size.magnitude_bits == 16)
           )

    assert Enum.any?(
             result.intermediates,
             &(&1.operation == :bit_xor and &1.size.magnitude_bits == 17)
           )

    for x <- 0..255,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :crc_step, [x])))
  end

  test "checks compiled arithmetic around signed power-of-two boundaries", %{beam: beam} do
    for width <- [1, 32, 64, 200] do
      limit = Integer.pow(2, width)

      for {name, operation, lower, upper} <- [
            {:increment, :addition, limit - 1, limit},
            {:decrement, :subtraction, -limit, -limit + 1}
          ] do
        assert {:ok, result} = infer(name, [size(lower, upper, width + 1)], beam)
        assert "integerCostSourceBound" in result.checked_theorems
        assert result.value_agreement == :checked
        assert result.runtime_correspondence == :not_checked
        assert result.unresolved_sizes == []
        assert {:cost, operation, [width + 1, 1]} in cost_items(result.upper_bound)

        for value <- [lower, upper] do
          actual = apply(Fixture, name, [value])
          assert IntegerSize.contains?(result.result_size, actual)
        end
      end
    end
  end

  test "cancellation preserves the sizes and costs of large signed products", %{beam: beam} do
    value = Integer.pow(2, 200) + 1
    inputs = [IntegerSize.from_integer(-value), IntegerSize.from_integer(value)]

    assert {:ok, result} = infer(:cancel_products, inputs, beam)
    assert result.result_size.lower == 0
    assert result.result_size.upper == 0
    assert apply(Fixture, :cancel_products, [-value, value]) == 0
    assert "integerCostSourceBound" in result.checked_theorems
    assert result.runtime_correspondence == :not_checked

    products = Enum.filter(result.intermediates, &(&1.operation == :multiply))
    assert length(products) == 2

    for product <- products do
      assert product.size.lower == value * value
      assert product.size.upper == value * value
      assert product.size.magnitude_bits == 402
    end

    items = cost_items(result.upper_bound)
    assert Enum.count(items, &(&1 == {:cost, :multiplication, [201, 201]})) == 2
    assert {:cost, :subtraction, [402, 402]} in items

    multiplication = Map.fetch!(charges(), :multiplication)
    budget = IntegerCostBound.evaluate(result.upper_bound, charges())
    assert budget >= 2 * multiplication.(201, 201)
  end

  test "a 64-bit mask preserves wider signed intermediates and their cost items", %{beam: beam} do
    limit = Integer.pow(2, 64)

    assert {:ok, result} = infer(:crc64_step, [size(-limit, limit, 65)], beam)
    assert result.result_size == size(0, limit - 1, 64)
    assert "integerCostSourceBound" in result.checked_theorems
    assert result.runtime_correspondence == :not_checked
    assert result.unresolved_sizes == []

    assert Enum.any?(
             result.intermediates,
             &(&1.operation == :shift_left and &1.size.magnitude_bits == 73)
           )

    assert Enum.any?(
             result.intermediates,
             &(&1.operation == :bit_xor and &1.size.magnitude_bits == 74)
           )

    items = cost_items(result.upper_bound)
    assert {:cost, :shift_left, [65, 8]} in items
    assert {:cost, :xor, [73, 63]} in items
    assert {:cost, :mask, [74, 64]} in items

    for value <- [-limit, -limit + 1, -1, 0, 1, limit - 1, limit] do
      actual = apply(Fixture, :crc64_step, [value])
      assert IntegerSize.contains?(result.result_size, actual)
    end
  end

  test "Lean rejects charging a large product as if its operands had zero width", %{beam: beam} do
    target = {Fixture, :cancel_products, 2}
    value = Integer.pow(2, 200) + 1
    inputs = [IntegerSize.from_integer(-value), IntegerSize.from_integer(value)]
    assert {:ok, core} = SearchBound.core_function(target, [beam])
    assert {:ok, candidate} = IntegerCostBound.infer_core(core, target, input_sizes: inputs)

    wrong_budget = erase_product_widths(candidate.upper_bound)
    assert wrong_budget != candidate.upper_bound
    assert Enum.any?(verify(%{candidate | upper_bound: wrong_budget}), &(&1.status == :error))
  end

  test "checks both Boolean branch orders and unary negation", %{beam: beam} do
    assert {:ok, result} = infer(:guarded, [size(-4, 4, 3)], beam)

    for x <- -4..4,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :guarded, [x])))
  end

  test "uses input, result, and cost contracts for a static call", %{beam: beam} do
    contract = %{
      input_size: size(-4, 4, 3),
      result_size: size(0, 4, 3),
      upper_bound: {:cost, :absolute, [3, 0]}
    }

    assert {:ok, result} =
             infer(:opaque, [size(-4, 4, 3)], beam,
               call_contracts: %{{:erlang, :abs, 1} => contract}
             )

    assert result.result_size == size(0, 4, 3)
    assert result.conditions.calls |> hd() |> Map.fetch!(:origin) == :user_contract
    assert result.cost_contract.functions == :symbolic

    assert result.applicability.parameters.absolute ==
             {:callee_parameter_1, :callee_parameter_2}

    assert result.applicability.call_contracts == result.conditions.calls
  end

  test "rechecks and reuses a derived callee bound", %{beam: beam} do
    input = size(-4, 4, 3)
    assert {:ok, callee} = infer(:helper, [input], beam)

    assert {:ok, caller} =
             infer(:caller, [input], beam, call_contracts: %{{Fixture, :helper, 1} => callee})

    assert "costReuse0" in caller.checked_theorems
    assert "Callee0.costDerivation" in caller.checked_theorems
    assert caller.conditions.calls |> hd() |> Map.fetch!(:origin) == :checked_model_bound

    for x <- -4..4,
        do: assert(IntegerSize.contains?(caller.result_size, apply(Fixture, :caller, [x])))
  end

  test "reuses a checked bound for a local unary call", %{beam: beam} do
    input = size(-4, 4, 3)
    assert {:ok, callee} = infer(:helper, [input], beam)

    assert {:ok, caller} =
             infer(:local_caller, [input], beam,
               call_contracts: %{{Fixture, :helper, 1} => callee}
             )

    assert "costReuse0" in caller.checked_theorems

    for x <- -4..4,
        do: assert(IntegerSize.contains?(caller.result_size, apply(Fixture, :local_caller, [x])))
  end

  test "handles multiple distinct call contracts", %{beam: beam} do
    input = size(-4, 4, 3)
    assert {:ok, callee} = infer(:helper, [input], beam)

    absolute = %{
      input_size: size(-12, 12, 5),
      result_size: size(0, 12, 5),
      upper_bound: {:cost, :absolute, [5, 0]}
    }

    assert {:ok, result} =
             infer(:two_calls, [input], beam,
               call_contracts: %{{Fixture, :helper, 1} => callee, {:erlang, :abs, 1} => absolute}
             )

    assert length(result.conditions.calls) == 2
    assert result.result_size == absolute.result_size
  end

  test "rechecks transitive callee evidence", %{beam: beam} do
    input = size(-4, 4, 3)
    assert {:ok, helper} = infer(:helper, [input], beam)

    assert {:ok, caller} =
             infer(:caller, [input], beam, call_contracts: %{{Fixture, :helper, 1} => helper})

    assert {:ok, result} =
             infer(:grandcaller, [input], beam,
               call_contracts: %{{Fixture, :caller, 1} => caller}
             )

    assert "Callee0.Callee0.costDerivation" in result.checked_theorems

    for x <- -4..4,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :grandcaller, [x])))
  end

  test "reports an unknown contracted output and rejects a mismatched callee target", %{
    beam: beam
  } do
    input = size(-4, 4, 3)

    contract = %{
      input_size: input,
      result_size: IntegerSize.unknown(),
      upper_bound: {:cost, :absolute, [3, 0]}
    }

    assert {:ok, result} =
             infer(:opaque, [input], beam, call_contracts: %{{:erlang, :abs, 1} => contract})

    assert result.unresolved_sizes != []
    assert {:ok, helper} = infer(:helper, [input], beam)

    assert {:error, {:integer_cost, _, {:callee_target_mismatch, _, _}}} =
             infer(:opaque, [input], beam, call_contracts: %{{:erlang, :abs, 1} => helper})
  end

  test "bounds growing accumulator sizes through a complete recursive derivation", %{beam: beam} do
    assert {:ok, result} = infer(:sum, [size(0, 4, 3), IntegerSize.from_integer(0)], beam)
    assert result.result_size.lower == 0
    assert result.result_size.upper == 10
    assert result.result_size.magnitude_bits > 3
    assert length(result.conditions.inferred_recursive_inputs) == 4
    assert "integerCostTotal" in result.checked_theorems

    for n <- 0..4,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :sum, [n, 0])))
  end

  test "checks a supplied recursive invariant at every call", %{beam: beam} do
    invariant = [%IntegerSize{lower: 0, upper: 4}, size(0, 255, 8)]

    assert {:ok, result} =
             infer(:crc_loop, [size(0, 4, 3), size(0, 255, 8)], beam,
               recursive_invariant: invariant
             )

    assert result.conditions.recursive_invariant == invariant
    assert result.applicability.recursive_invariant == invariant

    assert result.applicability.inferred_recursive_inputs ==
             result.conditions.inferred_recursive_inputs

    assert "costInvariants" in result.checked_theorems
    assert result.result_size == size(0, 255, 8)

    for n <- 0..4, acc <- [0, 1, 127, 255] do
      assert IntegerSize.contains?(result.result_size, apply(Fixture, :crc_loop, [n, acc]))
    end
  end

  test "rejects a violated recursive invariant", %{beam: beam} do
    assert {:error, {:integer_cost, _, {:recursive_invariant, _, _, _}}} =
             infer(:sum, [size(0, 4, 3), IntegerSize.from_integer(0)], beam,
               recursive_invariant: [
                 %IntegerSize{lower: 0, upper: 4},
                 IntegerSize.from_integer(0)
               ]
             )
  end

  test "reports unknown operand widths and absent or inapplicable contracts", %{beam: beam} do
    assert {:error, {:integer_cost, _, {:unknown_operand_width, _, _}}} =
             infer(:product, [IntegerSize.unknown()], beam)

    assert {:error, {:integer_cost_source, _, {:missing_call_contract, _, _}}} =
             infer(:opaque, [size(-4, 4, 3)], beam)

    contract = %{input_size: size(0, 4, 3), result_size: size(0, 4, 3), upper_bound: 0}

    assert {:error, {:integer_cost, _, {:call_precondition, _, _, _, _}}} =
             infer(:opaque, [size(-4, 4, 3)], beam,
               call_contracts: %{{:erlang, :abs, 1} => contract}
             )
  end

  test "does not treat an unfolding or node limit as evidence of termination", %{beam: beam} do
    inputs = [size(0, 4, 3), IntegerSize.from_integer(0)]

    assert {:error, {:integer_cost, _, {:unresolved_recursion, _, _}}} =
             infer(:sum, inputs, beam, max_unfolding: 1)

    assert {:error, {:integer_cost, _, {:unresolved_recursion, _, _}}} =
             infer(:forever, inputs, beam, max_unfolding: 2)

    assert {:error, {:integer_cost, _, {:analysis_node_limit, _, 1}}} =
             infer(:sum, inputs, beam, max_nodes: 1)
  end

  test "Lean rejects a wrong result, budget, source operation, or intermediate summary", %{
    beam: beam
  } do
    assert {:ok, core} = SearchBound.core_function({Fixture, :product, 1}, [beam])

    assert {:ok, candidate} =
             IntegerCostBound.infer_core(core, {Fixture, :product, 1},
               input_sizes: [size(-4, 4, 3)]
             )

    {:letOne, id, {:call2, module, _op, a, b}, body} = candidate.core_source
    [first, second] = candidate.derivation.children
    wrong_first = %{first | size: IntegerSize.from_integer(0)}

    for changed <- [
          %{candidate | result_size: IntegerSize.from_integer(0)},
          %{candidate | upper_bound: 0},
          %{candidate | core_source: {:letOne, id, {:call2, module, "+", a, b}, body}},
          %{candidate | derivation: %{candidate.derivation | children: [wrong_first, second]}}
        ] do
      assert Enum.any?(verify(changed), &(&1.status == :error))
    end
  end

  test "Lean rejects hiding a false invariant from the recorded condition list", %{beam: beam} do
    assert {:ok, core} = SearchBound.core_function({Fixture, :sum, 2}, [beam])

    assert {:ok, candidate} =
             IntegerCostBound.infer_core(core, {Fixture, :sum, 2},
               input_sizes: [size(0, 4, 3), IntegerSize.from_integer(0)]
             )

    conditions = %{
      candidate.conditions
      | recursive_invariant: [%IntegerSize{lower: 0, upper: 4}, IntegerSize.from_integer(0)],
        inferred_recursive_inputs: []
    }

    assert Enum.any?(verify(%{candidate | conditions: conditions}), &(&1.status == :error))
  end

  test "Lean rejects falsifying the callee result even when reused", %{beam: beam} do
    assert {:ok, callee} = infer(:helper, [size(-4, 4, 3)], beam)
    wrong = %{callee | result_size: IntegerSize.from_integer(0)}

    assert {:error, _reason} =
             infer(:caller, [size(-4, 4, 3)], beam,
               call_contracts: %{{Fixture, :helper, 1} => wrong}
             )
  end

  defp infer(name, inputs, beam, options \\ []) do
    ReductionBounds.infer_integer_cost_bound(
      {Fixture, name, length(inputs)},
      [beam_binaries: [beam], input_sizes: inputs] ++ options
    )
  end

  defp verify(candidate) do
    {proof, _evidence} = ProofInput.audit_bound(IntegerCostBound.proof(candidate), candidate)
    {:ok, postludes} = ProofInput.integer_cost_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    ReductionBounds.Verification.verify!(translation)
  end

  defp size(lower, upper, bits),
    do: %IntegerSize{lower: lower, upper: upper, magnitude_bits: bits}

  defp cost_items(0), do: []
  defp cost_items({:cost, _, _} = item), do: [item]

  defp cost_items({kind, left, right}) when kind in [:add, :max],
    do: cost_items(left) ++ cost_items(right)

  defp erase_product_widths({:cost, :multiplication, _}),
    do: {:cost, :multiplication, [0, 0]}

  defp erase_product_widths({kind, left, right}) when kind in [:add, :max],
    do: {kind, erase_product_widths(left), erase_product_widths(right)}

  defp erase_product_widths(other), do: other

  defp charges() do
    names = [
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

    Map.new(names, &{&1, fn a, b -> 1 + a + b + a * b end})
  end
end
