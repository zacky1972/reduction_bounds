defmodule ReductionBounds.BoundTransferTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{BoundTransfer, CostContract, IntegerSize, ProofInput}
  alias __MODULE__.Fixture

  @moduletag timeout: 120_000

  setup_all do
    source =
      __DIR__
      |> Path.join("../fixtures/integer_cost_programs.ex")
      |> File.read!()
      |> String.replace("ReductionBounds.Fixtures.IntegerCostPrograms", "#{Fixture}")

    [{Fixture, beam}] = Code.compile_string(source)
    on_exit(fn -> unload(Fixture) end)
    %{beam: beam}
  end

  test "rechecks and transfers arithmetic, branches, CRC expressions, and finite recursion", %{
    beam: beam
  } do
    for {name, inputs} <- [
          {:product, [size(-4, 4, 3)]},
          {:guarded, [size(-4, 4, 3)]},
          {:crc_step, [size(0, 255, 8)]},
          {:crc64_step, [size(0, 255, 8)]},
          {:sum, [size(0, 3, 2), IntegerSize.from_integer(0)]}
        ] do
      bound = original(name, inputs, beam)

      assert {:ok, result} =
               ReductionBounds.transfer_integer_bound(bound, contract(:destination, 1),
                 beam_binaries: [beam]
               )

      assert result.upper_bound == bound.upper_bound
      assert result.upper_bound_contract == :source
      assert result.upper_bound_value == result.comparison.budget_values.larger
      assert result.upper_bound_value > result.comparison.budget_values.smaller
      assert result.bound_transfer == :checked
      assert result.source_bound_rechecked
      assert result.comparison_rechecked
      assert result.contract_instantiation == :checked
      assert result.runtime_correspondence == :not_checked
      assert "SourceBound.integerCostSourceBound" in result.checked_theorems
      assert "Comparison.operationOrdering" in result.checked_theorems
      assert "transferredCostChain" in result.checked_theorems
      assert "transferredSourceBound" in result.checked_theorems
      assert "transferredTotal" in result.checked_theorems
      assert Enum.all?(result.reports, &(&1.status == :ok))
    end
  end

  test "retains a recursive size invariant during transfer", %{beam: beam} do
    inputs = [size(0, 3, 2), size(0, 255, 8)]
    invariant = [%IntegerSize{lower: 0, upper: 3}, size(0, 255, 8)]

    bound =
      original(:crc_loop, inputs, beam, recursive_invariant: invariant)

    assert {:ok, result} =
             ReductionBounds.transfer_integer_bound(bound, contract(:destination, 1),
               beam_binaries: [beam]
             )

    assert result.conditions.source.recursive_invariant == invariant
    assert "SourceBound.costInvariants" in result.checked_theorems
  end

  test "checks narrower transfer inputs and rejects a wider input domain", %{beam: beam} do
    bound = original(:product, [size(-4, 4, 3)], beam)
    destination = contract(:destination, 1)

    assert {:ok, result} =
             ReductionBounds.transfer_integer_bound(bound, destination,
               input_sizes: [size(-2, 2, 2)],
               beam_binaries: [beam]
             )

    assert result.input_sizes == [size(-2, 2, 2)]
    assert "transferInputCoverage" in result.checked_theorems

    assert {:error, {:insufficient_transfer_inputs, _, _}} =
             ReductionBounds.transfer_integer_bound(bound, destination,
               input_sizes: [size(-8, 8, 4)],
               beam_binaries: [beam]
             )
  end

  test "requires explicit callee correspondence and supports a shared external model", %{
    beam: beam
  } do
    bound = call_bound(beam)
    destination = contract(:destination, 1, %{absolute: {:argument_bits, :unused}})

    assert {:error, {:unresolved_callee_correspondence, [{:erlang, :abs, 1}]}} =
             ReductionBounds.transfer_integer_bound(bound, destination, beam_binaries: [beam])

    assert {:ok, result} =
             ReductionBounds.transfer_integer_bound(bound, destination,
               callee_correspondence: :shared,
               beam_binaries: [beam]
             )

    assert result.callee_correspondence == :shared_model
    assert result.conditions.source_call_contracts == :assumed
  end

  test "checks a supplied callee value and actual-cost correspondence in Lean", %{beam: beam} do
    bound = call_bound(beam)
    destination = contract(:destination, 1, %{absolute: {:argument_bits, :unused}})

    assert {:ok, result} =
             ReductionBounds.transfer_integer_bound(bound, destination,
               callee_correspondence: callee_proof(1, 2, 0),
               beam_binaries: [beam]
             )

    assert result.callee_correspondence == :checked
    assert "transferCallees" in result.checked_theorems

    for proof <- [callee_proof(9, 1, 0), callee_proof(1, 2, 1)] do
      assert {:error, {:verification_failed, _reports}} =
               ReductionBounds.transfer_integer_bound(bound, destination,
                 callee_correspondence: proof,
                 beam_binaries: [beam]
               )
    end
  end

  test "rechecks a reused callee rather than trusting its recorded proof status", %{beam: beam} do
    helper = original(:helper, [size(0, 4, 3)], beam)

    bound =
      original(:caller, [size(0, 4, 3)], beam, call_contracts: %{{Fixture, :helper, 1} => helper})

    assert {:ok, result} =
             ReductionBounds.transfer_integer_bound(bound, contract(:destination, 1),
               callee_correspondence: :shared,
               beam_binaries: [beam]
             )

    assert "SourceBound.Callee0.integerCostSound" in result.checked_theorems

    changed = put_in(bound.call_contracts[0].checked_bound.upper_bound, 0)

    assert {:error, {:original_bound_mismatch, {Fixture, :helper, 1}, :upper_bound}} =
             ReductionBounds.transfer_integer_bound(changed, contract(:destination, 1),
               callee_correspondence: :shared,
               beam_binaries: [beam]
             )
  end

  test "rejects altered bounds, certificates, and derivations before accepting a transfer", %{
    beam: beam
  } do
    bound = original(:product, [size(-4, 4, 3)], beam)

    for {field, value} <- [
          {:upper_bound, 0},
          {:translation_certificate, "by rfl"},
          {:derivation, %{}}
        ] do
      changed = Map.put(bound, field, value)

      assert {:error, {:original_bound_mismatch, _, ^field}} =
               ReductionBounds.transfer_integer_bound(changed, contract(:destination, 1),
                 beam_binaries: [beam]
               )
    end

    unlabelled = Map.drop(bound, [:checked_theorems, :reports])

    assert {:ok, _result} =
             ReductionBounds.transfer_integer_bound(unlabelled, contract(:destination, 1),
               beam_binaries: [beam]
             )
  end

  test "rejects reverse ordering, symbolic functions, and incompatible units", %{beam: beam} do
    bound = original(:product, [size(-4, 4, 3)], beam)

    assert {:error, {:unresolved_cost_order, _, _, _}} =
             ReductionBounds.transfer_integer_bound(bound, contract(:too_large, 3),
               beam_binaries: [beam]
             )

    assert {:error, {:incompatible_cost_contracts, :cost_unit}} =
             ReductionBounds.transfer_integer_bound(
               bound,
               %{contract(:other, 1) | cost_unit: :other},
               beam_binaries: [beam]
             )

    symbolic = %{bound | cost_contract: %CostContract{}}

    assert {:error, _reason} =
             ReductionBounds.transfer_integer_bound(symbolic, contract(:destination, 1),
               beam_binaries: [beam]
             )

    assert {:error, :invalid_original_bound} =
             ReductionBounds.transfer_integer_bound(%{}, contract(:destination, 1))
  end

  test "Lean rejects a falsified numeric result and changed comparison certificate", %{beam: beam} do
    bound = original(:product, [size(-4, 4, 3)], beam)
    options = [beam_binaries: [beam], max_nodes: 10_000, max_unfolding: 32]

    assert {:ok, candidate, _proof} =
             BoundTransfer.infer(bound, contract(:destination, 1), options)

    assert Enum.any?(verify(%{candidate | upper_bound_value: 0}), &(&1.status == :error))

    changed =
      put_in(
        candidate.comparison.derivations,
        Map.new(candidate.comparison.operations, &{&1, :refl})
      )

    assert Enum.any?(verify(changed), &(&1.status == :error))
  end

  test "rejects a bound when the supplied BEAM has changed", %{beam: _beam} do
    module = __MODULE__.Changed
    on_exit(fn -> unload(module) end)

    [{^module, first}] =
      Code.compile_string(
        "defmodule #{module} do\n @compile :debug_info\n def value(x), do: x + 1\nend"
      )

    assert {:ok, bound} =
             ReductionBounds.infer_integer_cost_bound({module, :value, 1},
               input_sizes: [size(0, 4, 3)],
               cost_contract: contract(:source, 2),
               beam_binaries: [first]
             )

    unload(module)

    [{^module, second}] =
      Code.compile_string(
        "defmodule #{module} do\n @compile :debug_info\n def value(x), do: x + 2\nend"
      )

    assert {:error, {:original_bound_mismatch, _, _}} =
             ReductionBounds.transfer_integer_bound(bound, contract(:destination, 1),
               beam_binaries: [second]
             )
  end

  test "the axiom audit rejects an asserted callee correspondence", %{beam: beam} do
    bound = call_bound(beam)
    proof = callee_proof(1, 2, 0)

    [definitions, _theorem] =
      String.split(proof.source, "theorem transferCalleeAgreement", parts: 2)

    source =
      definitions <>
        """
        axiom transferCalleeAgreement : ReductionBounds.BoundTransfer.ExternalAgreement
          (fun key argument => (SourceBound.costContracts key).input.Holds argument)
          transferExternalA transferExternalB
        """

    assert {:error, {:verification_failed, _reports}} =
             ReductionBounds.transfer_integer_bound(
               bound,
               contract(:destination, 1, %{absolute: {:argument_bits, :unused}}),
               callee_correspondence: %{proof | source: source},
               beam_binaries: [beam]
             )
  end

  defp original(name, inputs, beam, options \\ []) do
    target = {Fixture, name, length(inputs)}

    assert {:ok, bound} =
             ReductionBounds.infer_integer_cost_bound(
               target,
               [input_sizes: inputs, beam_binaries: [beam], cost_contract: contract(:source, 2)] ++
                 options
             )

    bound
  end

  defp call_bound(beam) do
    size = size(0, 4, 3)
    source = contract(:source, 2, %{absolute: {:argument_bits, :unused}})

    assert {:ok, bound} =
             ReductionBounds.infer_integer_cost_bound({Fixture, :opaque, 1},
               input_sizes: [size],
               beam_binaries: [beam],
               cost_contract: source,
               call_contracts: %{
                 {:erlang, :abs, 1} => %{
                   input_size: size,
                   result_size: size,
                   upper_bound: {:cost, :absolute, [3, 0]}
                 }
               }
             )

    bound
  end

  defp contract(id, base, auxiliary \\ %{}) do
    names = CostContract.operations() ++ Map.keys(auxiliary)
    functions = Map.new(names, &{&1, {:add, base, {:max, :left, :right}}})

    {:ok, result} =
      CostContract.new(id: id, functions: functions, auxiliary_parameters: auxiliary)

    result
  end

  defp callee_proof(small, large, difference) do
    %Lynx.Lean{
      file: "transfer_callees.lean",
      span: {1, 1},
      indentation: 0,
      source: """
      def transferExternalA : ReductionBounds.IntegerCost.External := fun _ argument => (argument, #{small})
      def transferExternalB : ReductionBounds.IntegerCost.External := fun _ argument => (argument + #{difference}, #{large})
      theorem transferCalleeAgreement : ReductionBounds.BoundTransfer.ExternalAgreement
          (fun key argument => (SourceBound.costContracts key).input.Holds argument)
          transferExternalA transferExternalB := by
        constructor
        · intro key argument _held; simp [transferExternalA, transferExternalB]
        · intro key argument _held; exact (by decide : #{small} ≤ #{large})
      """
    }
  end

  defp verify(candidate) do
    {proof, _evidence} = ProofInput.audit_bound(BoundTransfer.proof(candidate), candidate)
    {:ok, postludes} = ProofInput.transfer_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    ReductionBounds.Verification.verify!(translation)
  end

  defp size(lower, upper, bits),
    do: %IntegerSize{lower: lower, upper: upper, magnitude_bits: bits}

  defp unload(module) do
    :code.purge(module)
    :code.delete(module)
    :code.purge(module)
  end
end
