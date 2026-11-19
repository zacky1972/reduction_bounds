defmodule ReductionBounds.IntegerAnalysisTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.{IntegerAnalysis, IntegerSize}
  alias ReductionBounds.Fixtures.IntegerPrograms, as: Fixture

  setup_all do
    path = Path.expand("../fixtures/integer_programs.ex", __DIR__)
    [{Fixture, beam}] = Code.compile_file(path)

    on_exit(fn ->
      :code.purge(Fixture)
      :code.delete(Fixture)
      :code.purge(Fixture)
    end)

    %{beam: beam}
  end

  test "checks compiled bindings, comparison refinement, and branch joins", %{beam: beam} do
    input = %IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}

    assert {:ok, result} =
             ReductionBounds.infer_integer_sizes({Fixture, :conditional, 1},
               beam_binaries: [beam],
               input_sizes: [input]
             )

    assert result.result_size == %IntegerSize{lower: -7, upper: 13, magnitude_bits: 6}
    assert result.proof_scope == :reified_integer_fragment
    assert result.value_agreement == :not_checked
    assert result.cost_model == :not_analyzed
    assert result.unresolved_sizes == []
    assert "targetIntegerSizeBound" in result.checked_theorems
    assert [%{status: :ok}] = result.reports

    for x <- -2..4,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :conditional, [x])))

    conditions = Enum.flat_map(result.intermediates, &Map.get(&1, :conditions, []))
    assert Enum.any?(conditions, &(&1.truth and &1.size.upper == -1))
    assert Enum.any?(conditions, &(not &1.truth and &1.size.lower == 0))
  end

  test "tracks large intermediate sizes before a CRC-style mask", %{beam: beam} do
    input = %IntegerSize{lower: 0, upper: 255, magnitude_bits: 8}

    assert {:ok, result} =
             ReductionBounds.infer_integer_sizes({Fixture, :crc_step, 1},
               beam_binaries: [beam],
               input_sizes: [input]
             )

    assert result.result_size == %IntegerSize{lower: 0, upper: 255, magnitude_bits: 8}

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

  test "checks right shifts and prunes unreachable branches", %{beam: beam} do
    assert {:ok, right} =
             ReductionBounds.infer_integer_sizes({Fixture, :right, 1},
               beam_binaries: [beam],
               input_sizes: [%IntegerSize{lower: -64, upper: 63, magnitude_bits: 7}]
             )

    assert right.result_size == %IntegerSize{lower: -8, upper: 7, magnitude_bits: 7}

    assert {:ok, result} =
             ReductionBounds.infer_integer_sizes({Fixture, :impossible, 1},
               beam_binaries: [beam],
               input_sizes: [%IntegerSize{lower: 0, upper: 4}]
             )

    assert result.result_size.lower == 1
    assert result.result_size.upper == 5
    assert Enum.any?(result.intermediates, &(&1.size == :unreachable))
    assert result.unresolved_sizes != []
  end

  test "new bindings replace earlier information", %{beam: beam} do
    assert {:ok, result} =
             ReductionBounds.infer_integer_sizes({Fixture, :rebinding, 1},
               beam_binaries: [beam],
               input_sizes: [%IntegerSize{lower: -2, upper: 2, magnitude_bits: 2}]
             )

    assert result.result_size.lower == 2
    assert result.result_size.upper == 3

    for x <- -2..2,
        do: assert(IntegerSize.contains?(result.result_size, apply(Fixture, :rebinding, [x])))
  end

  test "handles reversed comparisons, expression tests, and argument order", %{beam: beam} do
    input = %IntegerSize{lower: -2, upper: 2, magnitude_bits: 2}

    for name <- [:reversed, :expression_test] do
      assert {:ok, result} =
               ReductionBounds.infer_integer_sizes({Fixture, name, 1},
                 beam_binaries: [beam],
                 input_sizes: [input]
               )

      for x <- -2..2 do
        assert IntegerSize.contains?(result.result_size, apply(Fixture, name, [x]))
      end
    end

    assert {:ok, pair} =
             ReductionBounds.infer_integer_sizes({Fixture, :pair, 2},
               beam_binaries: [beam],
               input_sizes: [IntegerSize.from_integer(2), IntegerSize.from_integer(-3)]
             )

    assert pair.result_size.lower == -1
    assert pair.result_size.upper == -1

    assert {:ok, constant} =
             ReductionBounds.infer_integer_sizes({Fixture, :no_args, 0},
               beam_binaries: [beam],
               input_sizes: []
             )

    assert constant.result_size == IntegerSize.from_integer(42)
  end

  test "an impossible input domain remains unreachable even for a constant", %{beam: beam} do
    assert {:ok, result} =
             ReductionBounds.infer_integer_sizes({Fixture, :constant, 1},
               beam_binaries: [beam],
               input_sizes: [:unreachable]
             )

    assert result.result_size == :unreachable
    assert result.unresolved_sizes == []
  end

  test "reports input contracts and unsupported operations with target and location", %{
    beam: beam
  } do
    for {name, arity} <- [unsupported: 1, unsupported_mask: 1, dynamic_shift: 2, recursive: 1] do
      target = {Fixture, name, arity}

      assert {:error, {:integer_analysis, ^target, _diagnostic}} =
               ReductionBounds.infer_integer_sizes(target, beam_binaries: [beam])
    end

    target = {Fixture, :conditional, 1}

    assert {:error, {:integer_analysis, ^target, {:invalid_input_sizes, ^target, 1, []}}} =
             ReductionBounds.infer_integer_sizes(target, beam_binaries: [beam], input_sizes: [])
  end

  test "Lean rejects a falsified result or intermediate size", %{beam: beam} do
    target = {Fixture, :conditional, 1}

    assert {:ok, candidate, _proof} =
             IntegerAnalysis.infer(target, [beam], [
               %IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}
             ])

    [first | rest] = candidate.intermediates
    false_trace = [%{first | size: :unreachable} | rest]

    for falsified <- [
          %{candidate | result_size: IntegerSize.from_integer(0)},
          %{candidate | intermediates: false_trace}
        ] do
      proof = IntegerAnalysis.proof(falsified)
      assert {:ok, postludes} = ReductionBounds.ProofInput.integer_postludes(proof)
      translation = Lynx.Translation.new(postludes: postludes)
      project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")

      reports =
        Lynx.Commands.verify!(project, Lynx.Translation.assemble(translation, cache: false))

      assert Enum.any?(reports, &(&1.status == :error))
    end
  end
end
