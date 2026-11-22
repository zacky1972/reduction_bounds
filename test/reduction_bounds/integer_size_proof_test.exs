defmodule ReductionBounds.IntegerSizeProofTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.IntegerSize

  test "Lean and Elixir agree at signed power-of-two boundaries" do
    checks =
      for width <- [1, 8, 32, 64, 200],
          sign <- [-1, 1],
          offset <- [-1, 0, 1],
          into: "" do
        limit = Integer.pow(2, width)
        value = sign * (limit + offset)
        exact = IntegerSize.from_integer(value)
        width_only = %IntegerSize{magnitude_bits: width}
        expected = offset < 0

        assert IntegerSize.contains?(width_only, value) == expected

        """
        example : Holds #{bounds(exact)} (#{value}) := by decide
        example : contains #{bounds(width_only)} (#{value}) = #{expected} := by decide
        """
      end

    assert [%{module: "Erlang.postlude", status: :ok}] = verify(checks)
  end

  test "Lean checks the semantics and agrees with Elixir on boundary cases" do
    checks =
      for size <- examples(),
          value <- values(),
          into: "" do
        expected = IntegerSize.contains?(size, value)

        """
        example : contains #{bounds(size)} (#{value}) = #{expected} := by decide
        """
      end

    reports = verify(checks <> audit())
    assert [%{module: "Erlang.postlude", status: :ok}] = reports
  end

  test "Lean rejects a nonzero value with a zero magnitude bound" do
    reports = verify("example : Holds { magnitudeBits := some 0 } 1 := by decide")
    assert Enum.any?(reports, &(&1.status == :error))
  end

  test "Lean agrees on normalization, unknown information, and unreachable information" do
    checks =
      for size <- [:unreachable | examples()], into: "" do
        original = domain(size)
        normalized = domain(IntegerSize.normalize(size))

        membership =
          for value <- values(), into: "" do
            expected = IntegerSize.contains?(size, value)
            "example : Domain.contains #{original} (#{value}) = #{expected} := by decide\n"
          end

        "example : Domain.normalize #{original} = #{normalized} := by decide\n" <> membership
      end

    assert [%{module: "Erlang.postlude", status: :ok}] = verify(checks <> audit())
  end

  test "Lean rejects classifying unknown information as unreachable" do
    reports = verify("example : Domain.normalize (.bounded {}) = .unreachable := by decide")
    assert Enum.any?(reports, &(&1.status == :error))
  end

  test "Lean checks constant descriptions and arithmetic transfer results" do
    constants =
      for value <- values(), into: "" do
        size = IntegerSize.from_integer(value)

        """
        example : singleton (#{value}) = #{bounds(size)} := by decide
        """
      end

    checks =
      for operation <- [:add, :subtract, :multiply],
          left <- arithmetic_examples(),
          right <- arithmetic_examples(),
          into: "" do
        result = apply(IntegerSize, operation, [left, right])

        """
        example : Domain.#{operation} #{domain(left)} #{domain(right)} = #{domain(result)} := by decide
        """
      end

    assert [%{module: "Erlang.postlude", status: :ok}] =
             verify(
               "set_option exponentiation.threshold 1024\n" <> constants <> checks <> audit()
             )
  end

  test "Lean rejects forgetting the carry bit and treating unrelated inputs as equal" do
    for source <- [
          "example : Holds { magnitudeBits := some 3 } (7 + 1) := by decide",
          "example : Holds { lower := some 0, upper := some 0 } ((1 : Int) - 3) := by decide"
        ] do
      assert Enum.any?(verify(source), &(&1.status == :error))
    end
  end

  test "Lean agrees on shift and mask transfers and on actual signed bit operations" do
    transfers =
      for size <- [:unreachable | examples()], width <- [0, 1, 4, 64, 200], into: "" do
        shifted = IntegerSize.shift_left(size, width)
        masked = IntegerSize.mask(size, width)

        """
        example : Domain.shiftLeft #{domain(size)} #{width} = #{domain(shifted)} := by decide
        example : Domain.mask #{domain(size)} #{width} = #{domain(masked)} := by decide
        """
      end

    values =
      for value <- values(), width <- [0, 1, 4, 64, 200], into: "" do
        shifted = Bitwise.bsl(value, width)
        masked = Bitwise.band(value, Integer.pow(2, width) - 1)

        """
        example : shiftValue (#{value}) #{width} = (#{shifted}) := by decide
        example : maskValue (#{value}) #{width} = (#{masked}) := by decide
        """
      end

    assert [%{module: "Erlang.postlude", status: :ok}] =
             verify(
               "set_option exponentiation.threshold 1024\n" <> transfers <> values <> audit()
             )
  end

  test "Lean rejects losing shifted bits and retaining a negative value after masking" do
    for source <- [
          "example : Holds { magnitudeBits := some 3 } (shiftValue 7 1) := by decide",
          "example : maskValue (-1) 4 = -1 := by decide"
        ] do
      assert Enum.any?(verify(source), &(&1.status == :error))
    end
  end

  test "Lean agrees on XOR, right shifts, joins, and comparison assumptions" do
    examples = [
      IntegerSize.unknown(),
      :unreachable,
      IntegerSize.from_integer(-1),
      IntegerSize.from_integer(0),
      %IntegerSize{lower: -4, upper: 7, magnitude_bits: 3},
      %IntegerSize{lower: 0},
      %IntegerSize{lower: 2, upper: 1}
    ]

    pairs =
      for left <- examples,
          right <- examples,
          {operation, lean} <- [bit_xor: "bitXor", join: "join"],
          into: "" do
        result = apply(IntegerSize, operation, [left, right])

        "example : Domain.#{lean} #{domain(left)} #{domain(right)} = #{domain(result)} := by decide\n"
      end

    shifts =
      for size <- examples, amount <- [0, 1, 8], into: "" do
        "example : Domain.shiftRight #{domain(size)} #{amount} = #{domain(IntegerSize.shift_right(size, amount))} := by decide\n"
      end

    branches =
      for size <- examples,
          op <- [:lt, :le, :eq, :ne, :ge, :gt],
          constant <- [-1, 0, 8],
          truth <- [true, false],
          into: "" do
        narrowed = IntegerSize.assume(size, op, constant, truth)

        "example : Domain.assume #{domain(size)} .#{op} (#{constant}) #{truth} = #{domain(narrowed)} := by decide\n"
      end

    values =
      for u <- [-8, -1, 0, 7], v <- [-8, -1, 0, 7], into: "" do
        "example : xorValue (#{u}) (#{v}) = (#{Bitwise.bxor(u, v)}) := by decide\n"
      end

    right_values =
      for value <- values(), amount <- [0, 1, 8], into: "" do
        "example : rightValue (#{value}) #{amount} = (#{Bitwise.bsr(value, amount)}) := by decide\n"
      end

    assert [%{status: :ok}] =
             verify(
               "set_option exponentiation.threshold 1024\n" <>
                 pairs <> shifts <> branches <> values <> right_values <> audit()
             )
  end

  defp arithmetic_examples() do
    [
      IntegerSize.unknown(),
      :unreachable,
      %IntegerSize{lower: 2, upper: 1},
      %IntegerSize{magnitude_bits: 0},
      IntegerSize.from_integer(-8),
      IntegerSize.from_integer(7),
      %IntegerSize{lower: -3, upper: 4, magnitude_bits: 3},
      %IntegerSize{lower: 0},
      %IntegerSize{upper: -1},
      %IntegerSize{magnitude_bits: 200}
    ]
  end

  defp domain(:unreachable), do: "(.unreachable : Domain)"
  defp domain(size), do: "(.bounded #{bounds(size)} : Domain)"

  defp examples() do
    [
      %IntegerSize{},
      %IntegerSize{lower: 0},
      %IntegerSize{lower: 3},
      %IntegerSize{lower: 1, magnitude_bits: 0},
      %IntegerSize{upper: -1, magnitude_bits: 0},
      %IntegerSize{upper: -1},
      %IntegerSize{magnitude_bits: 0},
      %IntegerSize{lower: -8, upper: 7, magnitude_bits: 3},
      %IntegerSize{lower: -8, upper: 7, magnitude_bits: 4},
      %IntegerSize{lower: 2, upper: 1},
      %IntegerSize{lower: 8, magnitude_bits: 3},
      %IntegerSize{upper: -8, magnitude_bits: 3},
      %IntegerSize{magnitude_bits: 200},
      %IntegerSize{lower: Integer.pow(2, 200), magnitude_bits: 200}
    ]
  end

  defp values() do
    limit = Integer.pow(2, 200)
    [-limit, -limit + 1, -9, -8, -7, -1, 0, 1, 7, 8, 9, limit - 1, limit]
  end

  defp bounds(size) do
    "({ lower := #{endpoint(size.lower)}, upper := #{endpoint(size.upper)}, " <>
      "magnitudeBits := #{bits(size.magnitude_bits)} } : Bounds)"
  end

  defp endpoint(:unbounded), do: "none"
  defp endpoint(value), do: "some (#{value})"
  defp bits(:unknown), do: "none"
  defp bits(value), do: "some #{value}"

  defp verify(source) do
    path =
      :reduction_bounds
      |> :code.priv_dir()
      |> List.to_string()
      |> Path.join("lean/reduction_bounds/IntegerSize.lean")

    proof = %Lynx.Lean{
      file: "integer_size_checks.lean",
      span: {1, 1},
      indentation: 0,
      source: "open ReductionBounds.IntegerSize\n" <> source
    }

    analysis_path = Path.join(Path.dirname(path), "IntegerAnalysis.lean")

    translation =
      Lynx.Translation.new(
        postludes: [Lynx.Lean.from_file!(path), Lynx.Lean.from_file!(analysis_path), proof]
      )

    project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    Lynx.Commands.verify!(project, Lynx.Translation.assemble(translation, cache: false))
  end

  defp audit() do
    """
    open Lean in
    run_cmd do
      for theoremName in #[``ReductionBounds.IntegerSize.containsCorrect,
          ``ReductionBounds.IntegerSize.unconstrained,
          ``ReductionBounds.IntegerSize.lowerBound,
          ``ReductionBounds.IntegerSize.upperBound,
          ``ReductionBounds.IntegerSize.magnitudeBound,
          ``ReductionBounds.IntegerSize.zeroMagnitude,
          ``ReductionBounds.IntegerSize.reversedRange,
          ``ReductionBounds.IntegerSize.witnessHolds,
          ``ReductionBounds.IntegerSize.domainContainsCorrect,
          ``ReductionBounds.IntegerSize.unknownHolds,
          ``ReductionBounds.IntegerSize.unreachableHolds,
          ``ReductionBounds.IntegerSize.normalizeSound,
          ``ReductionBounds.IntegerSize.normalizeUnreachableIff,
          ``ReductionBounds.IntegerSize.normalizeIdempotent,
          ``ReductionBounds.IntegerSize.unknownNotUnreachable,
          ``ReductionBounds.IntegerSize.magnitudeBitsCorrect,
          ``ReductionBounds.IntegerSize.magnitudeBitsMinimal,
          ``ReductionBounds.IntegerSize.singletonExact,
          ``ReductionBounds.IntegerSize.lowerAddSound,
          ``ReductionBounds.IntegerSize.upperAddSound,
          ``ReductionBounds.IntegerSize.lowerSubtractSound,
          ``ReductionBounds.IntegerSize.upperSubtractSound,
          ``ReductionBounds.IntegerSize.addMagnitudeBound,
          ``ReductionBounds.IntegerSize.addBitsSound,
          ``ReductionBounds.IntegerSize.multiplyMagnitudeBound,
          ``ReductionBounds.IntegerSize.multiplyBitsSound,
          ``ReductionBounds.IntegerSize.boundsAddSound,
          ``ReductionBounds.IntegerSize.boundsSubtractSound,
          ``ReductionBounds.IntegerSize.scaledInterval,
          ``ReductionBounds.IntegerSize.productInterval,
          ``ReductionBounds.IntegerSize.productRangeSound,
          ``ReductionBounds.IntegerSize.zeroValue,
          ``ReductionBounds.IntegerSize.boundsMultiplySound,
          ``ReductionBounds.IntegerSize.binarySound,
          ``ReductionBounds.IntegerSize.addSound,
          ``ReductionBounds.IntegerSize.subtractSound,
          ``ReductionBounds.IntegerSize.multiplySound,
          ``ReductionBounds.IntegerSize.shiftValueMultiply,
          ``ReductionBounds.IntegerSize.lowerShiftSound,
          ``ReductionBounds.IntegerSize.upperShiftSound,
          ``ReductionBounds.IntegerSize.shiftMagnitudeBound,
          ``ReductionBounds.IntegerSize.shiftBitsSound,
          ``ReductionBounds.IntegerSize.boundsShiftLeftSound,
          ``ReductionBounds.IntegerSize.maskRange,
          ``ReductionBounds.IntegerSize.maskResidue,
          ``ReductionBounds.IntegerSize.maskUnique,
          ``ReductionBounds.IntegerSize.maskMagnitudeBound,
          ``ReductionBounds.IntegerSize.maskZeroWidth,
          ``ReductionBounds.IntegerSize.maskInRange,
          ``ReductionBounds.IntegerSize.maskNegativeOne,
          ``ReductionBounds.IntegerSize.maskAfterFullShift,
          ``ReductionBounds.IntegerSize.boundsMaskSound,
          ``ReductionBounds.IntegerSize.unarySound,
          ``ReductionBounds.IntegerSize.shiftLeftSound,
          ``ReductionBounds.IntegerSize.maskSound,
          ``ReductionBounds.IntegerSize.rightMagnitude,
          ``ReductionBounds.IntegerSize.divideMonotone,
          ``ReductionBounds.IntegerSize.boundsShiftRightSound,
          ``ReductionBounds.IntegerSize.xorMagnitude,
          ``ReductionBounds.IntegerSize.boundsXorSound,
          ``ReductionBounds.IntegerSize.shiftRightSound,
          ``ReductionBounds.IntegerSize.xorSound,
          ``ReductionBounds.IntegerSize.boundsJoinLeft,
          ``ReductionBounds.IntegerSize.boundsJoinComm,
          ``ReductionBounds.IntegerSize.joinLeftSound,
          ``ReductionBounds.IntegerSize.joinComm,
          ``ReductionBounds.IntegerSize.joinRightSound,
          ``ReductionBounds.IntegerSize.lowerAtLeastSound,
          ``ReductionBounds.IntegerSize.upperAtMostSound,
          ``ReductionBounds.IntegerSize.boundsAssumeSound,
          ``ReductionBounds.IntegerSize.assumeSound,
          ``ReductionBounds.IntegerAnalysis.inferSound] do
        for dependency in ← Lean.collectAxioms theoremName do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
            throwError m!"Unexpected axiom in {theoremName}: {dependency}"
    """
  end
end
