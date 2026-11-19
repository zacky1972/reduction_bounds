defmodule ReductionBounds.IntegerSizeProofTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.IntegerSize

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

    translation = Lynx.Translation.new(postludes: [Lynx.Lean.from_file!(path), proof])
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
          ``ReductionBounds.IntegerSize.multiplySound] do
        for dependency in ← Lean.collectAxioms theoremName do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
            throwError m!"Unexpected axiom in {theoremName}: {dependency}"
    """
  end
end
