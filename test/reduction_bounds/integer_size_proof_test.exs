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

  defp examples do
    [
      %IntegerSize{},
      %IntegerSize{lower: 0},
      %IntegerSize{upper: -1},
      %IntegerSize{magnitude_bits: 0},
      %IntegerSize{lower: -8, upper: 7, magnitude_bits: 3},
      %IntegerSize{lower: -8, upper: 7, magnitude_bits: 4},
      %IntegerSize{lower: 2, upper: 1},
      %IntegerSize{lower: 8, magnitude_bits: 3},
      %IntegerSize{upper: -8, magnitude_bits: 3},
      %IntegerSize{magnitude_bits: 200}
    ]
  end

  defp values do
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

  defp audit do
    """
    open Lean in
    run_cmd do
      for theoremName in #[``ReductionBounds.IntegerSize.containsCorrect,
          ``ReductionBounds.IntegerSize.unconstrained,
          ``ReductionBounds.IntegerSize.lowerBound,
          ``ReductionBounds.IntegerSize.upperBound,
          ``ReductionBounds.IntegerSize.magnitudeBound,
          ``ReductionBounds.IntegerSize.zeroMagnitude,
          ``ReductionBounds.IntegerSize.reversedRange] do
        for dependency in ← Lean.collectAxioms theoremName do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
            throwError m!"Unexpected axiom in {theoremName}: {dependency}"
    """
  end
end
