defmodule ReductionBounds.ProofCacheSupport do
  import ExUnit.Assertions
  alias ReductionBounds.{ProofInput, Verification}

  def scenarios, do: [:reuse, :invalidation, :invalid_target, :invalid_shared]

  def run(:reuse, nonce) do
    first = input("theorem cachePilotOne : True := by trivial", nonce)
    second = input("theorem cachePilotTwo : True := by trivial", nonce)
    assert_cold(verify(first))
    reports = verify(second)
    assert_ok(reports)
    assert Enum.all?(Enum.drop(reports, -1), & &1.cached)
    refute List.last(reports).cached
    warm = verify(second)
    assert_ok(warm)
    assert Enum.all?(warm, & &1.cached)
    shared_only = verify(second, cache: :shared)
    assert_ok(shared_only)
    assert Enum.all?(Enum.drop(shared_only, -1), & &1.cached)
    refute List.last(shared_only).cached
    bypassed = verify(second, cache: false)
    assert_ok(bypassed)
    refute Enum.any?(bypassed, & &1.cached)
    embedded = verify(second, shared_modules: false)
    assert_ok(embedded)
    assert length(embedded) == 1
  end

  def run(:invalidation, nonce) do
    files = assemble(input("theorem cachePilotOptions : True := by trivial", nonce))
    assert_cold(verify(files))
    [size | rest] = files
    salt = :binary.decode_unsigned(:crypto.strong_rand_bytes(4))

    changed =
      update_in(
        size,
        ["preludes", Access.at(1), "source"],
        &(&1 <> "\n-- pilot revision #{salt}\n")
      )

    rebuilt = verify([changed | rest])
    assert_ok(rebuilt)
    refute Enum.any?(rebuilt, & &1.cached)
    assert Enum.all?(verify([changed | rest]), & &1.cached)

    options = [maxRecDepth: 10000 + salt]
    fresh_options = verify(files, options: options)
    assert_ok(fresh_options)
    refute Enum.any?(fresh_options, & &1.cached)
    assert Enum.all?(verify(files, options: options), & &1.cached)
  end

  def run(:invalid_target, nonce) do
    assert_cold(verify(input("theorem cachePilotInvalid : True := by trivial", nonce)))

    for source <- [
          "theorem cachePilotInvalid : False := by trivial",
          "theorem cachePilotInvalid : False := by sorry"
        ] do
      for _attempt <- 1..2 do
        reports = verify(input(source, nonce))
        target = List.last(reports)
        assert target.status == :error
        refute target.cached
        assert Enum.any?(target.diagnostics, &(&1.severity == :error))
      end
    end
  end

  def run(:invalid_shared, nonce) do
    files = assemble(input("theorem cachePilotDependency : True := by trivial", nonce))
    assert_cold(verify(files))
    [size | rest] = files

    broken =
      update_in(
        size,
        ["preludes", Access.at(1), "source"],
        &(&1 <> "\ntheorem brokenShared : False := by sorry\n")
      )

    for _attempt <- 1..2 do
      [shared | dependents] = verify([broken | rest])
      assert shared.status == :error
      refute shared.cached
      assert Enum.any?(shared.diagnostics, &(&1.severity == :error and &1.message =~ "sorryAx"))
      assert Enum.all?(dependents, &(&1.status == :skipped and not &1.cached))
    end

    invalid =
      update_in(
        size,
        ["preludes", Access.at(1), "source"],
        &(&1 <> "\n#check missingPilotDeclaration\n")
      )

    [report | _] = verify([invalid | rest])
    assert report.status == :error
    assert Enum.any?(report.diagnostics, &(&1.file == size["file"] and &1.severity == :error))
  end

  defp assemble(input, opts \\ []) do
    Verification.assemble(input, Keyword.merge([cache: true, shared_modules: true], opts))
  end

  defp verify(input, opts \\ []) do
    Verification.verify!(input, Keyword.merge([cache: true, shared_modules: true], opts))
  end

  defp input(source, nonce) do
    proof = %Lynx.Lean{source: source, file: "cache_pilot.lean", span: {1, 1}, indentation: 0}
    {:ok, [size | rest]} = ProofInput.integer_postludes(proof)
    size = %{size | source: size.source <> "\n-- isolated cache scenario #{nonce}\n"}
    Lynx.Translation.new(postludes: [size | rest])
  end

  defp assert_ok(reports) do
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok))
    assert List.last(reports).module == "Erlang.postlude"
  end

  defp assert_cold(reports) do
    assert_ok(reports)
    refute Enum.any?(reports, & &1.cached)
  end
end

defmodule ReductionBounds.ProofCacheTest do
  use ExUnit.Case,
    async: true,
    parameterize:
      for(scenario <- ReductionBounds.ProofCacheSupport.scenarios(), do: %{scenario: scenario})

  @moduletag timeout: 300_000

  setup context do
    :ok = ReductionBounds.TestFixtures.label_scenario(context)
    {:ok, nonce: Base.encode16(:crypto.strong_rand_bytes(12))}
  end

  test "isolated cache policy preserves checked artifacts and rejection", %{
    scenario: scenario,
    nonce: nonce
  } do
    ReductionBounds.ProofCacheSupport.run(scenario, nonce)
  end
end
