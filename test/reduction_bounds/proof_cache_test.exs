defmodule ReductionBounds.ProofCacheTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.{ProofInput, Verification}

  test "different proofs reuse theories, targets reuse checked artifacts, and bypass rechecks" do
    first = input("theorem cachePilotOne : True := by trivial")
    second = input("theorem cachePilotTwo : True := by trivial")
    assert_ok(verify(first))
    reports = verify(second)
    assert_ok(reports)
    assert Enum.all?(Enum.drop(reports, -1), & &1.cached)
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

  test "options and successful theory changes recheck their complete dependent closure" do
    files = assemble(input("theorem cachePilotOptions : True := by trivial"))
    assert_ok(verify(files))
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

  test "invalid and unfinished proofs cannot reuse a warm successful target" do
    assert_ok(verify(input("theorem cachePilotInvalid : True := by trivial")))

    for source <- [
          "theorem cachePilotInvalid : False := by trivial",
          "theorem cachePilotInvalid : False := by sorry"
        ] do
      for _attempt <- 1..2 do
        reports = verify(input(source))
        target = List.last(reports)
        assert target.status == :error
        refute target.cached
        assert Enum.any?(target.diagnostics, &(&1.severity == :error))
      end
    end
  end

  test "a changed failed shared theory invalidates downstream modules and preserves source locations" do
    files = assemble(input("theorem cachePilotDependency : True := by trivial"))
    assert_ok(verify(files))
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

  test "public integer claims, assumptions, and audited theorem names match the embedded path" do
    [{module, beam}] =
      Code.compile_string("""
      defmodule ReductionBounds.ProofCacheTest.Program do
        @compile :debug_info
        def product(x), do: x * x + 1
      end
      """)

    previous = System.get_env("REDUCTION_BOUNDS_PROOF_MODE")

    on_exit(fn ->
      :code.purge(module)
      :code.delete(module)
    end)

    try do
      for function <- [:infer_integer_sizes, :infer_integer_cost_bound] do
        options = [
          beam_binaries: [beam],
          input_sizes: [%ReductionBounds.IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}]
        ]

        System.put_env("REDUCTION_BOUNDS_PROOF_MODE", "embedded")

        assert {:ok, original} =
                 apply(ReductionBounds, function, [{module, :product, 1}, options])

        System.put_env("REDUCTION_BOUNDS_PROOF_MODE", "named")
        assert {:ok, named} = apply(ReductionBounds, function, [{module, :product, 1}, options])
        assert Map.delete(named, :reports) == Map.delete(original, :reports)
        assert Enum.all?(original.reports ++ named.reports, &(&1.status == :ok))
      end
    after
      if previous,
        do: System.put_env("REDUCTION_BOUNDS_PROOF_MODE", previous),
        else: System.delete_env("REDUCTION_BOUNDS_PROOF_MODE")
    end
  end

  defp assemble(input, opts \\ []) do
    Verification.assemble(input, Keyword.merge([cache: true, shared_modules: true], opts))
  end

  defp verify(input, opts \\ []) do
    Verification.verify!(input, Keyword.merge([cache: true, shared_modules: true], opts))
  end

  defp input(source) do
    proof = %Lynx.Lean{source: source, file: "cache_pilot.lean", span: {1, 1}, indentation: 0}
    {:ok, postludes} = ProofInput.integer_postludes(proof)
    Lynx.Translation.new(postludes: postludes)
  end

  defp assert_ok(reports) do
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok))
    assert List.last(reports).module == "Erlang.postlude"
  end
end
