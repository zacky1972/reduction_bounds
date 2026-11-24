defmodule ReductionBounds.ProofFamiliesTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.{ProofCache, ProofInput, ProofModules, Verification}

  for {family, roots} <- [
        {:core, [:normalize, :execution]},
        {:integer, [:integer_cost_source, :bound_transfer]},
        {:protocol, [:protocol_cost, :port_completion, :port_source]},
        {:lists, [:search, :list_primitives]},
        {:buffer, [:circular_buffer_sequence]}
      ] do
    @roots roots
    test "#{family} theories verify through named, reused, bypassed, and embedded paths" do
      input = family_input(@roots)

      for options <- [
            [cache: true, shared_modules: true],
            [cache: true, shared_modules: true],
            [cache: false, shared_modules: true],
            [cache: false, shared_modules: false]
          ] do
        reports = Verification.verify!(input, options)
        assert reports != []
        assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
        assert List.last(reports).module == "Erlang.postlude"
        if options[:cache] == false, do: refute(Enum.any?(reports, & &1.cached))
      end
    end
  end

  test "concurrent distinct targets compile a cold shared closure once" do
    nonce = Base.encode16(:crypto.strong_rand_bytes(12))
    first = integer_input("theorem preparedFirst : True := by trivial", nonce)
    second = integer_input("theorem preparedSecond : True := by trivial", nonce)

    results =
      [first, second]
      |> Task.async_stream(&Verification.verify!(&1, cache: true, shared_modules: true),
        max_concurrency: 2,
        timeout: 60_000
      )
      |> Enum.map(fn {:ok, reports} -> reports end)

    assert Enum.all?(List.flatten(results), &(&1.status == :ok))

    cold =
      Enum.count(results, fn reports -> Enum.any?(Enum.drop(reports, -1), &(not &1.cached)) end)

    assert cold == 1
    assert Enum.all?(results, &(not List.last(&1).cached))
  end

  @tag :tmp_dir
  test "readiness context changes with compiled dependency identities", %{tmp_dir: dir} do
    path = Path.join(dir, ".lake/build/lib/lean/Model.olean.hash")
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, "original")
    first = ProofCache.preparation_context(dir)
    File.write!(path, "changed")
    refute first == ProofCache.preparation_context(dir)
    File.rm!(path)
    refute first == ProofCache.preparation_context(dir)
  end

  @tag timeout: 120_000
  test "independent VMs publish complete checked artifacts atomically" do
    nonce = Base.encode16(:crypto.strong_rand_bytes(12))

    expression = """
    alias ReductionBounds.{ProofInput, Verification}
    proof = %Lynx.Lean{source: "theorem atomicPublication : True := by trivial", file: "atomic_publication.lean", span: {1, 1}, indentation: 0}
    {:ok, [size | rest]} = ProofInput.integer_postludes(proof)
    size = %{size | source: size.source <> "\\n-- #{nonce}\\n"}
    reports = Verification.verify!(Lynx.Translation.new(postludes: [size | rest]), cache: true, shared_modules: true)
    true = Enum.all?(reports, &(&1.status == :ok))
    IO.puts("proof_reports:" <> JSON.encode!(Enum.map(reports, &Map.take(&1, [:module, :status, :cached]))))
    """

    runs =
      1..2
      |> Task.async_stream(
        fn _ ->
          System.cmd("mix", ["run", "--no-compile", "-e", expression],
            env: [{"MIX_ENV", "test"}, {"ERL_FLAGS", "+S 2:2"}, {"LEAN_NUM_THREADS", "1"}],
            stderr_to_stdout: true
          )
        end,
        max_concurrency: 2,
        timeout: 90_000
      )
      |> Enum.to_list()

    for {:ok, {output, status}} <- runs do
      assert status == 0, output
      assert Enum.all?(publication_reports(output), &(&1["status"] == "ok"))
    end

    assert length(runs) == 2

    {output, status} =
      System.cmd("mix", ["run", "--no-compile", "-e", expression],
        env: [{"MIX_ENV", "test"}, {"ERL_FLAGS", "+S 2:2"}, {"LEAN_NUM_THREADS", "1"}],
        stderr_to_stdout: true
      )

    assert status == 0, output
    assert Enum.all?(publication_reports(output), & &1["cached"])
  end

  defp publication_reports(output) do
    reports =
      for line <- String.split(output, "\n"),
          [_prefix, json] <- [String.split(line, "proof_reports:", parts: 2)],
          do: JSON.decode!(json)

    assert [result] = reports, output
    result
  end

  defp family_input(roots) do
    proof = %Lynx.Lean{
      source: "theorem familySmoke : True := by trivial",
      file: "family_smoke.lean",
      span: {1, 1},
      indentation: 0
    }

    Lynx.Translation.new(postludes: ProofModules.load(roots) ++ [proof])
  end

  defp integer_input(source, nonce) do
    proof = %Lynx.Lean{
      source: source,
      file: "coordinated_target.lean",
      span: {1, 1},
      indentation: 0
    }

    {:ok, [size | rest]} = ProofInput.integer_postludes(proof)
    size = %{size | source: size.source <> "\n-- #{nonce}\n"}
    Lynx.Translation.new(postludes: [size | rest])
  end
end
