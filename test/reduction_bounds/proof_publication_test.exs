defmodule ReductionBounds.ProofPublicationTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.Verification

  @tag timeout: 120_000
  test "independent VMs publish complete checked artifacts atomically" do
    assert {0, _output} =
             Lynx.Commands.lake(Verification.project_dir(), [
               "--quiet",
               "build",
               "Lynx/Lynx.Runner"
             ])

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
            env: [
              {"MIX_ENV", "test"},
              {"ERL_FLAGS", "+S 2:2"},
              {"LEAN_NUM_THREADS", "1"},
              {"REDUCTION_BOUNDS_LEAN_JOBS", "1"}
            ],
            stderr_to_stdout: true
          )
        end,
        max_concurrency: 2,
        timeout: 90_000
      )
      |> Enum.to_list()

    assert length(runs) == 2

    reports =
      Enum.map(runs, fn run ->
        assert {:ok, {output, status}} = run
        assert status == 0, output
        result = publication_reports(output)
        assert Enum.all?(result, &(&1["status"] == "ok"))
        result
      end)

    assert Enum.any?(reports, fn result -> Enum.any?(result, &(not &1["cached"])) end)

    {output, status} =
      System.cmd("mix", ["run", "--no-compile", "-e", expression],
        env: [
          {"MIX_ENV", "test"},
          {"ERL_FLAGS", "+S 2:2"},
          {"LEAN_NUM_THREADS", "1"},
          {"REDUCTION_BOUNDS_LEAN_JOBS", "1"}
        ],
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
    assert result != [], output
    result
  end
end
