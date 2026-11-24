defmodule ReductionBounds.RpcCompletionProofTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_completion
  @moduletag timeout: 300_000
  alias ReductionBounds.{ProofInput, ProofCache, RpcCompletionProof, Verification}
  import ReductionBounds.MailboxSupport
  import ReductionBounds.RpcCostSupport, only: [cost_profile: 0]

  defp progress, do: [:client_progress, :request_progress, :server_progress, :response_progress]

  test "Lean proves successful completion and active bounds without any cost profile" do
    {:ok, c, proof} =
      RpcCompletionProof.build(profile(), [], success(),
        goal: :success,
        progress: progress() ++ [:no_failure_outcomes]
      )

    assert_ok(reports(proof))
    refute Map.has_key?(c, :upper_bounds)
    assert "ReductionBounds.RpcCompletion.suppliedSuccessfulCompletion" in c.checked_theorems
    assert c.lean_status == :not_checked
  end

  test "Lean connects completion moves to mailbox search, retained messages and terminal outcomes" do
    down = {:tuple5, {:atom, "DOWN"}, {:ref, 9}, {:atom, "process"}, {:pid, 2}, {:atom, "gone"}}

    for {p, queue, timeline} <- [
          {profile(), [{:atom, "old"}],
           sent() ++
             [:inspect] ++
             server() ++
             [{:arrive, reply()}, :inspect, {:protocol, :process_reply}]},
          {profile(), [{:atom, "old"}],
           sent() ++ [:inspect, :timeout, {:protocol, :handle_timeout}, {:arrive, reply()}]},
          {profile(monitor_id: 9), [],
           [{:protocol, :monitor_peer}] ++ sent() ++ [{:arrive, down}, :inspect]},
          {profile(), [], Enum.drop(success(), -1) ++ [{:protocol, :decode_error}]},
          {profile(timeout: :infinity), [], sent()}
        ] do
      {:ok, _, proof} = RpcCompletionProof.build(p, queue, timeline, progress: progress())
      assert_ok(reports(proof))
    end
  end

  test "cost safety remains verifiable without progress and a stalled execution cannot finish" do
    {:ok, c, proof} = RpcCompletionProof.build_with_cost(cost_profile(), [], sent())
    assert c.completion.status == :insufficient_assumptions
    assert_ok(reports(proof, cost: true))
    assert proof.source =~ "suppliedPendingCounterexample"
    refute proof.source =~ "theorem suppliedConditionalCompletion"
  end

  test "a replayed handler proof does not supply response progress" do
    alias ReductionBounds.{CostContract, IntegerCostBound, IntegerSize, RpcServerContract}
    alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Fixture
    {Fixture, beam} = ReductionBounds.TestFixtures.integer_cost_programs()
    functions = Map.new(CostContract.operations(), &{&1, 1})

    {:ok, contract} =
      CostContract.new(id: :completion_server, cost_unit: :server_work, functions: functions)

    {:ok, bound, _} =
      IntegerCostBound.infer({Fixture, :increment, 1},
        input_sizes: [IntegerSize.from_integer(5)],
        cost_contract: contract,
        beam_binaries: [beam]
      )

    {:ok, reuse} =
      RpcServerContract.reuse(bound, ReductionBounds.RpcCostSupport.frame(),
        beam_binaries: [beam]
      )

    cp = ReductionBounds.RpcCostSupport.cost_profile(server: reuse)

    {:ok, c, proof} =
      RpcCompletionProof.build_with_cost(cp, [], sent(),
        progress: progress() -- [:response_progress]
      )

    assert c.completion.status == :insufficient_assumptions
    assert c.completion.missing_assumptions == [:response_progress]
    assert c.server_contract.status == :replay_pending
    assert "RpcHandler.replayedCostSafety" in c.checked_theorems
    refute "ReductionBounds.RpcCompletion.suppliedConditionalCompletion" in c.checked_theorems
    assert_ok(reports(proof, cost: true, handler: :replay))
  end

  test "Lean rejects altered action budgets, semantic agreement and missing progress premises" do
    {:ok, _, proof} = RpcCompletionProof.build(profile(), [], success(), progress: progress())

    for {from, to} <- [
          {"rank suppliedInitial = 1211", "rank suppliedInitial = 1210"},
          {"suppliedMailboxResult, 97", "suppliedMailboxResult, 98"},
          {"execute RpcMailbox.suppliedConfig suppliedInitial RpcMailbox.suppliedTimeline",
           "execute RpcMailbox.suppliedConfig suppliedInitial []"},
          {"(progress : Progress behavior)", ""},
          {"suppliedRanking : Ranked RpcMailbox.suppliedConfig.session := canonicalRanking _",
           "suppliedRanking : Ranked RpcMailbox.suppliedConfig.session := by sorry"}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end
  end

  test "named reuse, embedded verification and dependency invalidation preserve the same obligations" do
    {:ok, _, proof} = RpcCompletionProof.build(profile(), [], sent(), progress: progress())
    first = reports(proof)
    assert_ok(first)
    reused = reports(proof)
    assert_ok(reused)
    assert Enum.any?(reused, &(&1.module == "ReductionBounds.Proofs.RpcCompletion" and &1.cached))
    assert_ok(reports(proof, shared_modules: false))
    {:ok, postludes} = ProofInput.rpc_completion_postludes(proof)

    files =
      Verification.assemble(Lynx.Translation.new(postludes: postludes),
        cache: true,
        shared_modules: true
      )

    index = Enum.find_index(files, &(&1["module"] == "ReductionBounds.Proofs.Mailbox"))

    changed =
      List.update_at(files, index, fn file ->
        update_in(file, ["preludes", Access.at(1), "source"], &(&1 <> "\n-- changed mailbox\n"))
      end)

    updated = ProofCache.finalize(changed, [], true)

    for {before, after_file} <- Enum.zip(files, updated) do
      if before["module"] in [
           "ReductionBounds.Proofs.Mailbox",
           "ReductionBounds.Proofs.RpcMailbox",
           "ReductionBounds.Proofs.RpcCompletion",
           "Erlang.postlude"
         ],
         do: refute(before["cache_key"] == after_file["cache_key"])
    end
  end

  defp reports(proof, options \\ []) do
    {:ok, postludes} = ProofInput.rpc_completion_postludes(proof, options)

    Verification.verify!(
      Lynx.Translation.new(postludes: postludes),
      Keyword.merge([cache: true, shared_modules: true], Keyword.take(options, [:shared_modules]))
    )
  end

  defp assert_ok(reports) do
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end
end
