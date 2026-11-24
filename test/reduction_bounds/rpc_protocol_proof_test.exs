defmodule ReductionBounds.RpcProtocolProofTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.{ProofCache, ProofInput, RpcProtocol, RpcProtocolProof, Verification}

  @moduletag :rpc_model
  @moduletag timeout: 300_000

  @success ~w(prepare send_request request_arrived receive_request handle_request send_reply
    reply_arrived receive_reply process_reply)a

  test "Lean checks canonical plain and monitored models and supported outcomes" do
    for {options, names, outcome} <- [
          {[], [], :pending},
          {[], [:prepare, :send_request], :pending},
          {[], @success, :success},
          {[],
           [
             :prepare,
             :send_request,
             :unrelated_arrived,
             :inspect_unrelated,
             :timeout_elapsed,
             :handle_timeout
           ], :timeout},
          {[], Enum.drop(@success, -1) ++ [:decode_error], :decode_error},
          {[monitor_id: 9],
           [:monitor_peer, :prepare, :send_request, :peer_down, :handle_peer_down],
           :peer_terminated},
          {[monitor_id: 9], [:monitor_peer | @success], :success}
        ] do
      {candidate, proof} = input(7, options, names)
      assert candidate.outcome == outcome
      assert candidate.lean_status == :not_checked
      assert "ReductionBounds.RpcProtocol.suppliedRpcTraceSound" in candidate.checked_theorems
      assert_ok(reports(proof))
    end
  end

  test "Lean rejects changed tokens, outcomes and canonical protocol declarations" do
    {_candidate, proof} = input(7, [], @success)

    for {from, to} <- [
          {"def suppliedSession : Session := ⟨7, none⟩",
           "def suppliedSession : Session := ⟨8, none⟩"},
          {~s(outcome Protocol.suppliedFinal = "success"),
           ~s(outcome Protocol.suppliedFinal = "timeout")},
          {~s("client_work"), ~s("wrong_unit")},
          {"checkTrace suppliedSession suppliedRpcEvents Protocol.suppliedStates = true := by decide",
           "checkTrace suppliedSession suppliedRpcEvents Protocol.suppliedStates = true := by sorry"}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end

    {_candidate, monitored} =
      input(7, [monitor_id: 9], [
        :monitor_peer,
        :prepare,
        :send_request,
        :peer_down,
        :handle_peer_down
      ])

    changed = String.replace(monitored.source, "⟨7, (some 9)⟩", "⟨7, (some 10)⟩")
    refute changed == monitored.source
    assert Enum.any?(reports(%{monitored | source: changed}), &(&1.status == :error))
  end

  test "named artifacts are reused across requests and embedded proofs remain checked" do
    {_, first} = input(1001, [], [:prepare])
    assert_ok(reports(first))
    {_, second} = input(1002, [], [:prepare])
    reused = reports(second)
    assert_ok(reused)
    assert Enum.any?(reused, &(&1.module == "ReductionBounds.Proofs.RpcProtocol" and &1.cached))
    assert_ok(reports(second, shared_modules: false))
  end

  test "new theory keys include protocol dependencies and change transitively" do
    {_, proof} = input(7, [], [:prepare])
    {:ok, postludes} = ProofInput.rpc_postludes(proof)

    [protocol, rpc, target] =
      Verification.assemble(Lynx.Translation.new(postludes: postludes),
        cache: true,
        shared_modules: true
      )

    assert rpc["imports"] == [protocol["module"]]

    changed =
      update_in(
        protocol,
        ["preludes", Access.at(1), "source"],
        &(&1 <> "\n-- different protocol\n")
      )

    updated = ProofCache.finalize([changed, rpc, target], [], true)

    assert Enum.zip_with([protocol, rpc, target], updated, &(&1["cache_key"] != &2["cache_key"])) ==
             [true, true, true]
  end

  defp input(id, options, names) do
    {:ok, model} = RpcProtocol.new(id, options)

    events =
      Enum.map(names, fn name ->
        {:ok, event} = RpcProtocol.event(model, name)
        event
      end)

    {:ok, candidate, proof} = RpcProtocolProof.build(model, events)
    {candidate, proof}
  end

  defp reports(proof, options \\ []) do
    {:ok, postludes} = ProofInput.rpc_postludes(proof)

    Verification.verify!(
      Lynx.Translation.new(postludes: postludes),
      Keyword.merge([cache: true, shared_modules: true], options)
    )
  end

  defp assert_ok(reports) do
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end
end
