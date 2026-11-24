defmodule ReductionBounds.MailboxProofTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_mailbox
  @moduletag timeout: 300_000
  alias ReductionBounds.{MailboxProof, ProofInput, RpcMailboxProof, Verification}
  import ReductionBounds.MailboxSupport

  test "Lean checks ordered matching, guards, retained order, cursor resumption and repeated receive counts" do
    clause = hd(spec().clauses)
    ordered = spec(clauses: [%{clause | guard: false}, clause])

    for {spec, queue, actions} <- [
          {ordered, [{:atom, "x"}, reply(), {:atom, "y"}], [:begin_receive, :inspect, :inspect]},
          {spec(), [{:atom, "old"}], [:begin_receive, :inspect, {:arrive, reply()}, :inspect]},
          {spec(), [{:atom, "old"}],
           [:begin_receive, :inspect, :timeout, :begin_receive, :inspect, :timeout]}
        ] do
      {:ok, _, proof} = MailboxProof.build(spec, queue, actions)
      assert_ok(reports(proof, :mailbox))
    end
  end

  test "Lean checks RPC coupling, response conditions, late arrivals and monitored outcomes" do
    down = {:tuple5, {:atom, "DOWN"}, {:ref, 9}, {:atom, "process"}, {:pid, 2}, {:atom, "gone"}}

    for {p, queue, timeline} <- [
          {profile(), [{:integer, -Integer.pow(2, 200)}],
           sent() ++
             server() ++ [{:arrive, reply()}, :inspect, :inspect, {:protocol, :process_reply}]},
          {profile(), [], sent() ++ [:timeout, {:protocol, :handle_timeout}, {:arrive, reply()}]},
          {profile(monitor_id: 9), [],
           [{:protocol, :monitor_peer}] ++ sent() ++ [{:arrive, down}, :inspect]}
        ] do
      {:ok, _, proof} = RpcMailboxProof.build(p, queue, timeline)
      assert_ok(reports(proof, :rpc_mailbox))
    end
  end

  test "Lean independently rejects false selected data, counters, conditions and projected RPC actions" do
    {:ok, _, proof} = RpcMailboxProof.build(profile(), [], success())

    for {from, to} <- [
          {"⟨100, 32, 256⟩", "⟨1, 0, 0⟩"},
          {"(.literal (.ref 7))", ".any"},
          {"def suppliedCounts : Counts := ⟨3, 1, 1, 1, 1, 1⟩",
           "def suppliedCounts : Counts := ⟨3, 1, 1, 0, 1, 1⟩"},
          {"(.arrive (.tuple3 (.atom \"reply\") (.ref 7) (.integer (9))))",
           "(.arrive (.tuple3 (.atom \"reply\") (.ref 8) (.integer (9))))"},
          {"def suppliedMailboxFinal : State := ⟨[]",
           "def suppliedMailboxFinal : State := ⟨[(.atom \"lost\")]"},
          {"suppliedCounts = true := by decide", "suppliedCounts = true := by sorry"}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source, from
      assert Enum.any?(reports(%{proof | source: changed}, :rpc_mailbox), &(&1.status == :error))
    end
  end

  test "shared mailbox theories support named cache reuse and embedded verification" do
    {:ok, _, first} = RpcMailboxProof.build(profile(), [], success())
    assert_ok(reports(first, :rpc_mailbox))
    second_timeline = sent() ++ [:timeout, {:protocol, :handle_timeout}]
    {:ok, _, second} = RpcMailboxProof.build(profile(), [], second_timeline)
    reused = reports(second, :rpc_mailbox)
    assert_ok(reused)
    assert Enum.any?(reused, &(&1.module == "ReductionBounds.Proofs.Mailbox" and &1.cached))
    assert_ok(reports(second, :rpc_mailbox, shared_modules: false))
  end

  test "message theory changes invalidate dependent mailbox and RPC artifacts" do
    {:ok, _, proof} = RpcMailboxProof.build(profile(), [], success())
    {:ok, postludes} = ProofInput.rpc_mailbox_postludes(proof)

    files =
      Verification.assemble(Lynx.Translation.new(postludes: postludes),
        cache: true,
        shared_modules: true
      )

    changed =
      List.update_at(files, 2, fn term ->
        update_in(
          term,
          ["preludes", Access.at(1), "source"],
          &(&1 <> "\n-- changed term measure\n")
        )
      end)

    updated = ReductionBounds.ProofCache.finalize(changed, [], true)

    assert Enum.zip_with(files, updated, &(&1["cache_key"] != &2["cache_key"])) ==
             [false, false, true, true, true, true]
  end

  defp reports(proof, type, options \\ []) do
    {:ok, postludes} =
      apply(
        ProofInput,
        if(type == :mailbox, do: :mailbox_postludes, else: :rpc_mailbox_postludes),
        [proof]
      )

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
