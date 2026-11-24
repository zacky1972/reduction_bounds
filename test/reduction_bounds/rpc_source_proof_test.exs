defmodule ReductionBounds.RpcSourceProofTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_source
  @moduletag timeout: 300_000
  alias ReductionBounds.{ProofCache, ProofInput, RpcSourceProof, Verification}
  alias ReductionBounds.Fixtures.{RpcClient, RpcHelpers}
  import ReductionBounds.RpcCostSupport

  test "Lean connects actual Core to a contracted protocol and conditional mailbox/cost certificates" do
    for f <- [:request, :reordered, :zero_timeout, :infinity_timeout] do
      {:ok, c, proof} = build(f)
      assert c.source_correspondence == :certificate_pending
      assert c.client_source_bound.cost_unit == :client_work
      assert c.upper_bounds.server.cost_unit == :server_work
      assert c.source_node_bound == 21
      refute Map.has_key?(c, :completion)
      refute Map.has_key?(c, :outcome)
      refute Map.has_key?(c, :trace)
      assert :source_termination in c.unverified
      assert "ReductionBounds.RpcSource.suppliedSourceAgreement" in c.checked_theorems

      assert "ReductionBounds.RpcSource.suppliedContractsWithoutNormalReturn" in c.checked_theorems

      assert_ok(reports(proof))
    end
  end

  test "Lean rejects changed source data, argument identities, clause certificates and budgets" do
    {:ok, _, proof} = build(:request)

    for {from, to} <-
          [
            {"(.atom \"request\")", "(.atom \"wrong_request\")"},
            {"suppliedCore.budget = 21", "suppliedCore.budget = 20"},
            {"def suppliedSourceFormula (nodeCharge : Nat) : Nat := ((21 * nodeCharge) + 1210)",
             "def suppliedSourceFormula (nodeCharge : Nat) : Nat := 0"},
            {"(.variable \"1\")", "(.variable \"2\")"},
            {"def suppliedTimeout : Value := (.integer (0))",
             "def suppliedTimeout : Value := (.integer (1))"},
            {"[\"reply\", \"timeout\"]", "[\"reply\", \"reply\"]"},
            {"(by decide) (by decide) (by decide) (by decide)",
             "(by sorry) (by decide) (by decide) (by decide)"}
          ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end
  end

  test "named reuse and embedded proofs retain the same explicit helper assumptions" do
    {:ok, _, proof} = build(:request)
    assert_ok(reports(proof))
    reused = reports(proof)
    assert_ok(reused)
    assert Enum.any?(reused, &(&1.module == "ReductionBounds.Proofs.RpcSource" and &1.cached))
    assert_ok(reports(proof, shared_modules: false))
    {:ok, postludes} = ProofInput.rpc_source_postludes(proof)

    files =
      Verification.assemble(Lynx.Translation.new(postludes: postludes),
        cache: true,
        shared_modules: true
      )

    index = Enum.find_index(files, &(&1["module"] == "ReductionBounds.Proofs.RpcCost"))

    changed =
      List.update_at(files, index, fn file ->
        update_in(
          file,
          ["preludes", Access.at(1), "source"],
          &(&1 <> "\n-- changed RPC cost theory\n")
        )
      end)

    updated = ProofCache.finalize(changed, [], true)

    for {before, after_file} <- Enum.zip(files, updated) do
      if before["module"] in [
           "ReductionBounds.Proofs.RpcCost",
           "ReductionBounds.Proofs.RpcSource",
           "Erlang.postlude"
         ],
         do: refute(before["cache_key"] == after_file["cache_key"])
    end
  end

  test "the source proof preserves replayed integer handler evidence and its assumptions" do
    alias ReductionBounds.{CostContract, IntegerCostBound, IntegerSize, RpcServerContract}
    alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Fixture
    {Fixture, beam} = ReductionBounds.TestFixtures.integer_cost_programs()

    {:ok, contract} =
      CostContract.new(
        id: :source_server,
        cost_unit: :server_work,
        functions: Map.new(CostContract.operations(), &{&1, 1})
      )

    {:ok, bound, _} =
      IntegerCostBound.infer({Fixture, :increment, 1},
        input_sizes: [IntegerSize.from_integer(5)],
        cost_contract: contract,
        beam_binaries: [beam]
      )

    {:ok, reuse} = RpcServerContract.reuse(bound, frame(), beam_binaries: [beam])

    {:ok, c, proof} =
      RpcSourceProof.build({RpcClient, :request, 4}, cost_profile(server: reuse),
        beam_binaries: ReductionBounds.TestFixtures.rpc_client_beams(),
        calls: %{reply: {RpcHelpers, :await_reply, 3}, decode: {RpcHelpers, :decode, 1}}
      )

    assert c.server_contract.status == :replay_pending
    assert "RpcHandler.replayedCostSafety" in c.checked_theorems
    assert :source_termination in c.verification_scope.unverified
    {:ok, postludes} = ProofInput.rpc_source_postludes(proof, handler: :replay)

    assert_ok(
      Verification.verify!(Lynx.Translation.new(postludes: postludes),
        cache: true,
        shared_modules: true
      )
    )
  end

  defp build(f),
    do:
      RpcSourceProof.build(
        {RpcClient, f, 4},
        cost_profile(
          conditions:
            ReductionBounds.MailboxSupport.profile(
              timeout: if(f == :infinity_timeout, do: :infinity, else: 0)
            )
        ),
        beam_binaries: ReductionBounds.TestFixtures.rpc_client_beams(),
        calls: %{reply: {RpcHelpers, :await_reply, 3}, decode: {RpcHelpers, :decode, 1}}
      )

  defp reports(proof, options \\ []) do
    {:ok, postludes} = ProofInput.rpc_source_postludes(proof)

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
