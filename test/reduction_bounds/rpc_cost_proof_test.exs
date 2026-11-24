defmodule ReductionBounds.RpcCostProofTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_cost
  @moduletag timeout: 300_000
  alias ReductionBounds.{
    CostContract,
    IntegerCostBound,
    IntegerSize,
    ProofInput,
    RpcCostProof,
    RpcServerContract,
    Verification
  }

  alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Fixture
  import ReductionBounds.MailboxSupport
  import ReductionBounds.RpcCostSupport

  test "Lean checks participant, prefix and assumed server composition theorems" do
    for timeline <- [success(), sent(), sent() ++ [:timeout, {:protocol, :handle_timeout}]] do
      {:ok, c, proof} = RpcCostProof.build(cost_profile(), [], timeline)
      assert_ok(reports(proof, c))
      assert c.lean_status == :not_checked
    end
  end

  test "handler composition replays Core evidence and input coverage with the same server unit" do
    {Fixture, beam} = ReductionBounds.TestFixtures.integer_cost_programs()
    functions = Map.new(CostContract.operations(), &{&1, {:add, 1, {:max, :left, :right}}})

    {:ok, contract} =
      CostContract.new(id: :rpc_server, cost_unit: :server_work, functions: functions)

    {:ok, original, _} =
      IntegerCostBound.infer({Fixture, :product, 1},
        input_sizes: [%IntegerSize{lower: 0, upper: 10, magnitude_bits: 4}],
        cost_contract: contract,
        beam_binaries: [beam]
      )

    {:ok, reuse} = RpcServerContract.reuse(original, frame(), beam_binaries: [beam])
    {:ok, c, proof} = RpcCostProof.build(cost_profile(server: reuse), [], success())
    assert c.server_contract.status == :replay_pending
    refute :server_handler_bound in c.verification_scope.assumptions
    assert_ok(reports(proof, c))
    assert "RpcHandler.composedServerBound" in c.checked_theorems

    changed = String.replace(proof.source, "fun _ => (5 : Int)", "fun _ => (6 : Int)")
    refute changed == proof.source
    assert Enum.any?(reports(%{proof | source: changed}, c), &(&1.status == :error))

    for forged <- [
          %{original | upper_bound: 0},
          %{original | target: {Fixture, :increment, 1}},
          %{original | core_source: :forged}
        ] do
      {:ok, reuse} = RpcServerContract.reuse(forged, frame(), beam_binaries: [beam])
      assert {:error, _} = RpcCostProof.build(cost_profile(server: reuse), [], success())
    end

    assert {:error, _} =
             RpcServerContract.reuse(
               %{original | cost_contract: %{contract | cost_unit: :client_work}},
               frame()
             )

    assert {:error, _} =
             RpcServerContract.reuse(
               %{original | cost_contract: %{contract | functions: :symbolic}},
               frame()
             )
  end

  test "Lean rejects lowered budgets, changed counts, rates and introduced axioms" do
    {:ok, c, proof} = RpcCostProof.build(cost_profile(), [], success())

    for {from, to} <-
          [
            {".server suppliedCaps suppliedRates = 232",
             ".server suppliedCaps suppliedRates = 231"},
            {"| .pattern => 1", "| .pattern => 0"},
            {"| .sendReply => 2", "| .sendReply => 1"}
          ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert Enum.any?(reports(%{proof | source: changed}, c), &(&1.status == :error))
    end

    changed =
      String.replace(
        proof.source,
        "intro op; cases op <;> decide",
        "intro op; cases op <;> sorry"
      )

    assert Enum.any?(reports(%{proof | source: changed}, c), &(&1.status == :error))
  end

  test "shared theories are reused and embedded verification has identical obligations" do
    {:ok, c, proof} = RpcCostProof.build(cost_profile(), [], success())
    assert_ok(reports(proof, c))
    reused = reports(proof, c)
    assert_ok(reused)
    assert Enum.any?(reused, &(&1.module == "ReductionBounds.Proofs.RpcCost" and &1.cached))
    assert_ok(reports(proof, c, shared_modules: false))
  end

  defp reports(proof, c, options \\ []) do
    {:ok, postludes} = ProofInput.rpc_cost_postludes(proof, handler: c.server_contract.kind)

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
