defmodule ReductionBounds.RpcWorkflowTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_workflow
  @moduletag timeout: 300_000
  alias ReductionBounds.{RpcCompletionProof, RpcResult}
  alias ReductionBounds.Fixtures.{RpcClient, RpcHelpers}
  import ReductionBounds.MailboxSupport
  import ReductionBounds.RpcCostSupport, only: [cost_profile: 0, cost_profile: 1, frame: 0]

  defp progress(), do: [:client_progress, :request_progress, :server_progress, :response_progress]

  for {label, goal} <- [termination: :termination, success: :success] do
    @goal goal
    test "public RPC cost workflow checks #{label} with conditional reporting" do
      assumptions = progress() ++ if(@goal == :success, do: [:no_failure_outcomes], else: [])

      {:ok, c} =
        ReductionBounds.verify_rpc_model(cost_profile(), [], success(),
          completion: [goal: @goal, progress: assumptions],
          timeout: 300_000
        )

      assert c.lean_status == :checked
      assert c.source_correspondence == :not_checked
      assert c.verification_scope.kind == :supplied_rpc_model
      assert c.completion.theorem_status == :checked_under_assumptions
      assert c.completion.actual_completion == :not_established
      assert c.completion.observed_outcome == :success
      assert c.server_contract.status == :assumed
      assert :participant_cost_safety in c.verification_scope.checked
      assert :model_termination_under_progress in c.verification_scope.conditional
      assert Enum.all?(c.reports, &(&1.status == :ok))
    end
  end

  test "missing progress leaves cost safety verified and missing assumptions explicit" do
    {:ok, c} = ReductionBounds.verify_rpc_model(cost_profile(), [], sent(), timeout: 300_000)
    assert c.lean_status == :checked
    assert c.completion.status == :insufficient_assumptions
    assert c.completion.theorem_status == :not_established
    assert c.completion.missing_assumptions == progress()
    assert c.verification_scope.conditional == []
    assert Enum.any?(c.diagnostics, &(&1.code == :missing_completion_assumption))
    refute "ReductionBounds.RpcCompletion.suppliedConditionalCompletion" in c.checked_theorems
  end

  test "conditions-only verification does not claim a cost bound" do
    {:ok, c} = ReductionBounds.verify_rpc_conditions(profile(), [], sent(), timeout: 300_000)
    assert c.lean_status == :checked
    refute Map.has_key?(c, :upper_bounds)
    refute :participant_cost_safety in c.verification_scope.checked
    assert :cost_bound in c.unverified
  end

  test "failure outcomes and late replies preserve their exact model meaning" do
    down = {:tuple5, {:atom, "DOWN"}, {:ref, 9}, {:atom, "process"}, {:pid, 2}, {:atom, "gone"}}

    for {cp, q, timeline, outcome} <- [
          {cost_profile(), [{:atom, "old"}],
           sent() ++ [:inspect, :timeout, {:protocol, :handle_timeout}, {:arrive, reply()}],
           :timeout},
          {cost_profile(), [], Enum.drop(success(), -1) ++ [{:protocol, :decode_error}],
           :decode_error},
          {cost_profile(conditions: profile(monitor_id: 9)), [],
           [{:protocol, :monitor_peer}] ++ sent() ++ [{:arrive, down}, :inspect],
           :peer_terminated}
        ] do
      {:ok, c} =
        ReductionBounds.verify_rpc_model(cp, q, timeline,
          completion: [goal: :success, progress: progress() ++ [:no_failure_outcomes]],
          timeout: 300_000
        )

      assert c.completion.status == :inconsistent_assumptions
      assert c.completion.observed_outcome == outcome
      assert c.completion.theorem_status == :not_established
      assert c.lean_status == :checked
    end
  end

  test "public source results preserve contracts, payload obligations and missing totality" do
    {:ok, c} =
      ReductionBounds.infer_rpc_bound({RpcClient, :request, 4}, cost_profile(), source_options())

    assert c.lean_status == :checked
    assert c.source_correspondence == :checked_under_contracts
    assert c.verification_scope.kind == :core_connected_rpc_client
    assert :unrestricted_source_correspondence in c.unverified
    refute :source_correspondence in c.unverified
    assert :reified_core_connection in c.verification_scope.checked
    assert c.completion.scope == :source_code
    assert c.completion.theorem_status == :not_established
    assert c.completion.actual_completion == :not_established
    assert c.call_contracts.reply.status == :assumed
    assert c.server_contract.status == :assumed
    assert :response_payload_association in c.unverified
    assert :native_receive in c.unsupported
    refute Map.has_key?(c, :outcome)
    refute Map.has_key?(c, :trace)
  end

  test "replayed handlers become checked under their retained contracts" do
    alias ReductionBounds.{CostContract, IntegerCostBound, IntegerSize, RpcServerContract}
    alias ReductionBounds.Fixtures.IntegerCostPrograms, as: Fixture
    {Fixture, beam} = ReductionBounds.TestFixtures.integer_cost_programs()

    {:ok, contract} =
      CostContract.new(
        id: :workflow,
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

    {:ok, c} =
      ReductionBounds.infer_rpc_bound(
        {RpcClient, :request, 4},
        cost_profile(server: reuse),
        source_options()
      )

    assert c.server_contract.status == :checked_under_contracts
    assert :handler_callee_contracts in c.verification_scope.assumptions
    assert :source_termination in c.unverified
  end

  test "unsupported source and unsafe option extensions are errors, not model fallback" do
    target = {RpcClient, :native_receive, 4}

    assert {:error, {:rpc_source, ^target, _}} =
             ReductionBounds.infer_rpc_bound(target, cost_profile(), source_options())

    for opts <- [
          [postlude: :unapproved],
          [reports: [%{status: :ok}]],
          [completion: :all],
          [timeout: -1],
          [beam_binaries: []]
        ] do
      assert {:error, _} = ReductionBounds.verify_rpc_model(cost_profile(), [], sent(), opts)
    end

    assert {:error, _} =
             ReductionBounds.infer_rpc_bound(:invalid, cost_profile(), source_options())
  end

  test "empty, incomplete, skipped or failed verification cannot promote a candidate" do
    {:ok, candidate, _} = RpcCompletionProof.build(profile(), [], sent())

    for reports <- [
          [],
          [%{module: "Shared", status: :ok}],
          [%{module: "Erlang.postlude", status: :skipped}],
          [%{module: "Erlang.postlude", status: :ok}, %{module: "Shared", status: :error}]
        ] do
      assert {:error, {:verification_failed, ^reports}} = RpcResult.verified(candidate, reports)
    end

    assert candidate.lean_status == :not_checked
  end

  test "verification timeout returns an error without a checked result" do
    assert {:error, :timeout} =
             ReductionBounds.verify_rpc_conditions(profile(), [], success(), timeout: 0)
  end

  defp source_options(),
    do: [
      timeout: 300_000,
      beam_binaries: ReductionBounds.TestFixtures.rpc_client_beams(),
      calls: %{reply: {RpcHelpers, :await_reply, 3}, decode: {RpcHelpers, :decode, 1}}
    ]
end
