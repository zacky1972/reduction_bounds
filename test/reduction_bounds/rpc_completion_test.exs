defmodule ReductionBounds.RpcCompletionTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_completion
  alias ReductionBounds.{RpcCompletion, RpcCompletionProof}
  import ReductionBounds.MailboxSupport
  import ReductionBounds.RpcCostSupport, only: [cost_profile: 0]

  defp progress, do: [:client_progress, :request_progress, :server_progress, :response_progress]

  test "progress assumptions concern continuations, not a successful example" do
    {:ok, c} = RpcCompletion.check_trace(profile(), [], success())
    assert c.completion.observed_outcome == :success
    assert c.completion.status == :insufficient_assumptions
    assert c.completion.missing_assumptions == progress()
    assert c.completion.elapsed_time_bound == :not_established
    assert c.completion.source_termination == :not_checked
  end

  test "each scheduling and delivery premise is independently required" do
    for missing <- progress() do
      {:ok, c} =
        RpcCompletion.check_trace(profile(), [], sent(), progress: progress() -- [missing])

      assert c.completion.missing_assumptions == [missing]
      assert c.completion.status == :insufficient_assumptions
    end
  end

  test "termination and successful completion have distinct assumptions" do
    {:ok, termination} = RpcCompletion.check_trace(profile(), [], sent(), progress: progress())
    assert termination.completion.status == :conditional

    {:ok, missing} =
      RpcCompletion.check_trace(profile(), [], success(), goal: :success, progress: progress())

    assert missing.completion.missing_assumptions == [:no_failure_outcomes]

    {:ok, success} =
      RpcCompletion.check_trace(profile(), [], success(),
        goal: :success,
        progress: progress() ++ [:no_failure_outcomes]
      )

    assert success.completion.status == :conditional
  end

  test "timeout, decoding failure and monitored peer death terminate without becoming success" do
    down = {:tuple5, {:atom, "DOWN"}, {:ref, 9}, {:atom, "process"}, {:pid, 2}, {:atom, "gone"}}
    decode = Enum.drop(success(), -1) ++ [{:protocol, :decode_error}]

    for {p, timeline, outcome} <- [
          {profile(), sent() ++ [:timeout, {:protocol, :handle_timeout}, {:arrive, reply()}],
           :timeout},
          {profile(), decode, :decode_error},
          {profile(monitor_id: 9),
           [{:protocol, :monitor_peer}] ++ sent() ++ [{:arrive, down}, :inspect],
           :peer_terminated}
        ] do
      {:ok, c} = RpcCompletion.check_trace(p, [], timeline, progress: progress())
      assert c.completion.status == :conditional
      assert c.completion.observed_outcome == outcome

      {:ok, bad} =
        RpcCompletion.check_trace(p, [], timeline,
          goal: :success,
          progress: progress() ++ [:no_failure_outcomes]
        )

      assert bad.completion.status == :inconsistent_assumptions

      {:ok, contradictory} =
        RpcCompletion.check_trace(p, [], timeline, progress: progress() ++ [:no_failure_outcomes])

      assert contradictory.completion.status == :inconsistent_assumptions
    end
  end

  test "observing timeout before its handler already contradicts no-failure success" do
    {:ok, c} =
      RpcCompletion.check_trace(profile(), [], sent() ++ [:timeout],
        goal: :success,
        progress: progress() ++ [:no_failure_outcomes]
      )

    assert c.completion.status == :inconsistent_assumptions
    assert c.completion.observed_outcome == :pending
  end

  test "suspension and timeout numerals do not supply progress or an elapsed time bound" do
    for timeout <- [0, 100, :infinity] do
      {:ok, c} = RpcCompletion.check_trace(profile(timeout: timeout), [], sent())
      assert c.completion.status == :insufficient_assumptions
      assert c.completion.active_action_bound == 1211
      assert c.completion.remaining_mailbox_steps == 99
    end
  end

  test "impossible receive limits do not yield a completion claim" do
    for limits <- [%{limits() | steps: 0}, %{limits() | receives: 0}] do
      {:ok, c} = RpcCompletion.check_trace(profile(limits: limits), [], [], progress: progress())
      assert c.completion.status == :inconsistent_limits
    end

    {:ok, c} =
      RpcCompletion.check_trace(profile(limits: %{limits() | inspections: 0}), [], sent(),
        goal: :success,
        progress: progress() ++ [:no_failure_outcomes]
      )

    assert c.completion.status == :inconsistent_limits
  end

  test "unknown progress, retries, callbacks and timeout-as-budget options are rejected" do
    for options <- [
          [progress: [:server_cost_bound]],
          [progress: :all],
          [progress: [fn -> true end]],
          [goal: :unconditional],
          [retries: 1],
          [limits: %{steps: 10}],
          [timeout: 100]
        ] do
      assert {:error, :invalid_rpc_completion_options} =
               RpcCompletion.check_trace(profile(), [], sent(), options)
    end
  end

  test "a missing completion premise leaves conditional cost safety available" do
    {:ok, c, proof} = RpcCompletionProof.build_with_cost(cost_profile(), [], sent())
    assert c.completion.status == :insufficient_assumptions
    assert c.upper_bounds.server.cost_unit == :server_work
    assert c.lean_status == :not_checked
    assert "ReductionBounds.RpcCost.suppliedCostSafety" in c.checked_theorems
    refute "ReductionBounds.RpcCompletion.suppliedConditionalCompletion" in c.checked_theorems
    refute proof.source =~ "theorem suppliedConditionalCompletion"
  end
end
