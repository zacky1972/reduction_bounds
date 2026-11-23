defmodule ReductionBounds.PortCompletionTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.{PortCompletion, PortProtocol, Protocol, ProtocolCost, ProtocolSize}

  @moduletag :port_completion

  test "separates observed outcomes from conditional termination" do
    for {names, outcome} <- [
          {[:prepare, :submit_accepted, :response_arrived, :receive_response, :decode], :success},
          {[:prepare, :submit_rejected, :return_rejection], :rejected},
          {[:prepare, :submit_accepted, :port_closed, :handle_closure], :port_closed},
          {[:prepare, :submit_accepted, :timeout_elapsed, :handle_timeout], :timeout},
          {[:prepare, :submit_accepted, :response_arrived, :receive_response, :decode_error],
           :decode_error},
          {[:prepare, :submit_suspended], :pending}
        ] do
      {profile, events} = input(names)

      assert {:ok, result} =
               PortCompletion.check_trace(profile, events, observations(events), options())

      assert result.completion.status == :conditional
      assert result.completion.observed_outcome == outcome
      assert result.completion.elapsed_time_bound == :not_established
      assert result.completion.active_event_bound == 139
      assert result.external_work == :not_bounded
      assert result.lean_status == :not_checked
    end
  end

  test "retains the cost result when progress, success or limits are missing" do
    {profile, events} = input([:prepare, :submit_accepted])

    for opts <- [
          [],
          Keyword.delete(options(), :progress),
          Keyword.put(options(), :goal, :success),
          Keyword.delete(options(), :limits)
        ] do
      assert {:ok, result} =
               PortCompletion.check_trace(profile, events, observations(events), opts)

      assert result.completion.status == :insufficient_assumptions
      assert result.completion.missing_assumptions != []
      assert result.upper_bounds.caller.cost_unit == :symbolic_work
    end
  end

  test "detects exhausted loop allowances and contradictions with successful completion" do
    {profile, events} = input([:prepare, :submit_rejected, :return_rejection])
    opts = Keyword.put(options(), :limits, %{rejections: 0, resumptions: 3, inspections: 8})

    assert {:ok, %{completion: %{status: :inconsistent_limits}}} =
             PortCompletion.check_trace(profile, events, observations(events), opts)

    opts =
      options()
      |> Keyword.put(:goal, :success)
      |> Keyword.update!(:progress, &[:no_failure_outcomes | &1])

    assert {:ok, %{completion: %{status: :inconsistent_assumptions}}} =
             PortCompletion.check_trace(profile, events, observations(events), opts)
  end

  test "rejects invalid transitions, malformed options and timeout during submission suspension" do
    {profile, events} = input([:prepare, :submit_suspended, :timeout_elapsed])

    assert {:error, {:invalid_protocol_trace, 2, _, _}} =
             PortCompletion.check_trace(profile, events, observations(events), options())

    {profile, events} = input([])

    for opts <- [
          [progress: [:missing]],
          [progress: [:caller_progress | :bad]],
          [limits: %{rejections: -1}],
          [goal: :unknown],
          [unexpected: true]
        ] do
      assert {:error, _} = PortCompletion.check_trace(profile, events, %{}, opts)
    end
  end

  defp options do
    [
      limits: %{rejections: 2, resumptions: 3, inspections: 8},
      progress: [:caller_progress, :submission_progress, :resumption_progress, :response_progress]
    ]
  end

  defp input(names) do
    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
        count_bounds: %{
          total_events: 30,
          submission_attempts: 4,
          submission_events: 8,
          resumptions: 3,
          retries: 3,
          receive_inspections: 8
        }
      )

    rules =
      for {{_, event} = context, _} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{},
          do: {context, %{counter: :total_events, cost: {:charge, :local}}}

    {:ok, profile} = ProtocolCost.new(conditions, rules)

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(conditions.contract, name)
        event
      end)

    {profile, events}
  end

  defp observations(events) do
    {:ok, observation} =
      ReductionBounds.ProtocolConditions.observe(%{request: [], response: [], message: []})

    Map.new(Enum.with_index(events), fn {_, i} -> {i, observation} end)
  end
end
