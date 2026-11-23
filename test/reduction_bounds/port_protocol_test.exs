defmodule ReductionBounds.PortProtocolTest do
  use ExUnit.Case, async: true

  @moduletag :protocol_model

  alias ReductionBounds.{PortProtocol, Protocol}

  test "models success, rejection, closure, suspension, and rejected-submission retries" do
    for {names, final} <- [
          {[:prepare, :submit_accepted, :response_arrived, :receive_response, :decode],
           :complete},
          {[:prepare, :submit_rejected, :return_rejection], :failed},
          {[:prepare, :submit_accepted, :port_closed, :handle_closure], :closed},
          {[
             :prepare,
             :submit_rejected,
             :retry,
             :submit_accepted,
             :response_arrived,
             :inspect_message,
             :receive_response,
             :decode
           ], :complete},
          {[
             :prepare,
             :submit_suspended,
             :resume_submission,
             :submit_accepted,
             :port_closed,
             :handle_closure
           ], :closed}
        ] do
      assert {:ok, trace} = check(names)
      assert trace.final == final
      assert trace.terminal?
    end
  end

  test "waiting is a state and environment events do not acquire caller ownership" do
    assert {:ok, prefix} = check([:prepare, :submit_accepted, :inspect_message])
    assert prefix.final == :awaiting_response
    refute prefix.terminal?

    assert {:ok, trace} = check([:prepare, :submit_accepted, :port_closed, :handle_closure])

    assert Enum.map(Protocol.events_for(trace, :caller), & &1.name) == [
             :prepare,
             :submit_accepted,
             :handle_closure
           ]

    observation = Enum.find(trace.events, &(&1.name == :port_closed))
    assert observation.owner == nil
    assert observation.cost_unit == nil
    refute Map.has_key?(Map.from_struct(trace), :cost_bound)
  end

  test "permits finite retries and inspections without claiming a uniform count bound" do
    retries = List.duplicate([:submit_rejected, :retry], 20) |> List.flatten()
    assert {:ok, trace} = check([:prepare] ++ retries ++ [:submit_accepted])
    refute trace.terminal?
    inspections = List.duplicate(:inspect_message, 20)
    assert {:ok, _} = check([:prepare, :submit_accepted] ++ inspections)
  end

  test "rejects response handling before arrival and submission after acceptance" do
    for names <- [
          [:prepare, :submit_accepted, :receive_response],
          [:prepare, :submit_accepted, :submit_accepted],
          [:prepare, :submit_accepted, :retry],
          [:prepare, :submit_accepted, :response_arrived, :response_arrived],
          [:prepare, :submit_accepted, :port_closed, :handle_closure, :prepare]
        ] do
      assert {:error, {:invalid_protocol_trace, _, _, {:transition_not_allowed, _, _}}} =
               check(names)
    end
  end

  defp check(names) do
    {:ok, contract} = PortProtocol.new()

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(contract, name)
        event
      end)

    Protocol.check_trace(contract, events)
  end
end
