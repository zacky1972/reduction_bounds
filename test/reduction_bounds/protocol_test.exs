defmodule ReductionBounds.ProtocolTest do
  use ExUnit.Case, async: true

  @moduletag :protocol_model

  alias ReductionBounds.Protocol
  alias ReductionBounds.Protocol.{Contract, Event}

  doctest Protocol

  test "keeps different participants and units separate" do
    {:ok, contract} =
      Protocol.new(
        participants: %{client: :client_work, server: :server_work},
        states: [:ready, :waiting, :done],
        initial: :ready,
        terminal: [:done],
        events: %{
          send_request: {:client, :client_work},
          compute: {:server, :server_work},
          arrival: {nil, nil}
        },
        transitions: [
          {:ready, :send_request, :waiting},
          {:waiting, :compute, :waiting},
          {:waiting, :arrival, :done}
        ]
      )

    events = events(contract, [:send_request, :compute, :arrival])
    assert {:ok, trace} = Protocol.check_trace(contract, events)
    assert trace.states == [:ready, :waiting, :waiting, :done]
    assert trace.terminal?

    assert [%Event{name: :send_request, cost_unit: :client_work}] =
             Protocol.events_for(trace, :client)

    assert [%Event{name: :compute, cost_unit: :server_work}] = Protocol.events_for(trace, :server)
    assert Protocol.events_for(trace, :unknown) == []
    assert {:ok, prefix} = Protocol.check_trace(contract, Enum.take(events, 1))
    refute prefix.terminal?
  end

  test "empty traces are admissible prefixes, not a progress guarantee" do
    contract = contract()
    assert {:ok, trace} = Protocol.check_trace(contract, [])
    assert trace.states == [:ready]
    assert trace.final == :ready
    refute trace.terminal?
  end

  test "rejects forged ownership, units, unknown events, and malformed events" do
    contract = contract()
    {:ok, event} = Protocol.event(contract, :work)

    for invalid <- [%{event | owner: :other}, %{event | cost_unit: :seconds}] do
      assert {:error,
              {:invalid_protocol_trace, 0, ^invalid, {:event_metadata_mismatch, :work, _}}} =
               Protocol.check_trace(contract, [invalid])
    end

    assert {:error, {:unknown_protocol_event, :missing}} = Protocol.event(contract, :missing)

    assert {:error, {:invalid_protocol_trace, 0, nil, {:invalid_protocol_event, nil}}} =
             Protocol.check_trace(contract, [nil])

    assert {:error, {:invalid_protocol_events, :invalid}} =
             Protocol.check_trace(contract, :invalid)

    assert {:error, {:invalid_protocol_events, [_ | :invalid]}} =
             Protocol.check_trace(contract, [event | :invalid])
  end

  test "diagnostics identify repeated occurrences and terminal states cannot advance" do
    contract = contract()
    [event] = events(contract, [:work])

    assert {:error, {:invalid_protocol_trace, 1, ^event, {:transition_not_allowed, :done, :work}}} =
             Protocol.check_trace(contract, [event, event])
  end

  test "rejects incomplete and ambiguous contract declarations" do
    base = contract()

    for states <- [[], [:ready, :ready], [:ready | :invalid]] do
      assert {:error, {:invalid_protocol_states, ^states}} =
               Protocol.validate(%{base | states: states})
    end

    assert {:error, {:invalid_protocol_initial, :absent}} =
             Protocol.validate(%{base | initial: :absent})

    assert {:error, {:invalid_protocol_terminal, [:absent]}} =
             Protocol.validate(%{base | terminal: [:absent]})

    for pair <- [{:unknown, :work}, {:caller, :wrong}, {:caller, nil}, {nil, :work}] do
      assert {:error, {:invalid_protocol_event, {:work, ^pair}}} =
               Protocol.validate(%{base | events: %{work: pair}})
    end

    for edge <- [nil, {:done, :work, :ready}, {:ready, :unknown, :done}, {:ready, :work, :absent}] do
      assert {:error, {:invalid_protocol_transition, ^edge}} =
               Protocol.validate(%{base | transitions: [edge]})
    end

    assert {:error, :ambiguous_protocol_transition} =
             Protocol.validate(%{base | transitions: base.transitions ++ base.transitions})

    assert {:error, :invalid_protocol_options} = Protocol.new(unknown: true)
    assert {:error, {:invalid_protocol_contract, :invalid}} = Protocol.validate(:invalid)

    assert {:error, {:invalid_protocol_participants, nil}} =
             Protocol.validate(%Contract{participants: nil})
  end

  defp contract() do
    {:ok, contract} =
      Protocol.new(
        participants: %{caller: :work},
        states: [:ready, :done],
        initial: :ready,
        terminal: [:done],
        events: %{work: {:caller, :work}},
        transitions: [{:ready, :work, :done}]
      )

    contract
  end

  defp events(contract, names) do
    Enum.map(names, fn name ->
      {:ok, event} = Protocol.event(contract, name)
      event
    end)
  end
end
