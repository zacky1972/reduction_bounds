defmodule ReductionBounds.RpcProtocolTest do
  use ExUnit.Case, async: true

  @moduletag :rpc_model

  alias ReductionBounds.{Protocol, RpcProtocol}
  alias ReductionBounds.RpcProtocol.{Event, Session}

  @success ~w(prepare send_request request_arrived receive_request handle_request send_reply
    reply_arrived receive_reply process_reply)a

  test "single-attempt success keeps client/server work and observations separate" do
    {:ok, model} = RpcProtocol.new(7)
    assert {:ok, result} = RpcProtocol.check_trace(model, events(model, @success))
    assert result.outcome == :success
    assert result.trace.terminal?
    assert result.lean_status == :not_checked
    assert result.source_correspondence == :not_checked
    assert result.verification_scope.checked == []
    assert :mailbox_semantics in result.verification_scope.unverified

    assert Enum.map(Protocol.events_for(result.trace, :server), & &1.name) ==
             [:receive_request, :handle_request, :send_reply]

    assert Enum.all?(Protocol.events_for(result.trace, :client), &(&1.cost_unit == :client_work))
    assert Enum.all?(Protocol.events_for(result.trace, :server), &(&1.cost_unit == :server_work))
    assert Enum.all?(result.events, &(&1.request_id == 7))
  end

  test "sending alone and unfinished prefixes establish no arrival or progress" do
    {:ok, model} = RpcProtocol.new(7)

    for names <- [[], [:prepare], [:prepare, :send_request]] do
      assert {:ok, result} = RpcProtocol.check_trace(model, events(model, names))
      assert result.outcome == :pending
      refute result.trace.terminal?
      assert :progress in result.verification_scope.unverified
    end

    assert {:error, {:invalid_protocol_trace, 2, _, _}} =
             RpcProtocol.check_trace(
               model,
               events(model, [:prepare, :send_request, :receive_reply])
             )
  end

  test "timeout and decode failure are outcomes distinct from successful replies" do
    {:ok, model} = RpcProtocol.new(7)

    assert {:ok, timeout} =
             RpcProtocol.check_trace(
               model,
               events(model, [:prepare, :send_request, :timeout_elapsed, :handle_timeout])
             )

    assert timeout.outcome == :timeout

    assert {:ok, error} =
             RpcProtocol.check_trace(
               model,
               events(model, Enum.drop(@success, -1) ++ [:decode_error])
             )

    assert error.outcome == :decode_error

    assert {:error, {:invalid_protocol_trace, _, _, _}} =
             RpcProtocol.check_trace(model, timeout.events ++ events(model, [:reply_arrived]))
  end

  test "monitor observations use a separate token and require explicit setup" do
    {:ok, plain} = RpcProtocol.new(7)
    assert {:error, {:unknown_protocol_event, :peer_down}} = RpcProtocol.event(plain, :peer_down)
    {:ok, model} = RpcProtocol.new(7, monitor_id: 9)
    names = [:monitor_peer, :prepare, :send_request, :peer_down, :handle_peer_down]
    assert {:ok, result} = RpcProtocol.check_trace(model, events(model, names))
    assert result.outcome == :peer_terminated
    assert hd(result.events).monitor_id == 9
    assert hd(result.events).request_id == nil

    assert {:error, {:rpc_correlation_mismatch, :peer_down, _}} =
             RpcProtocol.event(model, :peer_down, monitor_id: 7)

    assert {:error, {:invalid_protocol_trace, 0, _, _}} =
             RpcProtocol.check_trace(model, events(model, [:prepare]))
  end

  test "unrelated observations are permitted without claiming queue semantics" do
    {:ok, model} = RpcProtocol.new(7)

    names = [
      :prepare,
      :send_request,
      :unrelated_arrived,
      :inspect_unrelated,
      :timeout_elapsed,
      :handle_timeout
    ]

    assert {:ok, result} = RpcProtocol.check_trace(model, events(model, names))
    assert result.outcome == :timeout
    assert :matching_and_scanning in result.verification_scope.unverified
  end

  test "rejects repeated sends, retries and forged correlation or ownership" do
    {:ok, model} = RpcProtocol.new(7)
    assert {:error, {:unknown_protocol_event, :retry}} = RpcProtocol.event(model, :retry)

    assert {:error, {:invalid_protocol_trace, 2, _, _}} =
             RpcProtocol.check_trace(
               model,
               events(model, [:prepare, :send_request, :send_request])
             )

    [prepare] = events(model, [:prepare])

    for forged <- [%{prepare | request_id: 8}, %{prepare | monitor_id: 9}] do
      assert {:error, {:invalid_rpc_trace, 0, {:rpc_correlation_mismatch, :prepare, _}}} =
               RpcProtocol.check_trace(model, [forged])
    end

    forged = %{prepare | protocol: %{prepare.protocol | owner: :server}}

    assert {:error, {:invalid_protocol_trace, 0, _, {:event_metadata_mismatch, _, _}}} =
             RpcProtocol.check_trace(model, [forged])
  end

  test "validates session identity, canonical contract and input shapes" do
    for {id, options} <- [
          {-1, []},
          {nil, []},
          {7, [monitor_id: false]},
          {7, [distributed: true]},
          {7, nil}
        ] do
      assert {:error, :invalid_rpc_session} = RpcProtocol.new(id, options)
    end

    {:ok, model} = RpcProtocol.new(7)
    assert {:error, :invalid_rpc_session} = RpcProtocol.validate(%Session{})
    assert {:error, :invalid_rpc_session} = RpcProtocol.validate(nil)
    forged = %{model | contract: %{model.contract | terminal: []}}
    assert {:error, :invalid_rpc_session} = RpcProtocol.check_trace(forged, [])
    assert {:error, :invalid_rpc_events} = RpcProtocol.check_trace(model, :invalid)

    assert {:error, :invalid_rpc_events} =
             RpcProtocol.check_trace(model, [hd(events(model, [:prepare])) | :invalid])

    assert {:error, {:invalid_rpc_trace, 0, :invalid_rpc_event}} =
             RpcProtocol.check_trace(model, [%Event{}])

    assert {:error, :invalid_rpc_event_options} = RpcProtocol.event(model, :prepare, nil)
  end

  defp events(model, names) do
    Enum.map(names, fn name ->
      {:ok, event} = RpcProtocol.event(model, name)
      event
    end)
  end
end
