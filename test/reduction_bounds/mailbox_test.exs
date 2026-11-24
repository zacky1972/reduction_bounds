defmodule ReductionBounds.MailboxTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_mailbox
  alias ReductionBounds.{Mailbox, MailboxMatch, RpcTerm}
  import ReductionBounds.MailboxSupport

  test "removes only the first eligible message and preserves unmatched order" do
    a = {:atom, "a"}
    b = {:atom, "b"}
    r = reply()
    assert {:ok, result} = Mailbox.run(spec(), [a, r, b, r], [:begin_receive, :inspect, :inspect])
    assert result.state.queue == [a, b, r]
    assert result.state.selected == r
    assert result.counts.inspections == 2
    assert result.counts.pattern_attempts == 2
  end

  test "clause order and failed guards are counted before selecting a later clause" do
    p = profile().mailbox.clauses |> hd()
    first = %{p | guard: {:integer_ge, [2], 10}}
    assert MailboxMatch.choose([first, p], reply(5)) == {1, 2, 2}

    assert {:ok, result} =
             Mailbox.run(spec(clauses: [first, p]), [reply(5)], [:begin_receive, :inspect])

    assert result.state.clause == 1
    assert result.counts.guard_attempts == 2

    assert {:ok, missed} =
             Mailbox.run(spec(clauses: [first]), [reply(5)], [:begin_receive, :inspect])

    assert missed.state.queue == [reply(5)]
    assert missed.state.cursor == 1
  end

  test "a waiting receive continues after retained misses without scanning them again" do
    a = {:atom, "old"}

    assert {:ok, result} =
             Mailbox.run(spec(), [a], [:begin_receive, :inspect, {:arrive, reply()}, :inspect])

    assert result.state.queue == [a]
    assert result.counts.inspections == 2
    assert result.counts.arrivals == 1
  end

  test "a new receive restarts at the queue head and total inspections can exceed initial length" do
    a = {:atom, "old"}
    actions = [:begin_receive, :inspect, :timeout, :begin_receive, :inspect, :timeout]
    assert {:ok, result} = Mailbox.run(spec(), [a], actions)
    assert result.state.queue == [a]
    assert result.counts.receives == 2
    assert result.counts.inspections == 2

    assert {:error, {:mailbox_step, 4, :count_limit_exceeded}} =
             Mailbox.run(spec(limits: %{limits() | inspections: 1}), [a], actions)
  end

  test "after zero requires an exhausted queue and infinity does not admit timeout" do
    assert {:error, {:mailbox_step, 1, :timeout_requires_exhausted_search}} =
             Mailbox.run(spec(), [{:atom, "old"}], [:begin_receive, :timeout])

    assert {:error, {:mailbox_step, 2, _}} =
             Mailbox.run(spec(), [reply()], [:begin_receive, :inspect, :timeout])

    assert {:error, {:mailbox_step, 1, _}} =
             Mailbox.run(spec(timeout: :infinity), [], [:begin_receive, :timeout])

    assert {:ok, result} = Mailbox.run(spec(), [], [:begin_receive, :timeout, {:arrive, reply()}])
    assert result.state.phase == :timed_out
    assert result.state.queue == [reply()]
  end

  test "independent message dimensions include unrelated messages and large signed integers" do
    assert {:ok, nested} = RpcTerm.from_term([[], []])
    assert {:ok, size} = RpcTerm.measure(nested)
    assert size.bytes == 0 and size.nodes > 1
    assert {:ok, signed} = RpcTerm.measure({:integer, -Integer.pow(2, 200)})
    assert signed.integer_bits == 201
    assert {:ok, binary} = RpcTerm.measure({:binary, <<0, 255, 0>>})
    assert binary.nodes == 1 and binary.bytes == 3

    assert {:error, {:message_size_exceeded, _}} =
             Mailbox.initial(spec(message_size: %{cap() | integer_bits: 8}), [
               {:integer, -Integer.pow(2, 200)}
             ])

    assert {:error, {:mailbox_step, 0, {:message_size_exceeded, _}}} =
             Mailbox.run(spec(message_size: %{cap() | bytes: 1}), [], [
               {:arrive, {:binary, "large"}}
             ])
  end

  test "a late response is retained and scanned by a later receive with a different token" do
    {:ok, timed_out} = Mailbox.run(spec(), [], [:begin_receive, :timeout, {:arrive, reply()}])
    {:ok, next_session} = ReductionBounds.RpcProtocol.new(8)
    next_clauses = ReductionBounds.RpcConditions.clauses(next_session, true)
    next_reply = {:tuple3, {:atom, "reply"}, {:ref, 8}, {:integer, 9}}

    assert {:ok, next} =
             Mailbox.run(spec(clauses: next_clauses), timed_out.state.queue, [
               :begin_receive,
               :inspect,
               {:arrive, next_reply},
               :inspect
             ])

    assert next.state.selected == next_reply
    assert next.state.queue == [reply()]
    assert next.counts.inspections == 2
  end

  test "rejects missing conditions, callbacks, unsupported terms and malformed actions" do
    assert {:error, _} =
             Mailbox.new(
               clauses: spec().clauses,
               message_size: cap(),
               limits: %{inspections: 10},
               timeout: 0
             )

    assert {:error, _} = Mailbox.new(Map.to_list(%{spec() | message_size: %RpcTerm.Size{}}))

    assert {:error, _} =
             Mailbox.new(
               Map.to_list(%{spec() | clauses: [%{hd(spec().clauses) | guard: fn _ -> true end}]})
             )

    assert {:error, {:unsupported_rpc_value, _}} = RpcTerm.from_term(%{})
    assert {:error, {:unsupported_rpc_value, _}} = RpcTerm.from_term(make_ref())
    assert {:error, _} = Mailbox.initial(spec(), [:invalid])
    assert {:error, :invalid_mailbox_messages} = Mailbox.initial(spec(), [{:atom, "ok"} | :bad])
    assert {:error, :invalid_mailbox_actions} = Mailbox.run(spec(), [], [:begin_receive | :bad])
  end
end

defmodule ReductionBounds.RpcConditionsTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_mailbox
  alias ReductionBounds.{RpcConditions, RpcProtocol, RpcTerm}
  import ReductionBounds.MailboxSupport

  test "RPC observations come from the first eligible mailbox message" do
    assert {:ok, result} =
             RpcConditions.check_trace(
               profile(),
               [{:atom, "old"}],
               sent() ++
                 server() ++ [{:arrive, reply()}, :inspect, :inspect, {:protocol, :process_reply}]
             )

    assert result.outcome == :success
    assert result.mailbox.queue == [{:atom, "old"}]
    assert result.counts.inspections == 2
    assert result.protocol_counts.client_sends == 1
    assert result.protocol_counts.server_sends == 1
    assert result.source_correspondence == :not_checked
    assert result.lean_status == :not_checked
  end

  test "stale correlation and guard failure retain messages and permit bounded timeout" do
    stale = {:tuple3, {:atom, "reply"}, {:ref, 6}, {:integer, 99}}

    actions =
      sent() ++
        [
          {:arrive, stale},
          {:arrive, reply(-1)},
          :inspect,
          :inspect,
          :timeout,
          {:protocol, :handle_timeout}
        ]

    assert {:ok, result} =
             RpcConditions.check_trace(profile(reply_guard: {:integer_ge, [2], 0}), [], actions)

    assert result.outcome == :timeout
    assert result.mailbox.queue == [stale, reply(-1)]
    assert result.counts.guard_attempts == 1
  end

  test "timeout retains a late reply without reviving the terminated RPC" do
    actions = sent() ++ [:timeout, {:protocol, :handle_timeout}, {:arrive, reply()}]
    assert {:ok, result} = RpcConditions.check_trace(profile(), [], actions)
    assert result.outcome == :timeout
    assert result.mailbox.queue == [reply()]

    assert {:error, {:rpc_mailbox_step, _, :receive_not_allowed}} =
             RpcConditions.check_trace(profile(), [], actions ++ [:begin_receive])
  end

  test "monitor DOWN and reply races select the oldest eligible message" do
    p = profile(monitor_id: 9)
    down = {:tuple5, {:atom, "DOWN"}, {:ref, 9}, {:atom, "process"}, {:pid, 2}, {:atom, "gone"}}
    start = [{:protocol, :monitor_peer}] ++ sent() ++ server()

    assert {:ok, failed} =
             RpcConditions.check_trace(
               p,
               [],
               start ++ [{:arrive, down}, {:arrive, reply()}, :inspect]
             )

    assert failed.outcome == :peer_terminated and failed.mailbox.queue == [reply()]

    assert {:ok, ok} =
             RpcConditions.check_trace(
               p,
               [],
               start ++
                 [{:arrive, reply()}, {:arrive, down}, :inspect, {:protocol, :process_reply}]
             )

    assert ok.outcome == :success and ok.mailbox.queue == [down]
  end

  test "cannot bypass mailbox matching, widen canonical clauses or omit size/count conditions" do
    p = profile()

    assert {:error, {:rpc_mailbox_step, _, {:unsupported_rpc_timeline_item, _}}} =
             RpcConditions.check_trace(p, [], sent() ++ [{:protocol, :receive_reply}])

    forged = put_in(p.mailbox.clauses, [%{hd(p.mailbox.clauses) | pattern: :any}])
    assert {:error, :invalid_rpc_conditions} = RpcConditions.check_trace(forged, [], success())
    {:ok, s} = RpcProtocol.new(7)

    assert {:error, {:missing_rpc_size_condition, :request_size}} =
             RpcConditions.new(s, request(), [])

    assert {:error, _} =
             RpcConditions.new(s, request(),
               request_size: cap(),
               response_size: cap(),
               message_size: cap(),
               limits: limits(),
               protocol_limits: %{events: 10},
               timeout: 0
             )

    assert {:error, _} =
             RpcConditions.check_trace(
               profile(response_size: %RpcTerm.Size{nodes: 1, bytes: 0, integer_bits: 0}),
               [],
               success()
             )
  end
end
