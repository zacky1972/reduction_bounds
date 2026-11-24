defmodule ReductionBounds.RpcProtocol do
  @moduledoc """
  A supplied, single-attempt same-node RPC model on the protocol foundation.

  The client addresses one server by a direct PID, with at most one outstanding
  request. Natural-number identifiers are abstract correlation tokens, not
  actual Erlang references or proof of freshness. `monitor_id: id` enables an
  explicit process-monitor observation; sending never establishes delivery or
  detects a dead peer. Client/server event ownership and units stay separate.

  This first model checks declared transitions and correlation annotations.
  Arrival and unrelated-message events are observations, not a mailbox
  implementation. Queue order, matching patterns/guards, scan counts, sizes,
  costs, progress and source/runtime correspondence remain unverified.
  A terminal client trace does not cancel server work or remove late replies.
  Post-return mailbox effects, retries, aliases, priority messages, distributed
  peers and multiple outstanding requests are outside this model.

  `check_trace/2` is an Elixir check, not Lean proof evidence. The RPC proof
  builder connects the supplied trace to the canonical Lean model separately.
  """

  alias ReductionBounds.Protocol

  defmodule Session do
    @moduledoc "An abstract request, optional monitor and its canonical protocol."
    defstruct [:request_id, :monitor_id, :contract]

    @type t :: %__MODULE__{
            request_id: non_neg_integer(),
            monitor_id: non_neg_integer() | nil,
            contract: Protocol.Contract.t()
          }
  end

  defmodule Event do
    @moduledoc "A protocol event annotated with independent request/monitor tokens."
    defstruct [:protocol, :request_id, :monitor_id]

    @type t :: %__MODULE__{
            protocol: Protocol.Event.t(),
            request_id: non_neg_integer() | nil,
            monitor_id: non_neg_integer() | nil
          }
  end

  @request_events ~w(prepare send_request request_arrived receive_request handle_request
    send_reply reply_arrived receive_reply process_reply decode_error)a
  @monitor_events [:monitor_peer, :peer_down, :handle_peer_down]
  @waiting [
    :awaiting_request,
    :request_available,
    :request_received,
    :reply_ready,
    :awaiting_reply
  ]
  @terminal [:complete, :timed_out, :peer_terminated, :decode_failed]

  @spec new(non_neg_integer(), keyword()) :: {:ok, Session.t()} | {:error, term()}
  def new(request_id, options \\ []) do
    with true <- natural?(request_id),
         true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, monitor_id: nil),
         monitor_id = options[:monitor_id],
         true <- is_nil(monitor_id) or natural?(monitor_id),
         {:ok, contract} <- contract(not is_nil(monitor_id)) do
      {:ok, %Session{request_id: request_id, monitor_id: monitor_id, contract: contract}}
    else
      _ -> {:error, :invalid_rpc_session}
    end
  end

  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%Session{} = session) do
    with {:ok, canonical} <- new(session.request_id, monitor_id: session.monitor_id),
         true <- canonical == session do
      :ok
    else
      _ -> {:error, :invalid_rpc_session}
    end
  end

  def validate(_value), do: {:error, :invalid_rpc_session}

  @doc "Constructs an event; omitted token annotations use the session's tokens."
  @spec event(Session.t(), atom(), keyword()) :: {:ok, Event.t()} | {:error, term()}
  def event(session, name, options \\ []) do
    with :ok <- validate(session),
         true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, [:request_id, :monitor_id]),
         {:ok, protocol} <- Protocol.event(session.contract, name) do
      event = %Event{
        protocol: protocol,
        request_id:
          Keyword.get(options, :request_id, token(name, @request_events, session.request_id)),
        monitor_id:
          Keyword.get(options, :monitor_id, token(name, @monitor_events, session.monitor_id))
      }

      with :ok <- annotation(session, event), do: {:ok, event}
    else
      false -> {:error, :invalid_rpc_event_options}
      error -> error
    end
  end

  @doc "Checks one finite trace or unfinished prefix, with no cost/completion claim."
  @spec check_trace(Session.t(), [Event.t()]) :: {:ok, map()} | {:error, term()}
  def check_trace(session, events) do
    with :ok <- validate(session),
         :ok <- annotations(session, events, 0),
         {:ok, trace} <- Protocol.check_trace(session.contract, Enum.map(events, & &1.protocol)) do
      {:ok,
       %{
         source: :rpc_trace,
         session: session,
         events: events,
         trace: trace,
         outcome: outcome(trace.final),
         lean_status: :not_checked,
         source_correspondence: :not_checked,
         runtime_correspondence: :not_checked,
         verification_scope: %{
           kind: :supplied_rpc_model,
           checked: [],
           assumptions: [
             :same_node_direct_pid,
             :single_request,
             :declared_environment_observations
           ],
           trusted: [:model_serialization],
           unverified: [
             :mailbox_semantics,
             :matching_and_scanning,
             :sizes_and_counts,
             :cost_bound,
             :progress,
             :source_correspondence,
             :runtime_correspondence,
             :wall_clock_time
           ]
         }
       }}
    end
  end

  defp annotations(_session, [], _index), do: :ok

  defp annotations(session, [event | rest], index) do
    case annotation(session, event) do
      :ok -> annotations(session, rest, index + 1)
      {:error, reason} -> {:error, {:invalid_rpc_trace, index, reason}}
    end
  end

  defp annotations(_session, _events, _index), do: {:error, :invalid_rpc_events}

  defp annotation(session, %Event{protocol: %Protocol.Event{name: name}} = event) do
    expected =
      {token(name, @request_events, session.request_id),
       token(name, @monitor_events, session.monitor_id)}

    if {event.request_id, event.monitor_id} == expected,
      do: :ok,
      else: {:error, {:rpc_correlation_mismatch, name, expected}}
  end

  defp annotation(_session, _event), do: {:error, :invalid_rpc_event}
  defp token(name, names, value), do: if(name in names, do: value)
  defp natural?(value), do: is_integer(value) and value >= 0
  defp outcome(:complete), do: :success
  defp outcome(:timed_out), do: :timeout
  defp outcome(:peer_terminated), do: :peer_terminated
  defp outcome(:decode_failed), do: :decode_error
  defp outcome(_state), do: :pending

  defp contract(monitored) do
    client = {:client, :client_work}
    server = {:server, :server_work}
    environment = {nil, nil}

    events = %{
      prepare: client,
      send_request: client,
      request_arrived: environment,
      receive_request: server,
      handle_request: server,
      send_reply: server,
      reply_arrived: environment,
      receive_reply: client,
      process_reply: client,
      decode_error: client,
      unrelated_arrived: environment,
      inspect_unrelated: client,
      timeout_elapsed: environment,
      handle_timeout: client
    }

    Protocol.new(
      participants: %{client: :client_work, server: :server_work},
      states:
        [
          :idle,
          :monitored,
          :prepared,
          :awaiting_request,
          :request_available,
          :request_received,
          :reply_ready,
          :awaiting_reply,
          :reply_available,
          :reply_received,
          :timeout_observed,
          :peer_down_observed
        ] ++ @terminal,
      initial: :idle,
      terminal: @terminal,
      events:
        if(monitored,
          do:
            Map.merge(events, %{
              monitor_peer: client,
              peer_down: environment,
              handle_peer_down: client
            }),
          else: events
        ),
      transitions:
        preparation(monitored) ++
          [
            {:prepared, :send_request, :awaiting_request},
            {:awaiting_request, :request_arrived, :request_available},
            {:request_available, :receive_request, :request_received},
            {:request_received, :handle_request, :reply_ready},
            {:reply_ready, :send_reply, :awaiting_reply},
            {:awaiting_reply, :reply_arrived, :reply_available},
            {:reply_available, :receive_reply, :reply_received},
            {:reply_received, :process_reply, :complete},
            {:reply_received, :decode_error, :decode_failed},
            {:timeout_observed, :handle_timeout, :timed_out}
          ] ++ waiting_transitions(monitored)
    )
  end

  defp preparation(false), do: [{:idle, :prepare, :prepared}]

  defp preparation(true),
    do: [{:idle, :monitor_peer, :monitored}, {:monitored, :prepare, :prepared}]

  defp waiting_transitions(monitored) do
    inspections =
      for state <- @waiting ++ [:reply_available],
          event <- [:unrelated_arrived, :inspect_unrelated],
          do: {state, event, state}

    timeouts = for state <- @waiting, do: {state, :timeout_elapsed, :timeout_observed}

    down =
      if monitored,
        do: [
          {:peer_down_observed, :handle_peer_down, :peer_terminated}
          | for(state <- @waiting, do: {state, :peer_down, :peer_down_observed})
        ],
        else: []

    inspections ++ timeouts ++ down
  end
end
