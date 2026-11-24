defmodule ReductionBounds.RpcConditions do
  @moduledoc """
  Connects a supplied RPC trace to a checked client mailbox timeline.

  Timeline entries are `{:protocol, name}`, `{:arrive, reified_term}`,
  `:begin_receive`, `:inspect`, and `:timeout`. Receive/timeout/down observations
  are derived from mailbox execution, never accepted as free annotations.
  The coarse RPC arrival observation is emitted when the message is selected;
  physical modeled arrivals are recorded separately by mailbox actions.

  A single RPC receive is supported; retries remain zero. After client return,
  arrivals may append without reviving the operation. Generic `Mailbox` traces
  additionally support repeated receives. Conditions hold for this supplied
  execution; future arrival/count bounds remain explicit assumptions, not an
  inferred guarantee about all runtime executions. Server mailbox behavior,
  reply provenance, source correspondence, cost and progress remain unverified.
  """
  alias ReductionBounds.{Mailbox, MailboxMatch, RpcProtocol, RpcTerm}

  @counts [:events, :client_sends, :server_sends, :response_handlers, :retries]
  @work ~w(monitor_peer prepare send_request request_arrived receive_request handle_request send_reply process_reply decode_error handle_timeout)a
  @waiting ~w(awaiting_request request_available request_received reply_ready awaiting_reply reply_available)a

  @spec new(RpcProtocol.Session.t(), RpcTerm.t(), keyword()) :: {:ok, map()} | {:error, term()}
  def new(session, request, options) do
    with :ok <- RpcProtocol.validate(session),
         true <- Keyword.keyword?(options),
         {:ok, options} <-
           Keyword.validate(options, [
             :request_size,
             :response_size,
             :message_size,
             :limits,
             :protocol_limits,
             timeout: :infinity,
             reply_guard: true
           ]),
         :ok <- sizes(options),
         true <- MailboxMatch.guard?(options[:reply_guard]),
         true <- request?(request, session.request_id),
         {:ok, request_size} <- RpcTerm.measure(request),
         true <- RpcTerm.within?(request_size, options[:request_size]),
         :ok <- protocol_limits(options[:protocol_limits]),
         {:ok, mailbox} <-
           Mailbox.new(
             clauses: clauses(session, options[:reply_guard]),
             message_size: options[:message_size],
             limits: options[:limits],
             timeout: options[:timeout]
           ) do
      {:ok,
       %{
         session: session,
         request: request,
         request_size: options[:request_size],
         response_size: options[:response_size],
         mailbox: mailbox,
         reply_guard: options[:reply_guard],
         protocol_limits: options[:protocol_limits]
       }}
    else
      false -> {:error, :invalid_rpc_conditions}
      error -> error
    end
  end

  @spec validate(term()) :: :ok | {:error, term()}
  def validate(
        %{
          session: s,
          request: req,
          request_size: rs,
          response_size: ps,
          mailbox: mb,
          reply_guard: g,
          protocol_limits: limits
        } = profile
      ) do
    with :ok <- Mailbox.validate(mb),
         {:ok, canonical} <-
           new(s, req,
             request_size: rs,
             response_size: ps,
             message_size: mb.message_size,
             limits: mb.limits,
             protocol_limits: limits,
             timeout: mb.timeout,
             reply_guard: g
           ),
         true <- canonical == profile do
      :ok
    else
      _ -> {:error, :invalid_rpc_conditions}
    end
  end

  def validate(_value), do: {:error, :invalid_rpc_conditions}

  @spec check_trace(map(), list(), list()) :: {:ok, map()} | {:error, term()}
  def check_trace(profile, queue, timeline) do
    with :ok <- validate(profile),
         {:ok, mailbox} <- Mailbox.initial(profile.mailbox, queue),
         state = %{
           mailbox: mailbox,
           counts: Mailbox.zero(),
           protocol_state: :idle,
           events: [],
           actions: [],
           protocol_counts: Map.new(@counts, &{&1, 0})
         },
         {:ok, final} <- walk(profile, timeline, state, 0),
         {:ok, candidate} <- RpcProtocol.check_trace(profile.session, final.events) do
      scope = candidate.verification_scope

      {:ok,
       Map.merge(candidate, %{
         source: :rpc_mailbox,
         conditions: profile,
         initial_queue: queue,
         timeline: timeline,
         mailbox: final.mailbox,
         mailbox_actions: final.actions,
         counts: final.counts,
         protocol_counts: final.protocol_counts,
         matching_program: profile.mailbox.clauses,
         verification_scope: %{
           scope
           | kind: :supplied_rpc_mailbox_model,
             assumptions:
               scope.assumptions ++ [:declared_size_and_count_conditions, :ordinary_message_queue],
             unverified: [
               :all_trace_count_bounds,
               :server_mailbox,
               :reply_provenance,
               :cost_bound,
               :progress,
               :source_correspondence,
               :runtime_correspondence,
               :wall_clock_time
             ]
         }
       })}
    end
  end

  @doc false
  @spec clauses(RpcProtocol.Session.t(), term()) :: [MailboxMatch.clause()]
  def clauses(session, guard) do
    reply = %{
      kind: :reply,
      pattern:
        {:tuple3, {:literal, {:atom, "reply"}}, {:literal, {:ref, session.request_id}}, :any},
      guard: guard
    }

    if is_nil(session.monitor_id),
      do: [reply],
      else: [
        reply,
        %{
          kind: :peer_down,
          pattern:
            {:tuple5, {:literal, {:atom, "DOWN"}}, {:literal, {:ref, session.monitor_id}},
             {:literal, {:atom, "process"}}, :pid, :any},
          guard: true
        }
      ]
  end

  defp walk(_profile, [], state, _index), do: {:ok, state}

  defp walk(profile, [item | rest], state, index) do
    with {:ok, next} <- step(profile, state, item), true <- within?(profile, next) do
      walk(profile, rest, next, index + 1)
    else
      false -> {:error, {:rpc_mailbox_step, index, :count_limit_exceeded}}
      {:error, reason} -> {:error, {:rpc_mailbox_step, index, reason}}
    end
  end

  defp walk(_profile, _timeline, _state, _index), do: {:error, :invalid_rpc_timeline}

  defp step(profile, state, {:protocol, name}) when name in @work,
    do: push(profile, state, [name])

  defp step(profile, state, {:arrive, _} = action), do: mailbox_step(profile, state, action)

  defp step(profile, state, :begin_receive) do
    if state.protocol_state in @waiting and state.counts.receives == 0,
      do: mailbox_step(profile, state, :begin_receive),
      else: {:error, :receive_not_allowed}
  end

  defp step(profile, state, action) when action in [:inspect, :timeout] do
    if state.protocol_state in @waiting,
      do: mailbox_step(profile, state, action),
      else: {:error, :receive_not_allowed}
  end

  defp step(_profile, _state, item), do: {:error, {:unsupported_rpc_timeline_item, item}}

  defp mailbox_step(profile, state, action) do
    with {:ok, mailbox, delta} <- Mailbox.step(profile.mailbox, state.mailbox, action) do
      next = %{
        state
        | mailbox: mailbox,
          counts: Mailbox.add(state.counts, delta),
          actions: state.actions ++ [action]
      }

      project(profile, next, action)
    end
  end

  defp project(profile, %{mailbox: %{phase: :selected}} = state, :inspect) do
    with {:ok, size} <- RpcTerm.measure(state.mailbox.selected),
         true <- RpcTerm.within?(size, profile.response_size) do
      case Enum.at(profile.mailbox.clauses, state.mailbox.clause).kind do
        :reply -> push(profile, state, [:reply_arrived, :receive_reply])
        :peer_down -> push(profile, state, [:peer_down, :handle_peer_down])
      end
    else
      _ -> {:error, :response_size_exceeded}
    end
  end

  defp project(profile, state, :inspect), do: push(profile, state, [:inspect_unrelated])
  defp project(profile, state, :timeout), do: push(profile, state, [:timeout_elapsed])
  defp project(_profile, state, _action), do: {:ok, state}

  defp push(_profile, state, []), do: {:ok, state}

  defp push(profile, state, [name | rest]) do
    with {:ok, event} <- RpcProtocol.event(profile.session, name),
         {:ok, trace} <- RpcProtocol.check_trace(profile.session, state.events ++ [event]) do
      counts = state.protocol_counts |> Map.update!(:events, &(&1 + 1)) |> tick(name)

      push(
        profile,
        %{
          state
          | events: trace.events,
            protocol_state: trace.trace.final,
            protocol_counts: counts
        },
        rest
      )
    end
  end

  defp tick(c, :send_request), do: Map.update!(c, :client_sends, &(&1 + 1))
  defp tick(c, :send_reply), do: Map.update!(c, :server_sends, &(&1 + 1))

  defp tick(c, name)
       when name in [:process_reply, :decode_error, :handle_peer_down, :handle_timeout],
       do: Map.update!(c, :response_handlers, &(&1 + 1))

  defp tick(c, _name), do: c

  defp within?(profile, state),
    do:
      Mailbox.counts_within?(state.counts, profile.mailbox.limits) and
        Enum.all?(@counts, &(state.protocol_counts[&1] <= profile.protocol_limits[&1]))

  defp sizes(options) do
    case Enum.find(
           [:request_size, :response_size, :message_size],
           &(not RpcTerm.known?(options[&1]))
         ) do
      nil -> :ok
      field -> {:error, {:missing_rpc_size_condition, field}}
    end
  end

  defp protocol_limits(limits) when is_map(limits) and not is_struct(limits) do
    if Enum.sort(Map.keys(limits)) == Enum.sort(@counts) and
         Enum.all?(Map.values(limits), &(is_integer(&1) and &1 >= 0)) and limits.retries == 0,
       do: :ok,
       else: {:error, :invalid_rpc_count_conditions}
  end

  defp protocol_limits(_limits), do: {:error, :invalid_rpc_count_conditions}
  defp request?({:tuple3, {:atom, "request"}, {:ref, id}, _payload}, expected), do: id == expected
  defp request?(_term, _expected), do: false
end
