defmodule ReductionBounds.PortProtocol do
  @moduledoc """
  An initial, supplied Port protocol model, not an analysis of Port-using code.

  The caller is the Port owner and has at most one request in progress.
  Only rejected submissions can be retried; acceptance cannot be followed by
  another submission. Arrival and closure are environment observations with
  no owned work charge. Receiving, decoding, closure handling, and suspension handling are
  distinct caller-owned work events. Waiting itself is a state.

  The model permits unfinished prefixes, repeated receive inspections, and
  rejected-submission retries. It imposes no count bounds or progress
  assumptions. Units are symbolic labels and do not identify ERTS reductions.
  External computation and port-side costs are not inferred or bounded.

  `:timeout_elapsed` represents an application receive-timeout observation
  while awaiting a response, followed by caller-owned `:handle_timeout`.
  It is not a timeout option for port command submission and cannot interrupt
  a suspended submission. `:decode_error` is a distinct terminal outcome.
  Conditional completion requires separate progress and finite-loop conditions;
  neither an accepted command nor a cost bound establishes response arrival.
  """

  alias ReductionBounds.{Protocol, ProtocolConditions}
  alias ReductionBounds.ProtocolConditions.Rule

  @spec new() :: {:ok, Protocol.Contract.t()} | {:error, term()}
  def new() do
    work = {:caller, :symbolic_work}
    environment = {nil, nil}

    Protocol.new(
      participants: %{caller: :symbolic_work, port: :port_work, external: :external_work},
      states: [
        :idle,
        :prepared,
        :submission_wait,
        :submission_resumed,
        :rejected,
        :awaiting_response,
        :response_available,
        :response_received,
        :closure_observed,
        :timeout_observed,
        :timed_out,
        :decode_failed,
        :complete,
        :failed,
        :closed
      ],
      initial: :idle,
      terminal: [:complete, :failed, :closed, :timed_out, :decode_failed],
      events: %{
        prepare: work,
        submit_accepted: work,
        submit_rejected: work,
        submit_suspended: work,
        resume_submission: work,
        retry: work,
        return_rejection: work,
        inspect_message: work,
        receive_response: work,
        decode: work,
        decode_error: work,
        handle_timeout: work,
        timeout_elapsed: environment,
        handle_closure: work,
        response_arrived: environment,
        port_closed: environment
      },
      transitions:
        [
          {:idle, :prepare, :prepared},
          {:prepared, :submit_accepted, :awaiting_response},
          {:prepared, :submit_rejected, :rejected},
          {:prepared, :submit_suspended, :submission_wait},
          {:submission_wait, :resume_submission, :submission_resumed},
          {:submission_resumed, :submit_accepted, :awaiting_response},
          {:submission_resumed, :submit_rejected, :rejected},
          {:submission_resumed, :submit_suspended, :submission_wait},
          {:rejected, :retry, :prepared},
          {:rejected, :return_rejection, :failed},
          {:awaiting_response, :inspect_message, :awaiting_response},
          {:awaiting_response, :response_arrived, :response_available},
          {:response_available, :inspect_message, :response_available},
          {:response_available, :receive_response, :response_received},
          {:response_received, :decode, :complete},
          {:response_received, :decode_error, :decode_failed},
          {:awaiting_response, :timeout_elapsed, :timeout_observed},
          {:timeout_observed, :handle_timeout, :timed_out},
          {:closure_observed, :handle_closure, :closed}
        ] ++ closure_transitions()
    )
  end

  @doc """
  Builds explicit conditions for the initial Port model.

  Supply finite `data_bounds` for `:request`, `:response`, and `:message`,
  and `count_bounds` for `:total_events`, `:submission_attempts`,
  `:submission_events`, `:resumptions`, `:retries`, and `:receive_inspections`.
  Inspection counts include the matching response. Submission outcomes after
  resumption add work events but do not begin another submission attempt.

  Optional `integer_events` associates event names with integer-condition
  names in `integer_bounds`. These associations are user-supplied conditions,
  not a proof of request encoding or response decoding.
  """
  @spec conditions(keyword()) :: {:ok, ProtocolConditions.t()} | {:error, term()}
  def conditions(options) do
    with true <- Keyword.keyword?(options),
         {:ok, options} <-
           Keyword.validate(options, [
             :data_bounds,
             :integer_bounds,
             :count_bounds,
             :integer_events
           ]),
         {:ok, contract} <- new() do
      {integer_events, options} = Keyword.pop(options, :integer_events, %{})
      build_conditions(contract, options, integer_events)
    else
      false -> {:error, :invalid_protocol_condition_options}
      error -> error
    end
  end

  defp build_conditions(contract, options, integers) do
    with :ok <- integer_events(contract, integers) do
      rules =
        Map.new(contract.transitions, fn {state, event, _next} ->
          rule = %Rule{
            data: data_fields(event),
            integers: Map.get(integers, event, []),
            counts: counters(state, event)
          }

          {{state, event}, rule}
        end)

      ProtocolConditions.new(contract, Keyword.put(options, :rules, rules))
    end
  end

  defp integer_events(contract, values) when is_map(values) and not is_struct(values) do
    if Enum.all?(Map.keys(values), &Map.has_key?(contract.events, &1)),
      do: :ok,
      else: {:error, {:unknown_integer_event, Map.keys(values)}}
  end

  defp integer_events(_contract, values), do: {:error, {:invalid_integer_events, values}}

  defp data_fields(event)
       when event in [:prepare, :submit_accepted, :submit_rejected, :submit_suspended],
       do: [:request]

  defp data_fields(event)
       when event in [:response_arrived, :receive_response, :decode, :decode_error],
       do: [:response]

  defp data_fields(:inspect_message), do: [:message]
  defp data_fields(_event), do: []

  defp counters(:prepared, event)
       when event in [:submit_accepted, :submit_rejected, :submit_suspended],
       do: [:submission_events, :submission_attempts]

  defp counters(:submission_resumed, event)
       when event in [:submit_accepted, :submit_rejected, :submit_suspended],
       do: [:submission_events]

  defp counters(:submission_wait, :resume_submission), do: [:resumptions]
  defp counters(:rejected, :retry), do: [:retries]

  defp counters(_state, event) when event in [:inspect_message, :receive_response],
    do: [:receive_inspections]

  defp counters(_state, _event), do: []

  defp closure_transitions() do
    for state <- [
          :prepared,
          :submission_wait,
          :submission_resumed,
          :rejected,
          :awaiting_response,
          :response_available
        ],
        do: {state, :port_closed, :closure_observed}
  end
end
