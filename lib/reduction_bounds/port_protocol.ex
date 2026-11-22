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
  """

  alias ReductionBounds.Protocol

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
        :rejected,
        :awaiting_response,
        :response_available,
        :response_received,
        :closure_observed,
        :complete,
        :failed,
        :closed
      ],
      initial: :idle,
      terminal: [:complete, :failed, :closed],
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
          {:submission_wait, :resume_submission, :prepared},
          {:rejected, :retry, :prepared},
          {:rejected, :return_rejection, :failed},
          {:awaiting_response, :inspect_message, :awaiting_response},
          {:awaiting_response, :response_arrived, :response_available},
          {:response_available, :inspect_message, :response_available},
          {:response_available, :receive_response, :response_received},
          {:response_received, :decode, :complete},
          {:closure_observed, :handle_closure, :closed}
        ] ++ closure_transitions()
    )
  end

  defp closure_transitions() do
    for state <- [:prepared, :submission_wait, :rejected, :awaiting_response, :response_available],
        do: {state, :port_closed, :closure_observed}
  end
end
