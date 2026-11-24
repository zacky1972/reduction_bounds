defmodule ReductionBounds.RpcCompletion do
  @moduledoc """
  Conditional completion of the supplied single-attempt RPC/mailbox model.

  Completion is separate from cost safety: no rate or server cost bound implies
  scheduling, delivery or eventual selection. `check_trace/4` accepts
  `progress: [...]` and `goal: :termination | :success` (default `:termination`).
  Progress declarations are `:client_progress`, `:request_progress`,
  `:server_progress` and `:response_progress`. Each assumes an eventual next
  admitted action from every corresponding nonterminal continuation, respecting
  all size/count limits. Success additionally requires `:no_failure_outcomes`.
  A finite successful example is not evidence for those universal assumptions.

  The active-action rank uses the existing total mailbox step allowance and
  canonical RPC phases. Arrivals, receive setup, inspections and timeout consume
  mailbox steps; other protocol actions decrease the control phase. Suspension
  changes neither. Retries remain zero. Active-action counts are not elapsed
  time bounds. Timeout values are not progress evidence or cost budgets.

  Builders retain `lean_status: :not_checked`. Missing progress evidence produces
  `:insufficient_assumptions`; a separate cost proof can remain usable. Source
  termination, actual scheduling and runtime correspondence remain unverified.
  """
  alias ReductionBounds.RpcConditions

  @progress [:client_progress, :request_progress, :server_progress, :response_progress]
  @failure ~w(timeout_observed peer_down_observed timed_out peer_terminated decode_failed)a

  @spec check_trace(map(), list(), list(), keyword()) :: {:ok, map()} | {:error, term()}
  def check_trace(conditions, queue, timeline, options \\ []) do
    with {:ok, candidate} <- RpcConditions.check_trace(conditions, queue, timeline) do
      assess(candidate, options)
    end
  end

  @doc false
  @spec assess(map(), keyword()) :: {:ok, map()} | {:error, term()}
  def assess(candidate, options) do
    with {:ok, settings} <- settings(options) do
      required = @progress ++ if(settings.goal == :success, do: [:no_failure_outcomes], else: [])
      missing = required -- settings.progress

      completion = %{
        status: status(candidate, settings, missing),
        goal: settings.goal,
        assumptions: settings.progress,
        required_assumptions: required,
        missing_assumptions: missing,
        observed_outcome: candidate.outcome,
        active_action_bound: 11 + 12 * candidate.conditions.mailbox.limits.steps,
        remaining_mailbox_steps:
          candidate.conditions.mailbox.limits.steps - candidate.counts.steps,
        retries: 0,
        model: :instrumented_rpc_mailbox,
        external_progress:
          Map.new(@progress, &{&1, if(&1 in settings.progress, do: :assumed, else: :missing)}),
        elapsed_time_bound: :not_established,
        source_termination: :not_checked
      }

      {:ok, Map.put(candidate, :completion, completion)}
    end
  end

  defp settings(options) do
    with true <- Keyword.keyword?(options),
         {:ok, settings} <- Keyword.validate(options, progress: [], goal: :termination),
         true <- settings[:goal] in [:termination, :success],
         true <- is_list(settings[:progress]),
         true <- Enum.all?(settings[:progress], &(&1 in (@progress ++ [:no_failure_outcomes]))) do
      {:ok, %{goal: settings[:goal], progress: Enum.uniq(settings[:progress])}}
    else
      _ -> {:error, :invalid_rpc_completion_options}
    end
  end

  defp status(candidate, settings, missing) do
    cond do
      excludes_failures?(settings) and candidate.trace.final in @failure ->
        :inconsistent_assumptions

      impossible_limits?(candidate.conditions, settings.goal) ->
        :inconsistent_limits

      missing != [] ->
        :insufficient_assumptions

      true ->
        :conditional
    end
  end

  defp excludes_failures?(settings),
    do: settings.goal == :success or :no_failure_outcomes in settings.progress

  defp impossible_limits?(conditions, goal) do
    m = conditions.mailbox.limits
    p = conditions.protocol_limits

    base =
      m.steps < 2 or m.receives == 0 or p.client_sends == 0 or p.response_handlers == 0 or
        p.events == 0

    base or (goal == :success and (m.inspections == 0 or p.server_sends == 0))
  end
end
