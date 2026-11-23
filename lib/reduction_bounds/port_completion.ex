defmodule ReductionBounds.PortCompletion do
  @moduledoc """
  Explicit conditions for completion of the supplied external Port model.

  `check_trace/4` retains the participant cost result even when progress
  assumptions are missing. Options are `limits: %{rejections: r,
  resumptions: s, inspections: i}`, `progress: [...]`, and
  `goal: :termination | :success` (default `:termination`). Limits are natural
  numbers and apply over the entire interaction, not just the observed prefix.
  Inspections include retrieval of the matching response.

  The four progress declarations are `:caller_progress`,
  `:submission_progress`, `:resumption_progress`, and `:response_progress`.
  They assume an eventual next event in each corresponding nonterminal state,
  with the modeled transition and remaining limits respected. Arbitrarily
  long idle waiting is allowed. These declarations do not prove the actual
  scheduler, external program, or response delivery behaves that way.

  Termination includes success, final rejection, closure, application timeout,
  or decoding failure. Successful completion additionally requires
  `:no_failure_outcomes`. Active events decrease a natural rank; idle waiting
  does not. The bound on active event occurrences is not a bound on elapsed
  time. A proof builder emits theorems with explicit progress hypotheses;
  constructors leave `lean_status: :not_checked`.
  """

  alias ReductionBounds.{PortProtocol, ProtocolCost}

  @progress [:caller_progress, :submission_progress, :resumption_progress, :response_progress]
  @limit_keys [:rejections, :resumptions, :inspections]
  @outcomes %{
    complete: :success,
    failed: :rejected,
    closed: :port_closed,
    timed_out: :timeout,
    decode_failed: :decode_error
  }

  @spec check_trace(ProtocolCost.t(), list(), map(), keyword()) :: {:ok, map()} | {:error, term()}
  def check_trace(profile, events, observations \\ %{}, options \\ []) do
    with {:ok, result} <- ProtocolCost.check_trace(profile, events, observations),
         {:ok, contract} <- PortProtocol.new(),
         true <- profile.conditions.contract == contract,
         {:ok, settings} <- settings(options) do
      completion = completion(result.trace, settings)

      {:ok,
       Map.merge(result, %{
         source: :port_completion,
         completion: completion,
         verification_scope: :supplied_port_model,
         external_work: :not_bounded,
         trusted: [:model_serialization, :observation_association],
         unverified:
           Enum.uniq(
             result.unverified ++
               [:completion, :source_correspondence, :runtime_correspondence, :wall_clock_time]
           )
       })}
    else
      false -> {:error, :unsupported_port_contract}
      error -> error
    end
  end

  defp settings(options) do
    defaults = [limits: %{}, progress: [], goal: :termination]

    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, defaults),
         true <- options[:goal] in [:termination, :success],
         true <- valid_limits?(options[:limits]),
         true <- valid_progress?(options[:progress]) do
      {:ok, Map.new(options)}
    else
      false -> {:error, :invalid_port_completion_options}
      {:error, keys} -> {:error, {:unknown_port_completion_options, Enum.sort(keys)}}
    end
  end

  defp valid_limits?(limits) when is_map(limits) and not is_struct(limits),
    do: Enum.all?(limits, fn {key, n} -> key in @limit_keys and is_integer(n) and n >= 0 end)

  defp valid_limits?(_limits), do: false

  defp valid_progress?([]), do: true

  defp valid_progress?([value | rest]),
    do: value in (@progress ++ [:no_failure_outcomes]) and valid_progress?(rest)

  defp valid_progress?(_values), do: false

  defp completion(trace, settings) do
    needed =
      if settings.goal == :success, do: @progress ++ [:no_failure_outcomes], else: @progress

    missing =
      (needed -- settings.progress) ++
        Enum.map(@limit_keys -- Map.keys(settings.limits), &{:limit, &1})

    certificate = configurations(trace, settings.limits)

    %{
      status: completion_status(trace, settings, missing, certificate),
      goal: settings.goal,
      assumptions: settings.progress,
      required_assumptions: needed,
      missing_assumptions: missing,
      limits: settings.limits,
      observed_outcome: Map.get(@outcomes, trace.final, :pending),
      supported_outcomes: @outcomes,
      trace_evidence: certificate,
      active_event_bound: event_bound(settings.limits),
      successful_response_requires: [:no_failure_outcomes],
      external_progress:
        Map.new(
          @progress -- [:caller_progress],
          &{&1, if(&1 in settings.progress, do: :assumed, else: :missing)}
        ),
      elapsed_time_bound: :not_established
    }
  end

  defp completion_status(trace, %{goal: :success}, _missing, _certificate)
       when trace.final in [:failed, :closed, :timed_out, :decode_failed],
       do: :inconsistent_assumptions

  defp completion_status(
         _trace,
         %{goal: :success, limits: %{inspections: 0}},
         _missing,
         _certificate
       ),
       do: :inconsistent_limits

  defp completion_status(_trace, _settings, missing, certificate),
    do: status(missing, certificate)

  defp status([], {:ok, _}), do: :conditional
  defp status([], {:error, _}), do: :inconsistent_limits
  defp status(_missing, _certificate), do: :insufficient_assumptions

  defp event_bound(limits) do
    if Enum.all?(@limit_keys, &Map.has_key?(limits, &1)),
      do: 9 + 10 * Enum.sum(Map.values(limits)),
      else: :unknown
  end

  defp configurations(trace, limits) do
    if Enum.all?(@limit_keys, &Map.has_key?(limits, &1)) do
      initial = Map.put(limits, :state, hd(trace.states))

      trace.events
      |> Enum.zip(tl(trace.states))
      |> Enum.with_index()
      |> Enum.reduce_while({:ok, [initial]}, &advance/2)
      |> reverse_configurations()
    else
      {:error, :missing_completion_limits}
    end
  end

  defp advance({{event, state}, index}, {:ok, [previous | _] = configurations}) do
    key = counter(event.name)

    if key != nil and Map.fetch!(previous, key) == 0 do
      {:halt, {:error, {:port_completion_limit_exceeded, index, event.name, key}}}
    else
      next = Map.put(previous, :state, state)
      next = if key, do: Map.update!(next, key, &(&1 - 1)), else: next
      {:cont, {:ok, [next | configurations]}}
    end
  end

  defp reverse_configurations({:ok, configurations}), do: {:ok, Enum.reverse(configurations)}
  defp reverse_configurations(error), do: error

  defp counter(:submit_rejected), do: :rejections
  defp counter(:resume_submission), do: :resumptions
  defp counter(event) when event in [:inspect_message, :receive_response], do: :inspections
  defp counter(_event), do: nil
end
