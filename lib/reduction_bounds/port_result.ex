defmodule ReductionBounds.PortResult do
  @moduledoc false

  alias ReductionBounds.ProofInput

  @model_claims [
    :protocol_trace,
    :protocol_invariants,
    :participant_cost_safety,
    :finite_trace_and_prefix_cost_safety,
    :generated_formulas,
    :axiom_dependencies
  ]
  @source_claims [
    :core_value_agreement,
    :core_call_order,
    :core_argument_routing,
    :source_local_cost_bound,
    :source_protocol_trace_safety,
    :source_caller_bound,
    :generated_formulas,
    :axiom_dependencies
  ]

  @spec verified(map(), list()) :: {:ok, map()} | {:error, term()}
  def verified(candidate, reports) when is_list(reports) and reports != [] do
    if Enum.all?(reports, &match?(%{status: :ok}, &1)) do
      {:ok, finish(candidate, reports)}
    else
      {:error, {:verification_failed, reports}}
    end
  end

  def verified(_candidate, reports), do: {:error, {:verification_failed, reports}}

  defp finish(candidate, reports) do
    source? = candidate.source == :port_source
    completion = completion(candidate)
    scope = scope(candidate, source?, completion)

    clean_candidate(candidate, source?)
    |> Map.put(:reports, reports)
    |> Map.put(:lean_status, :checked)
    |> Map.put(:execution_domain, Map.get(candidate, :verification_scope))
    |> Map.put(:verification_scope, scope)
    |> Map.put(:source_correspondence, if(source?, do: :checked, else: :not_checked))
    |> Map.put(:completion, completion)
    |> Map.put(:checked_theorems, ProofInput.communication_theorems(candidate))
    |> Map.put(:conditions, conditions(candidate))
    |> Map.put(:diagnostics, diagnostics(candidate, completion))
    |> Map.put(:unverified, scope.unverified)
    |> Map.put(:external_work, :not_bounded)
    |> Map.put(:supported_outcomes, supported_outcomes(source?))
  end

  defp clean_candidate(candidate, true), do: Map.drop(candidate, [:trace, :rows, :counts])
  defp clean_candidate(candidate, false), do: candidate

  defp conditions(%{source: :port_source} = candidate), do: candidate.cost_profile.conditions
  defp conditions(candidate), do: candidate.conditions

  defp completion(%{source: :port_source}) do
    %{
      status: :not_established,
      scope: :source_code,
      theorem_status: :not_established,
      actual_completion: :not_established,
      missing_assumptions: [:source_totality, :source_prefix_correspondence]
    }
  end

  defp completion(candidate) do
    value = candidate.completion

    Map.merge(value, %{
      scope: :protocol_model,
      actual_completion: :not_established,
      theorem_status:
        if(value.status == :conditional, do: :checked_under_assumptions, else: :not_established)
    })
  end

  defp scope(candidate, source?, completion) do
    %{
      kind: if(source?, do: :core_connected_port_client, else: :supplied_port_model),
      checked: if(source?, do: @source_claims, else: @model_claims),
      conditional: conditional_claims(completion),
      assumptions: assumptions(candidate, completion),
      trusted:
        Enum.uniq(
          Map.get(candidate, :trusted, []) ++
            [:model_choice, :value_abstraction, :observation_association]
        ),
      unverified: unresolved(candidate, source?)
    }
  end

  defp conditional_claims(%{theorem_status: :checked_under_assumptions, goal: :success}),
    do: [:model_termination_under_progress, :model_success_under_failure_exclusion]

  defp conditional_claims(%{theorem_status: :checked_under_assumptions}),
    do: [:model_termination_under_progress]

  defp conditional_claims(_completion), do: []

  defp assumptions(candidate, completion) do
    %{
      protocol: %{
        caller_is_port_owner: true,
        outstanding_requests: 1,
        retry_only_after_rejection: true
      },
      size_and_count_conditions: conditions(candidate),
      observation_association: Map.get(candidate, :assumptions, []),
      call_contracts: Map.get(candidate, :call_contracts, %{}),
      primitive_contracts: Map.get(candidate, :primitive_contracts, []),
      completion: completion,
      external_work: :not_bounded
    }
  end

  defp unresolved(candidate, true),
    do:
      Enum.uniq(
        candidate.unverified ++ [:external_behavior, :environment_progress, :source_completion]
      )

  defp unresolved(_candidate, false),
    do: [
      :source_correspondence,
      :external_behavior,
      :environment_progress,
      :source_completion,
      :runtime_correspondence,
      :wall_clock_time
    ]

  defp diagnostics(%{source: :port_source}, _completion),
    do: [
      %{code: :assumed_call_contracts, severity: :condition},
      %{code: :source_completion_not_established, severity: :limitation},
      %{code: :source_prefixes_and_exceptions_not_checked, severity: :limitation}
    ]

  defp diagnostics(_candidate, completion) do
    missing =
      Enum.map(
        completion.missing_assumptions,
        &%{code: :missing_completion_assumption, condition: &1, severity: :condition}
      )

    inconsistent =
      case completion.status do
        :inconsistent_assumptions ->
          [%{code: :inconsistent_completion_assumptions, severity: :warning}]

        :inconsistent_limits ->
          [
            %{
              code: :inconsistent_completion_limits,
              evidence: completion.trace_evidence,
              severity: :warning
            }
          ]

        _ ->
          []
      end

    missing ++
      inconsistent ++ [%{code: :source_correspondence_not_checked, severity: :limitation}]
  end

  defp supported_outcomes(true), do: [:success, :rejected, :port_closed, :timeout]

  defp supported_outcomes(false),
    do: [:success, :rejected, :port_closed, :timeout, :decode_error, :pending]
end
