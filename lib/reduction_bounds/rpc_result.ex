defmodule ReductionBounds.RpcResult do
  @moduledoc false

  @spec verified(map(), list()) :: {:ok, map()} | {:error, term()}
  def verified(candidate, reports) when is_list(reports) and reports != [] do
    if Enum.all?(reports, &match?(%{status: :ok}, &1)) and
         Enum.any?(reports, &match?(%{module: "Erlang.postlude", status: :ok}, &1)) do
      {:ok, finish(candidate, reports)}
    else
      {:error, {:verification_failed, reports}}
    end
  end

  def verified(_candidate, reports), do: {:error, {:verification_failed, reports}}

  defp finish(candidate, reports) do
    source? = candidate.source == :rpc_source
    completion = completion(candidate, source?)
    original = candidate.verification_scope

    scope =
      Map.merge(original, %{
        kind: if(source?, do: :core_connected_rpc_client, else: :supplied_rpc_model),
        assumptions:
          Enum.uniq(
            original.assumptions ++
              Map.get(Map.get(candidate, :client_source_bound, %{}), :assumptions, [])
          ),
        checked: claims(source?, Map.has_key?(candidate, :upper_bounds)),
        conditional: conditional(source?, completion),
        trusted:
          Enum.uniq(
            Map.get(candidate, :trusted, []) ++ [:model_choice, :term_abstraction, :serialization]
          ),
        unverified:
          Enum.uniq(
            unresolved(original.unverified, source?) ++
              [:source_termination, :runtime_correspondence, :wall_clock_time]
          )
      })

    candidate
    |> Map.put(:execution_domain, original.kind)
    |> Map.put(:reports, reports)
    |> Map.put(:lean_status, :checked)
    |> Map.put(
      :source_correspondence,
      if(source?, do: :checked_under_contracts, else: :not_checked)
    )
    |> Map.put(:completion, completion)
    |> Map.put(:verification_scope, scope)
    |> Map.put(:unverified, scope.unverified)
    |> Map.put(:unsupported, unsupported(source?))
    |> Map.put(:diagnostics, diagnostics(completion, source?))
    |> handler_status()
  end

  defp unresolved(values, true),
    do:
      Enum.map(values, fn
        :source_correspondence -> :unrestricted_source_correspondence
        value -> value
      end)

  defp unresolved(values, false), do: values

  defp claims(true, _cost?),
    do: [
      :reified_core_connection,
      :request_and_argument_routing,
      :finite_normal_execution_protocol_agreement,
      :source_local_work_bound,
      :source_formula,
      :axiom_dependencies
    ]

  defp claims(false, true),
    do:
      claims(false, false) ++
        [:participant_cost_safety, :finite_trace_and_prefix_cost_safety, :generated_budgets]

  defp claims(false, false),
    do: [
      :supplied_rpc_mailbox_trace,
      :correlation,
      :ordered_matching,
      :size_and_count_conditions,
      :axiom_dependencies
    ]

  defp completion(_candidate, true),
    do: %{
      status: :not_established,
      scope: :source_code,
      theorem_status: :not_established,
      actual_completion: :not_established,
      missing_assumptions: [:source_totality, :source_prefix_correspondence]
    }

  defp completion(candidate, false) do
    c = candidate.completion

    Map.merge(c, %{
      scope: :protocol_model,
      actual_completion: :not_established,
      theorem_status:
        if(c.status == :conditional, do: :checked_under_assumptions, else: :not_established)
    })
  end

  defp conditional(true, _c),
    do: [
      :source_protocol_under_helper_contracts,
      :source_mailbox_and_cost_under_association_certificates
    ]

  defp conditional(false, %{theorem_status: :checked_under_assumptions, goal: :success}),
    do: [:model_termination_under_progress, :model_success_under_failure_exclusion]

  defp conditional(false, %{theorem_status: :checked_under_assumptions}),
    do: [:model_termination_under_progress]

  defp conditional(false, _c), do: []

  defp handler_status(%{server_contract: %{kind: :replay}} = c),
    do: put_in(c, [:server_contract, :status], :checked_under_contracts)

  defp handler_status(c), do: c

  defp unsupported(true),
    do: [
      :native_receive,
      :monitored_source,
      :retries,
      :recursion,
      :dynamic_calls,
      :exceptions,
      :source_prefixes,
      :receive_optimization
    ]

  defp unsupported(false),
    do: [
      :retries,
      :distributed_rpc,
      :priority_messages,
      :multiplexed_requests,
      :receive_optimization
    ]

  defp diagnostics(c, source?) do
    missing =
      Enum.map(
        c.missing_assumptions,
        &%{code: :missing_completion_assumption, condition: &1, severity: :condition}
      )

    inconsistency =
      if c.status in [:inconsistent_assumptions, :inconsistent_limits],
        do: [%{code: c.status, severity: :condition}],
        else: []

    source =
      if source?,
        do: [
          %{code: :assumed_helper_implementations, severity: :condition},
          %{code: :source_mailbox_association_required, severity: :condition}
        ],
        else: []

    missing ++ inconsistency ++ source
  end
end
