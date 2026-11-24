defmodule ReductionBounds.PortWorkflowTest do
  use ExUnit.Case, async: true
  @moduletag timeout: 300_000

  alias ReductionBounds.{PortProtocol, ProtocolConditions, ProtocolCost, ProtocolSize}
  alias ReductionBounds.Fixtures.{PortClient, PortHelpers}

  @moduletag :port_workflow

  for {label, names, outcome} <- [
        {:empty, [], :pending},
        {:waiting, [:prepare, :submit_suspended], :pending},
        {:success, [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode],
         :success},
        {:rejection, [:prepare, :submit_rejected, :return_rejection], :rejected},
        {:closure, [:prepare, :submit_accepted, :port_closed, :handle_closure], :port_closed},
        {:timeout, [:prepare, :submit_accepted, :timeout_elapsed, :handle_timeout], :timeout},
        {:decoding_failure,
         [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode_error],
         :decode_error},
        {:retry,
         [
           :prepare,
           :submit_rejected,
           :retry,
           :submit_accepted,
           :inspect_message,
           :response_arrived,
           :receive_response,
           :decode
         ], :success}
      ] do
    @names names
    @outcome outcome
    test "public model workflow verifies #{label} and reports its exact scope" do
      assert {:ok, result} =
               ReductionBounds.verify_port_model(profile(), @names,
                 observations: observations(@names),
                 completion: completion()
               )

      assert result.lean_status == :checked
      assert result.source_correspondence == :not_checked
      assert result.verification_scope.kind == :supplied_port_model
      assert :finite_trace_and_prefix_cost_safety in result.verification_scope.checked
      assert result.completion.observed_outcome == @outcome
      assert result.completion.theorem_status == :checked_under_assumptions
      assert result.completion.actual_completion == :not_established
      assert result.external_work == :not_bounded

      assert {:ok, 1156} =
               ProtocolCost.evaluate(result.upper_bounds.caller.formula, %{event_work: 1})

      assert "ReductionBounds.PortCompletion.suppliedConditionalCompletion" in result.checked_theorems

      assert "ReductionBounds.ProtocolCost.suppliedPrefixSafety" in result.checked_theorems
      report(result)
    end
  end

  test "missing progress preserves the checked cost bound without a completion theorem" do
    names = [:prepare, :submit_accepted]

    assert {:ok, result} =
             ReductionBounds.verify_port_model(profile(), names,
               observations: observations(names)
             )

    assert result.lean_status == :checked
    assert result.completion.status == :insufficient_assumptions
    assert result.completion.theorem_status == :not_established
    assert result.verification_scope.conditional == []

    refute "ReductionBounds.PortCompletion.suppliedConditionalCompletion" in result.checked_theorems

    assert Enum.any?(result.diagnostics, &(&1.code == :missing_completion_assumption))
    report(result)
  end

  test "failure exclusion is explicit and inconsistent success retains only cost safety" do
    names = [:prepare, :submit_rejected, :return_rejection]

    goal =
      completion()
      |> Keyword.put(:goal, :success)
      |> Keyword.update!(:progress, &[:no_failure_outcomes | &1])

    assert {:ok, result} =
             ReductionBounds.verify_port_model(profile(), names,
               observations: observations(names),
               completion: goal
             )

    assert result.completion.status == :inconsistent_assumptions
    assert result.verification_scope.conditional == []
    assert Enum.any?(result.diagnostics, &(&1.code == :inconsistent_completion_assumptions))
  end

  test "successful completion remains a model theorem under failure exclusion" do
    names = [:prepare, :submit_accepted]

    goal =
      completion()
      |> Keyword.put(:goal, :success)
      |> Keyword.update!(:progress, &[:no_failure_outcomes | &1])

    assert {:ok, result} =
             ReductionBounds.verify_port_model(profile(), names,
               observations: observations(names),
               completion: goal
             )

    assert :model_success_under_failure_exclusion in result.verification_scope.conditional

    assert "ReductionBounds.PortCompletion.suppliedSuccessfulCompletion" in result.checked_theorems

    assert result.completion.actual_completion == :not_established
  end

  test "inconsistent completion limits do not discard a checked cost bound" do
    names = [:prepare, :submit_rejected]
    opts = Keyword.put(completion(), :limits, %{rejections: 0, resumptions: 3, inspections: 8})

    assert {:ok, result} =
             ReductionBounds.verify_port_model(profile(), names,
               observations: observations(names),
               completion: opts
             )

    assert result.completion.status == :inconsistent_limits
    assert result.verification_scope.conditional == []
    assert Enum.any?(result.diagnostics, &(&1.code == :inconsistent_completion_limits))
    assert "ReductionBounds.ProtocolCost.suppliedCostSafety" in result.checked_theorems
  end

  test "public source workflow separates checked correspondence from assumed helpers and completion" do
    assert {:ok, result} =
             ReductionBounds.infer_port_bound({PortClient, :request, 2}, profile(),
               calls: %{
                 prepare: {PortHelpers, :prepare, 1},
                 reply: {PortHelpers, :await_reply, 1},
                 decode: {PortHelpers, :decode, 1}
               },
               beam_binaries: ReductionBounds.TestFixtures.port_client_beams()
             )

    assert result.source_correspondence == :checked
    assert result.verification_scope.kind == :core_connected_port_client
    assert result.completion.scope == :source_code
    assert result.completion.theorem_status == :not_established
    assert result.verification_scope.assumptions.call_contracts.reply.status == :assumed
    assert :source_prefixes in result.verification_scope.unverified
    assert :source_completion in result.verification_scope.unverified

    assert {:ok, 1181} =
             ProtocolCost.evaluate(result.upper_bounds.caller.formula, %{
               event_work: 1,
               source_node: 1
             })

    refute Map.has_key?(result, :trace)
    assert "ReductionBounds.PortSource.suppliedSourceBound" in result.checked_theorems

    refute "ReductionBounds.PortCompletion.suppliedConditionalCompletion" in result.checked_theorems

    report(result)
  end

  test "rejects malformed input, missing sizes, insufficient counts, invalid transitions and forged flags" do
    base = profile()

    for events <- [[:unknown], [:prepare | :invalid], [1]] do
      assert {:error, _} = ReductionBounds.verify_port_model(base, events)
    end

    assert {:error, {:invalid_protocol_trace, 2, _, _}} =
             ReductionBounds.verify_port_model(base, [:prepare, :submit_accepted, :retry],
               observations: observations([:prepare, :submit_accepted, :retry])
             )

    assert {:error, {:protocol_count_exceeded, :total_events, _, 0}} =
             ReductionBounds.verify_port_model(profile(total_events: 0), [:prepare],
               observations: observations([:prepare])
             )

    altered =
      put_in(base.conditions.data_bounds, Map.delete(base.conditions.data_bounds, :response))

    assert {:error, _} = ReductionBounds.verify_port_model(altered, [])

    assert {:error, :invalid_cost_profile} =
             ReductionBounds.verify_port_model(Map.put(base, :lean_status, :checked), [])

    for options <- [[timeout: -1], [unexpected: true], [completion: [unexpected: true]]] do
      assert {:error, _} = ReductionBounds.verify_port_model(base, [], options)
    end

    target = {PortClient, :wrong_port, 2}

    assert {:error, {:port_source, ^target, {:reply_argument_mismatch, path}}} =
             ReductionBounds.infer_port_bound(target, base,
               calls: %{
                 prepare: {PortHelpers, :prepare, 1},
                 reply: {PortHelpers, :await_reply, 1},
                 decode: {PortHelpers, :decode, 1}
               },
               beam_binaries: ReductionBounds.TestFixtures.port_client_beams()
             )

    assert path != []
    assert {:error, _} = ReductionBounds.PortResult.verified(%{}, [])
    assert {:error, _} = ReductionBounds.PortResult.verified(%{}, [%{status: :error}])
  end

  defp profile(overrides \\ []) do
    counts =
      Map.merge(
        %{
          total_events: 30,
          submission_attempts: 4,
          submission_events: 8,
          resumptions: 3,
          retries: 3,
          receive_inspections: 8
        },
        Map.new(overrides)
      )

    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
        count_bounds: counts
      )

    rules =
      for {{_, event} = context, rule} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{} do
        cost =
          Enum.reduce(rule.data, {:charge, :event_work}, fn slot, rest ->
            {:add, rest, {:add, {:data, slot, :bytes}, {:data, slot, :structure}}}
          end)

        {context, %{counter: List.first(rule.counts) || :total_events, cost: cost}}
      end

    {:ok, profile} = ProtocolCost.new(conditions, rules)
    profile
  end

  defp observations(names) do
    {:ok, observation} = ProtocolConditions.observe(%{request: [], response: [], message: []})
    Map.new(Enum.with_index(names), fn {_, index} -> {index, observation} end)
  end

  defp completion,
    do: [
      limits: %{rejections: 2, resumptions: 3, inspections: 8},
      progress: [:caller_progress, :submission_progress, :resumption_progress, :response_progress]
    ]

  defp report(result) do
    if System.get_env("REDUCTION_BOUNDS_REPORT") == "1" do
      IO.inspect(
        Map.take(result, [
          :target,
          :upper_bounds,
          :supported_outcomes,
          :conditions,
          :completion,
          :verification_scope,
          :checked_theorems,
          :diagnostics
        ]),
        label: "Port verification",
        limit: :infinity,
        printable_limit: :infinity
      )
    end
  end
end
