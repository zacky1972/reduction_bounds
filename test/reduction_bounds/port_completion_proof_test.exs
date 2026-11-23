defmodule ReductionBounds.PortCompletionProofTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{
    PortCompletionProof,
    PortProtocol,
    ProofInput,
    Protocol,
    ProtocolConditions,
    ProtocolCost,
    ProtocolSize
  }

  @moduletag :port_completion

  for {label, names} <- [
        {:empty, []},
        {:suspended, [:prepare, :submit_suspended]},
        {:success, [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode]},
        {:rejection, [:prepare, :submit_rejected, :return_rejection]},
        {:retry_and_closure,
         [
           :prepare,
           :submit_suspended,
           :resume_submission,
           :submit_rejected,
           :retry,
           :submit_accepted,
           :inspect_message,
           :port_closed,
           :handle_closure
         ]},
        {:timeout, [:prepare, :submit_accepted, :timeout_elapsed, :handle_timeout]},
        {:decode_failure,
         [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode_error]}
      ] do
    @scenario names
    test "Lean checks the #{label} path and conditional completion" do
      {profile, events, observations} = input(@scenario)

      assert {:ok, result, proof} =
               PortCompletionProof.build(profile, events, observations, options())

      assert result.completion.status == :conditional
      assert_ok(proof)
    end
  end

  test "Lean checks success under an additional failure-exclusion assumption" do
    {profile, events, observations} = input([:prepare, :submit_accepted])

    opts =
      options()
      |> Keyword.put(:goal, :success)
      |> Keyword.update!(:progress, &[:no_failure_outcomes | &1])

    {:ok, result, proof} = PortCompletionProof.build(profile, events, observations, opts)
    assert result.completion.status == :conditional
    assert proof.source =~ "theorem suppliedSuccessfulCompletion"
    assert_ok(proof)
  end

  test "missing progress preserves cost safety and emits no supplied completion theorem" do
    {profile, events, observations} = input([:prepare, :submit_accepted])
    {:ok, result, proof} = PortCompletionProof.build(profile, events, observations)
    assert result.completion.status == :insufficient_assumptions
    refute proof.source =~ "theorem suppliedConditionalCompletion"
    assert proof.source =~ "theorem suppliedCostSafety"
    assert_ok(proof)
  end

  test "Lean rejects altered transitions, budget evidence and unfinished completion proofs" do
    {profile, events, observations} = input([:prepare, :submit_accepted])
    {:ok, _, proof} = PortCompletionProof.build(profile, events, observations, options())

    for {from, to} <- [
          {~S|⟨"prepared", "submit_accepted", "awaiting_response"⟩|,
           ~S|⟨"prepared", "submit_accepted", "idle"⟩|},
          {"rank suppliedInitial = 139", "rank suppliedInitial = 0"},
          {"checkMoves suppliedContract suppliedInitial suppliedEvents suppliedConfigurations = true := by decide",
           "checkMoves suppliedContract suppliedInitial suppliedEvents suppliedConfigurations = true := by sorry"}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end
  end

  test "Lean exhibits permanent waiting without progress and rejects unconditional completion" do
    {profile, events, observations} = input([])
    {:ok, _, proof} = PortCompletionProof.build(profile, events, observations, options())

    waiting = """
    namespace ReductionBounds.PortCompletion
    example : ¬ ∃ n, ((stalledBehavior ReductionBounds.Protocol.suppliedContract suppliedInitial
        (by decide)).config n).state ∈ ReductionBounds.Protocol.suppliedContract.terminal :=
      stalledNotComplete _ _ (by decide) (by decide)
    end ReductionBounds.PortCompletion
    """

    assert_ok(%{proof | source: proof.source <> waiting})
    false_claim = String.replace(waiting, "example : ¬ ∃", "example : ∃")

    assert Enum.any?(
             reports(%{proof | source: proof.source <> false_claim}),
             &(&1.status == :error)
           )
  end

  defp options do
    [
      limits: %{rejections: 2, resumptions: 3, inspections: 8},
      progress: [:caller_progress, :submission_progress, :resumption_progress, :response_progress]
    ]
  end

  defp input(names) do
    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
        count_bounds: %{
          total_events: 30,
          submission_attempts: 4,
          submission_events: 8,
          resumptions: 3,
          retries: 3,
          receive_inspections: 8
        }
      )

    rules =
      for {{_, event} = context, _} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{},
          do: {context, %{counter: :total_events, cost: {:charge, :local}}}

    {:ok, profile} = ProtocolCost.new(conditions, rules)

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(conditions.contract, name)
        event
      end)

    {:ok, observation} = ProtocolConditions.observe(%{request: [], response: [], message: []})
    observations = Map.new(Enum.with_index(events), fn {_, i} -> {i, observation} end)
    {profile, events, observations}
  end

  defp assert_ok(proof) do
    reports = reports(proof)
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  defp reports(proof) do
    {:ok, postludes} = ProofInput.port_completion_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    Lynx.Commands.verify!(project, ProofInput.assemble(translation))
  end
end
