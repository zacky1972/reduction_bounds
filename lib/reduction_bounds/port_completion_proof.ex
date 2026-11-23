defmodule ReductionBounds.PortCompletionProof do
  @moduledoc false

  alias ReductionBounds.{PortCompletion, ProofInput, ProtocolCostProof}

  @spec build(ReductionBounds.ProtocolCost.t(), list(), map(), keyword()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(profile, events, observations \\ %{}, options \\ []) do
    with {:ok, result} <- PortCompletion.check_trace(profile, events, observations, options),
         {:ok, _cost, proof} <- ProtocolCostProof.build(profile, events, observations) do
      completion = result.completion

      source = """

      namespace ReductionBounds.PortCompletion
      open ReductionBounds.Protocol (suppliedContract suppliedEvents suppliedStates)

      theorem suppliedRanking : Ranked suppliedContract := by decide
      theorem suppliedPostAcceptance : PostAcceptanceSafe suppliedContract := by decide
      theorem suppliedSuccessSpec : SuccessSpec suppliedContract := by decide
      theorem suppliedInitialKnown : suppliedContract.initial ∈ suppliedContract.states := by decide

      theorem suppliedStateInvariant :
          ReductionBounds.Protocol.suppliedFinal ∈ suppliedContract.states := by
        apply ReductionBounds.Protocol.suppliedInvariant (fun s => s ∈ suppliedContract.states)
        · exact suppliedInitialKnown
        · intro before event after allowed _
          exact allowed.2.2.2.2.2

      theorem suppliedTerminalBudget
          (charge : ReductionBounds.ProtocolCost.Charges) (owner : String)
          (events : List ReductionBounds.Protocol.Event) (states : List String)
          (observations : List ReductionBounds.ProtocolConditions.Observation)
          (rows : ReductionBounds.ProtocolConditions.RowsHold ReductionBounds.ProtocolConditions.suppliedSpec
            suppliedContract.initial events states observations)
          (counts : ReductionBounds.ProtocolConditions.CountsHold ReductionBounds.ProtocolConditions.suppliedSpec
            suppliedContract.initial events states)
          (terminal : ReductionBounds.Protocol.finish suppliedContract.initial states ∈ suppliedContract.terminal) :
          ReductionBounds.ProtocolCost.traceCost ReductionBounds.ProtocolCost.suppliedEntries charge owner
            suppliedContract.initial events states observations ≤
            (ReductionBounds.ProtocolCost.boundExpr ReductionBounds.ProtocolConditions.suppliedSpec owner
              ReductionBounds.ProtocolCost.suppliedGroups).eval (charge owner) (fun _ => 0) ∧
          ReductionBounds.Protocol.finish suppliedContract.initial states ∈
            ["complete", "failed", "closed", "timed_out", "decode_failed"] := by
        exact ⟨ReductionBounds.ProtocolCost.suppliedCostSafety charge owner events states observations rows counts,
          by simpa [suppliedContract] using terminal⟩

      #{trace_evidence(completion)}
      #{completion_theorems(completion)}
      end ReductionBounds.PortCompletion
      """

      proof = %{proof | source: proof.source <> source}

      metadata = %{
        source: :port_completion,
        completion_status: completion.status,
        goal: completion.goal,
        trace_checked: match?({:ok, _}, completion.trace_evidence)
      }

      {proof, audit} = ProofInput.audit_bound(proof, metadata)
      {:ok, Map.put(result, :completion_proof_audit, audit), proof}
    end
  end

  defp trace_evidence(%{trace_evidence: {:ok, [initial | rest]}} = completion) do
    """
    def suppliedInitial : Configuration := #{configuration(initial)}
    def suppliedConfigurations : List Configuration := [#{Enum.map_join(rest, ", ", &configuration/1)}]
    theorem suppliedConfigurationStates :
        suppliedConfigurations.map Configuration.state = suppliedStates := by decide
    theorem suppliedMovesCertificate :
        checkMoves suppliedContract suppliedInitial suppliedEvents suppliedConfigurations = true := by decide
    theorem suppliedMoves : Moves suppliedContract suppliedInitial suppliedEvents
        (finish suppliedInitial suppliedConfigurations) :=
      checkMovesSound _ _ _ _ suppliedMovesCertificate
    theorem suppliedTraceRank : suppliedEvents.length + rank (finish suppliedInitial suppliedConfigurations) ≤
        rank suppliedInitial := suppliedMoves.bounded suppliedRanking
    theorem suppliedActiveBudget : rank suppliedInitial = #{completion.active_event_bound} := by decide
    """
  end

  defp trace_evidence(_completion), do: ""

  defp completion_theorems(%{status: :conditional} = completion) do
    """
    theorem suppliedConditionalCompletion (behavior : Behavior suppliedContract)
        (starts : behavior.config 0 = suppliedInitial) (progress : Progress behavior) :
        (∃ n, (behavior.config n).state ∈ suppliedContract.terminal) ∧
        (∀ n, activeCount behavior n ≤ #{completion.active_event_bound}) := by
      refine ⟨conditionalCompletion suppliedContract suppliedRanking suppliedInitialKnown behavior progress, ?_⟩
      intro n
      have bounded := eventCountBound suppliedContract suppliedRanking behavior n
      rw [starts, suppliedActiveBudget] at bounded
      omega
    #{success_theorem(completion.goal)}
    """
  end

  defp completion_theorems(_completion), do: ""

  defp success_theorem(:success) do
    """
    theorem suppliedSuccessfulCompletion (behavior : Behavior suppliedContract)
        (progress : Progress behavior) (safe : NoFailure behavior) :
        ∃ n, (behavior.config n).state = "complete" :=
      successfulCompletion suppliedContract suppliedRanking suppliedSuccessSpec suppliedInitialKnown behavior progress safe
    """
  end

  defp success_theorem(_goal), do: ""

  defp configuration(value),
    do:
      "⟨#{ProofInput.string(Atom.to_string(value.state))}, #{value.rejections}, #{value.resumptions}, #{value.inspections}⟩"
end
