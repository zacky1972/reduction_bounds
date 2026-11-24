defmodule ReductionBounds.RpcCompletionProof do
  @moduledoc false
  alias ReductionBounds.{ProofInput, RpcCompletion, RpcCostProof, RpcMailboxProof}

  @spec build(map(), list(), list(), keyword()) :: {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(conditions, queue, timeline, options \\ []) do
    with {:ok, candidate, proof} <- RpcMailboxProof.build(conditions, queue, timeline),
         {:ok, candidate} <- RpcCompletion.assess(candidate, options) do
      finish(candidate, proof, nil)
    end
  end

  @spec build_with_cost(map(), list(), list(), keyword()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build_with_cost(profile, queue, timeline, options \\ []) do
    with {:ok, candidate, proof} <- RpcCostProof.build(profile, queue, timeline),
         {:ok, candidate} <- RpcCompletion.assess(candidate, options) do
      finish(candidate, proof, candidate.server_contract.kind)
    end
  end

  defp finish(candidate, proof, handler) do
    completion = candidate.completion

    source = """
    namespace ReductionBounds.RpcCompletion
    def suppliedInitial : Configuration := initial RpcMailbox.suppliedConfig Mailbox.suppliedQueue
    def suppliedFinal : Configuration := ⟨RpcMailbox.suppliedMailboxResult, #{completion.remaining_mailbox_steps}⟩
    theorem suppliedRanking : Ranked RpcMailbox.suppliedConfig.session := canonicalRanking _
    theorem suppliedMovesCertificate :
        execute RpcMailbox.suppliedConfig suppliedInitial RpcMailbox.suppliedTimeline = some suppliedFinal := by decide
    theorem suppliedMoves : Moves RpcMailbox.suppliedConfig suppliedInitial RpcMailbox.suppliedTimeline suppliedFinal :=
      executeSound _ _ _ _ suppliedMovesCertificate
    theorem suppliedMailboxAgreement :
        RpcMailbox.Runs RpcMailbox.suppliedConfig suppliedInitial.model RpcMailbox.suppliedTimeline
          RpcMailbox.suppliedMailboxResult := suppliedMoves.erased
    theorem suppliedTraceRank : RpcMailbox.suppliedTimeline.length + rank suppliedFinal ≤ rank suppliedInitial :=
      suppliedMoves.bounded suppliedRanking
    theorem suppliedActiveBudget : rank suppliedInitial = #{completion.active_action_bound} := by decide
    theorem suppliedPendingCounterexample :
        ¬ ∃ n, ((stalledBehavior RpcMailbox.suppliedConfig Mailbox.suppliedQueue).config n).model.protocolState ∈
          (RpcProtocol.contract RpcMailbox.suppliedConfig.session).terminal := stalledNotComplete _ _
    #{completion_theorems(completion)}
    end ReductionBounds.RpcCompletion
    """

    proof = %{proof | file: "generated_rpc_completion.lean", source: proof.source <> source}

    metadata = %{
      source: :rpc_completion,
      handler: handler,
      completion_status: completion.status,
      goal: completion.goal
    }

    {proof, audit} = ProofInput.audit_bound(proof, metadata)
    scope = candidate.verification_scope

    result =
      Map.merge(candidate, audit)
      |> Map.put(:source, :rpc_completion)
      |> Map.put(:lean_status, :not_checked)
      |> Map.put(:verification_scope, %{
        scope
        | kind:
            if(handler,
              do: :conditional_rpc_completion_and_cost,
              else: :conditional_rpc_model_completion
            ),
          assumptions: Enum.uniq(scope.assumptions ++ completion.assumptions),
          unverified: Enum.uniq(scope.unverified ++ [:source_termination, :actual_progress])
      })

    {:ok, result, proof}
  end

  defp completion_theorems(%{status: :conditional} = c) do
    """
    theorem suppliedConditionalCompletion (behavior : Behavior RpcMailbox.suppliedConfig Mailbox.suppliedQueue)
        (progress : Progress behavior) :
        (∃ n, (behavior.config n).model.protocolState ∈ (RpcProtocol.contract RpcMailbox.suppliedConfig.session).terminal) ∧
        (∀ n, activeCount behavior n ≤ #{c.active_action_bound}) := by
      refine ⟨conditionalCompletion _ _ behavior progress, ?_⟩
      intro n
      have bounded := eventCountBound _ _ behavior n
      change activeCount behavior n + rank (behavior.config n) ≤ rank suppliedInitial at bounded
      rw [suppliedActiveBudget] at bounded
      omega
    #{success_theorem(c.goal)}
    """
  end

  defp completion_theorems(_completion), do: ""

  defp success_theorem(:success) do
    """
    theorem suppliedSuccessfulCompletion (behavior : Behavior RpcMailbox.suppliedConfig Mailbox.suppliedQueue)
        (progress : Progress behavior) (safe : NoFailure behavior) :
        ∃ n, (behavior.config n).model.protocolState = "complete" := successfulCompletion _ _ behavior progress safe
    """
  end

  defp success_theorem(_goal), do: ""
end
