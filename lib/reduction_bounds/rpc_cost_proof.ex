defmodule ReductionBounds.RpcCostProof do
  @moduledoc false
  alias ReductionBounds.{ProofInput, RpcCost, RpcMailboxProof, RpcServerContract, RpcTerm}

  @spec build(map(), list(), list()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(profile, queue, timeline) do
    with :ok <- RpcCost.validate(profile),
         true <- is_list(queue) and length(queue) <= profile.initial_messages,
         {:ok, witness, mailbox_proof} <-
           RpcMailboxProof.build(profile.conditions, queue, timeline),
         {:ok, server, handler_proof} <-
           RpcServerContract.resolve(profile.server, profile.conditions.request),
         counts = RpcCost.counts(witness),
         caps = RpcCost.limits(profile),
         true <- Enum.all?(counts, fn {op, n} -> n <= caps[op] end) do
      rates =
        profile.rates
        |> Map.new(fn {k, v} -> {k, v.upper_bound} end)
        |> Map.put(:handle_request, server.upper_bound)

      bounds =
        Map.new([:client, :server], fn owner ->
          {owner,
           %{
             upper_bound: RpcCost.budget(caps, rates, owner),
             cost_unit: if(owner == :client, do: :client_work, else: :server_work)
           }}
        end)

      frame_budget =
        caps.receive_request * rates.receive_request + caps.send_reply * rates.send_reply

      server =
        server
        |> Map.put(:frame_budget, frame_budget)
        |> Map.put(:call_limit, profile.server_calls)

      candidate = candidate(witness, profile, server, counts, caps, rates, bounds)

      source =
        mailbox_proof.source <>
          handler_source(handler_proof) <>
          certificate(profile, counts, rates, bounds) <>
          compose_source(server, bounds.server.upper_bound)

      proof = %{mailbox_proof | file: "generated_rpc_cost.lean", source: source}
      {proof, audit} = ProofInput.audit_bound(proof, %{source: :rpc_cost, handler: server.kind})
      {:ok, Map.merge(candidate, audit), proof}
    else
      false -> {:error, :rpc_cost_conditions_not_satisfied}
      error -> error
    end
  end

  defp candidate(witness, profile, server, counts, caps, rates, bounds) do
    Map.merge(witness, %{
      source: :rpc_cost,
      cost_profile: profile,
      server_contract: server,
      operation_counts: counts,
      operation_limits: caps,
      rates: rates,
      upper_bounds: bounds,
      lean_status: :not_checked,
      verification_scope: %{
        kind: :conditional_rpc_participant_cost_safety,
        assumptions:
          [
            :declared_size_and_count_conditions,
            :ordinary_message_queue,
            :local_cost_envelopes,
            :work_ledger_correspondence,
            :server_frame,
            :handler_argument_association,
            :handler_callee_contracts
          ] ++
            if(server.kind == :assumed, do: [:server_handler_bound], else: []),
        unverified: [
          :all_runtime_count_bounds,
          :server_mailbox,
          :reply_provenance,
          :handler_identity_in_rpc_source,
          :reply_encoding,
          :unfinished_server_source_prefixes,
          :progress,
          :source_correspondence,
          :runtime_correspondence,
          :wall_clock_time
        ]
      }
    })
  end

  defp handler_source(nil), do: ""

  defp handler_source(proof),
    do: "\nnamespace RpcHandler\n" <> proof.source <> "\nend RpcHandler\n"

  defp function(values) do
    "fun op => match op with\n" <>
      Enum.map_join(RpcCost.operations(), "\n", fn op ->
        "| .#{RpcCost.lean_operation(op)} => #{values[op]}"
      end)
  end

  defp certificate(profile, counts, rates, bounds) do
    """
    namespace ReductionBounds.RpcCost
    theorem suppliedServerRequestSize : RpcTerm.within (RpcTerm.measure RpcMailbox.suppliedConfig.request)
        #{RpcTerm.lean_size(profile.server.frame.message_size)} = true := by decide
    def suppliedCaps : Op → Nat := limits RpcMailbox.suppliedConfig #{profile.server_calls}
    def suppliedRates : Op → Nat := #{function(rates)}
    def suppliedOperationCounts : Op → Nat := #{function(counts)}
    theorem suppliedCountsMatch (op : Op) :
        count RpcMailbox.suppliedMailboxResult op = suppliedOperationCounts op := by
      cases op <;> decide
    theorem suppliedCountsFit : Fits RpcMailbox.suppliedMailboxResult suppliedCaps := by
      intro op; cases op <;> decide
    theorem suppliedClientBudget : budget .client suppliedCaps suppliedRates = #{bounds.client.upper_bound} := by decide
    theorem suppliedServerBudget : budget .server suppliedCaps suppliedRates = #{bounds.server.upper_bound} := by decide
    theorem suppliedCostSafety (work : Work)
        (covered : Covered RpcMailbox.suppliedMailboxResult suppliedRates work) (p : Participant) :
        actual p work ≤ budget p suppliedCaps suppliedRates :=
      participantSafety _ _ _ _ suppliedCountsFit covered p
    theorem suppliedPrefixSafety (front suffix : Work)
        (covered : Covered RpcMailbox.suppliedMailboxResult suppliedRates
          (fun op => front op ++ suffix op)) (p : Participant) :
        actual p front ≤ budget p suppliedCaps suppliedRates :=
      prefixSafety _ _ _ _ _ suppliedCountsFit covered p
    theorem admittedCostSafety (s : RpcMailbox.State) (items : List RpcMailbox.Item)
        (_run : RpcMailbox.Runs RpcMailbox.suppliedConfig
          {mailbox := Mailbox.initial Mailbox.suppliedQueue} items s)
        (fits : Fits s suppliedCaps) (work : Work) (covered : Covered s suppliedRates work)
        (p : Participant) : actual p work ≤ budget p suppliedCaps suppliedRates :=
      participantSafety _ _ _ _ fits covered p
    end ReductionBounds.RpcCost
    """
  end

  defp compose_source(%{kind: :assumed} = server, bound) do
    frame = frame_budget(server)

    """
    namespace ReductionBounds.RpcCost
    theorem suppliedServerComposition (frame handler invocations : Nat)
        (invocationLimit : invocations ≤ #{server.call_limit})
        (frameContract : frame ≤ #{frame}) (handlerContract : handler ≤ #{server.upper_bound}) :
        frame + invocations * handler ≤ #{bound} := by
      exact composeServerCalls _ _ _ _ _ _ frameContract handlerContract invocationLimit
    end ReductionBounds.RpcCost
    """
  end

  defp compose_source(server, bound) do
    frame = frame_budget(server)

    """
    namespace RpcHandler
    def requestEnv : ReductionBounds.IntegerAnalysis.Env := fun _ => (#{server.argument} : Int)
    theorem requestArgumentMatches :
        (match ReductionBounds.RpcMailbox.suppliedConfig.request with
         | .tuple3 _ _ (.integer n) => some n | _ => none) = some (requestEnv 0) := by decide
    theorem requestInputCovered : ReductionBounds.IntegerAnalysis.Covers transferInputs requestEnv := by
      intro index
      cases index with
      | zero => decide
      | succ index => trivial
    theorem composedServerBound (external : ReductionBounds.IntegerCost.External)
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts external)
        (value : Int) (handler frame invocations : Nat)
        (invocationLimit : invocations ≤ #{server.call_limit})
        (run : ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges external
          SourceBound.costProgram requestEnv value handler)
        (frameContract : frame ≤ #{frame}) : frame + invocations * handler ≤ #{bound} := by
      exact ReductionBounds.RpcCost.composeServerCalls _ _ _ _ _ _ frameContract
        (transferredNumericBound external calls requestEnv requestInputCovered value handler run) invocationLimit

    theorem replayedCoverage (external : ReductionBounds.IntegerCost.External)
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts external)
        (s : ReductionBounds.RpcMailbox.State)
        (work : ReductionBounds.RpcCost.Work)
        (lengths : ∀ op, (work op).length = ReductionBounds.RpcCost.count s op)
        (otherCosts : ∀ op, op ≠ .handleRequest → ∀ n ∈ work op, n ≤ ReductionBounds.RpcCost.suppliedRates op)
        (handlerRuns : ∀ n ∈ work .handleRequest, ∃ value,
          ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges external
            SourceBound.costProgram requestEnv value n)
        : ReductionBounds.RpcCost.Covered s ReductionBounds.RpcCost.suppliedRates work := by
      intro op
      refine ⟨lengths op, ?_⟩
      by_cases h : op = .handleRequest
      · subst op
        intro n hn
        obtain ⟨value, run⟩ := handlerRuns n hn
        exact transferredNumericBound external calls requestEnv requestInputCovered value n run
      · exact otherCosts op h

    theorem replayedCostSafety (external : ReductionBounds.IntegerCost.External)
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts external)
        (s : ReductionBounds.RpcMailbox.State)
        (fits : ReductionBounds.RpcCost.Fits s ReductionBounds.RpcCost.suppliedCaps)
        (work : ReductionBounds.RpcCost.Work)
        (lengths : ∀ op, (work op).length = ReductionBounds.RpcCost.count s op)
        (otherCosts : ∀ op, op ≠ .handleRequest → ∀ n ∈ work op, n ≤ ReductionBounds.RpcCost.suppliedRates op)
        (handlerRuns : ∀ n ∈ work .handleRequest, ∃ value,
          ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges external
            SourceBound.costProgram requestEnv value n)
        (p : ReductionBounds.RpcCost.Participant) :
        ReductionBounds.RpcCost.actual p work ≤
          ReductionBounds.RpcCost.budget p ReductionBounds.RpcCost.suppliedCaps ReductionBounds.RpcCost.suppliedRates :=
      ReductionBounds.RpcCost.participantSafety _ _ _ _ fits
        (replayedCoverage external calls s work lengths otherCosts handlerRuns) p

    theorem replayedPrefixSafety (external : ReductionBounds.IntegerCost.External)
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts external)
        (s : ReductionBounds.RpcMailbox.State)
        (fits : ReductionBounds.RpcCost.Fits s ReductionBounds.RpcCost.suppliedCaps)
        (front suffix : ReductionBounds.RpcCost.Work)
        (lengths : ∀ op, (front op ++ suffix op).length = ReductionBounds.RpcCost.count s op)
        (otherCosts : ∀ op, op ≠ .handleRequest → ∀ n ∈ front op ++ suffix op,
          n ≤ ReductionBounds.RpcCost.suppliedRates op)
        (handlerRuns : ∀ n ∈ front .handleRequest ++ suffix .handleRequest, ∃ value,
          ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges external
            SourceBound.costProgram requestEnv value n)
        (p : ReductionBounds.RpcCost.Participant) :
        ReductionBounds.RpcCost.actual p front ≤
          ReductionBounds.RpcCost.budget p ReductionBounds.RpcCost.suppliedCaps ReductionBounds.RpcCost.suppliedRates :=
      ReductionBounds.RpcCost.prefixSafety _ _ _ _ _ fits
        (replayedCoverage external calls s (fun op => front op ++ suffix op) lengths otherCosts handlerRuns) p
    end RpcHandler
    """
  end

  # The frame and handler contributions use the same rates and count caps.
  defp frame_budget(server), do: server.frame_budget
end
