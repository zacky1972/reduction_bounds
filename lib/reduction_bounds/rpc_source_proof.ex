defmodule ReductionBounds.RpcSourceProof do
  @moduledoc false
  alias ReductionBounds.{ProofInput, RpcCostProof, RpcSource, RpcTerm}

  @spec build(ReductionBounds.target(), map(), keyword()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(target, profile, options \\ []) do
    with {:ok, source} <- RpcSource.infer(target, profile, options),
         {:ok, cost, proof} <- RpcCostProof.build(profile, [], []) do
      {:let_value, request_binder, request_arg,
       {:seq_call, send_call, {:reply_case, reply_call, _, _, _, _}}} = source.core_source

      context = source.context

      formula =
        {:add, {:mul, source.source_node_bound, {:charge, :source_node}},
         cost.upper_bounds.client.upper_bound}

      code = """
      namespace ReductionBounds.RpcSource
      def suppliedRegistry : Registry
        | .send => ("erlang", "send")
        | .reply => #{mfa(source.calls.reply)}
        | .decode => #{mfa(source.calls.decode)}
      theorem suppliedRegistryValid : RegistryValid suppliedRegistry := by decide
      def suppliedCore : Core := #{core(source.core_source)}
      def suppliedContext : Context := #{ctx(context)}
      def suppliedTimeout : Value := #{RpcTerm.lean(source.timeout_value)}
      theorem suppliedTimeoutMatches : suppliedTimeout = timeoutValue RpcMailbox.suppliedConfig.mailbox.timeout := by decide
      def suppliedProgram : Program := #{program(source.program)}
      theorem suppliedConnection : Connect RpcProtocol.suppliedSession suppliedRegistry suppliedTimeout
          suppliedCore suppliedContext suppliedProgram := #{source.connection}
      theorem suppliedLocalBudget : suppliedCore.budget = #{source.source_node_bound} := by decide
      def suppliedSourceFormula (nodeCharge : Nat) : Nat := #{formula(formula)}
      theorem suppliedSourceFormulaMatches (nodeCharge : Nat) : suppliedSourceFormula nodeCharge =
          suppliedCore.budget * nodeCharge + RpcCost.budget .client RpcCost.suppliedCaps RpcCost.suppliedRates := by
        rw [suppliedLocalBudget, RpcCost.suppliedClientBudget]
        rfl
      def suppliedRequestArg : Arg := #{arg(request_arg)}
      theorem suppliedRequestConstruction (env : Env) (inputs : InputsHold RpcMailbox.suppliedConfig suppliedContext env) :
          suppliedRequestArg.eval env = RpcMailbox.suppliedConfig.request := by
        exact inputs.request
      def suppliedSendCall : Call := #{call(send_call)}
      def suppliedReplyCall : Call := #{call(reply_call)}
      def suppliedPreparedEnv (env : Env) : Env := bind env #{string(request_binder)} (suppliedRequestArg.eval env)
      theorem suppliedCorrelation (env : Env) (inputs : InputsHold RpcMailbox.suppliedConfig suppliedContext env) :
          env suppliedContext.token = .ref RpcMailbox.suppliedConfig.session.requestId := by
        exact (RpcTerm.Term.tuple3.inj inputs.request).2.1
      theorem suppliedSendArguments (env : Env) (inputs : InputsHold RpcMailbox.suppliedConfig suppliedContext env) :
          suppliedSendCall.args.map (Arg.eval (suppliedPreparedEnv env)) =
            [env suppliedContext.server, RpcMailbox.suppliedConfig.request] := by
        rw [← suppliedRequestConstruction env inputs]
        rfl
      theorem suppliedReplyArguments (env : Env) (inputs : InputsHold RpcMailbox.suppliedConfig suppliedContext env) :
          suppliedReplyCall.args.map (Arg.eval (suppliedPreparedEnv env)) =
            [env suppliedContext.server, env suppliedContext.token, timeoutValue RpcMailbox.suppliedConfig.mailbox.timeout] := by
        have time := inputs.timeout
        rw [← suppliedTimeoutMatches] at time ⊢
        simp_all [suppliedReplyCall, suppliedPreparedEnv, suppliedContext, suppliedTimeout, Arg.eval, bind]
      theorem suppliedDecodeTerminals : ∀ value,
          callAfter .decode value ∈ (RpcProtocol.contract RpcProtocol.suppliedSession).terminal := by
        intro value
        change (if value = .atom "decode_error" then "decode_failed" else "complete") ∈
          (RpcProtocol.contract RpcProtocol.suppliedSession).terminal
        split <;> decide
      theorem suppliedTimeoutTerminal : "timed_out" ∈ (RpcProtocol.contract RpcProtocol.suppliedSession).terminal := by decide

      theorem suppliedContractsWithoutNormalReturn (env : Env) :
          Contracts RpcProtocol.suppliedSession suppliedRegistry emptyExternal ∧
          ¬ ∃ value calls work, Evaluates emptyExternal suppliedCore env value calls work := by
        refine ⟨emptyContracts _ _, ?_⟩
        intro ⟨value, calls, work, run⟩
        cases run with
        | letValue rest =>
          cases rest with
          | seqCall invoked _ => exact invoked.2.2.2

      theorem suppliedSourceAgreement (external : External) (env : Env) (value : Value)
          (calls : List Invocation) (work : Nat)
          (inputs : InputsHold RpcMailbox.suppliedConfig suppliedContext env)
          (run : Evaluates external suppliedCore env value calls work)
          (contracts : Contracts RpcProtocol.suppliedSession suppliedRegistry external) :
          suppliedRequestArg.eval env = RpcMailbox.suppliedConfig.request ∧
          ∃ trace, Executes RpcProtocol.suppliedSession external suppliedProgram env value calls work trace ∧
            ∃ final, RpcProtocol.ValidTrace RpcProtocol.suppliedSession trace final ∧
              final ∈ (RpcProtocol.contract RpcProtocol.suppliedSession).terminal := by
        obtain ⟨trace, modeled⟩ := sourceAgreement suppliedConnection run
        obtain ⟨final, safe, terminal⟩ := modelSafe suppliedConnection modeled contracts suppliedDecodeTerminals suppliedTimeoutTerminal
        exact ⟨suppliedRequestConstruction env inputs, trace, modeled, final, safe, terminal⟩

      theorem suppliedSourceMailboxBridge (external : External) (env : Env) (value : Value)
          (calls : List Invocation) (work : Nat) (trace : List RpcProtocol.Event)
          (modeled : Executes RpcProtocol.suppliedSession external suppliedProgram env value calls work trace)
          (contracts : Contracts RpcProtocol.suppliedSession suppliedRegistry external)
          (queue : List RpcTerm.Term) (timeline : List RpcMailbox.Item) (state : RpcMailbox.State)
          (admitted : RpcMailbox.run RpcMailbox.suppliedConfig queue timeline = some state)
          (association : state.events = trace.map (fun e => e.protocol.name))
          (data : ReplyData RpcMailbox.suppliedConfig suppliedRegistry calls state)
          (projection : Protocol.Runs (RpcProtocol.contract RpcProtocol.suppliedSession) "idle"
            (trace.map RpcProtocol.Event.protocol) state.protocolState) :
          RpcMailbox.Runs RpcMailbox.suppliedConfig {mailbox := Mailbox.initial queue} timeline state ∧
          RpcProtocol.ValidTrace RpcProtocol.suppliedSession trace state.protocolState ∧
          state.protocolState ∈ (RpcProtocol.contract RpcProtocol.suppliedSession).terminal ∧
          ReplyData RpcMailbox.suppliedConfig suppliedRegistry calls state := by
        obtain ⟨final, segment, terminal⟩ :=
          modelSafe suppliedConnection modeled contracts suppliedDecodeTerminals suppliedTimeoutTerminal
        have same : final = state.protocolState := finalUnique segment.1 projection
        have _names := association
        exact ⟨(RpcMailbox.runSound _ _ _ _ admitted).2.2, same ▸ segment, same ▸ terminal, data⟩

      theorem suppliedSourceBound (external : External) (env : Env) (value : Value)
          (calls : List Invocation) (work : Nat) (trace : List RpcProtocol.Event)
          (inputs : InputsHold RpcMailbox.suppliedConfig suppliedContext env)
          (run : Evaluates external suppliedCore env value calls work)
          (modeled : Executes RpcProtocol.suppliedSession external suppliedProgram env value calls work trace)
          (contracts : Contracts RpcProtocol.suppliedSession suppliedRegistry external)
          (queue : List RpcTerm.Term) (timeline : List RpcMailbox.Item) (state : RpcMailbox.State)
          (admitted : RpcMailbox.run RpcMailbox.suppliedConfig queue timeline = some state)
          (initialQueueBound : queue.length ≤ #{profile.initial_messages})
          (association : state.events = trace.map (fun e => e.protocol.name))
          (data : ReplyData RpcMailbox.suppliedConfig suppliedRegistry calls state)
          (projection : Protocol.Runs (RpcProtocol.contract RpcProtocol.suppliedSession) "idle"
            (trace.map RpcProtocol.Event.protocol) state.protocolState)
          (ledger : RpcCost.Work) (fits : RpcCost.Fits state RpcCost.suppliedCaps)
          (covered : RpcCost.Covered state RpcCost.suppliedRates ledger) (nodeCharge : Nat) :
          suppliedRequestArg.eval env = RpcMailbox.suppliedConfig.request ∧
          state.protocolState ∈ (RpcProtocol.contract RpcProtocol.suppliedSession).terminal ∧
          work * nodeCharge + RpcCost.actual .client ledger ≤
            suppliedSourceFormula nodeCharge ∧
          RpcCost.actual .server ledger ≤ #{cost.upper_bounds.server.upper_bound} := by
        have wire := suppliedRequestConstruction env inputs
        have mailbox := suppliedSourceMailboxBridge external env value calls work trace modeled contracts queue timeline state admitted association data projection
        have _queue := initialQueueBound
        have bounds := (connectedCostBound suppliedConnection run modeled contracts suppliedDecodeTerminals
          suppliedTimeoutTerminal state RpcCost.suppliedCaps RpcCost.suppliedRates ledger fits covered association nodeCharge).2
        rw [suppliedLocalBudget, RpcCost.suppliedClientBudget, RpcCost.suppliedServerBudget] at bounds
        rw [suppliedSourceFormulaMatches, suppliedLocalBudget, RpcCost.suppliedClientBudget]
        exact ⟨wire, mailbox.2.2.1, bounds⟩
      end ReductionBounds.RpcSource
      """

      proof = %{proof | file: "generated_rpc_source.lean", source: proof.source <> code}

      {proof, audit} =
        ProofInput.audit_bound(proof, %{source: :rpc_source, handler: cost.server_contract.kind})

      candidate =
        cost
        |> Map.take([:cost_profile, :server_contract, :operation_limits, :rates, :upper_bounds])
        |> Map.merge(source)
        |> Map.merge(audit)
        |> Map.put(:client_source_bound, %{
          cost_unit: :client_work,
          formula: formula,
          assumptions: [:source_node_charge, :disjoint_source_node_accounting]
        })
        |> Map.put(:verification_scope, %{
          kind: :finite_normal_reified_core_under_rpc_helper_contracts,
          assumptions:
            cost.verification_scope.assumptions ++
              [
                :primitive_send_contract,
                :reply_helper_contract,
                :decode_helper_contract,
                :input_applicability,
                :mailbox_trace_association,
                :disjoint_source_node_accounting
              ],
          unverified: Enum.uniq(cost.verification_scope.unverified ++ source.unverified)
        })

      {:ok, candidate, proof}
    end
  end

  defp core({:let_value, binder, value, body}),
    do: "(.letValue #{string(binder)} #{arg(value)} #{core(body)})"

  defp core({:seq_call, call, body}), do: "(.seqCall #{call(call)} #{core(body)})"

  defp core({:reply_case, call, binder, order, a, b}),
    do:
      "(.replyCase #{call(call)} #{string(binder)} [#{Enum.map_join(order, ", ", &atom/1)}] #{core(a)} #{core(b)})"

  defp core({:tail_call, call}), do: "(.tailCall #{call(call)})"
  defp core({:ret, value}), do: "(.ret #{arg(value)})"

  defp program({:prepare, binder, value, body}),
    do: "(.prepare #{string(binder)} #{arg(value)} #{program(body)})"

  defp program({:send, call, body}), do: "(.send #{call(call)} #{program(body)})"

  defp program({:reply, call, binder, a, b}),
    do: "(.reply #{call(call)} #{string(binder)} #{program(a)} #{program(b)})"

  defp program({:decode, call}), do: "(.decode #{call(call)})"
  defp program({:timeout, _arg}), do: ".timeout"
  defp call({m, f, args}), do: "⟨#{atom(m)}, #{atom(f)}, [#{Enum.map_join(args, ", ", &arg/1)}]⟩"
  defp mfa({m, f, _}), do: "(#{atom(m)}, #{atom(f)})"
  defp arg({:var, name}), do: "(.variable #{string(name)})"
  defp arg({:literal, value}), do: "(.literal #{RpcTerm.lean(value)})"
  defp arg({:tuple3, a, b, c}), do: "(.tuple3 #{arg(a)} #{arg(b)} #{arg(c)})"

  defp ctx(c),
    do:
      "⟨#{atom(c.state)}, #{string(c.server)}, #{string(c.token)}, #{string(c.input)}, #{string(c.timeout)}, #{string(c.request)}, #{string(c.data)}⟩"

  defp formula(n) when is_integer(n), do: Integer.to_string(n)
  defp formula({:charge, :source_node}), do: "nodeCharge"
  defp formula({:mul, a, b}), do: "(#{formula(a)} * #{formula(b)})"
  defp formula({:add, a, b}), do: "(#{formula(a)} + #{formula(b)})"
  defp atom(value), do: string(Atom.to_string(value))
  defp string(value), do: ProofInput.string(value)
end
