defmodule ReductionBounds.PortSourceProof do
  @moduledoc false

  alias ReductionBounds.{PortSource, ProofInput, ProtocolCostProof}

  @spec build(ReductionBounds.target(), ReductionBounds.ProtocolCost.t(), keyword()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(target, profile, options \\ []) do
    with {:ok, candidate} <- PortSource.infer(target, profile, options),
         {:ok, _result, proof} <- ProtocolCostProof.build(profile, []) do
      source = """

      namespace ReductionBounds.PortSource
      open ReductionBounds.Protocol (suppliedContract)
      open ReductionBounds.ProtocolConditions (suppliedSpec)
      open ReductionBounds.ProtocolCost (suppliedEntries suppliedGroups suppliedCostCertificate)

      def suppliedRegistry : Registry
        | .prepare => #{mfa(candidate.calls.prepare)}
        | .submit => ("erlang", "port_command")
        | .reply => #{mfa(candidate.calls.reply)}
        | .decode => #{mfa(candidate.calls.decode)}
      theorem suppliedRegistryValid : RegistryValid suppliedRegistry := by decide
      def suppliedCore : Core := #{core(candidate.core_source)}
      def suppliedContext : Context := #{context(candidate.context)}
      def suppliedProgram : Program := #{model(candidate.model)}
      theorem suppliedConnection : Connect suppliedContract suppliedRegistry suppliedCore suppliedContext suppliedProgram :=
        #{candidate.connection}
      theorem suppliedLocalBudget : suppliedCore.budget = #{candidate.source_node_bound} := by decide
      def suppliedSourceFormula : ReductionBounds.ProtocolCost.Expr := #{expr(candidate.upper_bounds.caller.formula)}
      theorem suppliedSourceFormulaMatches : suppliedSourceFormula =
          .add (.mul (.constant suppliedCore.budget) (.charge "source_node"))
            (ReductionBounds.ProtocolCost.boundExpr suppliedSpec "caller" suppliedGroups) := by decide

      theorem suppliedSourceAgreement (external : External) (env : Env) (value : Value)
          (calls : List Invocation) (work : Nat)
          (run : Evaluates external suppliedCore env value calls work)
          (contracts : Contracts suppliedContract suppliedRegistry external) :
          ∃ trace, Executes external suppliedProgram env value calls work trace ∧
            ∃ final, ReductionBounds.Protocol.Runs suppliedContract suppliedContext.state trace final ∧
              final ∈ suppliedContract.terminal := by
        obtain ⟨trace, modeled⟩ := sourceAgreement suppliedConnection run
        exact ⟨trace, modeled, modelSafe suppliedConnection modeled contracts⟩

      theorem suppliedSourceBound (external : External) (env : Env) (value : Value)
          (calls : List Invocation) (work : Nat) (trace : List ReductionBounds.Protocol.Event)
          (run : Evaluates external suppliedCore env value calls work)
          (modeled : Executes external suppliedProgram env value calls work trace)
          (contracts : Contracts suppliedContract suppliedRegistry external)
          (charge : ReductionBounds.ProtocolCost.Charges) (states : List String)
          (observations : List ReductionBounds.ProtocolConditions.Observation)
          (rows : ReductionBounds.ProtocolConditions.RowsHold suppliedSpec suppliedContext.state trace states observations)
          (counts : ReductionBounds.ProtocolConditions.CountsHold suppliedSpec suppliedContext.state trace states) :
          work * charge "caller" "source_node" +
            ReductionBounds.ProtocolCost.traceCost suppliedEntries charge "caller" suppliedContext.state trace states observations ≤
            suppliedSourceFormula.eval (charge "caller") (fun _ => 0) := by
        rw [suppliedSourceFormulaMatches]
        simp only [ReductionBounds.ProtocolCost.Expr.eval, ReductionBounds.ProtocolCost.boundExprCorrect]
        exact (connectedCostBound suppliedConnection run modeled contracts suppliedSpec suppliedEntries suppliedGroups
          charge states observations suppliedCostCertificate rows counts).2
      end ReductionBounds.PortSource
      """

      proof = %{proof | source: proof.source <> source}
      {proof, audit} = ProofInput.audit_bound(proof, %{source: :port_source})
      {:ok, Map.put(candidate, :source_proof_audit, audit), proof}
    end
  end

  defp core({:ret, arg}), do: "(.ret #{arg(arg)})"

  defp core({:let_call, binder, call, body}),
    do: "(.letCall #{string(binder)} #{call(call)} #{core(body)})"

  defp core({:bool_case, call, first, a, b}),
    do: "(.boolCase #{call(call)} #{first} #{core(a)} #{core(b)})"

  defp core({:reply_case, call, binder, order, a, b, c}),
    do:
      "(.replyCase #{call(call)} #{string(binder)} #{list(order, &atom/1)} #{core(a)} #{core(b)} #{core(c)})"

  defp core({:tail_call, call}), do: "(.tailCall #{call(call)})"

  defp model({:ret, arg, events, final}),
    do: "(.ret #{arg(arg)} #{list(events, &event/1)} #{atom(final)})"

  defp model({:prepare, binder, call, body}),
    do: "(.prepare #{string(binder)} #{call(call)} #{model(body)})"

  defp model({:submit, call, first, a, b}),
    do: "(.submit #{call(call)} #{first} #{model(a)} #{model(b)})"

  defp model({:reply, call, binder, a, b, c}),
    do: "(.reply #{call(call)} #{string(binder)} #{model(a)} #{model(b)} #{model(c)})"

  defp model({:decode, call}), do: "(.decode #{call(call)})"

  defp context(ctx),
    do: "⟨#{atom(ctx.state)}, #{string(ctx.port)}, #{string(ctx.request)}, #{string(ctx.data)}⟩"

  defp call({m, f, args}), do: "⟨#{atom(m)}, #{atom(f)}, #{list(args, &arg/1)}⟩"
  defp mfa({m, f, _}), do: "(#{atom(m)}, #{atom(f)})"
  defp arg({:var, name}), do: "(.variable #{string(name)})"
  defp arg({:literal, value}), do: "(.literal #{value(value)})"
  defp value(value) when is_atom(value), do: "(.atom #{atom(value)})"
  defp value(value) when is_integer(value), do: "(.integer (#{value}))"
  defp value([]), do: ".nil"
  defp value([head | tail]), do: "(.cons #{value(head)} #{value(tail)})"
  defp event(name), do: "⟨#{atom(name)}, some \"caller\", some \"symbolic_work\"⟩"
  defp expr(value) when is_integer(value), do: "(.constant #{value})"
  defp expr({:charge, name}), do: "(.charge #{atom(name)})"
  defp expr({op, a, b}), do: "(.#{op} #{expr(a)} #{expr(b)})"
  defp atom(value), do: value |> Atom.to_string() |> string()
  defp string(value), do: ProofInput.string(value)
  defp list(values, emit), do: "[#{Enum.map_join(values, ", ", emit)}]"
end
