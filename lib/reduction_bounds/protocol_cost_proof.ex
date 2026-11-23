defmodule ReductionBounds.ProtocolCostProof do
  @moduledoc false

  alias ReductionBounds.{ProofInput, ProtocolConditionsProof, ProtocolCost}

  @spec build(ProtocolCost.t(), list(), map()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(profile, events, observations \\ %{}) do
    with {:ok, result} <- ProtocolCost.check_trace(profile, events, observations),
         {:ok, _conditions, proof} <-
           ProtocolConditionsProof.build(profile.conditions, events, observations) do
      source = """

      namespace ReductionBounds.ProtocolCost
      open ReductionBounds.Protocol (suppliedContract suppliedEvents suppliedStates)
      open ReductionBounds.ProtocolConditions (suppliedSpec suppliedObservations suppliedConditionsSound)

      def suppliedEntries : List Entry := #{entries(profile)}
      def suppliedGroups : List Group := #{list(profile.groups, &group/1)}
      theorem suppliedCostCertificate :
          CostSpecGood suppliedContract suppliedSpec suppliedEntries suppliedGroups := by decide

      theorem suppliedCostSafety (charge : Charges) (owner : String)
          (events : List ReductionBounds.Protocol.Event) (states : List String)
          (observations : List ReductionBounds.ProtocolConditions.Observation)
          (rows : ReductionBounds.ProtocolConditions.RowsHold suppliedSpec suppliedContract.initial events states observations)
          (counts : ReductionBounds.ProtocolConditions.CountsHold suppliedSpec suppliedContract.initial events states) :
          traceCost suppliedEntries charge owner suppliedContract.initial events states observations ≤
            (boundExpr suppliedSpec owner suppliedGroups).eval (charge owner) (fun _ => 0) := by
        rw [boundExprCorrect]
        exact costSafety suppliedContract suppliedSpec suppliedEntries suppliedGroups charge owner
          suppliedContract.initial events states observations suppliedCostCertificate rows counts

      theorem suppliedPrefixSafety (charge : Charges) (owner : String)
          (events : List ReductionBounds.Protocol.Event) (states : List String)
          (observations : List ReductionBounds.ProtocolConditions.Observation)
          (rows : ReductionBounds.ProtocolConditions.RowsHold suppliedSpec suppliedContract.initial events states observations)
          (counts : ReductionBounds.ProtocolConditions.CountsHold suppliedSpec suppliedContract.initial events states)
          (n : Nat) :
          traceCost suppliedEntries charge owner suppliedContract.initial
            (events.take n) (states.take n) (observations.take n) ≤
            (boundExpr suppliedSpec owner suppliedGroups).eval (charge owner) (fun _ => 0) := by
        rw [boundExprCorrect]
        exact prefixCostSafety suppliedContract suppliedSpec suppliedEntries suppliedGroups charge owner
          suppliedContract.initial events states observations suppliedCostCertificate rows counts n

      #{bounds(profile)}

      theorem suppliedTraceBudget (charge : Charges) (owner : String) :
          traceCost suppliedEntries charge owner suppliedContract.initial
            suppliedEvents suppliedStates suppliedObservations ≤
            (boundExpr suppliedSpec owner suppliedGroups).eval (charge owner) (fun _ => 0) :=
        suppliedCostSafety charge owner suppliedEvents suppliedStates suppliedObservations
          suppliedConditionsSound.1 suppliedConditionsSound.2

      theorem suppliedTracePrefixes (charge : Charges) (owner : String) (n : Nat) :
          traceCost suppliedEntries charge owner suppliedContract.initial
            (suppliedEvents.take n) (suppliedStates.take n) (suppliedObservations.take n) ≤
            (boundExpr suppliedSpec owner suppliedGroups).eval (charge owner) (fun _ => 0) :=
        suppliedPrefixSafety charge owner suppliedEvents suppliedStates suppliedObservations
          suppliedConditionsSound.1 suppliedConditionsSound.2 n
      end ReductionBounds.ProtocolCost
      """

      proof = %{proof | source: proof.source <> source}
      metadata = %{source: :protocol_cost, owners: Map.keys(profile.bounds) |> Enum.sort()}
      {proof, audit} = ProofInput.audit_bound(proof, metadata)
      {:ok, Map.put(result, :proof_audit, audit), proof}
    end
  end

  defp entries(profile) do
    profile.rules
    |> Enum.sort()
    |> list(fn {{state, event}, rule} ->
      {owner, unit} = Map.fetch!(profile.conditions.contract.events, event)

      "⟨#{name(state)}, ⟨#{name(event)}, some #{name(owner)}, some #{name(unit)}⟩, #{name(rule.counter)}, #{expr(rule.cost)}⟩"
    end)
  end

  defp group(group),
    do:
      "⟨#{name(group.owner)}, #{name(group.counter)}, #{group.limit}, #{list(group.alternatives, &expr/1)}⟩"

  defp bounds(profile) do
    profile.bounds
    |> Enum.sort()
    |> Enum.with_index()
    |> Enum.map_join("\n", fn {{owner, bound}, index} ->
      """
      def suppliedBound#{index} : Expr := #{expr(bound.formula)}
      theorem suppliedBoundMatches#{index} :
          suppliedBound#{index} = boundExpr suppliedSpec #{name(owner)} suppliedGroups := by decide
      """
    end)
  end

  defp expr(n) when is_integer(n), do: "(.constant #{n})"
  defp expr({:charge, value}), do: "(.charge #{name(value)})"
  defp expr({:data, slot, :bytes}), do: "(.feature (.bytes #{name(slot)}))"
  defp expr({:data, slot, :structure}), do: "(.feature (.structureSize #{name(slot)}))"
  defp expr({:integer, slot, :magnitude_bits}), do: "(.feature (.bits #{name(slot)}))"
  defp expr({op, left, right}), do: "(.#{op} #{expr(left)} #{expr(right)})"
  defp name(value), do: value |> Atom.to_string() |> ProofInput.string()
  defp list(values, emit), do: "[#{Enum.map_join(values, ", ", emit)}]"
end
