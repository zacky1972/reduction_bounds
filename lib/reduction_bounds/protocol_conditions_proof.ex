defmodule ReductionBounds.ProtocolConditionsProof do
  @moduledoc false

  alias ReductionBounds.{ProofInput, ProtocolConditions, ProtocolProof}

  @spec build(ProtocolConditions.t(), [ReductionBounds.Protocol.Event.t()], map()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(profile, events, observations \\ %{}) do
    with {:ok, result} <- ProtocolConditions.check_trace(profile, events, observations),
         {:ok, _trace, proof} <- ProtocolProof.build(profile.contract, events) do
      source = """

      namespace ReductionBounds.ProtocolConditions

      def suppliedSpec : Spec := {
        dataBounds := #{pairs(profile.data_bounds, &data_size/1)}
        integerBounds := #{pairs(profile.integer_bounds, &integer_size/1)}
        countBounds := #{pairs(profile.count_bounds, &to_string/1)}
        rules := #{rules(profile.rules)}
      }
      def suppliedObservations : List Observation := #{list(result.rows, &observation(&1.observation))}
      def suppliedCountValues : List (String × Nat) := #{pairs(result.counts, &to_string/1)}

      theorem suppliedConditionsCertificate :
          checkConditions ReductionBounds.Protocol.suppliedContract suppliedSpec
            ReductionBounds.Protocol.suppliedEvents ReductionBounds.Protocol.suppliedStates
            suppliedObservations = true := by decide

      theorem suppliedConditionsSound :
          RowsHold suppliedSpec ReductionBounds.Protocol.suppliedContract.initial
            ReductionBounds.Protocol.suppliedEvents ReductionBounds.Protocol.suppliedStates suppliedObservations ∧
          CountsHold suppliedSpec ReductionBounds.Protocol.suppliedContract.initial
            ReductionBounds.Protocol.suppliedEvents ReductionBounds.Protocol.suppliedStates := by
        have checked := checkConditionsSound
          ReductionBounds.Protocol.suppliedContract suppliedSpec
          ReductionBounds.Protocol.suppliedEvents ReductionBounds.Protocol.suppliedStates
          suppliedObservations suppliedConditionsCertificate
        exact ⟨checked.2.2.2.1, checked.2.2.2.2⟩

      theorem suppliedCountKeys :
          suppliedCountValues.map Prod.fst = suppliedSpec.countBounds.map Prod.fst := by decide

      theorem suppliedCountsMatch : ∀ entry ∈ suppliedCountValues,
          countFrom suppliedSpec ReductionBounds.Protocol.suppliedContract.initial entry.1
            ReductionBounds.Protocol.suppliedEvents ReductionBounds.Protocol.suppliedStates = entry.2 := by
        decide

      end ReductionBounds.ProtocolConditions
      """

      proof = %{proof | source: proof.source <> source}
      {proof, _audit} = ProofInput.audit_bound(proof, %{source: :protocol_conditions})
      {:ok, result, proof}
    end
  end

  defp data_size(size), do: "⟨#{size.bytes}, #{size.structure}⟩"

  defp integer_size(size),
    do:
      "⟨#{integer_endpoint(size.lower)}, #{integer_endpoint(size.upper)}, (some #{size.magnitude_bits})⟩"

  defp integer_endpoint(:unbounded), do: "none"
  defp integer_endpoint(value), do: "(some (#{value}))"

  defp rules(values) do
    values
    |> Enum.sort()
    |> list(fn {{state, event}, rule} ->
      "⟨#{name(state)}, #{name(event)}, #{strings(rule.data)}, #{strings(rule.integers)}, #{strings(rule.counts)}⟩"
    end)
  end

  defp observation(value),
    do:
      "⟨#{pairs(value.data, &data_size/1)}, #{pairs(value.integers, fn value -> "(#{value})" end)}⟩"

  defp pairs(values, emit),
    do: values |> Enum.sort() |> list(fn {key, value} -> "(#{name(key)}, #{emit.(value)})" end)

  defp strings(values), do: list(values, &name/1)
  defp name(value), do: value |> Atom.to_string() |> ProofInput.string()
  defp list(values, emit), do: "[#{Enum.map_join(values, ", ", emit)}]"
end
