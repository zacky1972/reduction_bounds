defmodule ReductionBounds.ProtocolProof do
  @moduledoc false

  alias ReductionBounds.{ProofInput, Protocol}

  @spec build(Protocol.Contract.t(), [Protocol.Event.t()]) ::
          {:ok, Protocol.Trace.t(), Lynx.Lean.t()} | {:error, term()}
  def build(contract, events) do
    with {:ok, trace} <- Protocol.check_trace(contract, events) do
      source = """
      namespace ReductionBounds.Protocol

      def suppliedContract : Contract := {
        participants := #{participants(contract.participants)}
        states := #{strings(contract.states)}
        initial := #{name(contract.initial)}
        terminal := #{strings(contract.terminal)}
        events := #{event_declarations(contract.events)}
        transitions := #{edges(contract.transitions)}
      }
      def suppliedEvents : List Event := #{list(events, &event/1)}
      def suppliedStates : List String := #{strings(tl(trace.states))}
      def suppliedFinal : String := #{name(trace.final)}

      theorem suppliedCertificate :
          checkTrace suppliedContract suppliedEvents suppliedStates = true := by decide

      theorem suppliedWellFormed : suppliedContract.wellFormed = true :=
        (checkTraceSound _ _ _ suppliedCertificate).1

      theorem suppliedTraceSound :
          Runs suppliedContract suppliedContract.initial suppliedEvents suppliedFinal :=
        (checkTraceSound _ _ _ suppliedCertificate).2

      theorem suppliedInvariant (invariant : String → Prop)
          (initial : invariant suppliedContract.initial)
          (step : ∀ before event after, Allowed suppliedContract before event after →
            invariant before → invariant after) : invariant suppliedFinal :=
        suppliedTraceSound.preserves invariant initial step

      theorem suppliedEventsValid : ∀ event ∈ suppliedEvents,
          event ∈ suppliedContract.events ∧ eventMetadata suppliedContract event = true :=
        suppliedTraceSound.eventsValid

      end ReductionBounds.Protocol
      """

      proof = %Lynx.Lean{
        file: "generated_protocol_trace.lean",
        span: {1, 1},
        indentation: 0,
        source: source
      }

      {proof, _audit} = ProofInput.audit_bound(proof, %{source: :protocol_trace})
      {:ok, trace, proof}
    end
  end

  defp participants(values),
    do: values |> Enum.sort() |> list(fn {owner, unit} -> "(#{name(owner)}, #{name(unit)})" end)

  defp event_declarations(values) do
    values
    |> Enum.sort()
    |> list(fn {key, {owner, unit}} ->
      event(%Protocol.Event{name: key, owner: owner, cost_unit: unit})
    end)
  end

  defp event(%Protocol.Event{name: key, owner: owner, cost_unit: unit}),
    do: "⟨#{name(key)}, #{optional(owner)}, #{optional(unit)}⟩"

  defp edges(values),
    do:
      list(values, fn {before, event, after_state} ->
        "⟨#{name(before)}, #{name(event)}, #{name(after_state)}⟩"
      end)

  defp strings(values), do: list(values, &name/1)
  defp optional(nil), do: "none"
  defp optional(value), do: "(some #{name(value)})"
  defp name(value), do: value |> Atom.to_string() |> ProofInput.string()
  defp list(values, emit), do: "[#{Enum.map_join(values, ", ", emit)}]"
end
