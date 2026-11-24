defmodule ReductionBounds.RpcProtocolProof do
  @moduledoc false

  alias ReductionBounds.{ProofInput, Protocol, ProtocolProof, RpcProtocol}

  @spec build(RpcProtocol.Session.t(), [RpcProtocol.Event.t()]) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(session, events) do
    with {:ok, candidate} <- RpcProtocol.check_trace(session, events),
         {:ok, _trace, base} <-
           ProtocolProof.build(session.contract, Enum.map(events, & &1.protocol)) do
      source = """
      namespace ReductionBounds.RpcProtocol

      def suppliedSession : Session := ⟨#{session.request_id}, #{optional(session.monitor_id)}⟩
      def suppliedRpcEvents : List Event := [#{Enum.map_join(events, ", ", &event/1)}]

      theorem suppliedContractMatches :
          Protocol.suppliedContract = contract suppliedSession := by rfl

      theorem suppliedErasure :
          suppliedRpcEvents.map Event.protocol = Protocol.suppliedEvents := by rfl

      theorem suppliedRpcCertificate :
          checkTrace suppliedSession suppliedRpcEvents Protocol.suppliedStates = true := by decide

      theorem suppliedRpcTraceSound :
          ValidTrace suppliedSession suppliedRpcEvents Protocol.suppliedFinal :=
        (checkTraceSound _ _ _ suppliedRpcCertificate).2

      theorem suppliedOutcomeMatches :
          outcome Protocol.suppliedFinal = #{ProofInput.string(Atom.to_string(candidate.outcome))} := by decide

      end ReductionBounds.RpcProtocol
      """

      proof = %{base | file: "generated_rpc_trace.lean", source: base.source <> source}
      {proof, audit} = ProofInput.audit_bound(proof, %{source: :rpc_trace})
      {:ok, Map.merge(candidate, audit), proof}
    end
  end

  defp event(%RpcProtocol.Event{protocol: %Protocol.Event{} = event} = annotated) do
    protocol =
      "⟨#{name(event.name)}, #{optional_name(event.owner)}, #{optional_name(event.cost_unit)}⟩"

    "⟨#{protocol}, #{optional(annotated.request_id)}, #{optional(annotated.monitor_id)}⟩"
  end

  defp name(value), do: value |> Atom.to_string() |> ProofInput.string()
  defp optional_name(nil), do: "none"
  defp optional_name(value), do: "(some #{name(value)})"
  defp optional(nil), do: "none"
  defp optional(value), do: "(some #{value})"
end
