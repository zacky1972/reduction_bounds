defmodule ReductionBounds.RpcMailboxProof do
  @moduledoc false
  alias ReductionBounds.{MailboxProof, ProofInput, RpcConditions, RpcProtocolProof, RpcTerm}

  @spec build(map(), list(), list()) :: {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(profile, queue, timeline) do
    with {:ok, candidate} <- RpcConditions.check_trace(profile, queue, timeline),
         {:ok, _rpc, rpc_proof} <- RpcProtocolProof.build(profile.session, candidate.events),
         {:ok, _mailbox, mailbox_proof} <-
           MailboxProof.build(profile.mailbox, queue, candidate.mailbox_actions) do
      config =
        "⟨RpcProtocol.suppliedSession, #{RpcTerm.lean(profile.request)}, #{RpcTerm.lean_size(profile.request_size)}, #{RpcTerm.lean_size(profile.response_size)}, Mailbox.suppliedMailboxSpec, #{ReductionBounds.MailboxMatch.lean_guard(profile.reply_guard)}, #{counts(profile.protocol_limits)}⟩"

      names =
        Enum.map_join(
          candidate.events,
          ", ",
          &ProofInput.string(Atom.to_string(&1.protocol.name))
        )

      final =
        "⟨Mailbox.suppliedMailboxFinal, Mailbox.suppliedCounts, #{ProofInput.string(Atom.to_string(candidate.trace.final))}, [#{names}], #{counts(candidate.protocol_counts)}⟩"

      source = """
      namespace ReductionBounds.RpcMailbox
      def suppliedConfig : Config := #{config}
      def suppliedTimeline : List Item := [#{Enum.map_join(timeline, ", ", &item/1)}]
      def suppliedMailboxResult : State := #{final}
      theorem suppliedTimelineCertificate :
          run suppliedConfig Mailbox.suppliedQueue suppliedTimeline = some suppliedMailboxResult := by decide
      theorem suppliedTimelineSound :
          Runs suppliedConfig {mailbox := Mailbox.initial Mailbox.suppliedQueue}
            suppliedTimeline suppliedMailboxResult :=
        (runSound _ _ _ _ suppliedTimelineCertificate).2.2
      theorem suppliedProtocolProjection :
          suppliedMailboxResult.events = RpcProtocol.suppliedRpcEvents.map (fun e => e.protocol.name) := by rfl
      theorem suppliedFinalAgreement : suppliedMailboxResult.protocolState = Protocol.suppliedFinal := by rfl
      theorem suppliedMailboxActions :
          suppliedTimeline.filterMap (fun i => match i with | .mailbox a => some a | _ => none)
            = Mailbox.suppliedActions := by rfl
      end ReductionBounds.RpcMailbox
      """

      proof = %{
        rpc_proof
        | file: "generated_rpc_mailbox.lean",
          source: rpc_proof.source <> mailbox_proof.source <> source
      }

      {proof, audit} = ProofInput.audit_bound(proof, %{source: :rpc_mailbox})
      {:ok, Map.merge(candidate, audit), proof}
    end
  end

  defp counts(c),
    do:
      "⟨#{Enum.map_join([:events, :client_sends, :server_sends, :response_handlers, :retries], ", ", &c[&1])}⟩"

  defp item({:protocol, name}), do: "(.protocol #{ProofInput.string(Atom.to_string(name))})"
  defp item(action), do: "(.mailbox #{MailboxProof.action(action)})"
end
