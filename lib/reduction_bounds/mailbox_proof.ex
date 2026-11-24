defmodule ReductionBounds.MailboxProof do
  @moduledoc false
  alias ReductionBounds.{Mailbox, MailboxMatch, ProofInput, RpcTerm}

  @spec build(Mailbox.spec(), list(), list()) :: {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(spec, initial, actions) do
    with {:ok, result} <- Mailbox.run(spec, initial, actions) do
      source = """
      namespace ReductionBounds.Mailbox
      def suppliedMailboxSpec : Spec := #{lean_spec(spec)}
      def suppliedQueue : List RpcTerm.Term := #{terms(initial)}
      def suppliedActions : List Action := [#{Enum.map_join(actions, ", ", &action/1)}]
      def suppliedMailboxFinal : State := #{state(result.state)}
      def suppliedCounts : Counts := #{counts(result.counts)}
      theorem suppliedMailboxCertificate :
          check suppliedMailboxSpec suppliedQueue suppliedActions suppliedMailboxFinal suppliedCounts = true := by decide
      theorem suppliedMailboxRun :
          Runs suppliedMailboxSpec (Mailbox.initial suppliedQueue) suppliedActions suppliedMailboxFinal suppliedCounts :=
        (checkSound _ _ _ _ _ suppliedMailboxCertificate).2.2.1
      theorem suppliedMailboxLimits : suppliedCounts.within suppliedMailboxSpec.limits = true :=
        (checkSound _ _ _ _ _ suppliedMailboxCertificate).2.2.2
      end ReductionBounds.Mailbox
      """

      proof = %Lynx.Lean{
        source: source,
        file: "generated_mailbox.lean",
        span: {1, 1},
        indentation: 0
      }

      {proof, audit} = ProofInput.audit_bound(proof, %{source: :mailbox})
      {:ok, Map.merge(result, audit), proof}
    end
  end

  @doc false
  @spec lean_spec(Mailbox.spec()) :: String.t()
  def lean_spec(spec) do
    clauses =
      Enum.map_join(spec.clauses, ", ", fn c ->
        "⟨#{ProofInput.string(Atom.to_string(c.kind))}, #{MailboxMatch.lean_pattern(c.pattern)}, #{MailboxMatch.lean_guard(c.guard)}⟩"
      end)

    "⟨[#{clauses}], #{RpcTerm.lean_size(spec.message_size)}, #{counts(spec.limits)}, #{if(spec.timeout == :infinity, do: "none", else: "(some #{spec.timeout})")}⟩"
  end

  @doc false
  @spec terms(list()) :: String.t()
  def terms(terms), do: "[#{Enum.map_join(terms, ", ", &RpcTerm.lean/1)}]"
  @doc false
  @spec counts(map()) :: String.t()
  def counts(c), do: "⟨#{Enum.map_join(Mailbox.counters(), ", ", &c[&1])}⟩"
  @doc false
  @spec state(Mailbox.state()) :: String.t()
  def state(s),
    do:
      "⟨#{terms(s.queue)}, #{s.cursor}, .#{if(s.phase == :timed_out, do: "timedOut", else: s.phase)}, #{if(is_nil(s.selected), do: "none", else: "(some #{RpcTerm.lean(s.selected)})")}, #{if(is_nil(s.clause), do: "none", else: "(some #{s.clause})")}⟩"

  @doc false
  @spec action(term()) :: String.t()
  def action({:arrive, t}), do: "(.arrive #{RpcTerm.lean(t)})"
  def action(:begin_receive), do: ".beginReceive"
  def action(:inspect), do: ".inspect"
  def action(:timeout), do: ".timeout"
end
