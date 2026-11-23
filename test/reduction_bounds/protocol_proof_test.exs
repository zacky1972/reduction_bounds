defmodule ReductionBounds.ProtocolProofTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{PortProtocol, ProofInput, Protocol, ProtocolProof}

  @moduletag :protocol_model

  test "Lean checks supplied Port traces, including unfinished prefixes" do
    for names <- [
          [],
          [:prepare, :submit_accepted],
          [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode],
          [:prepare, :submit_rejected, :retry, :submit_accepted, :port_closed, :handle_closure],
          [:prepare, :submit_suspended, :resume_submission, :submit_rejected, :return_rejection]
        ] do
      {:ok, contract, events} = input(names)
      assert {:ok, trace, proof} = ProtocolProof.build(contract, events)
      assert trace.events == events
      assert_ok(proof)
    end
  end

  test "the checked invariant rule proves that the final state is declared" do
    {:ok, contract, events} = input([:prepare, :submit_accepted])
    {:ok, _trace, proof} = ProtocolProof.build(contract, events)

    source = """

    namespace ReductionBounds.Protocol
    example : suppliedFinal ∈ suppliedContract.states := by
      apply suppliedInvariant (fun state => state ∈ suppliedContract.states)
      · decide
      · intro before event after allowed _invariant
        exact allowed.2.2.2.2.2
    end ReductionBounds.Protocol
    """

    assert_ok(%{proof | source: proof.source <> source})
  end

  test "Elixir rejects invalid traces before generating Lean evidence" do
    {:ok, contract, events} = input([:prepare, :submit_accepted, :retry])

    assert {:error, {:invalid_protocol_trace, 2, _, {:transition_not_allowed, _, :retry}}} =
             ProtocolProof.build(contract, events)
  end

  test "Lean rejects altered states and altered event ownership independently" do
    {:ok, contract, events} = input([:prepare])
    {:ok, _trace, proof} = ProtocolProof.build(contract, events)

    for {from, to} <- [
          {~s(def suppliedStates : List String := ["prepared"]),
           ~s(def suppliedStates : List String := ["complete"])},
          {~S|def suppliedEvents : List Event := [⟨"prepare", (some "caller"), (some "symbolic_work")⟩]|,
           ~S|def suppliedEvents : List Event := [⟨"prepare", (some "external"), (some "external_work")⟩]|}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end
  end

  test "Lean rejects an unfinished replacement for a checked certificate" do
    {:ok, contract, events} = input([:prepare])
    {:ok, _trace, proof} = ProtocolProof.build(contract, events)

    changed =
      String.replace(
        proof.source,
        "checkTrace suppliedContract suppliedEvents suppliedStates = true := by decide",
        "checkTrace suppliedContract suppliedEvents suppliedStates = true := by sorry"
      )

    refute changed == proof.source
    assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
  end

  defp input(names) do
    {:ok, contract} = PortProtocol.new()

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(contract, name)
        event
      end)

    {:ok, contract, events}
  end

  defp assert_ok(proof) do
    reports = reports(proof)
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  defp reports(proof) do
    {:ok, postludes} = ProofInput.protocol_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)

    ReductionBounds.Verification.verify!(translation,
      postlude_imports: ["Erlang.erlang", "Erlang.maps"]
    )
  end
end
