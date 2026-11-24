defmodule ReductionBounds.ProtocolProofSupport do
  import ExUnit.Assertions
  alias ReductionBounds.{PortProtocol, ProofInput, Protocol}

  def scenarios do
    [
      empty: [],
      unfinished: [:prepare, :submit_accepted],
      success: [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode],
      retry_and_closure: [
        :prepare,
        :submit_rejected,
        :retry,
        :submit_accepted,
        :port_closed,
        :handle_closure
      ],
      suspended_and_rejected: [
        :prepare,
        :submit_suspended,
        :resume_submission,
        :submit_rejected,
        :return_rejection
      ]
    ]
  end

  def input(names) do
    {:ok, contract} = PortProtocol.new()

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(contract, name)
        event
      end)

    {:ok, contract, events}
  end

  def assert_ok(proof) do
    reports = reports(proof)
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  def reports(proof) do
    {:ok, postludes} = ProofInput.protocol_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)

    ReductionBounds.Verification.verify!(translation,
      postlude_imports: ["Erlang.erlang", "Erlang.maps"]
    )
  end
end

defmodule ReductionBounds.ProtocolProofTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.ProtocolProof
  import ReductionBounds.ProtocolProofSupport

  @moduletag :protocol_model
  @moduletag timeout: 300_000

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
end

defmodule ReductionBounds.ProtocolProofScenarioTest do
  use ExUnit.Case,
    async: true,
    parameterize:
      for(
        {scenario, _names} <- ReductionBounds.ProtocolProofSupport.scenarios(),
        do: %{scenario: scenario}
      )

  alias ReductionBounds.ProtocolProof
  import ReductionBounds.ProtocolProofSupport

  @moduletag :protocol_model
  @moduletag timeout: 300_000

  setup context do
    ReductionBounds.TestFixtures.label_scenario(context)
  end

  test "Lean checks supplied Port traces, including unfinished prefixes", %{scenario: scenario} do
    names = Keyword.fetch!(scenarios(), scenario)
    {:ok, contract, events} = input(names)
    assert {:ok, trace, proof} = ProtocolProof.build(contract, events)
    assert trace.events == events
    assert_ok(proof)
  end
end
