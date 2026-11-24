defmodule ReductionBounds.ProtocolConditionsProofSupport do
  import ExUnit.Assertions

  alias ReductionBounds.{
    IntegerSize,
    PortProtocol,
    ProofInput,
    Protocol,
    ProtocolConditions,
    ProtocolSize
  }

  def scenarios do
    [
      empty: [],
      inspected_response: [
        :prepare,
        :submit_accepted,
        :inspect_message,
        :response_arrived,
        :inspect_message,
        :receive_response,
        :decode
      ],
      suspended_submission: [:prepare, :submit_suspended, :resume_submission, :submit_accepted]
    ]
  end

  def input(names) do
    limit = Integer.pow(2, 130)

    {:ok, profile} =
      PortProtocol.conditions(
        data_bounds: %{
          request: %ProtocolSize{bytes: 8, structure: 16},
          response: %ProtocolSize{bytes: 4, structure: 8},
          message: %ProtocolSize{bytes: 8, structure: 8}
        },
        integer_bounds: %{
          accumulator: %IntegerSize{lower: -limit, upper: limit, magnitude_bits: 131}
        },
        integer_events: %{prepare: [:accumulator]},
        count_bounds: %{
          total_events: 20,
          submission_attempts: 3,
          submission_events: 5,
          resumptions: 3,
          retries: 2,
          receive_inspections: 5
        }
      )

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(profile.contract, name)
        event
      end)

    {:ok, observation} =
      ProtocolConditions.observe(
        %{request: [[], []], response: <<1, 2>>, message: []},
        %{accumulator: limit}
      )

    observations =
      events |> Enum.with_index() |> Map.new(fn {_event, index} -> {index, observation} end)

    {profile, events, observations}
  end

  def assert_ok(proof) do
    reports = reports(proof)
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  def assert_error(proof) do
    assert Enum.any?(reports(proof), &(&1.status == :error))
  end

  def reports(proof) do
    {:ok, postludes} = ProofInput.protocol_condition_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)

    ReductionBounds.Verification.verify!(translation,
      postlude_imports: ["Erlang.erlang", "Erlang.maps"]
    )
  end
end

defmodule ReductionBounds.ProtocolConditionsProofTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.ProtocolConditionsProof
  import ReductionBounds.ProtocolConditionsProofSupport

  @moduletag :protocol_conditions
  @moduletag timeout: 300_000

  test "Lean independently rejects changed size evidence, caps, and reported counts" do
    {profile, events, observations} =
      input([
        :prepare,
        :submit_accepted,
        :inspect_message,
        :response_arrived,
        :inspect_message,
        :receive_response,
        :decode
      ])

    {:ok, _result, proof} = ProtocolConditionsProof.build(profile, events, observations)

    for {from, to} <- [
          {"⟨0, 5⟩", "⟨0, 17⟩"},
          {~S|("receive_inspections", 5)|, ~S|("receive_inspections", 2)|},
          {~S|("submission_attempts", 1)|, ~S|("submission_attempts", 0)|}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source
      assert_error(%{proof | source: changed})
    end
  end

  test "Lean rejects a missing magnitude condition even on an empty trace" do
    {profile, events, observations} = input([])
    {:ok, _result, proof} = ProtocolConditionsProof.build(profile, events, observations)
    changed = String.replace(proof.source, "(some 131)", "none")
    refute changed == proof.source
    assert_error(%{proof | source: changed})
  end

  test "Lean rejects an unfinished condition certificate" do
    {profile, events, observations} = input([:prepare])
    {:ok, _result, proof} = ProtocolConditionsProof.build(profile, events, observations)

    changed =
      String.replace(
        proof.source,
        "suppliedObservations = true := by decide",
        "suppliedObservations = true := by sorry"
      )

    refute changed == proof.source
    assert_error(%{proof | source: changed})
  end
end

defmodule ReductionBounds.ProtocolConditionsProofScenarioTest do
  use ExUnit.Case,
    async: true,
    parameterize:
      for(
        {scenario, _names} <- ReductionBounds.ProtocolConditionsProofSupport.scenarios(),
        do: %{scenario: scenario}
      )

  alias ReductionBounds.ProtocolConditionsProof
  import ReductionBounds.ProtocolConditionsProofSupport

  @moduletag :protocol_conditions
  @moduletag timeout: 300_000

  setup context do
    ReductionBounds.TestFixtures.label_scenario(context)
  end

  test "Lean checks sizes, large integers, state-dependent counts, and empty prefixes", %{
    scenario: scenario
  } do
    names = Keyword.fetch!(scenarios(), scenario)
    {profile, events, observations} = input(names)
    assert {:ok, result, proof} = ProtocolConditionsProof.build(profile, events, observations)
    assert result.lean_status == :not_checked
    assert_ok(proof)
  end
end
