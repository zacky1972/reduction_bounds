defmodule ReductionBounds.ProtocolCostProofTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{
    IntegerSize,
    PortProtocol,
    ProofInput,
    Protocol,
    ProtocolConditions,
    ProtocolCost,
    ProtocolCostProof,
    ProtocolSize
  }

  @moduletag :protocol_cost

  test "Lean proves universal finite trace and prefix budgets including suspended and empty runs" do
    for names <- [
          [],
          [:prepare, :submit_suspended],
          [
            :prepare,
            :submit_rejected,
            :retry,
            :submit_accepted,
            :inspect_message,
            :response_arrived,
            :receive_response,
            :decode
          ]
        ] do
      {profile, events, observations} = input(names)
      assert {:ok, result, proof} = ProtocolCostProof.build(profile, events, observations)
      assert result.upper_bounds.caller.cost_unit == :symbolic_work
      assert result.unmodeled_participants |> Enum.sort() == [:external, :port]
      assert_ok(proof)
    end
  end

  test "Lean keeps two participants and distinct units separate" do
    {:ok, contract} =
      Protocol.new(
        participants: %{client: :client_work, server: :server_work},
        states: [:ready],
        initial: :ready,
        terminal: [],
        events: %{send_request: {:client, :client_work}, compute: {:server, :server_work}},
        transitions: [{:ready, :send_request, :ready}, {:ready, :compute, :ready}]
      )

    {:ok, conditions} =
      ProtocolConditions.new(contract,
        count_bounds: %{total_events: 3},
        rules: %{
          {:ready, :send_request} => %ProtocolConditions.Rule{},
          {:ready, :compute} => %ProtocolConditions.Rule{}
        }
      )

    {:ok, profile} =
      ProtocolCost.new(conditions, %{
        {:ready, :send_request} => %{counter: :total_events, cost: {:charge, :base}},
        {:ready, :compute} => %{counter: :total_events, cost: {:charge, :base}}
      })

    events =
      Enum.map([:send_request, :compute], fn name ->
        {:ok, event} = Protocol.event(contract, name)
        event
      end)

    assert profile.bounds.client.cost_unit == :client_work
    assert profile.bounds.server.cost_unit == :server_work
    assert {:ok, 6} = ProtocolCost.evaluate(profile.bounds.client.formula, %{base: 2})
    assert {:ok, 21} = ProtocolCost.evaluate(profile.bounds.server.formula, %{base: 7})
    {:ok, _, proof} = ProtocolCostProof.build(profile, events)
    assert_ok(proof)
  end

  test "Lean rejects changed formulas, counters, unsupported size evidence and unfinished proofs" do
    {profile, events, observations} = input([:prepare, :submit_suspended])
    {:ok, _, proof} = ProtocolCostProof.build(profile, events, observations)

    for {from, to} <- [
          {"def suppliedBound0 : Expr :=", "def suppliedBound0 : Expr := .add (.constant 1)"},
          {~S|"submission_attempts", 3|, ~S|"submission_attempts", 0|},
          {"⟨0, 1⟩", "⟨0, 99⟩"},
          {"suppliedGroups := by decide", "suppliedGroups := by sorry"}
        ] do
      changed = String.replace(proof.source, from, to)
      refute changed == proof.source, from
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end
  end

  defp input(names) do
    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
        integer_bounds: %{accumulator: %IntegerSize{magnitude_bits: 131}},
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

    rules =
      for {context = {_, event}, rule} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{} do
        expr =
          Enum.reduce(rule.data, {:charge, :base}, fn slot, expr ->
            {:add, expr, {:mul, {:data, slot, :bytes}, {:data, slot, :structure}}}
          end)

        expr =
          if :accumulator in rule.integers,
            do: {:max, expr, {:integer, :accumulator, :magnitude_bits}},
            else: expr

        {context, %{counter: List.first(rule.counts) || :total_events, cost: expr}}
      end

    {:ok, profile} = ProtocolCost.new(conditions, rules)

    events =
      Enum.map(names, fn name ->
        {:ok, event} = Protocol.event(conditions.contract, name)
        event
      end)

    {:ok, observation} =
      ProtocolConditions.observe(%{request: [], response: [], message: []}, %{
        accumulator: Integer.pow(2, 130)
      })

    observations = events |> Enum.with_index() |> Map.new(fn {_, i} -> {i, observation} end)
    {profile, events, observations}
  end

  defp assert_ok(proof) do
    reports = reports(proof)
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  defp reports(proof) do
    {:ok, postludes} = ProofInput.protocol_cost_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)

    ReductionBounds.Verification.verify!(translation,
      postlude_imports: ["Erlang.erlang", "Erlang.maps"]
    )
  end
end
