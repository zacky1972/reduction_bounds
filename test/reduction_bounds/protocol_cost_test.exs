defmodule ReductionBounds.ProtocolCostTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.{PortProtocol, ProtocolCost, ProtocolSize}

  @moduletag :protocol_cost

  test "groups alternatives by owner and counter and substitutes both data dimensions" do
    {conditions, rules} = input()
    assert {:ok, profile} = ProtocolCost.new(conditions, rules)
    assert Map.keys(profile.bounds) == [:caller]
    assert Enum.sort(profile.unmodeled_participants) == [:external, :port]
    assert {:ok, value} = ProtocolCost.evaluate(profile.bounds.caller.formula, %{base: 2})
    assert value > 0
    assert {:ok, result} = ProtocolCost.check_trace(profile, [])
    assert result.lean_status == :not_checked
    assert :progress in result.unverified
  end

  test "rejects missing work, environmental charges, unknown features and uncounted contexts" do
    {conditions, rules} = input()
    context = {:prepared, :submit_accepted}

    for changed <- [
          Map.delete(rules, context),
          Map.put(rules, {:awaiting_response, :response_arrived}, %{
            counter: :total_events,
            cost: 1
          }),
          Map.put(rules, context, %{counter: :retries, cost: 1}),
          Map.put(rules, context, %{counter: :total_events, cost: {:data, :missing, :bytes}}),
          Map.put(rules, context, %{counter: :total_events, cost: -1})
        ] do
      assert {:error, _} = ProtocolCost.new(conditions, changed)
    end
  end

  test "rejects forged formula metadata and missing natural charges" do
    {conditions, rules} = input()
    {:ok, profile} = ProtocolCost.new(conditions, rules)

    assert {:error, :invalid_cost_profile} =
             ProtocolCost.check_trace(%{profile | bounds: %{}}, [])

    assert {:error, {:missing_natural_charge, :base}} =
             ProtocolCost.evaluate({:charge, :base}, %{})
  end

  defp input do
    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
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
      Map.new(conditions.rules, fn {context, rule} ->
        expr =
          Enum.reduce(rule.data, {:charge, :base}, fn slot, expr ->
            {:add, expr, {:add, {:data, slot, :bytes}, {:data, slot, :structure}}}
          end)

        {context, %{counter: List.first(rule.counts) || :total_events, cost: expr}}
      end)

    rules =
      Map.filter(rules, fn {{_, event}, _} ->
        elem(conditions.contract.events[event], 0) != nil
      end)

    {conditions, rules}
  end
end
