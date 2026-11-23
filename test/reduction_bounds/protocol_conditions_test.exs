defmodule ReductionBounds.ProtocolConditionsTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.{IntegerSize, PortProtocol, Protocol, ProtocolConditions, ProtocolSize}
  alias ReductionBounds.ProtocolConditions.{Observation, Rule}

  @moduletag :protocol_conditions

  test "reports explicit conditions and counts the matching receive inspection" do
    profile = profile()
    names = [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode]
    observations = observations(profile, names)

    assert {:ok, result} =
             ProtocolConditions.check_trace(profile, events(profile, names), observations)

    assert result.counts == %{
             total_events: 5,
             submission_attempts: 1,
             submission_events: 1,
             resumptions: 0,
             retries: 0,
             receive_inspections: 1
           }

    assert result.conditions == profile
    assert result.lean_status == :not_checked
    assert :progress in result.unverified
    assert :size_summary_association in result.assumptions
  end

  test "does not count resumed submission results as new attempts" do
    profile = profile()

    names = [
      :prepare,
      :submit_suspended,
      :resume_submission,
      :submit_suspended,
      :resume_submission,
      :submit_accepted
    ]

    assert {:ok, result} =
             ProtocolConditions.check_trace(
               profile,
               events(profile, names),
               observations(profile, names)
             )

    assert result.counts.submission_attempts == 1
    assert result.counts.submission_events == 3
    assert result.counts.resumptions == 2
    refute result.trace.terminal?
  end

  test "counts repeated and matching inspections across response arrival" do
    profile = profile()

    names = [
      :prepare,
      :submit_rejected,
      :retry,
      :submit_accepted,
      :inspect_message,
      :response_arrived,
      :inspect_message,
      :receive_response,
      :decode
    ]

    assert {:ok, result} =
             ProtocolConditions.check_trace(
               profile,
               events(profile, names),
               observations(profile, names)
             )

    assert result.counts.retries == 1
    assert result.counts.submission_attempts == 2
    assert result.counts.receive_inspections == 3
    limited = %{profile | count_bounds: Map.put(profile.count_bounds, :receive_inspections, 2)}

    assert {:error, {:protocol_count_exceeded, :receive_inspections, 3, 2}} =
             ProtocolConditions.check_trace(
               limited,
               events(limited, names),
               observations(limited, names)
             )
  end

  test "requires independent response and structural bounds" do
    profile = profile()

    assert {:error,
            {:invalid_protocol_condition_rule, _, {:missing_protocol_condition, :data, :response}}} =
             ProtocolConditions.validate(%{
               profile
               | data_bounds: Map.delete(profile.data_bounds, :response)
             })

    assert {:error, {:invalid_protocol_condition, :data, {:response, _}}} =
             ProtocolConditions.validate(%{
               profile
               | data_bounds: Map.put(profile.data_bounds, :response, %ProtocolSize{})
             })

    limited = %{
      profile
      | data_bounds: Map.put(profile.data_bounds, :request, %ProtocolSize{bytes: 0, structure: 4})
    }

    {:ok, observed} = ProtocolConditions.observe(%{request: [[], []]})

    assert {:error,
            {:protocol_condition_failed, 0, :idle, :prepare,
             {:data_size_exceeded, :request, _, _}}} =
             ProtocolConditions.check_trace(limited, events(limited, [:prepare]), %{0 => observed})
  end

  test "uses Issue 1 integer range and magnitude conditions without assuming an encoding" do
    limit = Integer.pow(2, 200)

    {:ok, profile} =
      PortProtocol.conditions(
        options() ++
          [
            integer_bounds: %{
              numerator: %IntegerSize{lower: -limit, upper: limit, magnitude_bits: 201}
            },
            integer_events: %{prepare: [:numerator]}
          ]
      )

    {:ok, observed} = ProtocolConditions.observe(%{request: <<1>>}, %{numerator: limit})

    assert {:ok, _} =
             ProtocolConditions.check_trace(profile, events(profile, [:prepare]), %{0 => observed})

    wrong = %{observed | integers: %{numerator: limit + 1}}

    assert {:error,
            {:protocol_condition_failed, 0, :idle, :prepare,
             {:integer_condition_failed, :numerator, _, _}}} =
             ProtocolConditions.check_trace(profile, events(profile, [:prepare]), %{0 => wrong})

    assert {:error, {:protocol_data, :request, {:invalid_iodata, ^limit}}} =
             ProtocolConditions.observe(%{request: [limit]})
  end

  test "rejects missing observations, caps, unknown fields, and incomplete rule coverage" do
    profile = profile()

    assert {:error,
            {:protocol_condition_failed, 0, :idle, :prepare, {:missing_data_size, :request}}} =
             ProtocolConditions.check_trace(profile, events(profile, [:prepare]))

    assert {:error, {:missing_protocol_condition, :count, :total_events}} =
             ProtocolConditions.validate(%{
               profile
               | count_bounds: Map.delete(profile.count_bounds, :total_events)
             })

    assert {:error, :protocol_condition_rule_coverage} =
             ProtocolConditions.validate(%{profile | rules: %{}})

    assert {:error, {:invalid_observation_index, {1, _}}} =
             ProtocolConditions.check_trace(profile, [], %{1 => %Observation{}})

    assert {:error, _} = PortProtocol.conditions(options() ++ [rules: %{}])
    assert {:error, _} = PortProtocol.conditions(options() ++ [integer_events: %{unknown: []}])
    wrong = Map.put(profile.rules, {:idle, :prepare}, %Rule{counts: [:total_events]})

    assert {:error,
            {:invalid_protocol_condition_rule, {:idle, :prepare}, :total_events_is_implicit}} =
             ProtocolConditions.validate(%{profile | rules: wrong})
  end

  test "zero-length prefixes do not need observations or imply completion" do
    profile = profile()
    assert {:ok, result} = ProtocolConditions.check_trace(profile, [])
    assert Enum.all?(result.counts, fn {_key, count} -> count == 0 end)
    refute result.trace.terminal?
  end

  defp profile() do
    {:ok, result} = PortProtocol.conditions(options())
    result
  end

  defp options() do
    [
      data_bounds: %{
        request: %ProtocolSize{bytes: 8, structure: 10},
        response: %ProtocolSize{bytes: 4, structure: 8},
        message: %ProtocolSize{bytes: 8, structure: 8}
      },
      count_bounds: %{
        total_events: 30,
        submission_attempts: 3,
        submission_events: 5,
        resumptions: 3,
        retries: 2,
        receive_inspections: 5
      }
    ]
  end

  defp events(profile, names) do
    Enum.map(names, fn name ->
      {:ok, event} = Protocol.event(profile.contract, name)
      event
    end)
  end

  defp observations(profile, names) do
    {:ok, trace} = Protocol.check_trace(profile.contract, events(profile, names))

    trace.states
    |> Enum.drop(-1)
    |> Enum.zip(names)
    |> Enum.with_index()
    |> Map.new(fn {{state, name}, index} ->
      rule = profile.rules[{state, name}]
      data = Map.new(rule.data, &{&1, <<1>>})
      {:ok, observation} = ProtocolConditions.observe(data)
      {index, observation}
    end)
  end
end
