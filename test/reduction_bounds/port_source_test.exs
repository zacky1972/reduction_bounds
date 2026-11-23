defmodule ReductionBounds.PortSourceTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.{PortProtocol, PortSource, ProtocolCost, ProtocolSize}
  alias ReductionBounds.Fixtures.{PortClient, PortHelpers}

  @moduletag :port_source

  test "retains bindings, argument identities, clause order and source overhead" do
    for function <- [:request, :reordered] do
      assert {:ok, result} = PortSource.infer({PortClient, function, 2}, profile(), options())
      assert result.source_correspondence == :certificate_pending
      assert result.source_node_bound == 25
      assert {:add, {:mul, 25, {:charge, :source_node}}, _} = result.upper_bounds.caller.formula
      assert result.call_contracts.reply.status == :assumed
      assert :helper_implementations in result.unverified
      assert result.lean_status == :not_checked
      assert {:let_call, _, {PortHelpers, :prepare, [_]}, _} = result.core_source
    end
  end

  test "rejects incorrect Port routing, blocking submission and native receive with source locations" do
    for {function, reason} <- [
          wrong_port: :reply_argument_mismatch,
          blocking: :unsupported_submission,
          native_receive: :unsupported_expression
        ] do
      target = {PortClient, function, 2}

      assert {:error, {:port_source, ^target, detail}} =
               PortSource.infer(target, profile(), options())

      assert elem(detail, 0) == reason
      assert is_list(elem(detail, 1))
    end
  end

  test "reports missing contracts and rejects substituted helpers" do
    target = {PortClient, :request, 2}

    assert {:error, {:port_source, ^target, {:missing_port_call_contracts, _}}} =
             PortSource.infer(target, profile(), [])

    opts = Keyword.update!(options(), :calls, &Map.put(&1, :decode, {PortHelpers, :prepare, 1}))

    assert {:error, {:port_source, ^target, :ambiguous_port_call_contracts}} =
             PortSource.infer(target, profile(), opts)
  end

  defp options,
    do: [
      beam_binaries: ReductionBounds.TestFixtures.port_client_beams(),
      calls: %{
        prepare: {PortHelpers, :prepare, 1},
        reply: {PortHelpers, :await_reply, 1},
        decode: {PortHelpers, :decode, 1}
      }
    ]

  defp profile do
    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
        count_bounds: %{
          total_events: 30,
          submission_attempts: 4,
          submission_events: 8,
          resumptions: 3,
          retries: 3,
          receive_inspections: 8
        }
      )

    rules =
      for {{_, event} = context, _} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{},
          do: {context, %{counter: :total_events, cost: {:charge, :local}}}

    {:ok, profile} = ProtocolCost.new(conditions, rules)
    profile
  end
end
