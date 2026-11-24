defmodule ReductionBounds.RpcCostTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_cost
  alias ReductionBounds.{RpcCost, RpcCostProof, RpcServerContract, IntegerSize}
  import ReductionBounds.MailboxSupport
  import ReductionBounds.RpcCostSupport

  test "separates participants and replaces coarse observations with mailbox counts" do
    assert {:ok, c, _proof} = RpcCostProof.build(cost_profile(), [], success())
    assert c.lean_status == :not_checked
    assert c.server_contract.status == :assumed
    assert c.upper_bounds.client.cost_unit == :client_work
    assert c.upper_bounds.server.cost_unit == :server_work
    assert c.operation_counts.receive_setup == 1
    assert c.operation_counts.inspect == 1
    assert c.operation_counts.pattern == 1
    assert c.operation_counts.guard == 1
    refute Map.has_key?(c.operation_counts, :receive_reply)
    refute Map.has_key?(c.operation_counts, :inspect_unrelated)
    assert c.upper_bounds.server.upper_bound == 232
    assert :server_handler_bound in c.verification_scope.assumptions
    assert :progress in c.verification_scope.unverified
  end

  test "cost safety applies to pending, timeout and monitored prefixes without claiming completion" do
    down = {:tuple5, {:atom, "DOWN"}, {:ref, 9}, {:atom, "process"}, {:pid, 2}, {:atom, "gone"}}

    for {p, timeline} <- [
          {cost_profile(), sent()},
          {cost_profile(),
           sent() ++ [:timeout, {:protocol, :handle_timeout}, {:arrive, reply()}]},
          {cost_profile(conditions: profile(monitor_id: 9)),
           [{:protocol, :monitor_peer}] ++ sent() ++ [{:arrive, down}, :inspect]}
        ] do
      assert {:ok, c, _} = RpcCostProof.build(p, [], timeline)
      assert c.operation_counts.handle_request == 0
      assert c.server_contract.status == :assumed
    end
  end

  test "all rates are explicit and units cannot be mixed" do
    for bad <- [
          Map.delete(rates(), :pattern),
          Map.put(rates(), :handle_request, %{upper_bound: 0, cost_unit: :server_work}),
          put_in(rates(), [:send_request, :cost_unit], :server_work),
          put_in(rates(), [:inspect, :upper_bound], -1),
          put_in(rates(), [:guard, :upper_bound], :unknown)
        ] do
      assert {:error, :invalid_rpc_cost_rates} =
               RpcCost.new(profile(), bad, server_contract(),
                 initial_messages: 1,
                 server_calls: 1
               )
    end
  end

  test "requires independent server frame and a compatible unary integer input" do
    assert {:error, :invalid_rpc_server_frame} =
             RpcServerContract.assume({__MODULE__, :f, 1}, %IntegerSize{}, 1, %{})

    assert {:error, :rpc_handler_requires_unary_target} =
             RpcServerContract.assume({__MODULE__, :f, 2}, %IntegerSize{}, 1, frame())

    narrow = %{server_contract() | input: IntegerSize.from_integer(4)}

    assert {:error, :rpc_handler_input_not_covered} =
             RpcCostProof.build(cost_profile(server: narrow), [], success())

    small_frame =
      put_in(server_contract(), [:frame, :message_size], %ReductionBounds.RpcTerm.Size{
        nodes: 1,
        bytes: 0,
        integer_bits: 0
      })

    assert {:error, :rpc_server_request_size_exceeded} =
             RpcCostProof.build(cost_profile(server: small_frame), [], sent())

    assert {:error, :unsupported_rpc_handler_payload} =
             RpcServerContract.resolve(
               server_contract(),
               {:tuple3, {:atom, "request"}, {:ref, 7}, {:atom, "payload"}}
             )

    wrong_unit = Map.put(server_contract(), :cost_unit, :client_work)

    assert {:error, _} =
             RpcCost.new(profile(), rates(), wrong_unit, initial_messages: 1, server_calls: 1)
  end

  test "validates queue and invocation caps and refuses forged profiles" do
    assert {:error, _} =
             RpcCost.new(profile(), rates(), server_contract(),
               initial_messages: 0,
               server_calls: 2
             )

    assert {:error, _} = RpcCost.new(profile(), rates(), server_contract(), server_calls: 1)
    p = %{cost_profile() | initial_messages: 0}
    assert {:error, _} = RpcCostProof.build(p, [{:atom, "old"}], sent())
    assert {:error, _} = RpcCostProof.build(%{p | server_calls: 0}, [], success())
    assert {:error, _} = RpcCostProof.build(Map.put(p, :lean_status, :checked), [], sent())
  end
end
