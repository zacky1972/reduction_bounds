defmodule ReductionBounds.RpcSourceTest do
  use ExUnit.Case, async: true
  @moduletag :rpc_source
  alias ReductionBounds.RpcSource
  alias ReductionBounds.Fixtures.{RpcClient, RpcHelpers}
  import ReductionBounds.RpcCostSupport

  test "retains request fields, argument identities, clause order and source work" do
    for function <- [:request, :reordered, :zero_timeout] do
      assert {:ok, c} = infer(function)
      assert c.source_correspondence == :certificate_pending
      assert c.source_node_bound == 21

      assert {:let_value, _, {:tuple3, {:literal, {:atom, "request"}}, _, _},
              {:seq_call, {:erlang, :send, _}, _}} = c.core_source

      assert c.call_contracts.reply.status == :assumed
      assert c.call_contracts.reply.totality == :not_established
      assert c.primitive_contracts |> hd() |> Map.fetch!(:delivery) == :not_established
      assert :helper_matching_and_scanning in c.unverified
      assert c.lean_status == :not_checked
    end

    {:ok, a} = infer(:request)
    {:ok, b} = infer(:reordered)
    refute a.core_source == b.core_source
  end

  test "literal timeout agrees with conditions rather than implying progress" do
    cp = cost_profile(conditions: ReductionBounds.MailboxSupport.profile(timeout: :infinity))
    assert {:ok, c} = RpcSource.infer({RpcClient, :infinity_timeout, 4}, cp, options())
    assert c.timeout_value == {:atom, "infinity"}
    assert {:error, {:rpc_source, _, {:reply_argument_mismatch, _}}} = infer(:wrong_timeout)
    refute Map.has_key?(c, :completion)
  end

  test "rejects wrong correlation, destination, payload, returned outcome and repeated sends" do
    for {f, reason} <- [
          wrong_token: :reply_argument_mismatch,
          wrong_request: :request_construction_mismatch,
          wrong_server: :send_argument_mismatch,
          wrong_decode: :decode_argument_mismatch,
          wrong_return: :unsupported_workflow,
          repeated_send: :unsupported_workflow
        ] do
      assert {:error, {:rpc_source, target, detail}} = infer(f)
      assert target == {RpcClient, f, 4}
      assert elem(detail, 0) == reason
      assert is_list(elem(detail, 1))
    end
  end

  test "unsupported native receive, guards, dynamic calls, helpers, recursion and exceptions never fall back" do
    for f <- [:native_receive, :guarded, :dynamic, :helper_preparation, :recursive, :exception] do
      assert {:error, {:rpc_source, {RpcClient, ^f, 4}, detail}} = infer(f)
      assert is_list(elem(detail, 1))
    end
  end

  test "requires named helper contracts and rejects monitored profiles and unsupported option forms" do
    assert {:error, {:rpc_source, _, {:required_rpc_source_contracts, _}}} =
             RpcSource.infer({RpcClient, :request, 4}, cost_profile())

    cp = cost_profile(conditions: ReductionBounds.MailboxSupport.profile(monitor_id: 9))

    assert {:error, {:rpc_source, _, {:unsupported_monitor, []}}} =
             RpcSource.infer({RpcClient, :request, 4}, cp, options())

    for o <- [
          [calls: %{}, receive_optimization: :fresh_ref],
          [calls: fn -> true end],
          [beam_binaries: [123]]
        ] do
      assert {:error, {:rpc_source, _, _}} =
               RpcSource.infer({RpcClient, :request, 4}, cost_profile(), o)
    end
  end

  test "requires debug information, the documented arity and unambiguous helper identities" do
    beam =
      Enum.find(ReductionBounds.TestFixtures.rpc_client_beams(), fn binary ->
        Keyword.fetch!(:beam_lib.info(binary), :module) == RpcClient
      end)

    {:ok, {RpcClient, stripped}} = :beam_lib.strip(beam)
    target = {RpcClient, :request, 4}

    assert {:error, {:rpc_source, ^target, _}} =
             RpcSource.infer(
               target,
               cost_profile(),
               Keyword.put(options(), :beam_binaries, [stripped])
             )

    assert {:error, {:rpc_source, _, {:unsupported_target_arity, [], 4}}} =
             RpcSource.infer({RpcClient, :request, 3}, cost_profile(), options())

    assert {:error, {:rpc_source, _, {:invalid_target, []}}} =
             RpcSource.infer(:invalid, cost_profile(), options())

    bad = Keyword.update!(options(), :calls, &Map.put(&1, :decode, {RpcHelpers, :await_reply, 1}))

    assert {:error, {:rpc_source, _, :ambiguous_rpc_source_contracts}} =
             RpcSource.infer(target, cost_profile(), bad)
  end

  defp infer(f), do: RpcSource.infer({RpcClient, f, 4}, cost_profile(), options())

  defp options(),
    do: [
      beam_binaries: ReductionBounds.TestFixtures.rpc_client_beams(),
      calls: %{reply: {RpcHelpers, :await_reply, 3}, decode: {RpcHelpers, :decode, 1}}
    ]
end
