defmodule ReductionBounds.RpcCostSupport do
  alias ReductionBounds.{IntegerSize, RpcCost, RpcServerContract}
  import ReductionBounds.MailboxSupport

  def frame do
    %{
      message_size: cap(),
      reply_size: cap(),
      initial_messages: 10,
      arrivals: 10,
      inspections: 20,
      pattern_attempts: 20,
      guard_attempts: 20
    }
  end

  def rates do
    Map.new(RpcCost.operations() -- [:handle_request], fn op ->
      {op,
       %{
         cost_unit: if(RpcCost.owner(op) == :client, do: :client_work, else: :server_work),
         upper_bound: 2
       }}
    end)
  end

  def server_contract do
    {:ok, c} =
      RpcServerContract.assume(
        {__MODULE__, :handler, 1},
        %IntegerSize{lower: 0, upper: 10, magnitude_bits: 4},
        30,
        frame()
      )

    c
  end

  def cost_profile(options \\ []) do
    {:ok, p} =
      RpcCost.new(
        Keyword.get(options, :conditions, profile()),
        rates(),
        Keyword.get(options, :server, server_contract()),
        initial_messages: 10,
        server_calls: 1
      )

    p
  end
end
