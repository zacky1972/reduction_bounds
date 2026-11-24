defmodule ReductionBounds.RpcCost do
  @moduledoc """
  Conditional participant-specific budgets for the supplied single-attempt RPC.

  Rates are finite natural upper envelopes, each with `:upper_bound` and
  `:cost_unit` (`:client_work` or `:server_work`). Every operation returned by
  `operations/0` must be declared, except `:handle_request`, supplied by the
  server contract. Zero is allowed only as an explicit declaration.

  Client envelopes apply under the RPC sizes, matching program, queue cap
  (`initial_messages + arrivals`) and count conditions. Server receive/send
  envelopes apply under the independent server frame. They must include all
  work assigned to those modeled operations, including server selection work.
  Choosing finite rates asserts their applicability; this module does not
  derive VM costs from sizes. Large integers, copies and guard traversal must
  be covered by the supplied envelopes.

  `RpcCostProof.build/3` checks a finite timeline and constructs universal
  conditional cost-safety and prefix theorems. Builders retain `:not_checked`
  until submitted to the existing verification boundary. Bounds count mailbox
  inspection, pattern attempts and guard attempts separately, without charging
  coarse receive/inspect observations again. Client and server units are never
  added. This stage does not establish RPC completion or source correspondence.
  """
  alias ReductionBounds.{RpcConditions, RpcServerContract}

  @client [
    :prepare,
    :monitor_peer,
    :send_request,
    :process_reply,
    :decode_error,
    :handle_timeout,
    :handle_peer_down,
    :receive_setup,
    :inspect,
    :pattern,
    :guard
  ]
  @server [:receive_request, :send_reply, :handle_request]
  @lean ~w(prepare monitor sendRequest processReply decodeError handleTimeout handleDown receiveSetup inspect pattern guard receiveRequest sendReply handleRequest)

  @spec operations() :: [atom()]
  def operations(), do: @client ++ @server

  @spec new(map(), map(), map(), keyword()) :: {:ok, map()} | {:error, term()}
  def new(conditions, rates, server, options) do
    with :ok <- RpcConditions.validate(conditions),
         :ok <- rates(rates),
         true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, [:initial_messages, :server_calls]),
         true <- Enum.all?([:initial_messages, :server_calls], &natural?(options[&1])),
         true <- options[:server_calls] <= 1,
         :ok <- RpcServerContract.validate(server) do
      {:ok,
       %{
         conditions: conditions,
         rates: rates,
         server: server,
         initial_messages: options[:initial_messages],
         server_calls: options[:server_calls]
       }}
    else
      false -> {:error, :invalid_rpc_cost_conditions}
      error -> error
    end
  end

  @doc false
  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%{conditions: c, rates: r, server: s, initial_messages: i, server_calls: n} = p) do
    case new(c, r, s, initial_messages: i, server_calls: n) do
      {:ok, ^p} -> :ok
      _ -> {:error, :invalid_rpc_cost_profile}
    end
  end

  def validate(_profile), do: {:error, :invalid_rpc_cost_profile}

  @doc false
  @spec owner(atom()) :: :client | :server
  def owner(op) when op in @client, do: :client
  def owner(op) when op in @server, do: :server

  @doc false
  @spec lean_operation(atom()) :: String.t()
  def lean_operation(op), do: Enum.zip(operations(), @lean) |> Map.new() |> Map.fetch!(op)

  @doc false
  @spec counts(map()) :: map()
  def counts(candidate) do
    names = Enum.map(candidate.events, & &1.protocol.name)

    Map.new(operations(), fn op ->
      n =
        case op do
          :receive_setup -> candidate.counts.receives
          :inspect -> candidate.counts.inspections
          :pattern -> candidate.counts.pattern_attempts
          :guard -> candidate.counts.guard_attempts
          _ -> Enum.count(names, &(&1 == op))
        end

      {op, n}
    end)
  end

  @doc false
  @spec limits(map()) :: map()
  def limits(profile) do
    p = profile.conditions.protocol_limits
    m = profile.conditions.mailbox.limits

    Map.new(operations(), &{&1, operation_limit(&1, p, m, profile.server_calls)})
  end

  defp operation_limit(:receive_setup, _p, m, _n), do: m.receives
  defp operation_limit(:inspect, _p, m, _n), do: m.inspections
  defp operation_limit(:pattern, _p, m, _n), do: m.pattern_attempts
  defp operation_limit(:guard, _p, m, _n), do: m.guard_attempts
  defp operation_limit(:send_request, p, _m, _n), do: p.client_sends
  defp operation_limit(:send_reply, p, _m, _n), do: p.server_sends
  defp operation_limit(:handle_request, _p, _m, n), do: n

  defp operation_limit(op, p, _m, _n)
       when op in [:process_reply, :decode_error, :handle_timeout, :handle_peer_down],
       do: p.response_handlers

  defp operation_limit(_op, p, _m, _n), do: p.events

  @doc false
  @spec budget(map(), map(), :client | :server) :: non_neg_integer()
  def budget(counts, rates, participant) do
    operations()
    |> Enum.filter(&(owner(&1) == participant))
    |> Enum.reduce(0, fn op, acc -> acc + counts[op] * rates[op] end)
  end

  defp rates(rates) when is_map(rates) and not is_struct(rates) do
    expected = operations() -- [:handle_request]

    if Enum.sort(Map.keys(rates)) == Enum.sort(expected) and
         Enum.all?(expected, &rate?(rates[&1], owner(&1))),
       do: :ok,
       else: {:error, :invalid_rpc_cost_rates}
  end

  defp rates(_rates), do: {:error, :invalid_rpc_cost_rates}

  defp rate?(%{cost_unit: unit, upper_bound: n} = r, owner),
    do: map_size(r) == 2 and unit == unit(owner) and natural?(n)

  defp rate?(_rate, _owner), do: false
  defp unit(:client), do: :client_work
  defp unit(:server), do: :server_work
  defp natural?(n), do: is_integer(n) and n >= 0
end
