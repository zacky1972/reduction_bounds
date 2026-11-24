defmodule ReductionBounds.MailboxSupport do
  alias ReductionBounds.{Mailbox, RpcConditions, RpcProtocol, RpcTerm}
  def cap, do: %RpcTerm.Size{nodes: 100, bytes: 32, integer_bits: 256}
  def limits, do: Map.new(Mailbox.counters(), &{&1, 100})
  def request, do: {:tuple3, {:atom, "request"}, {:ref, 7}, {:integer, 5}}
  def reply(n \\ 9), do: {:tuple3, {:atom, "reply"}, {:ref, 7}, {:integer, n}}

  def profile(options \\ []) do
    {:ok, session} = RpcProtocol.new(7, monitor_id: Keyword.get(options, :monitor_id))
    options = Keyword.delete(options, :monitor_id)

    defaults = [
      request_size: cap(),
      response_size: cap(),
      message_size: cap(),
      limits: limits(),
      protocol_limits: %{
        events: 100,
        client_sends: 1,
        server_sends: 1,
        response_handlers: 1,
        retries: 0
      },
      timeout: 0
    ]

    {:ok, profile} = RpcConditions.new(session, request(), Keyword.merge(defaults, options))
    profile
  end

  def spec(options \\ []) do
    p = profile()
    {:ok, spec} = Mailbox.new(Keyword.merge(Map.to_list(p.mailbox), options))
    spec
  end

  def sent, do: [{:protocol, :prepare}, {:protocol, :send_request}, :begin_receive]

  def server,
    do:
      Enum.map(
        [:request_arrived, :receive_request, :handle_request, :send_reply],
        &{:protocol, &1}
      )

  def success,
    do: sent() ++ server() ++ [{:arrive, reply()}, :inspect, {:protocol, :process_reply}]
end
