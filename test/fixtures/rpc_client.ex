defmodule ReductionBounds.Fixtures.RpcHelpers do
  @moduledoc false
  @compile :debug_info

  def await_reply(_server, token, timeout) do
    receive do
      {:reply, ^token, data} -> {:reply, data}
    after
      timeout -> :timeout
    end
  end

  def decode(data), do: data
  def prepare(token, input), do: {:request, token, input}
end

defmodule ReductionBounds.Fixtures.RpcClient do
  @moduledoc false
  @compile :debug_info
  alias ReductionBounds.Fixtures.RpcHelpers, as: Helpers

  def request(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def reordered(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      :timeout -> :timeout
      {:reply, data} -> Helpers.decode(data)
    end
  end

  def zero_timeout(server, token, input, _timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, 0) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def infinity_timeout(server, token, input, _timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, :infinity) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def wrong_token(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, input, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def wrong_request(server, token, input, timeout) do
    request = {:request, input, token}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def wrong_server(server, token, input, timeout) do
    request = {:request, token, input}
    send(input, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def wrong_decode(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, _data} -> Helpers.decode(input)
      :timeout -> :timeout
    end
  end

  def wrong_timeout(server, token, input, _timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, 1) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def wrong_return(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :ok
    end
  end

  def repeated_send(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def guarded(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} when is_integer(data) -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def dynamic(server, token, input, timeout) do
    request = {:request, token, input}
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> input.(data)
      :timeout -> :timeout
    end
  end

  def native_receive(server, token, input, timeout) do
    send(server, {:request, token, input})

    receive do
      {:reply, ^token, data} -> data
    after
      timeout -> :timeout
    end
  end

  def helper_preparation(server, token, input, timeout) do
    request = Helpers.prepare(token, input)
    send(server, request)

    case Helpers.await_reply(server, token, timeout) do
      {:reply, data} -> Helpers.decode(data)
      :timeout -> :timeout
    end
  end

  def recursive(server, token, input, timeout), do: recursive(server, token, input, timeout)

  def exception(server, token, input, timeout) do
    try do
      request(server, token, input, timeout)
    catch
      _ -> :timeout
    end
  end
end
