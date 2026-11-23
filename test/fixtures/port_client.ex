defmodule ReductionBounds.Fixtures.PortHelpers do
  @moduledoc false
  @compile :debug_info

  def prepare(payload), do: payload

  def await_reply(port) do
    receive do
      {^port, {:data, payload}} -> {:data, payload}
      {^port, :closed} -> :closed
    after
      1_000 -> :timeout
    end
  end

  def decode(payload), do: payload
end

defmodule ReductionBounds.Fixtures.PortClient do
  @moduledoc false
  @compile :debug_info

  alias ReductionBounds.Fixtures.PortHelpers, as: Helpers

  def request(port, input) do
    prepared = Helpers.prepare(input)

    case :erlang.port_command(port, prepared, [:nosuspend]) do
      true ->
        case Helpers.await_reply(port) do
          {:data, data} -> Helpers.decode(data)
          :closed -> :closed
          :timeout -> :timeout
        end

      false ->
        :rejected
    end
  end

  def reordered(port, input) do
    prepared = Helpers.prepare(input)

    case :erlang.port_command(port, prepared, [:nosuspend]) do
      false ->
        :rejected

      true ->
        case Helpers.await_reply(port) do
          :timeout -> :timeout
          :closed -> :closed
          {:data, data} -> Helpers.decode(data)
        end
    end
  end

  def wrong_port(port, input) do
    prepared = Helpers.prepare(input)

    case :erlang.port_command(port, prepared, [:nosuspend]) do
      true ->
        case Helpers.await_reply(input) do
          {:data, data} -> Helpers.decode(data)
          :closed -> :closed
          :timeout -> :timeout
        end

      false ->
        :rejected
    end
  end

  def blocking(port, input) do
    prepared = Helpers.prepare(input)

    case :erlang.port_command(port, prepared) do
      true -> Helpers.decode(input)
      false -> :rejected
    end
  end

  def native_receive(port, _input) do
    receive do
      {^port, data} -> data
    end
  end
end
