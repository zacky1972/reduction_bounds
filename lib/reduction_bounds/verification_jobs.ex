defmodule ReductionBounds.VerificationJobs do
  @moduledoc false
  use GenServer

  @spec configured_limit() :: pos_integer()
  def configured_limit() do
    value =
      System.get_env("REDUCTION_BOUNDS_LEAN_JOBS") ||
        Application.get_env(:reduction_bounds, :lean_jobs, 2)

    case value do
      n when is_integer(n) and n > 0 ->
        n

      text when is_binary(text) ->
        case Integer.parse(text) do
          {n, ""} when n > 0 -> n
          _ -> raise ArgumentError, "Lean job limit must be a positive integer"
        end

      _ ->
        raise ArgumentError, "Lean job limit must be a positive integer"
    end
  end

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts) do
    limit = Keyword.get_lazy(opts, :limit, &configured_limit/0)
    unless is_integer(limit) and limit > 0, do: raise(ArgumentError, "invalid Lean job limit")
    name = Keyword.get(opts, :name, __MODULE__)
    GenServer.start_link(__MODULE__, limit, if(name, do: [name: name], else: []))
  end

  @spec run((-> term()) | (map() -> term()), GenServer.server()) :: {term(), map()}
  def run(fun, server \\ __MODULE__)
  def run(fun, server) when is_function(fun, 0), do: run(fn _metadata -> fun.() end, server)

  def run(fun, server) when is_function(fun, 1) do
    if server == __MODULE__, do: Application.ensure_all_started(:reduction_bounds)
    started = System.monotonic_time(:microsecond)
    coordinator = GenServer.whereis(server)
    {lease, active, limit} = GenServer.call(coordinator, :checkout, :infinity)
    acquired = System.monotonic_time(:microsecond)
    metadata = %{queue_ms: (acquired - started) / 1000, active_at_start: active, limit: limit}

    running = System.monotonic_time(:microsecond)

    try do
      result = invoke(fun, metadata, coordinator, lease)
      elapsed = (System.monotonic_time(:microsecond) - running) / 1000
      {result, Map.put(metadata, :runner_call_wall_ms, elapsed)}
    after
      release(coordinator, lease)
    end
  end

  defp invoke(fun, metadata, coordinator, lease) do
    task =
      Task.Supervisor.async_nolink(ReductionBounds.VerificationWorkers, fn ->
        worker = self()
        spawn(fn -> watch(coordinator, worker) end)

        case GenServer.call(coordinator, {:attach, lease, worker}, :infinity) do
          :ok ->
            try do
              {:returned, fun.(metadata)}
            catch
              kind, reason -> {:raised, kind, reason, __STACKTRACE__}
            end

          :cancelled ->
            {:cancelled}
        end
      end)

    case Task.await(task, :infinity) do
      {:returned, result} -> result
      {:raised, kind, reason, stack} -> :erlang.raise(kind, reason, stack)
      {:cancelled} -> exit(:shutdown)
    end
  end

  defp watch(coordinator, worker) do
    coordinator_ref = Process.monitor(coordinator)
    worker_ref = Process.monitor(worker)

    receive do
      {:DOWN, ^coordinator_ref, :process, _, _} -> Process.exit(worker, :kill)
      {:DOWN, ^worker_ref, :process, _, _} -> :ok
    end
  end

  defp release(server, lease) do
    GenServer.call(server, {:release, lease})
  catch
    :exit, _reason -> :ok
  end

  @spec stats(GenServer.server()) :: map()
  def stats(server \\ __MODULE__), do: GenServer.call(server, :stats)

  @impl true
  def init(limit), do: {:ok, %{limit: limit, active: %{}, waiting: :queue.new(), peak: 0}}

  @impl true
  def handle_call(:checkout, from, state) do
    monitor = Process.monitor(elem(from, 0))
    entry = {from, monitor}

    if map_size(state.active) < state.limit do
      {reply, state} = grant(entry, state)
      {:reply, reply, state}
    else
      {:noreply, %{state | waiting: :queue.in(entry, state.waiting)}}
    end
  end

  def handle_call({:attach, lease, worker}, {worker, _}, state) do
    case state.active[lease] do
      %{worker: nil, from: {owner, _}} = entry ->
        if Process.alive?(owner) do
          entry = %{entry | worker: worker, worker_monitor: Process.monitor(worker)}
          {:reply, :ok, put_in(state.active[lease], entry)}
        else
          Process.demonitor(entry.owner_monitor, [:flush])
          {:reply, :cancelled, state |> Map.update!(:active, &Map.delete(&1, lease)) |> wake()}
        end

      _ ->
        {:reply, :cancelled, state}
    end
  end

  def handle_call({:release, lease}, {pid, _} = from, state) do
    case state.active[lease] do
      %{from: {^pid, _}, worker: nil} = entry ->
        Process.demonitor(entry.owner_monitor, [:flush])
        {:reply, :ok, state |> Map.update!(:active, &Map.delete(&1, lease)) |> wake()}

      %{from: {^pid, _}} = entry ->
        # Keep the slot until the supervised worker has actually terminated.
        {:noreply, put_in(state.active[lease], %{entry | releaser: from})}

      _ ->
        {:reply, :ok, state}
    end
  end

  def handle_call(:stats, _from, state) do
    {:reply,
     %{
       limit: state.limit,
       active: map_size(state.active),
       queued: :queue.len(state.waiting),
       peak: state.peak
     }, state}
  end

  @impl true
  def handle_info({:DOWN, monitor, :process, _pid, _reason}, state) do
    case Enum.find(state.active, fn {_lease, entry} ->
           entry.owner_monitor == monitor or entry.worker_monitor == monitor
         end) do
      {lease, %{worker_monitor: ^monitor} = entry} ->
        Process.demonitor(entry.owner_monitor, [:flush])
        if entry.releaser, do: GenServer.reply(entry.releaser, :ok)
        {:noreply, state |> Map.update!(:active, &Map.delete(&1, lease)) |> wake()}

      {lease, %{worker: nil}} ->
        {:noreply, state |> Map.update!(:active, &Map.delete(&1, lease)) |> wake()}

      {_lease, %{worker: worker}} ->
        Process.exit(worker, :kill)
        {:noreply, state}

      nil ->
        waiting = :queue.filter(fn {_from, ref} -> ref != monitor end, state.waiting)
        {:noreply, %{state | waiting: waiting}}
    end
  end

  defp grant({from, monitor}, state) do
    lease = make_ref()

    active =
      Map.put(state.active, lease, %{
        from: from,
        owner_monitor: monitor,
        worker: nil,
        worker_monitor: nil,
        releaser: nil
      })

    count = map_size(active)
    {{lease, count, state.limit}, %{state | active: active, peak: max(state.peak, count)}}
  end

  defp wake(state) when map_size(state.active) >= state.limit, do: state

  defp wake(state) do
    case :queue.out(state.waiting) do
      {:empty, _} ->
        state

      {{:value, {from, monitor} = entry}, rest} ->
        state = %{state | waiting: rest}

        if Process.alive?(elem(from, 0)) do
          {reply, state} = grant(entry, state)
          GenServer.reply(from, reply)
          wake(state)
        else
          Process.demonitor(monitor, [:flush])
          wake(state)
        end
    end
  end
end
