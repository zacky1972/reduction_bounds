defmodule ReductionBounds.ProofPreparation do
  @moduledoc false
  use GenServer

  alias ReductionBounds.ProofCache

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts), do: GenServer.start_link(__MODULE__, opts, name: __MODULE__)

  @spec run([map()], String.t(), (-> [map()])) :: {[map()], map()}
  def run(files, project, verify) do
    started = System.monotonic_time(:microsecond)

    shared =
      for %{"module" => name, "cache_key" => key} <- files,
          String.starts_with?(name, "ReductionBounds.Proofs."),
          do: {name, key}

    if shared == [] do
      {verify.(), %{mode: :bypassed, wall_ms: 0.0}}
    else
      context = ProofCache.preparation_context(project)
      keys = Map.new(shared, fn {name, key} -> {name, {context, key}} end)
      coordinated(keys, verify, started)
    end
  end

  @spec coordinate(map(), (-> [map()])) :: [map()]
  def coordinate(keys, verify) do
    {reports, _coordination} = coordinated(keys, verify, System.monotonic_time(:microsecond))
    reports
  end

  defp coordinated(keys, verify, started) do
    {:ok, _apps} = Application.ensure_all_started(:reduction_bounds)

    acquired = GenServer.call(__MODULE__, {:acquire, Map.values(keys)}, :infinity)
    elapsed = (System.monotonic_time(:microsecond) - started) / 1000

    case acquired do
      :ready -> {reused(keys, verify), %{mode: :ready, wall_ms: elapsed}}
      {:owner, lease} -> {owned(lease, keys, verify), %{mode: :owner, wall_ms: elapsed}}
    end
  end

  defp owned(lease, keys, verify) do
    reports = verify.()
    {ready, failed} = classify(keys, reports)
    finish({:complete, lease, ready, failed})
    reports
  catch
    kind, reason ->
      finish({:complete, lease, [], Map.values(keys)})
      :erlang.raise(kind, reason, __STACKTRACE__)
  end

  defp reused(keys, verify) do
    reports = verify.()
    {_ready, failed} = classify(keys, reports)
    unless failed == [], do: finish({:invalidate, failed})
    reports
  catch
    kind, reason ->
      finish({:invalidate, Map.values(keys)})
      :erlang.raise(kind, reason, __STACKTRACE__)
  end

  defp classify(keys, reports) do
    ready = for %{module: name, status: :ok} <- reports, Map.has_key?(keys, name), do: keys[name]
    {ready, Map.values(keys) -- ready}
  end

  defp finish(message) do
    GenServer.call(__MODULE__, message)
  catch
    # Losing advisory readiness must not change an already checked proof result.
    :exit, _reason -> :ok
  end

  @impl true
  def init(_opts), do: {:ok, %{ready: MapSet.new(), owners: %{}, held: %{}, waiters: []}}

  @impl true
  def handle_call({:acquire, keys}, from, state) do
    case acquire(keys, from, state) do
      {:granted, reply, state} ->
        {:reply, reply, state}

      :blocked ->
        monitor = Process.monitor(elem(from, 0))
        {:noreply, %{state | waiters: state.waiters ++ [{from, keys, monitor}]}}
    end
  end

  def handle_call({:invalidate, keys}, _from, state) do
    {:reply, :ok, %{state | ready: MapSet.difference(state.ready, MapSet.new(keys))}}
  end

  def handle_call({:complete, lease, ready, failed}, {pid, _tag}, state) do
    case Map.get(state.owners, lease) do
      %{pid: ^pid, keys: owned} ->
        ready = MapSet.intersection(owned, MapSet.new(ready))
        retained = MapSet.difference(state.ready, MapSet.new(failed))
        state = %{state | ready: MapSet.union(retained, ready)}
        {:reply, :ok, state |> release(lease) |> wake()}

      _ ->
        {:reply, :ok, state}
    end
  end

  @impl true
  def handle_info({:DOWN, monitor, :process, _pid, _reason}, state) do
    case Enum.find(state.owners, fn {_lease, owner} -> owner.monitor == monitor end) do
      {lease, _owner} -> {:noreply, state |> release(lease) |> wake()}
      nil -> {:noreply, %{state | waiters: Enum.reject(state.waiters, &(elem(&1, 2) == monitor))}}
    end
  end

  defp acquire(keys, from, state) do
    missing = keys |> MapSet.new() |> MapSet.difference(state.ready)

    cond do
      MapSet.size(missing) == 0 ->
        {:granted, :ready, state}

      Enum.any?(missing, &Map.has_key?(state.held, &1)) ->
        :blocked

      true ->
        lease = make_ref()
        pid = elem(from, 0)
        owner = %{pid: pid, monitor: Process.monitor(pid), keys: missing}
        held = Enum.reduce(missing, state.held, &Map.put(&2, &1, lease))

        {:granted, {:owner, lease},
         %{state | held: held, owners: Map.put(state.owners, lease, owner)}}
    end
  end

  defp release(state, lease) do
    {owner, owners} = Map.pop!(state.owners, lease)
    Process.demonitor(owner.monitor, [:flush])
    %{state | owners: owners, held: Map.drop(state.held, MapSet.to_list(owner.keys))}
  end

  defp wake(state) do
    Enum.reduce(state.waiters, %{state | waiters: []}, fn {from, keys, monitor} = waiter, state ->
      case acquire(keys, from, state) do
        :blocked ->
          %{state | waiters: state.waiters ++ [waiter]}

        {:granted, reply, state} ->
          Process.demonitor(monitor, [:flush])
          GenServer.reply(from, reply)
          state
      end
    end)
  end
end
