# cspell:words ppid
defmodule ReductionBounds.Benchmark.Command do
  @moduledoc false

  @spec run(String.t(), [String.t()], [{String.t(), String.t()}], String.t()) :: map()
  def run(executable, args, env, log_path) do
    executable = System.find_executable(executable) || raise "missing executable: #{executable}"
    started = System.monotonic_time(:millisecond)
    {:ok, log} = File.open(log_path, [:write, :binary])

    try do
      port =
        Port.open({:spawn_executable, executable}, [
          :binary,
          :exit_status,
          :use_stdio,
          :stderr_to_stdout,
          args: args,
          env: Enum.map(env, fn {key, value} -> {to_charlist(key), to_charlist(value)} end)
        ])

      pid =
        case Port.info(port, :os_pid) do
          {:os_pid, pid} -> pid
          nil -> nil
        end

      sampler = Task.async(fn -> sample(pid, %{peak: nil, cpu: %{}, available: false}) end)
      status = collect(port, log)
      finished = System.monotonic_time(:millisecond)
      send(sampler.pid, :stop)
      samples = Task.await(sampler, 10_000)
      cpu = if samples.available, do: Enum.sum(Map.values(samples.cpu))

      %{
        command: [executable | args],
        exit_status: status,
        wall_ms: finished - started,
        sampled_peak_tree_rss_bytes: samples.peak,
        sampled_tree_cpu_ms: cpu,
        sampled_tree_cpu_percent: if(cpu, do: cpu / max(finished - started, 1) * 100),
        memory_sampling_interval_ms: 100,
        log: log_path
      }
    after
      File.close(log)
    end
  end

  defp collect(port, log) do
    receive do
      {^port, {:data, bytes}} ->
        IO.binwrite(log, bytes)
        collect(port, log)

      {^port, {:exit_status, status}} ->
        status
    end
  end

  defp sample(pid, state) do
    state =
      case snapshot(pid) do
        nil ->
          state

        rows ->
          peak = max(state.peak || 0, Enum.sum(for {_, _, bytes, _} <- rows, do: bytes))

          cpu =
            Enum.reduce(rows, state.cpu, fn {id, _, _, ms}, acc ->
              Map.update(acc, id, ms, &max(&1, ms))
            end)

          %{peak: peak, cpu: cpu, available: true}
      end

    receive do
      :stop -> state
    after
      100 -> sample(pid, state)
    end
  end

  defp snapshot(nil), do: nil

  defp snapshot(pid) do
    case System.cmd("ps", ["-axo", "pid=,ppid=,rss=,time="], stderr_to_stdout: true) do
      {output, 0} ->
        rows =
          for line <- String.split(output, "\n"),
              [id, parent, size, time] <- [String.split(line)],
              do:
                {String.to_integer(id), String.to_integer(parent), String.to_integer(size) * 1024,
                 cpu_ms(time)}

        tree_rows(rows, pid)

      _ ->
        nil
    end
  rescue
    _error -> nil
  end

  defp tree_rows(rows, pid) do
    if Enum.any?(rows, fn {id, _, _, _} -> id == pid end) do
      pids = descendants(rows, MapSet.new([pid]))
      Enum.filter(rows, fn {id, _, _, _} -> id in pids end)
    end
  end

  @spec cpu_ms(String.t()) :: non_neg_integer()
  def cpu_ms(time) do
    {days, clock} =
      case String.split(time, "-") do
        [clock] -> {0, clock}
        [days, clock] -> {String.to_integer(days), clock}
      end

    parts = String.split(clock, ":")

    {hours, minutes, seconds} =
      case parts do
        [h, m, s] -> {String.to_integer(h), String.to_integer(m), s}
        [m, s] -> {0, String.to_integer(m), s}
      end

    {seconds, ""} = Float.parse(seconds)
    round(((days * 24 + hours) * 3600 + minutes * 60 + seconds) * 1000)
  end

  defp descendants(rows, pids) do
    expanded =
      Enum.reduce(rows, pids, fn {id, parent, _, _}, acc ->
        if parent in acc, do: MapSet.put(acc, id), else: acc
      end)

    if expanded == pids, do: pids, else: descendants(rows, expanded)
  end
end
