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

      sampler = Task.async(fn -> sample(pid, nil) end)
      status = collect(port, log)
      finished = System.monotonic_time(:millisecond)
      send(sampler.pid, :stop)
      peak = Task.await(sampler, 10_000)

      %{
        command: [executable | args],
        exit_status: status,
        wall_ms: finished - started,
        sampled_peak_tree_rss_bytes: peak,
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

  defp sample(pid, peak) do
    current = rss(pid)
    peak = if current, do: max(peak || 0, current), else: peak

    receive do
      :stop -> peak
    after
      100 -> sample(pid, peak)
    end
  end

  defp rss(nil), do: nil

  defp rss(pid) do
    case System.cmd("ps", ["-axo", "pid=,ppid=,rss="], stderr_to_stdout: true) do
      {output, 0} ->
        rows =
          for line <- String.split(output, "\n"),
              [id, parent, size] <- [String.split(line)],
              do:
                {String.to_integer(id), String.to_integer(parent), String.to_integer(size) * 1024}

        tree_rss(rows, pid)

      _ ->
        nil
    end
  rescue
    _error -> nil
  end

  defp tree_rss(rows, pid) do
    if Enum.any?(rows, fn {id, _, _} -> id == pid end) do
      pids = descendants(rows, MapSet.new([pid]))
      Enum.sum(for {id, _, bytes} <- rows, id in pids, do: bytes)
    end
  end

  defp descendants(rows, pids) do
    expanded =
      Enum.reduce(rows, pids, fn {id, parent, _}, acc ->
        if parent in acc, do: MapSet.put(acc, id), else: acc
      end)

    if expanded == pids, do: pids, else: descendants(rows, expanded)
  end
end
