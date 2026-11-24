defmodule ReductionBounds.Profile do
  @moduledoc false

  @spec measure(atom(), String.t(), (-> term())) :: term()
  def measure(stage, label, fun) do
    if path = System.get_env("REDUCTION_BOUNDS_BENCH_EVENTS") do
      started = System.monotonic_time(:microsecond)

      try do
        fun.()
      after
        emit_to(path, %{
          event: :phase,
          stage: stage,
          label: label,
          wall_ms: (System.monotonic_time(:microsecond) - started) / 1000
        })
      end
    else
      fun.()
    end
  end

  @spec emit(map()) :: :ok
  def emit(event) do
    if path = System.get_env("REDUCTION_BOUNDS_BENCH_EVENTS"), do: emit_to(path, event), else: :ok
  end

  @spec emit_to(String.t(), map()) :: :ok
  def emit_to(path, event) do
    event =
      Map.merge(event, %{
        os_pid: System.pid(),
        schema_version: 2,
        process: inspect(self()),
        context: test_context(),
        monotonic_us: System.monotonic_time(:microsecond)
      })

    :global.trans({{__MODULE__, path}, self()}, fn ->
      File.write(path, [JSON.encode!(event), "\n"], [:append])
    end)

    :ok
  rescue
    _error -> :ok
  end

  defp test_context() do
    [self() | Process.get(:"$callers", [])] |> Enum.find_value(&label_context/1)
  end

  defp label_context(pid), do: label_context_for(Process.get_label(pid))

  defp label_context_for({module, test}) when is_atom(module) and is_atom(test),
    do: base_context(module, test)

  defp label_context_for({module, test, parameters}) when is_atom(module) and is_atom(test) do
    if context = base_context(module, test),
      do: Map.put(context, :parameters, inspect(parameters))
  end

  defp label_context_for(_label), do: nil

  defp base_context(module, test) do
    if function_exported?(module, :__ex_unit__, 0),
      do: %{module: inspect(module), test: Atom.to_string(test)}
  end
end
