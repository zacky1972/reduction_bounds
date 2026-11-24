defmodule ReductionBounds.Benchmark.TestFormatter do
  @moduledoc false
  use GenServer

  @impl true
  def init(_opts), do: {:ok, System.fetch_env!("REDUCTION_BOUNDS_BENCH_EVENTS")}

  @impl true
  def handle_cast({:test_finished, test}, state) do
    ReductionBounds.Profile.emit_to(state, %{
      event: :test_finished,
      module: inspect(test.module),
      test: Atom.to_string(test.name),
      file: test.tags[:file],
      line: test.tags[:line],
      async: test.tags[:async] == true,
      wall_ms: test.time / 1000,
      state: inspect(test.state)
    })

    {:noreply, state}
  end

  def handle_cast({:suite_finished, times}, state) do
    ReductionBounds.Profile.emit_to(state, %{event: :suite_finished, times_us: times})
    {:noreply, state}
  end

  def handle_cast(_event, state), do: {:noreply, state}
end
