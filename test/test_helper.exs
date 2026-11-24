ExUnit.start()

defmodule ReductionBounds.TestFixtures do
  [{module, beam}] = Code.compile_file(Path.expand("fixtures/bounded_counter.ex", __DIR__))
  @bounded_counter {module, beam}

  @port_modules Code.compile_file(Path.expand("fixtures/port_client.ex", __DIR__))
  @port_beams Enum.map(@port_modules, &elem(&1, 1))

  def bounded_counter, do: @bounded_counter
  def port_client_beams, do: @port_beams
end

if System.get_env("REDUCTION_BOUNDS_BENCH_EVENTS") do
  ExUnit.configure(
    formatters:
      Enum.uniq(ExUnit.configuration()[:formatters] ++ [ReductionBounds.Benchmark.TestFormatter])
  )
end
