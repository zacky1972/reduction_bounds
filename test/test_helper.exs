ExUnit.start()

defmodule ReductionBounds.TestFixtures do
  [{module, beam}] = Code.compile_file(Path.expand("fixtures/bounded_counter.ex", __DIR__))
  @bounded_counter {module, beam}

  @port_modules Code.compile_file(Path.expand("fixtures/port_client.ex", __DIR__))
  @port_beams Enum.map(@port_modules, &elem(&1, 1))

  @integer_programs Code.compile_file(Path.expand("fixtures/integer_programs.ex", __DIR__))
  @integer_cost_programs Code.compile_file(
                           Path.expand("fixtures/integer_cost_programs.ex", __DIR__)
                         )
  @integer_cost_cases Code.compile_file(Path.expand("fixtures/integer_cost_cases.ex", __DIR__))

  def integer_programs, do: hd(@integer_programs)
  def integer_cost_programs, do: hd(@integer_cost_programs)
  def integer_cost_cases, do: hd(@integer_cost_cases)

  def integer_cost_beams,
    do: Enum.map(@integer_cost_programs ++ @integer_cost_cases, &elem(&1, 1))

  def label_scenario(%{module: module, test: test, program: program}) do
    Process.set_label({module, test, %{program: program}})
    :ok
  end

  def bounded_counter, do: @bounded_counter
  def port_client_beams, do: @port_beams
end

if System.get_env("REDUCTION_BOUNDS_BENCH_EVENTS") do
  ExUnit.configure(
    formatters:
      Enum.uniq(ExUnit.configuration()[:formatters] ++ [ReductionBounds.Benchmark.TestFormatter])
  )
end
