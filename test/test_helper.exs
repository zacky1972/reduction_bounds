ExUnit.start()
Code.require_file("support/mailbox_support.ex", __DIR__)

defmodule ReductionBounds.TestFixtures do
  [{module, beam}] = Code.compile_file(Path.expand("fixtures/bounded_counter.ex", __DIR__))
  @bounded_counter {module, beam}

  @rpc_modules Code.compile_file(Path.expand("fixtures/rpc_client.ex", __DIR__))
  def rpc_client_beams(), do: Enum.map(@rpc_modules, &elem(&1, 1))

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

  def label_scenario(%{module: module, test: test, scenario: scenario}) do
    Process.set_label({module, test, %{scenario: scenario}})
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

Code.require_file("support/rpc_cost_support.ex", __DIR__)
