ExUnit.start()

defmodule ReductionBounds.TestFixtures do
  [{module, beam}] = Code.compile_file(Path.expand("fixtures/bounded_counter.ex", __DIR__))
  @bounded_counter {module, beam}

  def bounded_counter, do: @bounded_counter
end
