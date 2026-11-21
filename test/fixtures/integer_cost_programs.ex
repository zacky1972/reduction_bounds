defmodule ReductionBounds.Fixtures.IntegerCostPrograms do
  @moduledoc false
  @compile :debug_info

  def product(x) do
    squared = x * x
    squared + 1
  end

  def crc_step(x), do: Bitwise.band(Bitwise.bxor(Bitwise.bsl(x, 8), 7), 255)
  def helper(x), do: x * 3
  def local_caller(x), do: helper(x) + 1
  def caller(x), do: __MODULE__.helper(x) + 1
  def grandcaller(x), do: __MODULE__.caller(x) * 2
  def two_calls(x), do: :erlang.abs(__MODULE__.helper(x))
  def opaque(x), do: :erlang.abs(x)
  def guarded(x), do: if(x < 0, do: -x, else: x + 1)

  def sum(counter, accumulator) do
    if counter > 0 do
      sum(counter - 1, accumulator + counter)
    else
      accumulator
    end
  end

  def crc_loop(counter, accumulator) do
    if counter > 0 do
      next = Bitwise.band(Bitwise.bxor(Bitwise.bsl(accumulator, 1), counter), 255)
      crc_loop(counter - 1, next)
    else
      accumulator
    end
  end

  def forever(counter, accumulator), do: forever(counter, accumulator)
end
