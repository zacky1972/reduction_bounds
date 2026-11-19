defmodule ReductionBounds.Fixtures.IntegerPrograms do
  @moduledoc false
  @compile :debug_info

  def conditional(x) do
    y = x * 3
    if y < 0, do: y - 1, else: y + 1
  end

  def crc_step(x), do: Bitwise.band(Bitwise.bxor(Bitwise.bsl(x, 8), 7), 255)
  def right(x), do: Bitwise.bsr(x, 3)
  def impossible(x), do: if(x < 0, do: x - 100, else: x + 1)

  def rebinding(x) do
    x = if x < 0, do: 1, else: 2
    if x < 0, do: -100, else: x + 1
  end

  def reversed(x), do: if(0 < x, do: -x, else: x * 2)
  def expression_test(x), do: if(x + 1 > 0, do: x, else: 0)
  def pair(x, y), do: x + y
  def no_args(), do: 42
  def constant(_x), do: 1
  def unsupported(x), do: abs(x)
  def dynamic_shift(x, amount), do: Bitwise.bsl(x, amount)
  def unsupported_mask(x), do: Bitwise.band(x, 10)
  def recursive(x), do: recursive(x - 1)
end
