defmodule ReductionBounds.Fixtures.IntegerCostCases do
  @moduledoc false
  @compile :debug_info

  # Integer arithmetic before the sample-variance division and square root.
  def variance_numerator(sum, sum_squares, count) do
    scaled_squares = count * sum_squares
    squared_sum = sum * sum
    scaled_squares - squared_sum
  end

  def variance_denominator(count), do: count * (count - 1)

  # Arithmetic kernels of a table-driven CRC with a 64-bit state.
  # The table lookup is outside these functions; its result is an input.
  def crc64_update(crc, table_entry) do
    shifted = Bitwise.bsl(crc, 8)
    mixed = Bitwise.bxor(shifted, table_entry)
    Bitwise.band(mixed, 0xFFFFFFFFFFFFFFFF)
  end

  def crc64_reflected_update(crc, table_entry) do
    shifted = Bitwise.bsr(crc, 8)
    mixed = Bitwise.bxor(shifted, table_entry)
    Bitwise.band(mixed, 0xFFFFFFFFFFFFFFFF)
  end

  def crc64_index(crc, byte) do
    high = Bitwise.bsr(crc, 56)
    mixed = Bitwise.bxor(high, byte)
    Bitwise.band(mixed, 255) + 1
  end

  def crc64_reflected_index(crc, byte) do
    mixed = Bitwise.bxor(crc, byte)
    Bitwise.band(mixed, 255) + 1
  end
end
