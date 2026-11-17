defmodule ReductionBounds.IntegerSize do
  @moduledoc """
  Holds an integer's inclusive value range and magnitude bit-length bound.

  The lower and upper bounds describe the same integer as the magnitude
  bit-length bound. A finite lower bound `lower` means `lower <= value`,
  and a finite upper bound `upper` means `value <= upper`.

  A magnitude bit-length bound `bits` means `abs(value) < 2^bits`. It
  measures the magnitude independently of the sign, so a bound of zero
  describes only the integer zero. For example, values from -8 through 7
  have a magnitude bit-length bound of 4.

  Each field can be supplied independently. The default value represents
  any integer, with both endpoints unbounded and its magnitude bit-length
  bound unknown.

  ## Examples

      iex> alias ReductionBounds.IntegerSize
      iex> size = %IntegerSize{lower: -8, upper: 7, magnitude_bits: 4}
      iex> {size.lower, size.upper, size.magnitude_bits}
      {-8, 7, 4}

      iex> alias ReductionBounds.IntegerSize
      iex> size = %IntegerSize{lower: 0}
      iex> {size.lower, size.upper, size.magnitude_bits}
      {0, :unbounded, :unknown}
  """

  @typedoc "An inclusive integer endpoint, or an absent bound."
  @type bound :: integer() | :unbounded

  @typedoc "An upper bound on magnitude bit length, or unknown information."
  @type magnitude_bits :: non_neg_integer() | :unknown

  @typedoc "Value-range and magnitude bit-length information for an integer."
  @type t :: %__MODULE__{
          lower: bound(),
          upper: bound(),
          magnitude_bits: magnitude_bits()
        }

  defstruct lower: :unbounded, upper: :unbounded, magnitude_bits: :unknown
end
