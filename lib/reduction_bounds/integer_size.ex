defmodule ReductionBounds.IntegerSize do
  @moduledoc """
  Represents integer size information, including an unreachable state.

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

  The mathematical meaning is the set of integers satisfying all supplied
  constraints simultaneously. Contradictory constraints denote the empty
  set. `valid?/1` checks field types, and `contains?/2` tests membership.
  These definitions use mathematical integers and do not assume any
  particular runtime representation.

  `unknown/0` returns the default struct, which admits every integer.
  `unreachable/0` returns `:unreachable`, which admits no integer.
  `normalize/1` converts contradictory constraints to `:unreachable`
  and preserves every satisfiable struct unchanged. Unknown information
  must not be used to represent an impossible branch. This domain does
  not by itself establish whether a program branch can execute.

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

  @typedoc "Value-range and magnitude constraints before normalization."
  @type constraints :: %__MODULE__{
          lower: bound(),
          upper: bound(),
          magnitude_bits: magnitude_bits()
        }

  @typedoc "Integer constraints, or an explicit state admitting no integer."
  @type t :: constraints() | :unreachable

  defstruct lower: :unbounded, upper: :unbounded, magnitude_bits: :unknown

  @doc """
  Returns unconstrained information, which admits every integer.

      iex> ReductionBounds.IntegerSize.unknown()
      %ReductionBounds.IntegerSize{}
  """
  @spec unknown() :: constraints()
  def unknown(), do: %__MODULE__{}

  @doc """
  Returns the state admitting no integer.

      iex> ReductionBounds.IntegerSize.unreachable()
      :unreachable
  """
  @spec unreachable() :: :unreachable
  def unreachable(), do: :unreachable

  @doc """
  Converts constraints admitting no integer to `:unreachable`.

  All satisfiable structs are returned unchanged. The check tests the
  interval's point nearest zero against all constraints. If any integer
  satisfies them, that point does too. No enumeration is required.

  Raises `ArgumentError` for malformed information.

      iex> alias ReductionBounds.IntegerSize
      iex> IntegerSize.normalize(IntegerSize.unknown())
      %IntegerSize{}
      iex> IntegerSize.normalize(%IntegerSize{lower: 8, magnitude_bits: 3})
      :unreachable
      iex> IntegerSize.normalize(%IntegerSize{lower: 0, magnitude_bits: 0})
      %IntegerSize{lower: 0, magnitude_bits: 0}
  """
  @spec normalize(t()) :: t()
  def normalize(:unreachable), do: :unreachable

  def normalize(%__MODULE__{} = size) do
    ensure_valid!(size)
    if contains?(size, witness(size)), do: size, else: :unreachable
  end

  def normalize(_size), do: raise(ArgumentError, "invalid integer size information")

  @doc """
  Returns whether the information admits no integer.

  This checks both the explicit state and contradictory constraints.
  Unknown information returns false. Program reachability requires
  separate evidence connecting these constraints to a program state.

      iex> alias ReductionBounds.IntegerSize
      iex> IntegerSize.unreachable?(IntegerSize.unknown())
      false
      iex> IntegerSize.unreachable?(%IntegerSize{lower: 2, upper: 1})
      true
  """
  @spec unreachable?(t()) :: boolean()
  def unreachable?(size), do: normalize(size) == :unreachable

  @doc """
  Returns whether the information has a valid representation.

  This checks the representation, not whether its constraints admit an
  integer. The explicit `:unreachable` state is valid. For example,
  `lower: 2, upper: 1` is a valid representation of the empty set.
  """
  @spec valid?(term()) :: boolean()
  def valid?(:unreachable), do: true

  def valid?(%__MODULE__{lower: lower, upper: upper, magnitude_bits: bits}) do
    valid_bound?(lower) and valid_bound?(upper) and valid_bits?(bits)
  end

  def valid?(_size), do: false

  @doc """
  Returns whether an integer satisfies all supplied constraints.

  Endpoints are inclusive; the magnitude limit is strict. Unspecified
  fields impose no constraint. Contradictory constraints represent the
  empty set and never contain a value. The explicit `:unreachable`
  state also returns false for every integer.

  Raises `ArgumentError` for a malformed representation or a non-integer
  value. This function does not infer or normalize bounds.

  ## Examples

      iex> alias ReductionBounds.IntegerSize
      iex> size = %IntegerSize{lower: -8, upper: 7, magnitude_bits: 3}
      iex> Enum.map([-8, -7, 0, 7, 8], &IntegerSize.contains?(size, &1))
      [false, true, true, true, false]

      iex> ReductionBounds.IntegerSize.contains?(%ReductionBounds.IntegerSize{}, -123)
      true
  """
  @spec contains?(t(), integer()) :: boolean()
  def contains?(:unreachable, value) when is_integer(value), do: false

  def contains?(%__MODULE__{} = size, value) when is_integer(value) do
    ensure_valid!(size)

    above_lower?(size.lower, value) and below_upper?(size.upper, value) and
      within_bits?(size.magnitude_bits, value)
  end

  def contains?(_size, _value) do
    raise ArgumentError, "expected integer size information and an integer value"
  end

  defp ensure_valid!(size) do
    unless valid?(size), do: raise(ArgumentError, "invalid integer size information")
  end

  defp witness(%__MODULE__{lower: :unbounded, upper: :unbounded}), do: 0
  defp witness(%__MODULE__{lower: :unbounded, upper: upper}), do: min(0, upper)
  defp witness(%__MODULE__{lower: lower, upper: :unbounded}), do: max(lower, 0)
  defp witness(%__MODULE__{lower: lower, upper: upper}), do: max(lower, min(0, upper))

  defp valid_bound?(:unbounded), do: true
  defp valid_bound?(value), do: is_integer(value)

  defp valid_bits?(:unknown), do: true
  defp valid_bits?(value), do: is_integer(value) and value >= 0

  defp above_lower?(:unbounded, _value), do: true
  defp above_lower?(lower, value), do: lower <= value

  defp below_upper?(:unbounded, _value), do: true
  defp below_upper?(upper, value), do: value <= upper

  defp within_bits?(:unknown, _value), do: true
  defp within_bits?(bits, value), do: abs(value) < Integer.pow(2, bits)
end
