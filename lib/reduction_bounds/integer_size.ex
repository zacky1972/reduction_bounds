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

  `from_integer/1` describes a constant. `add/2`, `subtract/2`, and
  `multiply/2` propagate size information for independently chosen operand
  values. They validate and normalize both operands, propagate unreachable
  states, and return conservative descriptions of the results. They are
  reusable domain operations; automatic extraction from program expressions
  and size-dependent cost inference are subsequent work.

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

  @doc """
  Returns exact range and magnitude information for an integer constant.

      iex> ReductionBounds.IntegerSize.from_integer(-8)
      %ReductionBounds.IntegerSize{lower: -8, upper: -8, magnitude_bits: 4}
      iex> ReductionBounds.IntegerSize.from_integer(0)
      %ReductionBounds.IntegerSize{lower: 0, upper: 0, magnitude_bits: 0}
  """
  @spec from_integer(integer()) :: constraints()
  def from_integer(value) when is_integer(value) do
    bits = if value == 0, do: 0, else: length(Integer.digits(abs(value), 2))
    %__MODULE__{lower: value, upper: value, magnitude_bits: bits}
  end

  def from_integer(_value), do: raise(ArgumentError, "expected an integer constant")

  @doc """
  Bounds addition for every pair of values in the operand descriptions.

  Finite lower bounds are added, as are finite upper bounds. If both
  magnitude bounds are known, the result uses `max(left_bits, right_bits) + 1`.
  An unknown component stays unknown when the rule cannot bound it.
  An unreachable operand makes the result unreachable.

      iex> alias ReductionBounds.IntegerSize
      iex> IntegerSize.add(IntegerSize.from_integer(7), IntegerSize.from_integer(1))
      %IntegerSize{lower: 8, upper: 8, magnitude_bits: 4}
  """
  @spec add(t(), t()) :: t()
  def add(left, right), do: combine(left, right, &add_constraints/2)

  @doc """
  Bounds subtraction for every pair of values in the operand descriptions.

  The lower endpoint is `left.lower - right.upper`, and the upper endpoint
  is `left.upper - right.lower`, when the required endpoints are finite.
  Known magnitude bounds use `max(left_bits, right_bits) + 1`.
  Reusing the same description on both sides does not imply that the
  concrete operands are equal; this domain does not track correlations.

      iex> alias ReductionBounds.IntegerSize
      iex> IntegerSize.subtract(IntegerSize.from_integer(8), IntegerSize.from_integer(8))
      %IntegerSize{lower: 0, upper: 0, magnitude_bits: 5}
  """
  @spec subtract(t(), t()) :: t()
  def subtract(left, right), do: combine(left, right, &subtract_constraints/2)

  @doc """
  Bounds multiplication for every pair of values in the operand descriptions.

  When all endpoints are finite, the range uses the minimum and maximum
  of the four endpoint products. Otherwise both range endpoints are
  unbounded. Known magnitude bounds are added. A known zero operand
  yields exact zero unless an operand is unreachable.

  This rule is sound but may lose information for one-sided ranges.
  These functions do not assign costs or model a runtime integer format.

      iex> alias ReductionBounds.IntegerSize
      iex> IntegerSize.multiply(IntegerSize.from_integer(-8), IntegerSize.from_integer(2))
      %IntegerSize{lower: -16, upper: -16, magnitude_bits: 6}
  """
  @spec multiply(t(), t()) :: t()
  def multiply(left, right), do: combine(left, right, &multiply_constraints/2)

  defp combine(left, right, operation) do
    case {normalize(left), normalize(right)} do
      {:unreachable, _right} -> :unreachable
      {_left, :unreachable} -> :unreachable
      {left, right} -> normalize(operation.(left, right))
    end
  end

  defp add_constraints(left, right) do
    %__MODULE__{
      lower: add_endpoint(left.lower, right.lower),
      upper: add_endpoint(left.upper, right.upper),
      magnitude_bits: arithmetic_bits(left.magnitude_bits, right.magnitude_bits, :add)
    }
  end

  defp subtract_constraints(left, right) do
    %__MODULE__{
      lower: subtract_endpoint(left.lower, right.upper),
      upper: subtract_endpoint(left.upper, right.lower),
      magnitude_bits: arithmetic_bits(left.magnitude_bits, right.magnitude_bits, :add)
    }
  end

  defp multiply_constraints(left, right) do
    if zero?(left) or zero?(right) do
      from_integer(0)
    else
      {lower, upper} = product_range(left, right)

      %__MODULE__{
        lower: lower,
        upper: upper,
        magnitude_bits: arithmetic_bits(left.magnitude_bits, right.magnitude_bits, :multiply)
      }
    end
  end

  defp add_endpoint(:unbounded, _right), do: :unbounded
  defp add_endpoint(_left, :unbounded), do: :unbounded
  defp add_endpoint(left, right), do: left + right

  defp subtract_endpoint(:unbounded, _right), do: :unbounded
  defp subtract_endpoint(_left, :unbounded), do: :unbounded
  defp subtract_endpoint(left, right), do: left - right

  defp arithmetic_bits(:unknown, _right, _operation), do: :unknown
  defp arithmetic_bits(_left, :unknown, _operation), do: :unknown
  defp arithmetic_bits(left, right, :add), do: max(left, right) + 1
  defp arithmetic_bits(left, right, :multiply), do: left + right

  defp zero?(%__MODULE__{magnitude_bits: 0}), do: true
  defp zero?(%__MODULE__{lower: 0, upper: 0}), do: true
  defp zero?(_size), do: false

  defp product_range(
         %__MODULE__{lower: lower_left, upper: upper_left},
         %__MODULE__{lower: lower_right, upper: upper_right}
       )
       when is_integer(lower_left) and is_integer(upper_left) and
              is_integer(lower_right) and is_integer(upper_right) do
    products = [
      lower_left * lower_right,
      lower_left * upper_right,
      upper_left * lower_right,
      upper_left * upper_right
    ]

    {Enum.min(products), Enum.max(products)}
  end

  defp product_range(_left, _right), do: {:unbounded, :unbounded}

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
