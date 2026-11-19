defmodule ReductionBounds.IntegerSizeTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.IntegerSize

  doctest IntegerSize

  test "defaults to an unbounded range and unknown magnitude bit length" do
    assert %IntegerSize{} == %IntegerSize{
             lower: :unbounded,
             upper: :unbounded,
             magnitude_bits: :unknown
           }
  end

  test "holds a signed range and a magnitude bit-length bound together" do
    size = %IntegerSize{lower: -8, upper: 7, magnitude_bits: 4}

    assert size.lower == -8
    assert size.upper == 7
    assert size.magnitude_bits == 4
  end

  test "holds either endpoint without a magnitude bit-length bound" do
    lower_only = %IntegerSize{lower: 0}
    upper_only = %IntegerSize{upper: -1}

    assert {lower_only.lower, lower_only.upper, lower_only.magnitude_bits} ==
             {0, :unbounded, :unknown}

    assert {upper_only.lower, upper_only.upper, upper_only.magnitude_bits} ==
             {:unbounded, -1, :unknown}
  end

  test "holds a magnitude bit-length bound without finite endpoints" do
    size = %IntegerSize{magnitude_bits: 8}

    assert {size.lower, size.upper, size.magnitude_bits} ==
             {:unbounded, :unbounded, 8}
  end

  test "holds the bounds for zero" do
    size = %IntegerSize{lower: 0, upper: 0, magnitude_bits: 0}

    assert {size.lower, size.upper, size.magnitude_bits} == {0, 0, 0}
  end

  test "preserves bounds larger than a machine word" do
    limit = Integer.pow(2, 200)
    size = %IntegerSize{lower: -limit, upper: limit, magnitude_bits: 201}

    assert size.lower == -limit
    assert size.upper == limit
    assert size.magnitude_bits == 201
  end

  test "membership enforces every supplied constraint and strict magnitude endpoints" do
    size = %IntegerSize{lower: -8, upper: 7, magnitude_bits: 3}

    assert Enum.filter(-10..10, &IntegerSize.contains?(size, &1)) == Enum.to_list(-7..7)
    assert IntegerSize.contains?(%IntegerSize{lower: -8, upper: 7, magnitude_bits: 4}, -8)
    refute IntegerSize.contains?(%IntegerSize{magnitude_bits: 3}, 8)
    refute IntegerSize.contains?(%IntegerSize{magnitude_bits: 3}, -8)
  end

  test "absent components impose no constraints" do
    for value <- [-Integer.pow(2, 200), -1, 0, 1, Integer.pow(2, 200)] do
      assert IntegerSize.contains?(%IntegerSize{}, value)
    end

    assert IntegerSize.contains?(%IntegerSize{lower: 0}, 0)
    refute IntegerSize.contains?(%IntegerSize{lower: 0}, -1)
    assert IntegerSize.contains?(%IntegerSize{upper: -1}, -1)
    refute IntegerSize.contains?(%IntegerSize{upper: -1}, 0)
  end

  test "zero magnitude admits only zero" do
    size = %IntegerSize{magnitude_bits: 0}
    assert IntegerSize.contains?(size, 0)
    refute IntegerSize.contains?(size, -1)
    refute IntegerSize.contains?(size, 1)
  end

  test "contradictory constraints are well formed but admit no integer" do
    for size <- [
          %IntegerSize{lower: 2, upper: 1},
          %IntegerSize{lower: 8, magnitude_bits: 3},
          %IntegerSize{upper: -8, magnitude_bits: 3}
        ] do
      assert IntegerSize.valid?(size)
      refute Enum.any?(-20..20, &IntegerSize.contains?(size, &1))
    end
  end

  test "rejects malformed fields and noninteger values" do
    for size <- [
          %IntegerSize{lower: nil},
          %IntegerSize{upper: 1.5},
          %IntegerSize{magnitude_bits: -1},
          %IntegerSize{magnitude_bits: 1.5}
        ] do
      refute IntegerSize.valid?(size)
      assert_raise ArgumentError, fn -> IntegerSize.contains?(size, 0) end
    end

    refute IntegerSize.valid?(%{})
    assert_raise ArgumentError, fn -> IntegerSize.contains?(%IntegerSize{}, 1.0) end
    assert_raise ArgumentError, fn -> IntegerSize.contains?(%{}, 0) end
  end

  test "membership supports magnitudes above a machine word" do
    limit = Integer.pow(2, 200)
    size = %IntegerSize{lower: -limit, upper: limit, magnitude_bits: 200}
    assert IntegerSize.contains?(size, limit - 1)
    assert IntegerSize.contains?(size, -limit + 1)
    refute IntegerSize.contains?(size, limit)
    refute IntegerSize.contains?(size, -limit)
  end

  test "unknown and unreachable denote different sets" do
    assert IntegerSize.unknown() == %IntegerSize{}
    assert IntegerSize.unreachable() == :unreachable
    assert IntegerSize.valid?(:unreachable)
    refute IntegerSize.unreachable?(IntegerSize.unknown())
    assert IntegerSize.unreachable?(:unreachable)

    for value <- [-Integer.pow(2, 200), -1, 0, 1, Integer.pow(2, 200)] do
      assert IntegerSize.contains?(IntegerSize.unknown(), value)
      refute IntegerSize.contains?(:unreachable, value)
    end

    assert_raise ArgumentError, fn -> IntegerSize.contains?(:unreachable, 1.0) end
  end

  test "normalization detects every kind of empty constraint set" do
    limit = Integer.pow(2, 200)

    for size <- [
          %IntegerSize{lower: 2, upper: 1},
          %IntegerSize{lower: 8, magnitude_bits: 3},
          %IntegerSize{upper: -8, magnitude_bits: 3},
          %IntegerSize{lower: 1, magnitude_bits: 0},
          %IntegerSize{upper: -1, magnitude_bits: 0},
          %IntegerSize{lower: limit, magnitude_bits: 200},
          %IntegerSize{upper: -limit, magnitude_bits: 200}
        ] do
      assert IntegerSize.normalize(size) == :unreachable
      assert IntegerSize.unreachable?(size)
    end
  end

  test "normalization preserves satisfiable constraints unchanged" do
    limit = Integer.pow(2, 200)

    for size <- [
          IntegerSize.unknown(),
          %IntegerSize{lower: 3},
          %IntegerSize{upper: -3},
          %IntegerSize{lower: -7, upper: -3, magnitude_bits: 3},
          %IntegerSize{lower: 0, upper: 0, magnitude_bits: 0},
          %IntegerSize{lower: -8, upper: 7, magnitude_bits: 4},
          %IntegerSize{lower: limit, upper: limit, magnitude_bits: 201}
        ] do
      assert IntegerSize.normalize(size) == size
      refute IntegerSize.unreachable?(size)
    end
  end

  test "normalization preserves membership and is idempotent on an exhaustive small domain" do
    endpoints = [:unbounded | Enum.to_list(-5..5)]

    for lower <- endpoints, upper <- endpoints, bits <- [:unknown, 0, 1, 2, 3] do
      size = %IntegerSize{lower: lower, upper: upper, magnitude_bits: bits}
      normalized = IntegerSize.normalize(size)
      members = Enum.filter(-16..16, &IntegerSize.contains?(size, &1))

      assert normalized == :unreachable == (members == [])
      assert IntegerSize.normalize(normalized) == normalized
      assert Enum.filter(-16..16, &IntegerSize.contains?(normalized, &1)) == members
    end

    assert IntegerSize.normalize(:unreachable) == :unreachable
  end

  test "normalization rejects malformed information instead of treating it as unreachable" do
    for size <- [
          nil,
          :unknown,
          %{},
          %IntegerSize{lower: nil},
          %IntegerSize{upper: 1.5},
          %IntegerSize{magnitude_bits: -1}
        ] do
      assert_raise ArgumentError, fn -> IntegerSize.normalize(size) end
      assert_raise ArgumentError, fn -> IntegerSize.unreachable?(size) end
    end
  end

  test "integer constants have exact signed ranges and minimal magnitude widths" do
    for {value, width} <- [{0, 0}, {1, 1}, {-1, 1}, {7, 3}, {-8, 4}] do
      assert IntegerSize.from_integer(value) ==
               %IntegerSize{lower: value, upper: value, magnitude_bits: width}
    end

    large = Integer.pow(2, 200)
    assert IntegerSize.from_integer(large).magnitude_bits == 201
    assert IntegerSize.from_integer(-large).magnitude_bits == 201
    assert_raise ArgumentError, fn -> IntegerSize.from_integer(1.0) end
  end

  test "addition and subtraction propagate signed endpoints and magnitude bounds" do
    left = %IntegerSize{lower: -4, upper: 7, magnitude_bits: 3}
    right = %IntegerSize{lower: -2, upper: 1, magnitude_bits: 2}

    assert IntegerSize.add(left, right) ==
             %IntegerSize{lower: -6, upper: 8, magnitude_bits: 4}

    assert IntegerSize.subtract(left, right) ==
             %IntegerSize{lower: -5, upper: 9, magnitude_bits: 4}
  end

  test "multiplication accounts for all signed endpoint products" do
    left = %IntegerSize{lower: -4, upper: 7, magnitude_bits: 3}
    right = %IntegerSize{lower: -2, upper: 1, magnitude_bits: 2}

    assert IntegerSize.multiply(left, right) ==
             %IntegerSize{lower: -14, upper: 8, magnitude_bits: 5}

    assert IntegerSize.multiply(
             %IntegerSize{lower: -5, upper: -2},
             %IntegerSize{lower: -3, upper: -1}
           ) == %IntegerSize{lower: 2, upper: 15}
  end

  test "partial information remains sound and zero multiplication stays precise" do
    assert IntegerSize.add(%IntegerSize{lower: 2}, %IntegerSize{lower: 3}) ==
             %IntegerSize{lower: 5}

    assert IntegerSize.subtract(%IntegerSize{lower: 2}, %IntegerSize{upper: 3}) ==
             %IntegerSize{lower: -1}

    assert IntegerSize.multiply(%IntegerSize{lower: 2}, IntegerSize.unknown()) ==
             IntegerSize.unknown()

    assert IntegerSize.multiply(%IntegerSize{magnitude_bits: 3}, %IntegerSize{magnitude_bits: 4}) ==
             %IntegerSize{magnitude_bits: 7}

    for zero <- [%IntegerSize{magnitude_bits: 0}, %IntegerSize{lower: 0, upper: 0}] do
      assert IntegerSize.multiply(zero, IntegerSize.unknown()) == IntegerSize.from_integer(0)
      assert IntegerSize.multiply(IntegerSize.unknown(), zero) == IntegerSize.from_integer(0)
    end
  end

  test "arithmetic propagates unreachable operands while rejecting malformed operands" do
    empty = %IntegerSize{lower: 3, upper: 2}
    zero = IntegerSize.from_integer(0)

    for operation <- [:add, :subtract, :multiply],
        unreachable <- [:unreachable, empty] do
      assert apply(IntegerSize, operation, [unreachable, zero]) == :unreachable
      assert apply(IntegerSize, operation, [zero, unreachable]) == :unreachable
      assert_raise ArgumentError, fn -> apply(IntegerSize, operation, [:unreachable, nil]) end
      assert_raise ArgumentError, fn -> apply(IntegerSize, operation, [nil, :unreachable]) end
    end
  end

  test "arithmetic bounds contain every result on a finite operand domain" do
    descriptions = [
      IntegerSize.unknown(),
      :unreachable,
      %IntegerSize{lower: 2, upper: 1},
      %IntegerSize{magnitude_bits: 0},
      %IntegerSize{lower: -5, upper: -2, magnitude_bits: 3},
      %IntegerSize{lower: -3, upper: 4, magnitude_bits: 3},
      %IntegerSize{lower: 0},
      %IntegerSize{upper: -1},
      %IntegerSize{magnitude_bits: 3}
    ]

    for left <- descriptions, right <- descriptions do
      add = IntegerSize.add(left, right)
      difference = IntegerSize.subtract(left, right)
      product = IntegerSize.multiply(left, right)

      for u <- -8..8,
          v <- -8..8,
          IntegerSize.contains?(left, u),
          IntegerSize.contains?(right, v) do
        assert IntegerSize.contains?(add, u + v)
        assert IntegerSize.contains?(difference, u - v)
        assert IntegerSize.contains?(product, u * v)
      end
    end
  end

  test "independent operands and large intermediate results are not inferred from final cancellation" do
    interval = %IntegerSize{lower: 1, upper: 3, magnitude_bits: 2}

    assert IntegerSize.subtract(interval, interval) ==
             %IntegerSize{lower: -2, upper: 2, magnitude_bits: 3}

    value = Integer.pow(2, 200)
    input = IntegerSize.from_integer(value)
    product = IntegerSize.multiply(input, input)
    cancelled = IntegerSize.subtract(product, product)

    assert product == %IntegerSize{
             lower: value * value,
             upper: value * value,
             magnitude_bits: 402
           }

    assert cancelled == %IntegerSize{lower: 0, upper: 0, magnitude_bits: 403}
    assert IntegerSize.contains?(cancelled, 0)
  end

  test "left shifts propagate signed endpoints and constant magnitude growth" do
    assert IntegerSize.shift_left(IntegerSize.from_integer(-3), 2) ==
             %IntegerSize{lower: -12, upper: -12, magnitude_bits: 4}

    assert IntegerSize.shift_left(%IntegerSize{lower: -3}, 2) == %IntegerSize{lower: -12}
    assert IntegerSize.shift_left(%IntegerSize{upper: -3}, 2) == %IntegerSize{upper: -12}

    assert IntegerSize.shift_left(%IntegerSize{magnitude_bits: 3}, 2) ==
             %IntegerSize{magnitude_bits: 5}

    size = %IntegerSize{lower: -3, upper: 4, magnitude_bits: 3}
    assert IntegerSize.shift_left(size, 0) == size
    assert IntegerSize.shift_left(IntegerSize.unknown(), 8) == IntegerSize.unknown()
  end

  test "low-bit masks bound negative values without carrying over their magnitude bound" do
    cap = Integer.pow(2, 64) - 1
    masked = IntegerSize.mask(IntegerSize.from_integer(-1), 64)
    assert masked == %IntegerSize{lower: 0, upper: cap, magnitude_bits: 64}
    assert IntegerSize.contains?(masked, Bitwise.band(-1, cap))
    refute IntegerSize.contains?(masked, -1)

    assert IntegerSize.mask(IntegerSize.unknown(), 4) ==
             %IntegerSize{lower: 0, upper: 15, magnitude_bits: 4}
  end

  test "zero and unreachable states survive shifts and masks" do
    zero = IntegerSize.from_integer(0)
    empty = %IntegerSize{lower: 3, upper: 2}

    for operation <- [:shift_left, :mask], width <- [0, 1, 64, 200] do
      assert apply(IntegerSize, operation, [zero, width]) == zero
      assert apply(IntegerSize, operation, [%IntegerSize{magnitude_bits: 0}, width]) == zero
      assert apply(IntegerSize, operation, [:unreachable, width]) == :unreachable
      assert apply(IntegerSize, operation, [empty, width]) == :unreachable
    end

    assert IntegerSize.mask(IntegerSize.unknown(), 0) == zero
  end

  test "shift amounts and mask widths must be nonnegative integer constants" do
    for operation <- [:shift_left, :mask],
        width <- [-1, 1.0, :unknown, %IntegerSize{lower: 0}],
        size <- [:unreachable, IntegerSize.unknown()] do
      assert_raise ArgumentError, fn -> apply(IntegerSize, operation, [size, width]) end
    end

    for operation <- [:shift_left, :mask] do
      assert_raise ArgumentError, fn -> apply(IntegerSize, operation, [nil, 4]) end

      assert_raise ArgumentError, fn ->
        apply(IntegerSize, operation, [%IntegerSize{magnitude_bits: -1}, 4])
      end
    end
  end

  test "shift and mask bounds contain actual bitwise results on signed inputs" do
    large = Integer.pow(2, 200)
    values = Enum.to_list(-32..32) ++ [-large, -large + 1, large - 1, large]

    descriptions = [
      IntegerSize.unknown(),
      :unreachable,
      %IntegerSize{lower: 3, upper: 2},
      %IntegerSize{lower: -5, upper: -1, magnitude_bits: 3},
      %IntegerSize{lower: -3, upper: 4, magnitude_bits: 3},
      %IntegerSize{lower: 0},
      %IntegerSize{upper: -1},
      %IntegerSize{magnitude_bits: 0}
    ]

    for size <- descriptions, width <- [0, 1, 2, 4, 8, 64, 200] do
      shifted = IntegerSize.shift_left(size, width)
      masked = IntegerSize.mask(size, width)
      factor = Integer.pow(2, width)

      for value <- values, IntegerSize.contains?(size, value) do
        actual_shift = Bitwise.bsl(value, width)
        actual_mask = Bitwise.band(value, factor - 1)
        assert actual_shift == value * factor
        assert actual_mask == Integer.mod(value, factor)
        assert IntegerSize.contains?(shifted, actual_shift)
        assert IntegerSize.contains?(masked, actual_mask)
      end
    end
  end

  test "a small masked result does not erase a large pre-mask intermediate" do
    input = IntegerSize.from_integer(Integer.pow(2, 100))
    shifted = IntegerSize.shift_left(input, 100)
    masked = IntegerSize.mask(shifted, 64)

    assert shifted == %IntegerSize{
             lower: Integer.pow(2, 200),
             upper: Integer.pow(2, 200),
             magnitude_bits: 201
           }

    assert masked == %IntegerSize{lower: 0, upper: Integer.pow(2, 64) - 1, magnitude_bits: 64}
    assert IntegerSize.contains?(masked, 0)
    assert shifted.magnitude_bits == 201
  end
end
