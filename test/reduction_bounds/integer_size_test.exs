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
end
