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
end
