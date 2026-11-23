defmodule ReductionBounds.ProtocolSizeTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.ProtocolSize

  @moduletag :protocol_conditions
  doctest ProtocolSize

  test "bytes and structural traversal units are independent" do
    for {data, bytes, structure} <- [
          {<<>>, 0, 1},
          {[], 0, 1},
          {[[], []], 0, 5},
          {[[[]]], 0, 5},
          {[1, 2], 2, 5},
          {[<<1, 2>> | <<3>>], 3, 3},
          {<<0::8000>>, 1000, 1}
        ] do
      assert {:ok, %ProtocolSize{bytes: ^bytes, structure: ^structure}} =
               ProtocolSize.from_iodata(data)
    end

    assert {:ok, data} = ProtocolSize.from_iodata([[], []])
    refute ProtocolSize.within?(data, %ProtocolSize{bytes: 0, structure: 4})
    assert ProtocolSize.within?(data, %ProtocolSize{bytes: 0, structure: 5})
  end

  test "unknown dimensions do not establish inclusion" do
    refute ProtocolSize.known?(%ProtocolSize{})
    refute ProtocolSize.known?(%ProtocolSize{bytes: -1, structure: 0})
    refute ProtocolSize.within?(%ProtocolSize{}, %ProtocolSize{bytes: 1, structure: 1})
    refute ProtocolSize.within?(%ProtocolSize{bytes: 0, structure: 1}, %ProtocolSize{})
  end

  test "rejects scalar, non-byte, and malformed iodata" do
    for data <- [
          1,
          :unknown,
          [256],
          [-1],
          [Integer.pow(2, 200)],
          [1 | 2],
          [<<1>> | :invalid],
          <<1::1>>
        ] do
      assert {:error, {:invalid_iodata, _}} = ProtocolSize.from_iodata(data)
    end
  end
end
