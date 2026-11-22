defmodule ReductionBounds.IntegerCostCasesTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{IntegerCostBound, IntegerSize, ProofInput, SearchBound}
  alias ReductionBounds.Fixtures.IntegerCostCases, as: Fixture

  @moduletag timeout: 120_000

  setup_all do
    [{Fixture, beam}] =
      Code.compile_file(Path.expand("../fixtures/integer_cost_cases.ex", __DIR__))

    on_exit(fn ->
      :code.purge(Fixture)
      :code.delete(Fixture)
      :code.purge(Fixture)
    end)

    %{beam: beam}
  end

  test "checks variance cancellation for large closely spaced signed samples", %{beam: beam} do
    base = 1_788_878_897_448
    large = Integer.pow(2, 200)

    for samples <- [
          [base, base + 1, base + 2],
          [-base - 2, -base - 1, -base],
          [large - 1, large, large + 1],
          [large, large, large]
        ] do
      sum = Enum.sum(samples)
      squares = Enum.sum(Enum.map(samples, &(&1 * &1)))
      count = length(samples)
      inputs = Enum.map([sum, squares, count], &IntegerSize.from_integer/1)

      assert {:ok, result} = infer(:variance_numerator, inputs, beam)
      assert_checked(result)

      # n * sum(x^2) - sum(x)^2 equals the sum of squared pair differences.
      expected = pair_differences(samples)
      assert apply(Fixture, :variance_numerator, [sum, squares, count]) == expected
      assert result.result_size.lower == expected
      assert result.result_size.upper == expected
      assert expected in [0, 6]

      products = Enum.filter(result.intermediates, &(&1.operation == :multiply))
      assert length(products) == 2
      assert Enum.any?(products, &(&1.size.lower == count * squares))
      assert Enum.any?(products, &(&1.size.lower == sum * sum))
      assert Enum.all?(products, &(&1.size.lower > Integer.pow(2, 64)))

      [sum_size, square_size, count_size] = inputs
      items = cost_items(result.upper_bound)
      widths = [count_size.magnitude_bits, square_size.magnitude_bits]

      assert {:cost, :multiplication, widths} in items
      assert {:cost, :multiplication, [sum_size.magnitude_bits, sum_size.magnitude_bits]} in items
    end
  end

  test "bounds the variance numerator over independent summary intervals", %{beam: beam} do
    inputs = [domain(-256, 256), domain(0, 16_384), domain(2, 4)]
    assert {:ok, result} = infer(:variance_numerator, inputs, beam)
    assert_checked(result)

    for x <- [-64, -1, 0, 1, 64],
        y <- [-64, -1, 0, 1, 64],
        z <- [-64, -1, 0, 1, 64] do
      samples = [x, y, z]
      sum = x + y + z
      squares = x * x + y * y + z * z
      expected = pair_differences(samples)
      assert apply(Fixture, :variance_numerator, [sum, squares, 3]) == expected
      assert IntegerSize.contains?(result.result_size, expected)
    end
  end

  test "checks the positive denominator on the sample-variance input domain", %{beam: beam} do
    assert {:ok, result} = infer(:variance_denominator, [domain(2, 8)], beam)
    assert_checked(result)
    assert result.result_size.lower == 2
    assert result.result_size.upper == 56

    for count <- 2..8 do
      actual = apply(Fixture, :variance_denominator, [count])
      assert actual == count * (count - 1)
      assert IntegerSize.contains?(result.result_size, actual)
    end
  end

  test "checks normal and reflected table-driven CRC update expressions", %{beam: beam} do
    limit = Integer.pow(2, 64)
    input = domain(0, limit - 1)

    for {name, operation, shifted_bits, mixed_bits} <- [
          {:crc64_update, :shift_left, 72, 73},
          {:crc64_reflected_update, :shift_right, 64, 65}
        ] do
      assert {:ok, result} = infer(name, [input, input], beam)
      assert_checked(result)
      assert result.result_size == input
      items = cost_items(result.upper_bound)
      assert {:cost, operation, [64, 8]} in items
      assert {:cost, :xor, [shifted_bits, 64]} in items
      assert {:cost, :mask, [mixed_bits, 64]} in items

      assert Enum.any?(
               result.intermediates,
               &(&1.operation == operation and &1.size.magnitude_bits == shifted_bits)
             )

      for crc <- [0, 1, Integer.pow(2, 63), limit - 1],
          entry <- [0, 0x42F0E1EBA9EA3693, limit - 1] do
        shifted = if name == :crc64_update, do: crc * 256, else: div(crc, 256)
        expected = Integer.mod(Bitwise.bxor(shifted, entry), limit)
        actual = apply(Fixture, name, [crc, entry])
        assert actual == expected
        assert IntegerSize.contains?(result.result_size, actual)
      end
    end
  end

  test "checks the one-based table index expressions for every input byte", %{beam: beam} do
    limit = Integer.pow(2, 64)
    inputs = [domain(0, limit - 1), domain(0, 255)]

    for name <- [:crc64_index, :crc64_reflected_index] do
      assert {:ok, result} = infer(name, inputs, beam)
      assert_checked(result)
      assert result.result_size.lower == 1
      assert result.result_size.upper == 256

      for crc <- [0, 1, Integer.pow(2, 63), limit - 1], byte <- 0..255 do
        prefix = if name == :crc64_index, do: div(crc, Integer.pow(2, 56)), else: crc
        expected = Integer.mod(Bitwise.bxor(prefix, byte), 256) + 1
        actual = apply(Fixture, name, [crc, byte])
        assert actual == expected
        assert IntegerSize.contains?(result.result_size, actual)
      end
    end
  end

  test "Lean rejects discarding the variance computation because its result is small", %{
    beam: beam
  } do
    large = Integer.pow(2, 200)
    samples = [large - 1, large, large + 1]
    sum = Enum.sum(samples)
    squares = Enum.sum(Enum.map(samples, &(&1 * &1)))
    inputs = Enum.map([sum, squares, 3], &IntegerSize.from_integer/1)
    target = {Fixture, :variance_numerator, 3}
    assert {:ok, core} = SearchBound.core_function(target, [beam])
    assert {:ok, candidate} = IntegerCostBound.infer_core(core, target, input_sizes: inputs)
    assert Enum.any?(verify(%{candidate | upper_bound: 0}), &(&1.status == :error))
  end

  defp infer(name, inputs, beam) do
    ReductionBounds.infer_integer_cost_bound(
      {Fixture, name, length(inputs)},
      beam_binaries: [beam],
      input_sizes: inputs
    )
  end

  defp assert_checked(result) do
    assert result.proof_scope == :reified_core_integer_cost_fragment
    assert result.value_agreement == :checked
    assert result.runtime_correspondence == :not_checked
    assert result.unresolved_sizes == []
    assert result.conditions.calls == []
    assert "integerCostSourceBound" in result.checked_theorems
    assert "integerCostTotal" in result.checked_theorems
    assert result.reports != []
    assert Enum.all?(result.reports, &(&1.status == :ok))
  end

  defp domain(lower, upper) do
    bits = IntegerSize.from_integer(max(abs(lower), abs(upper))).magnitude_bits
    %IntegerSize{lower: lower, upper: upper, magnitude_bits: bits}
  end

  defp pair_differences(samples) do
    for {left, index} <- Enum.with_index(samples),
        right <- Enum.drop(samples, index + 1),
        reduce: 0 do
      total -> total + (left - right) * (left - right)
    end
  end

  defp cost_items(0), do: []
  defp cost_items({:cost, _, _} = item), do: [item]

  defp cost_items({kind, left, right}) when kind in [:add, :max],
    do: cost_items(left) ++ cost_items(right)

  defp verify(candidate) do
    {proof, _evidence} = ProofInput.audit_bound(IntegerCostBound.proof(candidate), candidate)
    {:ok, postludes} = ProofInput.integer_cost_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    Lynx.Commands.verify!(project, Lynx.Translation.assemble(translation, cache: false))
  end
end
