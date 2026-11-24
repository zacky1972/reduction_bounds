defmodule ReductionBounds.ProofModeComparisonTest do
  use ExUnit.Case, async: false

  test "public integer claims, assumptions, and audited theorem names match the embedded path" do
    [{module, beam}] =
      Code.compile_string("""
      defmodule ReductionBounds.ProofModeComparisonTest.Program do
        @compile :debug_info
        def product(x), do: x * x + 1
      end
      """)

    previous = System.get_env("REDUCTION_BOUNDS_PROOF_MODE")

    on_exit(fn ->
      :code.purge(module)
      :code.delete(module)
    end)

    try do
      for function <- [:infer_integer_sizes, :infer_integer_cost_bound] do
        options = [
          beam_binaries: [beam],
          input_sizes: [%ReductionBounds.IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}]
        ]

        System.put_env("REDUCTION_BOUNDS_PROOF_MODE", "embedded")

        assert {:ok, original} =
                 apply(ReductionBounds, function, [{module, :product, 1}, options])

        System.put_env("REDUCTION_BOUNDS_PROOF_MODE", "named")
        assert {:ok, named} = apply(ReductionBounds, function, [{module, :product, 1}, options])
        assert Map.delete(named, :reports) == Map.delete(original, :reports)
        assert Enum.all?(original.reports ++ named.reports, &(&1.status == :ok))
      end
    after
      if previous,
        do: System.put_env("REDUCTION_BOUNDS_PROOF_MODE", previous),
        else: System.delete_env("REDUCTION_BOUNDS_PROOF_MODE")
    end
  end
end
