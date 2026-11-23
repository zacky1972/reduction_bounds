defmodule ReductionBounds.ExecutionBoundTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.{ExecutionBound, ProofInput}
  alias ReductionBounds.ExecutionBoundTest.{Callee, Fixture}

  defmodule Callee do
    def step(n), do: n + 1
  end

  setup_all do
    [{Fixture, beam}] =
      Code.compile_string("""
      defmodule #{inspect(Fixture)} do
        @compile :debug_info
        def run(0), do: 0
        def run(n) do
          x = #{inspect(Callee)}.step(n)
          x + run(n - 1)
        end

        def choose(0), do: 0
        def choose(n) do
          x = #{inspect(Callee)}.step(n)
          case x do
            0 -> n
            y -> y + n
          end
        end

        def nondecreasing(0), do: 0
        def nondecreasing(n), do: nondecreasing(n)

        def unsupported(0), do: 0
        def unsupported(_n), do: :unsupported_value
      end
      """)

    %{beam: beam}
  end

  test "checks the candidate bound and termination for a recursive caller", %{beam: beam} do
    callee = {Callee, :step, 1}

    assert {:ok,
            %{
              precondition: {:nonnegative_integer, 0},
              termination: :under_call_contracts,
              call_contracts: %{^callee => 5},
              upper_bound: %{zero: {:add, {:charge, :branch}, 0}, successor: equation},
              reports: [%{status: :ok}]
            }} =
             ReductionBounds.infer_verified_bound({Fixture, :run, 1},
               beam_binaries: [beam],
               call_contracts: %{callee => 5}
             )

    assert {:contract, callee} in terms(equation)
    assert :previous in terms(equation)
    assert apply(Fixture, :run, [3]) == 9
  end

  test "checks a zero test after a static call", %{beam: beam} do
    assert {:ok, %{upper_bound: %{successor: equation}, reports: [%{status: :ok}]}} =
             ReductionBounds.infer_verified_bound({Fixture, :choose, 1},
               beam_binaries: [beam],
               call_contracts: %{{Callee, :step, 1} => 5}
             )

    assert :max in terms(equation)
  end

  test "reports a missing static call contract and an unsupported expression", %{beam: beam} do
    callee = {Callee, :step, 1}

    assert {:error, {:unresolved_call_contracts, [^callee]}} =
             ReductionBounds.infer_verified_bound({Fixture, :run, 1}, beam_binaries: [beam])

    assert {:error,
            {:unsupported_core, :unsupported_expression, {:c_literal, _, :unsupported_value}}} =
             ReductionBounds.infer_verified_bound({Fixture, :unsupported, 1},
               beam_binaries: [beam]
             )
  end

  test "Lean rejects a recursive call with an unchanged input", %{beam: beam} do
    assert {:error, {:verification_failed, [%{status: :error, diagnostics: diagnostics}]}} =
             ReductionBounds.infer_verified_bound({Fixture, :nondecreasing, 1},
               beam_binaries: [beam]
             )

    assert Enum.any?(
             diagnostics,
             &(&1.severity == :error and &1.message =~ "targetProgram.valid")
           )
  end

  test "Lean rejects a candidate with a smaller base bound", %{beam: beam} do
    callee = {Callee, :step, 1}
    assert {:ok, _, proof} = ExecutionBound.infer({Fixture, :run, 1}, [beam], %{callee => 5})

    source = String.replace(proof.source, ~s/| 0 => ((charge "branch") + 0)/, "| 0 => 0")
    refute source == proof.source
    assert {:ok, postludes} = ProofInput.execution_postludes(%{proof | source: source})
    translation = Lynx.Translation.new(postludes: postludes)

    assert [%{status: :error, diagnostics: diagnostics}] =
             ReductionBounds.Verification.verify!(translation,
               postlude_imports: ["Erlang.erlang", "Erlang.maps"]
             )

    assert Enum.any?(diagnostics, &(&1.severity == :error and &1.message =~ "targetUpper"))
  end

  defp terms({operation, left, right}) when operation in [:add, :max],
    do: [operation | terms(left) ++ terms(right)]

  defp terms(term), do: [term]
end
