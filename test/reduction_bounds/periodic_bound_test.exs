defmodule ReductionBounds.PeriodicBoundTest do
  use ExUnit.Case, async: true
  @moduletag timeout: 300_000

  import Lynx.Lean

  alias ReductionBounds.PeriodicBoundTest.Batcher

  setup_all do
    [{Batcher, beam}] =
      Code.compile_string("""
      defmodule #{inspect(Batcher)} do
        @compile :debug_info

        def enqueue_pair(pending, period) do
          advanced = pending + 2

          if advanced >= period do
            {advanced - period, true}
          else
            {advanced, false}
          end
        end

        def drop_remaining(pending, period) do
          advanced = pending + 2
          if advanced >= period, do: {0, true}, else: {advanced, false}
        end
      end
      """)

    %{beam: beam}
  end

  test "infers the same rule as the buffer with a stride of two", %{beam: beam} do
    target = {Batcher, :enqueue_pair, 2}
    events = {:div, {:add, :initial, {:mul, :n, 2}}, :period}

    assert {:ok,
            %{
              periodic_rule: :constant_stride_reset,
              stride: 2,
              origin: 0,
              event_count: ^events,
              upper_bound: {:add, {:mul, :n, :base}, {:mul, ^events, :surcharge}},
              conditions: %{derived: derived, supplied: []},
              reports: reports
            }} = ReductionBounds.infer_periodic_bound(target, beam_binaries: [beam])

    assert Enum.all?(reports, &(&1.status == :ok))
    assert {:invariant, {:lt, :state, :period}} in derived
    assert {:stride_fits, {:le, 2, :period}} in derived

    for period <- 2..7, initial <- 0..(period - 1), steps <- 0..12 do
      {pending, batches} =
        Enum.reduce(List.duplicate(:pair, steps), {initial, 0}, fn _, {state, count} ->
          {next, emitted} = apply(Batcher, :enqueue_pair, [state, period])
          {next, count + if(emitted, do: 1, else: 0)}
        end)

      assert batches == div(initial + steps * 2, period)
      assert pending == rem(initial + steps * 2, period)
    end
  end

  test "checks and reports a supplied parity invariant and size measure", %{beam: beam} do
    contract = ~LEAN"""
    def periodicInvariant (period state : Nat) : Prop :=
      period % 2 = 0 ∧ state % 2 = 0

    def periodicMeasure (_period state : Nat) : Nat := state + 2

    theorem periodicInvariantStep (period state : Nat)
        (_valid : periodicDomain period state) (initial : periodicInvariant period state) :
        periodicInvariant period (periodicNext period state) := by
      obtain ⟨periodEven, stateEven⟩ := initial
      refine ⟨periodEven, ?_⟩
      by_cases reset : period ≤ state + 2 <;>
        simp [periodicNext, counterStep, inferredStride, reset] <;> omega

    theorem periodicMeasureBounds (period state : Nat)
        (_valid : periodicDomain period state) (_initial : periodicInvariant period state) :
        state ≤ periodicMeasure period state := by
      simp [periodicMeasure]
    """

    source = contract.source
    events = {:div, {:add, {:measure, :periodic_measure}, {:mul, :n, 2}}, :period}

    assert {:ok,
            %{
              measured_event_upper_bound: ^events,
              measured_upper_bound: {:add, {:mul, :n, :base}, {:mul, ^events, :surcharge}},
              conditions: %{
                supplied: [
                  {:invariant, :periodic_invariant},
                  {:size_measure, :periodic_measure},
                  {:lean_source, ^source}
                ]
              },
              reports: reports
            }} =
             ReductionBounds.infer_periodic_bound({Batcher, :enqueue_pair, 2},
               beam_binaries: [beam],
               periodic_contract: contract
             )

    assert Enum.all?(reports, &(&1.status == :ok))
  end

  test "rejects a reset that discards the remainder", %{beam: beam} do
    target = {Batcher, :drop_remaining, 2}

    assert {:error, {:unsupported_periodic_transition, ^target}} =
             ReductionBounds.infer_periodic_bound(target, beam_binaries: [beam])
  end

  test "rejects a contract that assumes its size proof", %{beam: beam} do
    contract = ~LEAN"""
    def periodicInvariant (_period _state : Nat) : Prop := True
    def periodicMeasure (_period _state : Nat) : Nat := 0

    theorem periodicInvariantStep (period state : Nat)
        (_valid : periodicDomain period state) (_initial : periodicInvariant period state) :
        periodicInvariant period (periodicNext period state) := trivial

    theorem periodicMeasureBounds (period state : Nat)
        (_valid : periodicDomain period state) (_initial : periodicInvariant period state) :
        state ≤ periodicMeasure period state := by
      sorry
    """

    assert {:error, {:verification_failed, reports}} =
             ReductionBounds.infer_periodic_bound({Batcher, :enqueue_pair, 2},
               beam_binaries: [beam],
               periodic_contract: contract
             )

    assert Enum.all?(Enum.drop(reports, -1), &(&1.status == :ok))
    assert %{status: :error, diagnostics: diagnostics} = List.last(reports)
    assert Enum.any?(diagnostics, &(&1.severity == :error and &1.message =~ "sorryAx"))
  end
end
