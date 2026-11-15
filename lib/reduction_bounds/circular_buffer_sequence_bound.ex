defmodule ReductionBounds.CircularBufferSequenceBound do
  @moduledoc false
  # cspell:words cerl primop simp simpa cons rcases succ symm

  alias ReductionBounds.{CircularBufferBound, SearchBound}

  @initializer {CircularBuffer, :new, 1}

  @spec infer([binary()]) :: {:ok, map()} | {:error, term()}
  def infer(beams) do
    with {:ok, single} <- CircularBufferBound.infer(beams),
         {:ok, core} <- SearchBound.core_function(@initializer, beams),
         true <- empty_initializer?(core) do
      {:ok, sequence_candidate(single)}
    else
      false -> {:error, {:unsupported_circular_buffer_shape, @initializer}}
      {:error, _} = error -> error
    end
  end

  defp sequence_candidate(%{path_bounds: paths} = single) do
    {:add, local_rotation, reversal} = paths.rotate
    base = {:max, paths.consume, {:max, paths.fill, local_rotation}}
    surcharge = replace_capacity(reversal)
    rotations = {:if_zero, :m, 0, {:div, {:sub, :n, 1}, :m}}
    positive = {:add, {:mul, :n, base}, {:mul, rotations, surcharge}}

    single
    |> Map.drop([:path_bounds])
    |> Map.merge(%{
      domain: :integer_insertions_from_empty_circular_buffer,
      value_model: :circular_buffer_sequence_model,
      size_measure: %{m: :capacity, n: :insertions},
      rotation_count: rotations,
      base_cost: base,
      rotation_surcharge: surcharge,
      upper_bound: {:if_zero, :m, {:mul, :n, paths.zero}, positive}
    })
  end

  defp replace_capacity(:n), do: :m

  defp replace_capacity(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&replace_capacity/1) |> List.to_tuple()
  end

  defp replace_capacity(other), do: other

  defp empty_initializer?(
         {:c_fun, _, [{:c_var, _, input}], {:c_case, _, {:c_var, _, input}, clauses}}
       ) do
    case :cerl_trees.map(&:cerl.set_ann(&1, []), {:c_values, [], clauses}) do
      {:c_values, [],
       [
         {:c_clause, [], [{:c_var, [], size}], guard,
          {:c_map, [], {:c_literal, [], empty}, fields, false}},
         {:c_clause, [], [{:c_var, [], _}], {:c_literal, [], true},
          {:c_primop, [], {:c_literal, [], :match_fail}, _}}
       ]}
      when empty == %{} ->
        capacity_guard?(guard, input, size) and initializer_fields?(fields, size)

      _ ->
        false
    end
  end

  defp empty_initializer?(_), do: false

  defp initializer_fields?(fields, size) do
    expected = %{
      __struct__: {:c_literal, [], CircularBuffer},
      a: {:c_literal, [], []},
      b: {:c_literal, [], []},
      count: {:c_literal, [], 0},
      max_size: {:c_var, [], size}
    }

    Enum.sort(fields) ==
      Enum.sort(
        Enum.map(expected, fn {key, value} ->
          {:c_map_pair, [], {:c_literal, [], :assoc}, {:c_literal, [], key}, value}
        end)
      )
  end

  defp capacity_guard?(
         {:c_try, [],
          {:c_let, [], [{:c_var, [], checked}],
           {:c_case, [],
            {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :is_integer},
             [{:c_var, [], tested}]},
            [
              {:c_clause, [], [{:c_literal, [], true}], {:c_literal, [], true},
               {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :>=},
                [{:c_var, [], tested}, {:c_literal, [], 0}]}},
              {:c_clause, [], [{:c_literal, [], false}], {:c_literal, [], true},
               {:c_literal, [], false}},
              {:c_clause, [], [{:c_var, [], _}], {:c_literal, [], true}, _}
            ]},
           {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :"=:="},
            [{:c_var, [], checked}, {:c_literal, [], true}]}}, [{:c_var, [], result}],
          {:c_var, [], result}, _, {:c_literal, [], false}},
         input,
         size
       ),
       do: tested in [input, size]

  defp capacity_guard?(_guard, _input, _size), do: false

  @spec proof() :: Lynx.Lean.t()
  def proof() do
    proof = CircularBufferBound.proof()

    %{
      proof
      | file: "generated_circular_buffer_sequence_bound.lean",
        source: proof.source <> "\n" <> transition_proof() <> counting_proof()
    }
  end

  defp transition_proof() do
    """
    def newModel (m : Nat) : BufferState := ⟨[], [], 0, m⟩

    def rotationStep (s : BufferState) : Nat :=
      match s.b with
      | _ :: _ => 0
      | [] => if s.count < s.capacity then 0 else if s.a.isEmpty then 0 else 1

    theorem insertCapacity (s : BufferState) (item : Int) :
        (insertModel s item).capacity = s.capacity := by
      cases s with
      | mk a b count capacity =>
        cases b with
        | nil =>
          cases a <;> by_cases fills : count < capacity <;> simp [insertModel, fills]
        | cons head tail => rfl

    theorem insertAdvance (s : BufferState) (item : Int) (valid : s.valid)
        (positive : 0 < s.capacity) :
        s.a.length + 1 = rotationStep s * s.capacity + (insertModel s item).a.length ∧
          0 < (insertModel s item).a.length := by
      rcases s with ⟨a, b, count, capacity⟩
      change 0 < capacity at positive
      cases b with
      | cons head tail => simp [rotationStep, insertModel]
      | nil =>
        by_cases fills : count < capacity
        · simp [rotationStep, insertModel, fills]
        · cases a with
          | nil => simp [BufferState.valid] at valid; omega
          | cons head tail =>
            simp [rotationStep, insertModel, fills, BufferState.valid] at valid ⊢
            omega

    def insertionBase (bufferCharge : Nat → Nat) : Nat :=
      max (bufferCharge 0) (max (bufferCharge 1) (bufferCharge 2))

    def rotationSurcharge (reverseCharge : Nat → Nat → Nat)
        (bufferCharge : Nat → Nat) (m : Nat) : Nat :=
      bufferCharge 4 + Reverse.listRefinedUpperBound reverseCharge m

    theorem insertBudget (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
        (s : BufferState) (valid : s.valid) (positive : 0 < s.capacity) :
        insertCost reverseCharge bufferCharge s ≤
          insertionBase bufferCharge +
          rotationStep s * rotationSurcharge reverseCharge bufferCharge s.capacity := by
      have sizeBound : s.a.length ≤ s.capacity := by
        rcases valid with ⟨lengths, bounded, _⟩
        omega
      have consumes : bufferCharge 0 ≤ insertionBase bufferCharge := Nat.le_max_left _ _
      have fillsBudget : bufferCharge 1 ≤ insertionBase bufferCharge :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have rotatesBudget : bufferCharge 2 ≤ insertionBase bufferCharge :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      rcases s with ⟨a, b, count, capacity⟩
      change 0 < capacity at positive
      cases b with
      | cons head tail => simpa [insertCost, consumeCost, rotationStep] using consumes
      | nil =>
        by_cases fills : count < capacity
        · simpa [insertCost, fillCost, rotationStep, fills] using fillsBudget
        · cases a with
          | nil => simp [BufferState.valid] at valid; omega
          | cons head tail =>
            simp [insertCost, rotateCost, rotationStep, fills, rotationSurcharge]
            exact Nat.add_le_add rotatesBudget
              (Nat.add_le_add_left (enumReverseCostBound reverseCharge
                (head :: tail) capacity sizeBound) (bufferCharge 4))

    structure InsertionRun where
      state : BufferState
      rotations : Nat
      cost : Nat

    def insertMany (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
        (s : BufferState) : List Int → InsertionRun
      | [] => ⟨s, 0, 0⟩
      | item :: rest =>
        let suffix := insertMany reverseCharge bufferCharge (insertModel s item) rest
        ⟨suffix.state, rotationStep s + suffix.rotations,
          insertCost reverseCharge bufferCharge s + suffix.cost⟩

    theorem insertManyFromPositive (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
        (s : BufferState) (items : List Int) (valid : s.valid) (positive : 0 < s.capacity) :
        let run := insertMany reverseCharge bufferCharge s items
        run.state.valid ∧ run.state.capacity = s.capacity ∧
        s.a.length + items.length = run.rotations * s.capacity + run.state.a.length ∧
        (0 < s.a.length ∨ items ≠ [] → 0 < run.state.a.length) ∧
        run.cost ≤ items.length * insertionBase bufferCharge +
          run.rotations * rotationSurcharge reverseCharge bufferCharge s.capacity := by
      induction items generalizing s with
      | nil => simp [insertMany, valid]
      | cons item rest ih =>
        have capacity := insertCapacity s item
        have nextPositive : 0 < (insertModel s item).capacity := by rwa [capacity]
        obtain ⟨endValid, endCapacity, balance, nonempty, cost⟩ :=
          ih (insertModel s item) (insertPreserves s item valid) nextPositive
        rw [capacity] at endCapacity balance cost
        obtain ⟨advance, nextNonempty⟩ := insertAdvance s item valid positive
        have stepCost := insertBudget reverseCharge bufferCharge s valid positive
        simp only [insertMany, List.length_cons, Nat.add_mul, Nat.succ_mul]
        refine ⟨endValid, endCapacity, by omega, fun _ => nonempty (Or.inl nextNonempty), ?_⟩
        omega

    """
  end

  defp counting_proof() do
    """
    theorem insertManyZero (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
        (items : List Int) :
        let run := insertMany reverseCharge bufferCharge (newModel 0) items
        run.state = newModel 0 ∧ run.rotations = 0 ∧ run.cost = items.length * bufferCharge 3 := by
      induction items with
      | nil => simp [insertMany]
      | cons item rest ih =>
        obtain ⟨state, rotations, cost⟩ := ih
        have step := insertZeroCapacity reverseCharge bufferCharge (newModel 0) item (by
          simp [newModel, BufferState.valid]) rfl
        have noRotation : rotationStep (newModel 0) = 0 := rfl
        simp only [insertMany, step.1, step.2, noRotation, state, rotations, cost, Nat.zero_add,
          List.length_cons, Nat.succ_mul, Nat.add_comm, and_self]

    def sequenceRotationCount (m n : Nat) : Nat :=
      if m = 0 then 0 else (n - 1) / m

    theorem insertManyRotationCount (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
        (m : Nat) (items : List Int) :
        (insertMany reverseCharge bufferCharge (newModel m) items).rotations =
          sequenceRotationCount m items.length := by
      by_cases zero : m = 0
      · subst m
        simpa [sequenceRotationCount] using (insertManyZero reverseCharge bufferCharge items).2.1
      · cases items with
        | nil => simp [insertMany, sequenceRotationCount, zero]
        | cons item rest =>
          have positive : 0 < m := by omega
          have valid : (newModel m).valid := by simp [newModel, BufferState.valid]
          obtain ⟨endValid, endCapacity, balance, nonempty, _⟩ :=
            insertManyFromPositive reverseCharge bufferCharge (newModel m) (item :: rest) valid positive
          let run := insertMany reverseCharge bufferCharge (newModel m) (item :: rest)
          have sum : (item :: rest).length = run.rotations * m + run.state.a.length := by
            simpa [run, newModel] using balance
          have endNonempty : 0 < run.state.a.length := nonempty (Or.inr (by simp))
          have endBound : run.state.a.length ≤ m := by
            rcases endValid with ⟨lengths, bounded, _⟩
            change run.state.count = run.state.a.length + run.state.b.length at lengths
            change run.state.count ≤ run.state.capacity at bounded
            change run.state.capacity = m at endCapacity
            omega
          simp only [sequenceRotationCount, if_neg zero]
          change run.rotations = (List.length (item :: rest) - 1) / m
          symm
          apply Nat.div_eq_of_lt_le
          · omega
          · rw [Nat.add_mul, Nat.one_mul]
            omega

    def insertionSequenceUpperBound (reverseCharge : Nat → Nat → Nat)
        (bufferCharge : Nat → Nat) (m n : Nat) : Nat :=
      if m = 0 then n * bufferCharge 3
      else n * insertionBase bufferCharge +
        sequenceRotationCount m n * rotationSurcharge reverseCharge bufferCharge m

    theorem insertManyCostBound (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
        (m : Nat) (items : List Int) :
        (insertMany reverseCharge bufferCharge (newModel m) items).cost ≤
          insertionSequenceUpperBound reverseCharge bufferCharge m items.length := by
      by_cases zero : m = 0
      · subst m
        simp [insertionSequenceUpperBound, (insertManyZero reverseCharge bufferCharge items).2.2]
      · have positive : 0 < m := by omega
        have valid : (newModel m).valid := by simp [newModel, BufferState.valid]
        have cost := (insertManyFromPositive reverseCharge bufferCharge
          (newModel m) items valid positive).2.2.2.2
        rw [insertManyRotationCount reverseCharge bufferCharge m items] at cost
        simpa [insertionSequenceUpperBound, zero, newModel] using cost
    """
  end
end
