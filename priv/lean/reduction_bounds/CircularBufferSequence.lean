def newModel (m : Nat) : BufferState := ⟨[], [], 0, m⟩

def rotationStep (s : BufferState) : Nat :=
  match insertPath s with
  | .rotate => 1
  | _ => 0

theorem insertCapacity (s : BufferState) (item : Int) :
    (insertModel s item).capacity = s.capacity := by
  cases path : insertPath s <;> simp [insertModel, path]

theorem insertAdvance (s : BufferState) (item : Int) (valid : s.valid)
    (positive : 0 < s.capacity) :
    s.a.length + 1 = rotationStep s * s.capacity + (insertModel s item).a.length ∧
      0 < (insertModel s item).a.length := by
  rcases s with ⟨a, b, count, capacity⟩
  change 0 < capacity at positive
  cases b with
  | cons head tail => simp [rotationStep, insertModel, insertPath]
  | nil =>
    by_cases fills : count < capacity
    · simp [rotationStep, insertModel, insertPath, fills]
    · cases a with
      | nil => simp [BufferState.valid] at valid; omega
      | cons head tail =>
        simp [rotationStep, insertModel, insertPath, fills, BufferState.valid] at valid ⊢
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
  | cons head tail => simpa [insertCost, consumeCost, rotationStep, insertPath] using consumes
  | nil =>
    by_cases fills : count < capacity
    · simpa [insertCost, fillCost, rotationStep, insertPath, fills] using fillsBudget
    · cases a with
      | nil => simp [BufferState.valid] at valid; omega
      | cons head tail =>
        simp [insertCost, rotateCost, rotationStep, insertPath, fills, rotationSurcharge]
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

theorem validZeroState (s : BufferState) (valid : s.valid) (zero : s.capacity = 0) :
    s = newModel 0 := by
  rcases s with ⟨a, b, count, capacity⟩
  change capacity = 0 at zero
  subst capacity
  simp [BufferState.valid] at valid
  have aEmpty : a.length = 0 := by omega
  have bEmpty : b.length = 0 := by omega
  have countZero : count = 0 := by omega
  simp [newModel, List.length_eq_zero_iff.mp aEmpty, List.length_eq_zero_iff.mp bEmpty, countZero]

def sequenceRotationCountFrom (m a n : Nat) : Nat :=
  if m = 0 then 0 else (a + n - 1) / m

theorem insertManyRotationCountFrom (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) (items : List Int) (valid : s.valid) :
    (insertMany reverseCharge bufferCharge s items).rotations =
      sequenceRotationCountFrom s.capacity s.a.length items.length := by
  by_cases zero : s.capacity = 0
  · rw [validZeroState s valid zero]
    simpa [sequenceRotationCountFrom, newModel] using
      (insertManyZero reverseCharge bufferCharge items).2.1
  · have positive : 0 < s.capacity := by omega
    by_cases noProgress : s.a.length + items.length = 0
    · have empty : items = [] := List.length_eq_zero_iff.mp (by omega)
      have aEmpty : s.a.length = 0 := by omega
      simp [empty, aEmpty, insertMany, sequenceRotationCountFrom]
    · obtain ⟨endValid, endCapacity, balance, nonempty, _⟩ :=
        insertManyFromPositive reverseCharge bufferCharge s items valid positive
      let run := insertMany reverseCharge bufferCharge s items
      change s.a.length + items.length = run.rotations * s.capacity + run.state.a.length at balance
      have endNonempty : 0 < run.state.a.length := nonempty (by
        by_cases hasA : 0 < s.a.length
        · exact Or.inl hasA
        · have lengthZero : s.a.length = 0 := by omega
          exact Or.inr (fun empty => noProgress (by simp [empty, lengthZero])))
      have endBound : run.state.a.length ≤ s.capacity := by
        rcases endValid with ⟨lengths, bounded, _⟩
        calc
          run.state.a.length ≤ run.state.a.length + run.state.b.length := Nat.le_add_right _ _
          _ = run.state.count := lengths.symm
          _ ≤ run.state.capacity := bounded
          _ = s.capacity := endCapacity
      simp only [sequenceRotationCountFrom, ite_eq_right zero]
      change run.rotations = (s.a.length + items.length - 1) / s.capacity
      symm
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.add_mul, Nat.one_mul]
        omega

def sequenceRotationCount (m n : Nat) : Nat :=
  sequenceRotationCountFrom m 0 n

theorem insertManyRotationCount (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (m : Nat) (items : List Int) :
    (insertMany reverseCharge bufferCharge (newModel m) items).rotations =
      sequenceRotationCount m items.length := by
  simpa [sequenceRotationCount, newModel] using
    insertManyRotationCountFrom reverseCharge bufferCharge (newModel m) items
      (by simp [newModel, BufferState.valid])

def insertionSequenceUpperBoundFrom (reverseCharge : Nat → Nat → Nat)
    (bufferCharge : Nat → Nat) (m a n : Nat) : Nat :=
  if m = 0 then n * bufferCharge 3
  else n * insertionBase bufferCharge +
    sequenceRotationCountFrom m a n * rotationSurcharge reverseCharge bufferCharge m

theorem insertManyCostBoundFrom (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) (items : List Int) (valid : s.valid) :
    (insertMany reverseCharge bufferCharge s items).cost ≤
      insertionSequenceUpperBoundFrom reverseCharge bufferCharge
        s.capacity s.a.length items.length := by
  by_cases zero : s.capacity = 0
  · rw [validZeroState s valid zero]
    simpa [insertionSequenceUpperBoundFrom, newModel] using
      Nat.le_of_eq (insertManyZero reverseCharge bufferCharge items).2.2
  · have positive : 0 < s.capacity := by omega
    have cost := (insertManyFromPositive reverseCharge bufferCharge s items valid positive).2.2.2.2
    rw [insertManyRotationCountFrom reverseCharge bufferCharge s items valid] at cost
    simpa [insertionSequenceUpperBoundFrom, zero] using cost

def insertionSequenceUpperBound (reverseCharge : Nat → Nat → Nat)
    (bufferCharge : Nat → Nat) (m n : Nat) : Nat :=
  insertionSequenceUpperBoundFrom reverseCharge bufferCharge m 0 n

theorem insertManyCostBound (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (m : Nat) (items : List Int) :
    (insertMany reverseCharge bufferCharge (newModel m) items).cost ≤
      insertionSequenceUpperBound reverseCharge bufferCharge m items.length := by
  simpa [insertionSequenceUpperBound, newModel] using
    insertManyCostBoundFrom reverseCharge bufferCharge (newModel m) items
      (by simp [newModel, BufferState.valid])
