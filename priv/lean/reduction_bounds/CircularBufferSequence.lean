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

def insertMany (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (state : BufferState) (items : List Int) : ReductionBounds.Periodic.Run BufferState :=
  ReductionBounds.Periodic.run insertModel (fun s _ => rotationStep s)
    (fun s _ => insertCost reverseCharge bufferCharge s) state items

def bufferRule (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (period : Nat) : ReductionBounds.Periodic.Rule BufferState Int := {
  period, stride := 1, origin := 1
  size := fun s => s.a.length
  invariant := fun s => s.valid ∧ s.capacity = period
  next := insertModel
  event := fun s _ => rotationStep s
  cost := fun s _ => insertCost reverseCharge bufferCharge s
  base := insertionBase bufferCharge
  surcharge := rotationSurcharge reverseCharge bufferCharge period
}

theorem bufferObligations (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (period : Nat) (positive : 0 < period) :
    ReductionBounds.Periodic.Obligations (bufferRule reverseCharge bufferCharge period) := by
  refine ⟨positive, ?_, ?_, ?_, ?_⟩
  · intro s valid
    change s.a.length < period + 1
    obtain ⟨⟨lengths, bounded, _⟩, fixed⟩ := valid
    omega
  · intro s item valid
    exact ⟨insertPreserves s item valid.1, (insertCapacity s item).trans valid.2⟩
  · intro s item valid
    have fixed : s.capacity = period := valid.2
    have nonzero : 0 < s.capacity := by rwa [fixed]
    obtain ⟨balance, landed⟩ := insertAdvance s item valid.1 nonzero
    exact ⟨by simpa [bufferRule, fixed] using balance, Nat.succ_le_of_lt landed⟩
  · intro s item valid
    have fixed : s.capacity = period := valid.2
    have nonzero : 0 < s.capacity := by rwa [fixed]
    simpa [bufferRule, fixed] using insertBudget reverseCharge bufferCharge s valid.1 nonzero

theorem insertManyContents (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) (items : List Int) (valid : s.valid) :
    (insertMany reverseCharge bufferCharge s items).state.contents =
      items.foldl (fifoInsert s.capacity) s.contents := by
  induction items generalizing s with
  | nil => rfl
  | cons item rest ih =>
    simp only [insertMany] at ih
    simp only [insertMany, ReductionBounds.Periodic.run, List.foldl_cons]
    rw [ih (insertModel s item) (insertPreserves s item valid),
      insertCapacity s item, insertContents s item valid]

def fifoLatest (capacity : Nat) (history : List Int) : List Int :=
  history.drop (history.length - capacity)

private theorem fifoInsertLatest (capacity : Nat) (history : List Int) (item : Int) :
    fifoInsert capacity (fifoLatest capacity history) item =
      fifoLatest capacity (history ++ [item]) := by
  have dropped : history.length - capacity ≤ history.length := Nat.sub_le _ _
  unfold fifoInsert fifoLatest
  rw [← List.drop_append_of_le_length (l₂ := [item]) dropped, List.drop_drop]
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  congr 1
  omega

private theorem fifoFoldLatest (capacity : Nat) (initial items : List Int) :
    items.foldl (fifoInsert capacity) (fifoLatest capacity initial) =
      fifoLatest capacity (initial ++ items) := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons, fifoInsertLatest, ih]
    simp [List.append_assoc]

theorem insertManyLatest (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) (items : List Int) (valid : s.valid) :
    (insertMany reverseCharge bufferCharge s items).state.contents =
      fifoLatest s.capacity (s.contents ++ items) := by
  have bound : s.contents.length ≤ s.capacity := by
    rcases valid with ⟨lengths, bounded, _⟩
    simp only [BufferState.contents, List.length_append, List.length_reverse]
    omega
  have initial : fifoLatest s.capacity s.contents = s.contents := by
    simp [fifoLatest, Nat.sub_eq_zero_of_le bound]
  rw [insertManyContents reverseCharge bufferCharge s items valid]
  simpa only [initial] using fifoFoldLatest s.capacity s.contents items

theorem insertManyZero (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (items : List Int) :
    let run := insertMany reverseCharge bufferCharge (newModel 0) items
    run.state = newModel 0 ∧ run.events = 0 ∧ run.cost = items.length * bufferCharge 3 := by
  induction items with
  | nil => simp [insertMany, ReductionBounds.Periodic.run]
  | cons item rest ih =>
    obtain ⟨state, rotations, cost⟩ := ih
    simp only [insertMany] at state rotations cost
    have step := insertZeroCapacity reverseCharge bufferCharge (newModel 0) item (by
      simp [newModel, BufferState.valid]) rfl
    have noRotation : rotationStep (newModel 0) = 0 := rfl
    simp only [insertMany, ReductionBounds.Periodic.run, step.1, step.2, noRotation, state, rotations, cost, Nat.zero_add,
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
    (insertMany reverseCharge bufferCharge s items).events =
      sequenceRotationCountFrom s.capacity s.a.length items.length := by
  by_cases zero : s.capacity = 0
  · rw [validZeroState s valid zero]
    simpa [sequenceRotationCountFrom, newModel] using
      (insertManyZero reverseCharge bufferCharge items).2.1
  · have positive : 0 < s.capacity := by omega
    have checked := bufferObligations reverseCharge bufferCharge s.capacity positive
    have count := ReductionBounds.Periodic.eventCount checked s items ⟨valid, rfl⟩
    change (insertMany reverseCharge bufferCharge s items).events =
      ReductionBounds.Periodic.eventFormula s.capacity 1 1 s.a.length items.length at count
    simpa [sequenceRotationCountFrom, ReductionBounds.Periodic.eventFormula, zero] using count

def sequenceRotationCount (m n : Nat) : Nat :=
  sequenceRotationCountFrom m 0 n

theorem insertManyRotationCount (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (m : Nat) (items : List Int) :
    (insertMany reverseCharge bufferCharge (newModel m) items).events =
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
    have checked := bufferObligations reverseCharge bufferCharge s.capacity positive
    have bound := ReductionBounds.Periodic.costBound checked s items ⟨valid, rfl⟩
    change (insertMany reverseCharge bufferCharge s items).cost ≤
      ReductionBounds.Periodic.costFormula (insertionBase bufferCharge)
        (rotationSurcharge reverseCharge bufferCharge s.capacity)
        (ReductionBounds.Periodic.eventFormula s.capacity 1 1 s.a.length items.length)
        items.length at bound
    simpa [insertionSequenceUpperBoundFrom, sequenceRotationCountFrom,
      ReductionBounds.Periodic.costFormula, ReductionBounds.Periodic.eventFormula, zero] using bound

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
