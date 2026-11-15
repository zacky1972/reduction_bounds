structure BufferState where
  a : List Int
  b : List Int
  count : Nat
  capacity : Nat

def BufferState.valid (s : BufferState) : Prop :=
  s.count = s.a.length + s.b.length ∧ s.count ≤ s.capacity ∧
    (s.b ≠ [] → s.count = s.capacity)

inductive InsertPath where
  | consume (tail : List Int)
  | fill
  | rotate
  | zero

def insertPath (s : BufferState) : InsertPath :=
  match s.b with
  | _ :: tail => .consume tail
  | [] =>
    if s.count < s.capacity then .fill
    else if s.a.isEmpty then .zero
    else .rotate

def insertModel (s : BufferState) (item : Int) : BufferState :=
  match insertPath s with
  | .consume tail => { s with a := item :: s.a, b := tail }
  | .fill => { s with a := item :: s.a, count := s.count + 1 }
  | .rotate => { s with a := [item], b := (enumReverseList s.a).tail }
  | .zero => s

def insertCost (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) : Nat :=
  match insertPath s with
  | .consume _ => consumeCost reverseCharge bufferCharge s.a
  | .fill => fillCost reverseCharge bufferCharge s.a
  | .rotate => rotateCost reverseCharge bufferCharge s.a
  | .zero => zeroCost reverseCharge bufferCharge s.a

theorem insertPreserves (s : BufferState) (item : Int) (valid : s.valid) :
    (insertModel s item).valid := by
  rcases s with ⟨a, b, count, capacity⟩
  cases b with
  | nil =>
    by_cases fills : count < capacity
    · simp [BufferState.valid, insertModel, insertPath, fills] at valid ⊢
      omega
    · cases a with
      | nil => simpa [insertModel, insertPath, fills] using valid
      | cons head tail =>
        simp [BufferState.valid, insertModel, insertPath, fills, enumReverseListValue, List.length_tail] at valid ⊢
        omega
  | cons head tail =>
    simp [BufferState.valid, insertModel, insertPath] at valid ⊢
    omega

theorem bufferRotationSize (s : BufferState) (valid : s.valid)
    (empty : s.b = []) (full : ¬ s.count < s.capacity) :
    s.a.length = s.capacity := by
  rcases valid with ⟨lengths, bounded, _⟩
  simp [empty] at lengths
  omega

theorem insertCostBound (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) (item : Int) (valid : s.valid) :
    (insertModel s item).valid ∧
      insertCost reverseCharge bufferCharge s ≤
        bufferUpperBound reverseCharge bufferCharge s.capacity := by
  refine ⟨insertPreserves s item valid, ?_⟩
  have lengthBound : s.a.length ≤ s.capacity := by
    rcases valid with ⟨lengths, bounded, _⟩
    omega
  cases path : insertPath s with
  | consume _ =>
    simpa [insertCost, path] using consumeBound reverseCharge bufferCharge s.a s.capacity lengthBound
  | fill =>
    simpa [insertCost, path] using fillBound reverseCharge bufferCharge s.a s.capacity lengthBound
  | rotate =>
    simpa [insertCost, path] using rotateBound reverseCharge bufferCharge s.a s.capacity lengthBound
  | zero =>
    simpa [insertCost, path] using zeroBound reverseCharge bufferCharge s.a s.capacity lengthBound

theorem insertZeroCapacity (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
    (s : BufferState) (item : Int) (valid : s.valid) (zeroCapacity : s.capacity = 0) :
    insertModel s item = s ∧ insertCost reverseCharge bufferCharge s = bufferCharge 3 := by
  rcases s with ⟨a, b, count, capacity⟩
  change capacity = 0 at zeroCapacity
  simp [BufferState.valid] at valid
  have ac : a.length = 0 := by omega
  have bc : b.length = 0 := by omega
  have cc : count = 0 := by omega
  simp [insertModel, insertCost, insertPath, zeroCost, List.length_eq_zero_iff.mp ac,
    List.length_eq_zero_iff.mp bc, cc, zeroCapacity]
