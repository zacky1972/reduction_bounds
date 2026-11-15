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

def BufferState.contents (s : BufferState) : List Int :=
  s.b ++ s.a.reverse

-- The FIFO specification keeps the newest items in oldest-to-newest order.
def fifoInsert (capacity : Nat) (items : List Int) (item : Int) : List Int :=
  (items ++ [item]).drop (items.length + 1 - capacity)

private theorem fifoInsertRoom (capacity : Nat) (items : List Int) (item : Int)
    (room : items.length < capacity) :
    fifoInsert capacity items item = items ++ [item] := by
  have drops : items.length + 1 - capacity = 0 := by omega
  simp only [fifoInsert, drops, List.drop_zero]

private theorem fifoInsertFull (capacity : Nat) (oldest : Int) (rest : List Int)
    (item : Int) (full : (oldest :: rest).length = capacity) :
    fifoInsert capacity (oldest :: rest) item = rest ++ [item] := by
  have drops : (oldest :: rest).length + 1 - capacity = 1 := by omega
  simp only [fifoInsert, drops, List.cons_append, List.drop_succ_cons, List.drop_zero]

theorem insertContents (s : BufferState) (item : Int) (valid : s.valid) :
    (insertModel s item).contents = fifoInsert s.capacity s.contents item := by
  rcases s with ⟨a, b, count, capacity⟩
  change count = a.length + b.length ∧ count ≤ capacity ∧
    (b ≠ [] → count = capacity) at valid
  rcases valid with ⟨lengths, bounded, full⟩
  cases b with
  | cons oldest rest =>
    have atCapacity := full (by simp)
    simp only [List.length_cons] at lengths
    have contentsFull : (oldest :: (rest ++ a.reverse)).length = capacity := by
      simp only [List.length_cons, List.length_append, List.length_reverse]
      omega
    simpa [BufferState.contents, insertModel, insertPath, List.reverse_cons, List.append_assoc]
      using (fifoInsertFull capacity oldest (rest ++ a.reverse) item contentsFull).symm
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at lengths
    by_cases fills : count < capacity
    · have room : a.reverse.length < capacity := by
        simp only [List.length_reverse]
        omega
      simpa [BufferState.contents, insertModel, insertPath, fills, List.reverse_cons]
        using (fifoInsertRoom capacity a.reverse item room).symm
    · have atCapacity : a.length = capacity := by omega
      cases a with
      | nil =>
        have zero : capacity = 0 := atCapacity.symm
        simp [BufferState.contents, insertModel, insertPath, fifoInsert, zero]
      | cons newest rest =>
        cases reversed : (newest :: rest).reverse with
        | nil =>
          have impossible := congrArg List.length reversed
          simp at impossible
        | cons oldest older =>
          have contentsFull : (oldest :: older).length = capacity := by
            rw [← reversed, List.length_reverse, atCapacity]
          simpa [BufferState.contents, insertModel, insertPath, fills, enumReverseListValue, reversed]
            using (fifoInsertFull capacity oldest older item contentsFull).symm
