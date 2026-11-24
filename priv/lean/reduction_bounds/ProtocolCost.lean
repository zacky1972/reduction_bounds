namespace ReductionBounds.ProtocolCost

open ReductionBounds.Protocol (Contract Event)
open ReductionBounds.ProtocolConditions (Spec Rule Observation RowsHold CountsHold findRule)

inductive Feature where
  | bytes (name : String)
  | structureSize (name : String)
  | bits (name : String)
  deriving DecidableEq

def actualFeature (observation : Observation) : Feature → Nat
  | .bytes name => ((observation.data.lookup name).map (·.bytes)).getD 0
  | .structureSize name => ((observation.data.lookup name).map (·.structureSize)).getD 0
  | .bits name => ((observation.integers.lookup name).map ReductionBounds.IntegerSize.magnitudeBits).getD 0

def boundFeature (spec : Spec) : Feature → Nat
  | .bytes name => ((spec.dataBounds.lookup name).map (·.bytes)).getD 0
  | .structureSize name => ((spec.dataBounds.lookup name).map (·.structureSize)).getD 0
  | .bits name => ((spec.integerBounds.lookup name).bind (·.magnitudeBits)).getD 0

def Supported (spec : Spec) (rule : Rule) : Feature → Prop
  | .bytes name | .structureSize name => name ∈ rule.data
  | .bits name => name ∈ rule.integers ∧
      ((spec.integerBounds.lookup name).bind (·.magnitudeBits)).isSome = true

instance (spec : Spec) (rule : Rule) (feature : Feature) : Decidable (Supported spec rule feature) := by
  cases feature <;> unfold Supported <;> infer_instance

theorem featureBound (spec : Spec) (rule : Rule) (observation : Observation) (feature : Feature)
    (supported : Supported spec rule feature)
    (held : ReductionBounds.ProtocolConditions.RowHolds spec rule observation) :
    actualFeature observation feature ≤ boundFeature spec feature := by
  cases feature with
  | bytes name =>
    have h := held.2.1 name supported
    cases a : spec.dataBounds.lookup name <;> cases b : observation.data.lookup name <;>
      simp [ReductionBounds.ProtocolConditions.DataAt, a, b] at h
    simpa [actualFeature, boundFeature, a, b] using h.1
  | structureSize name =>
    have h := held.2.1 name supported
    cases a : spec.dataBounds.lookup name <;> cases b : observation.data.lookup name <;>
      simp [ReductionBounds.ProtocolConditions.DataAt, a, b] at h
    simpa [actualFeature, boundFeature, a, b] using h.2
  | bits name =>
    have h := held.2.2 name supported.1
    cases a : spec.integerBounds.lookup name with
    | none => simp [Supported, a] at supported
    | some bound =>
      cases bits : bound.magnitudeBits with
      | none => simp [Supported, a, bits] at supported
      | some width =>
        cases b : observation.integers.lookup name with
        | none => simp [ReductionBounds.ProtocolConditions.IntegerAt, a, b] at h
        | some value =>
          have magnitude := ReductionBounds.IntegerSize.magnitudeBound bound value width
            (by simpa [ReductionBounds.ProtocolConditions.IntegerAt, a, b] using h) bits
          simpa [actualFeature, boundFeature, a, b, bits] using
            ReductionBounds.IntegerSize.magnitudeBitsMinimal value width magnitude

inductive Expr where
  | constant (value : Nat)
  | charge (name : String)
  | feature (value : Feature)
  | add (left right : Expr)
  | mul (left right : Expr)
  | max (left right : Expr)
  deriving DecidableEq

def Expr.eval (charge : String → Nat) (parameter : Feature → Nat) : Expr → Nat
  | .constant n => n
  | .charge name => charge name
  | .feature value => parameter value
  | .add a b => a.eval charge parameter + b.eval charge parameter
  | .mul a b => a.eval charge parameter * b.eval charge parameter
  | .max a b => Nat.max (a.eval charge parameter) (b.eval charge parameter)

def Expr.features : Expr → List Feature
  | .constant _ | .charge _ => []
  | .feature value => [value]
  | .add a b | .mul a b | .max a b => a.features ++ b.features

def Expr.cap (spec : Spec) : Expr → Expr
  | .feature value => .constant (boundFeature spec value)
  | .add a b => .add (a.cap spec) (b.cap spec)
  | .mul a b => .mul (a.cap spec) (b.cap spec)
  | .max a b => .max (a.cap spec) (b.cap spec)
  | expr => expr

theorem Expr.capCorrect (spec : Spec) (expr : Expr) (charge : String → Nat) (parameter : Feature → Nat) :
    (expr.cap spec).eval charge parameter = expr.eval charge (boundFeature spec) := by
  induction expr <;> simp_all [Expr.cap, Expr.eval]

theorem Expr.monotone (expr : Expr) (charge : String → Nat) (a b : Feature → Nat)
    (bounded : ∀ f ∈ expr.features, a f ≤ b f) : expr.eval charge a ≤ expr.eval charge b := by
  induction expr with
  | constant | charge => exact Nat.le_refl _
  | feature value => exact bounded value (by simp [Expr.features])
  | add left right ihLeft ihRight =>
    have h := List.forall_mem_append.mp (by simpa [Expr.features] using bounded)
    exact Nat.add_le_add (ihLeft h.1) (ihRight h.2)
  | mul left right ihLeft ihRight =>
    have h := List.forall_mem_append.mp (by simpa [Expr.features] using bounded)
    exact Nat.mul_le_mul (ihLeft h.1) (ihRight h.2)
  | max left right ihLeft ihRight =>
    have h := List.forall_mem_append.mp (by simpa [Expr.features] using bounded)
    exact Nat.max_le.mpr ⟨Nat.le_trans (ihLeft h.1) (Nat.le_max_left _ _),
      Nat.le_trans (ihRight h.2) (Nat.le_max_right _ _)⟩

structure Entry where
  before : String
  event : Event
  counter : String
  expression : Expr

structure Group where
  owner : String
  counter : String
  limit : Nat
  alternatives : List Expr

def findEntry (entries : List Entry) (before : String) (event : Event) : Option Entry :=
  entries.find? (fun entry => entry.before == before && entry.event == event)

def EntryGood (spec : Spec) (groups : List Group) (entry : Entry) : Prop :=
  match findRule spec entry.before entry.event.name, entry.event.owner with
  | some rule, some owner =>
    (∀ f ∈ entry.expression.features, Supported spec rule f) ∧
    (entry.counter = "total_events" ∨ entry.counter ∈ rule.counts) ∧
    ∃ group ∈ groups, group.owner = owner ∧ group.counter = entry.counter ∧
      entry.expression ∈ group.alternatives
  | _, _ => False

instance (spec : Spec) (groups : List Group) (entry : Entry) : Decidable (EntryGood spec groups entry) := by
  unfold EntryGood
  cases findRule spec entry.before entry.event.name <;> cases entry.event.owner <;> infer_instance

def CostSpecGood (contract : Contract) (spec : Spec) (entries : List Entry) (groups : List Group) : Prop :=
  (∀ entry ∈ entries, EntryGood spec groups entry) ∧
  (∀ group ∈ groups, (group.counter, group.limit) ∈ spec.countBounds) ∧
  contract.transitions.all (fun edge => contract.events.all (fun event =>
    if event.name == edge.event && event.owner.isSome then
      (findEntry entries edge.before event).isSome else true)) = true

instance (contract : Contract) (spec : Spec) (entries : List Entry) (groups : List Group) :
    Decidable (CostSpecGood contract spec entries groups) := by
  unfold CostSpecGood
  infer_instance

def maximum (spec : Spec) (charge : String → Nat) : List Expr → Nat
  | [] => 0
  | expr :: rest => Nat.max (expr.eval charge (boundFeature spec)) (maximum spec charge rest)

theorem maximumMember (spec : Spec) (charge : String → Nat) (expr : Expr) (xs : List Expr)
    (member : expr ∈ xs) : expr.eval charge (boundFeature spec) ≤ maximum spec charge xs := by
  induction xs with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

def sumWith {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | head :: rest => f head + sumWith f rest

theorem sumMember {α : Type} (f : α → Nat) (xs : List α) (x : α) (member : x ∈ xs) :
    f x ≤ sumWith f xs := by
  induction xs with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih member) (Nat.le_add_left _ _)

theorem sumAdd {α : Type} (f g : α → Nat) (xs : List α) :
    sumWith (fun x => f x + g x) xs = sumWith f xs + sumWith g xs := by
  induction xs <;> simp_all [sumWith] <;> omega

theorem sumMono {α : Type} (f g : α → Nat) (xs : List α)
    (bounded : ∀ x ∈ xs, f x ≤ g x) : sumWith f xs ≤ sumWith g xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons head rest ih =>
    exact Nat.add_le_add (bounded head (by simp)) (ih (fun x h => bounded x (by simp [h])))

def tick (spec : Spec) (before : String) (event : Event) (counter : String) : Nat :=
  if counter == "total_events" then 1 else
    match findRule spec before event.name with
    | none => 0
    | some rule => if rule.counts.contains counter then 1 else 0

abbrev Charges := String → String → Nat

def stepBudget (spec : Spec) (groups : List Group) (charge : Charges) (owner before : String)
    (event : Event) : Nat :=
  sumWith (fun group => if group.owner = owner then
    tick spec before event group.counter * maximum spec (charge owner) group.alternatives else 0) groups

def localCost (entries : List Entry) (charge : Charges) (owner before : String)
    (event : Event) (observation : Observation) : Nat :=
  if event.owner = some owner then
    match findEntry entries before event with
    | none => 0
    | some entry => entry.expression.eval (charge owner) (actualFeature observation)
  else 0

theorem localBound (spec : Spec) (entries : List Entry) (groups : List Group) (charge : Charges)
    (owner before : String) (event : Event) (observation : Observation) (rule : Rule)
    (foundRule : findRule spec before event.name = some rule)
    (held : ReductionBounds.ProtocolConditions.RowHolds spec rule observation)
    (good : ∀ entry ∈ entries, EntryGood spec groups entry) :
    localCost entries charge owner before event observation ≤ stepBudget spec groups charge owner before event := by
  unfold localCost
  split
  next owned =>
    cases found : findEntry entries before event with
    | none => exact Nat.zero_le _
    | some entry =>
      change entries.find? (fun entry => entry.before == before && entry.event == event) = some entry at found
      have matched := Bool.and_eq_true_iff.mp (show (entry.before == before && entry.event == event) = true from List.find?_some (p := fun (e : Entry) => e.before == before && e.event == event) found)
      have beforeEq : entry.before = before := of_decide_eq_true matched.1
      have eventEq : entry.event = event := of_decide_eq_true matched.2
      have valid := good entry (List.mem_of_find?_eq_some found)
      simp only [EntryGood, beforeEq, eventEq, foundRule, owned] at valid
      obtain ⟨supported, counted, group, member, groupOwner, groupCounter, alternative⟩ := valid
      have exprBound := entry.expression.monotone (charge owner) _ _
        (fun f h => featureBound spec rule observation f (supported f h) held)
      have capBound := maximumMember spec (charge owner) entry.expression group.alternatives alternative
      have one : tick spec before event group.counter = 1 := by
        rw [groupCounter]
        rcases counted with counted | counted <;> simp [tick, counted, foundRule]
      have groupBound := sumMember (fun g => if g.owner = owner then
        tick spec before event g.counter * maximum spec (charge owner) g.alternatives else 0) groups group member
      simp only [groupOwner, one, Nat.one_mul] at groupBound
      exact Nat.le_trans exprBound (Nat.le_trans capBound groupBound)
  next => exact Nat.zero_le _

def traceCost (entries : List Entry) (charge : Charges) (owner before : String) :
    List Event → List String → List Observation → Nat
  | event :: events, after :: states, observation :: observations =>
    localCost entries charge owner before event observation + traceCost entries charge owner after events states observations
  | _, _, _ => 0

def credits (spec : Spec) (groups : List Group) (charge : Charges) (owner before : String)
    (events : List Event) (states : List String) : Nat :=
  sumWith (fun group => if group.owner = owner then
    ReductionBounds.ProtocolConditions.countFrom spec before group.counter events states *
      maximum spec (charge owner) group.alternatives else 0) groups

theorem creditsCons (spec : Spec) (groups : List Group) (charge : Charges) (owner before after : String)
    (event : Event) (events : List Event) (states : List String) :
    credits spec groups charge owner before (event :: events) (after :: states) =
      stepBudget spec groups charge owner before event + credits spec groups charge owner after events states := by
  unfold credits stepBudget
  rw [← sumAdd]
  congr 1
  funext group
  split <;> simp [ReductionBounds.ProtocolConditions.countFrom, tick, Nat.add_mul] <;> rfl

theorem traceBound (spec : Spec) (entries : List Entry) (groups : List Group) (charge : Charges)
    (owner before : String) (events : List Event) (states : List String) (observations : List Observation)
    (held : RowsHold spec before events states observations)
    (good : ∀ entry ∈ entries, EntryGood spec groups entry) :
    traceCost entries charge owner before events states observations ≤ credits spec groups charge owner before events states := by
  induction events generalizing before states observations with
  | nil => cases states <;> cases observations <;> exact Nat.zero_le _
  | cons event events ih =>
    cases states with
    | nil => cases observations <;> simp [RowsHold] at held
    | cons after states =>
      cases observations with
      | nil => simp [RowsHold] at held
      | cons observation observations =>
        cases found : findRule spec before event.name with
        | none => simp [RowsHold, found] at held
        | some rule =>
          have parts : ReductionBounds.ProtocolConditions.RowHolds spec rule observation ∧
              RowsHold spec after events states observations := by simpa [RowsHold, found] using held
          rw [creditsCons]
          exact Nat.add_le_add (localBound spec entries groups charge owner before event observation rule found parts.1 good)
            (ih after states observations parts.2)

def ownerBound (spec : Spec) (groups : List Group) (charge : Charges) (owner : String) : Nat :=
  sumWith (fun group => if group.owner = owner then
    group.limit * maximum spec (charge owner) group.alternatives else 0) groups

theorem costSafety (contract : Contract) (spec : Spec) (entries : List Entry) (groups : List Group)
    (charge : Charges) (owner before : String) (events : List Event) (states : List String)
    (observations : List Observation) (good : CostSpecGood contract spec entries groups)
    (rows : RowsHold spec before events states observations)
    (counts : CountsHold spec before events states) :
    traceCost entries charge owner before events states observations ≤ ownerBound spec groups charge owner := by
  apply Nat.le_trans (traceBound spec entries groups charge owner before events states observations rows good.1)
  apply sumMono
  intro group member
  split
  · exact Nat.mul_le_mul_right _ (counts _ (good.2.1 group member))
  · exact Nat.le_refl _

theorem prefixCostLe (entries : List Entry) (charge : Charges) (owner before : String)
    (events : List Event) (states : List String) (observations : List Observation) (n : Nat) :
    traceCost entries charge owner before (events.take n) (states.take n) (observations.take n) ≤
      traceCost entries charge owner before events states observations := by
  induction events generalizing before states observations n with
  | nil => simp [traceCost]
  | cons event events ih =>
    cases states <;> cases observations <;> cases n <;> simp only [List.take_zero, List.take_succ_cons, traceCost]
    all_goals try exact Nat.zero_le _
    exact Nat.add_le_add_left (ih _ _ _ _) _

theorem prefixCostSafety (contract : Contract) (spec : Spec) (entries : List Entry) (groups : List Group)
    (charge : Charges) (owner before : String) (events : List Event) (states : List String)
    (observations : List Observation) (good : CostSpecGood contract spec entries groups)
    (rows : RowsHold spec before events states observations) (counts : CountsHold spec before events states)
    (n : Nat) : traceCost entries charge owner before (events.take n) (states.take n) (observations.take n) ≤
      ownerBound spec groups charge owner :=
  Nat.le_trans (prefixCostLe entries charge owner before events states observations n)
    (costSafety contract spec entries groups charge owner before events states observations good rows counts)

def maximumExpr (spec : Spec) : List Expr → Expr
  | [] => .constant 0
  | expr :: rest => .max (expr.cap spec) (maximumExpr spec rest)

def boundExpr (spec : Spec) (owner : String) : List Group → Expr
  | [] => .constant 0
  | group :: rest => if group.owner = owner then
      .add (.mul (.constant group.limit) (maximumExpr spec group.alternatives)) (boundExpr spec owner rest)
    else boundExpr spec owner rest

theorem maximumExprCorrect (spec : Spec) (xs : List Expr) (charge : String → Nat) :
    (maximumExpr spec xs).eval charge (fun _ => 0) = maximum spec charge xs := by
  induction xs <;> simp_all [maximumExpr, maximum, Expr.eval, Expr.capCorrect]

theorem boundExprCorrect (spec : Spec) (groups : List Group) (charge : Charges) (owner : String) :
    (boundExpr spec owner groups).eval (charge owner) (fun _ => 0) = ownerBound spec groups charge owner := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    by_cases h : group.owner = owner <;>
      simp [boundExpr, ownerBound, sumWith, h, Expr.eval, maximumExprCorrect, ih]

end ReductionBounds.ProtocolCost
