namespace ReductionBounds.Execution

open ReductionBounds.Core (CostTree)

abbrev Charges := String → Nat
abbrev Callee := String → Nat → Nat → Nat → Prop
abbrev Outcome := Nat → Nat → Prop
abbrev Env := String → Nat

def bind (env : Env) (name : String) (value : Nat) : Env :=
  fun key => if key = name then value else env key

inductive Operand where
  | local (name : String)
  | literal (value : Nat)

def Operand.read (env : Env) : Operand → Nat
  | .local name => env name
  | .literal value => value

def Operand.scoped (names : List String) : Operand → Bool
  | .local name => decide (name ∈ names)
  | .literal _ => true

inductive Expr where
  | value (operand : Operand)
  | predecessor (operand : Operand)
  | add (left right : Operand)
  | letIn (name : String) (rhs body : Expr)
  | ifZero (test : Expr) (zero : Expr) (name : String) (positive : Expr)
  | call (callee : String) (argument : Operand)
  | recur (argument : Operand)

def Expr.scoped (names : List String) : Expr → Bool
  | .value operand | .predecessor operand | .call _ operand | .recur operand =>
    operand.scoped names
  | .add left right => left.scoped names && right.scoped names
  | .letIn name rhs body => rhs.scoped names && body.scoped (name :: names)
  | .ifZero test zero name positive =>
    test.scoped names && zero.scoped names && positive.scoped (name :: names)

def forget (name : String) (names : List String) : List String :=
  names.filter (fun known => known != name)

def Expr.afterBind (rhs : Expr) (name : String) (names : List String) : List String :=
  match rhs with
  | .predecessor _ => name :: forget name names
  | _ => forget name names

def Expr.allowed (recursive : Bool) (inputNames predNames : List String) : Expr → Bool
  | .predecessor (.local name) => recursive && decide (name ∈ inputNames)
  | .recur (.local name) => recursive && decide (name ∈ predNames)
  | .predecessor _ | .recur _ => false
  | .letIn name rhs body => rhs.allowed recursive inputNames predNames &&
      body.allowed recursive (forget name inputNames) (rhs.afterBind name predNames)
  | .ifZero test zero name positive => test.allowed recursive inputNames predNames &&
      (zero.allowed recursive inputNames predNames &&
        positive.allowed recursive (forget name inputNames) (forget name predNames))
  | _ => true

def Knows (env : Env) (value : Nat) (names : List String) : Prop :=
  ∀ name ∈ names, env name = value

private theorem forgetSound (known : Knows env value names) :
    Knows (bind env name bound) value (forget name names) := by
  intro key member
  have ⟨present, different⟩ := List.mem_filter.mp member
  have ne : key ≠ name := by simpa using different
  simp [bind, ne, known key present]

private theorem readKnown {argument : Operand}
    (allowed : (match argument with
      | .local name => recursive && decide (name ∈ names)
      | .literal _ => false) = true)
    (known : Knows env value names) :
    recursive = true ∧ argument.read env = value := by
  cases argument with
  | literal => contradiction
  | «local» name =>
    have parts := Bool.and_eq_true_iff.mp allowed
    exact ⟨parts.1, known name (of_decide_eq_true parts.2)⟩

private theorem recurIndex (allowed : (Expr.recur argument).allowed recursive inputs preds = true)
    (known : Knows env (n - 1) preds) :
    recursive = true ∧ argument.read env = n - 1 :=
  readKnown (by cases argument <;> exact allowed) known

private theorem predecessorInput
    (allowed : (Expr.predecessor operand).allowed recursive inputs preds = true)
    (known : Knows env n inputs) : operand.read env = n :=
  (readKnown (by cases operand <;> exact allowed) known).2

def Expr.tree (charge cap : Charges) (previous : Nat) : Expr → CostTree
  | .value _ => .paid 0
  | .predecessor _ => .paid (charge "subtract")
  | .add _ _ => .paid (charge "add")
  | .letIn _ rhs body =>
    .seq (.paid (charge "bind")) (.seq (rhs.tree charge cap previous) (body.tree charge cap previous))
  | .ifZero test zero _ positive =>
    .seq (.paid (charge "branch")) (.seq (test.tree charge cap previous)
      (.branch (zero.tree charge cap previous) (positive.tree charge cap previous)))
  | .call callee _ => .seq (.paid (charge "call")) (.paid (cap callee))
  | .recur _ => .seq (.paid (charge "recursive_call")) (.paid previous)

inductive Eval (charge : Charges) (external : Callee) (self : Nat → Outcome) (n : Nat) :
    Env → Expr → Nat → Nat → Prop where
  | value : Eval charge external self n env (.value operand) (operand.read env) 0
  | predecessor : Eval charge external self n env (.predecessor operand) (operand.read env - 1) (charge "subtract")
  | add : Eval charge external self n env (.add left right)
      (left.read env + right.read env) (charge "add")
  | letIn : Eval charge external self n env rhs a before →
      Eval charge external self n (bind env name a) body result afterCost →
      Eval charge external self n env (.letIn name rhs body) result (charge "bind" + (before + afterCost))
  | zero : Eval charge external self n env test 0 tested →
      Eval charge external self n env zero result cost →
      Eval charge external self n env (.ifZero test zero name positive) result
        (charge "branch" + (tested + cost))
  | positive : Eval charge external self n env test value tested → value ≠ 0 →
      Eval charge external self n (bind env name value) positive result cost →
      Eval charge external self n env (.ifZero test zero name positive) result
        (charge "branch" + (tested + cost))
  | call : external callee (argument.read env) result cost →
      Eval charge external self n env (.call callee argument) result (charge "call" + cost)
  | recur : self (argument.read env) result cost →
      Eval charge external self n env (.recur argument) result (charge "recursive_call" + cost)

def Expr.callees : Expr → List String
  | .letIn _ rhs body => rhs.callees ++ body.callees
  | .ifZero test yes _ no => test.callees ++ (yes.callees ++ no.callees)
  | .call callee _ => [callee]
  | _ => []

def CallBounds (external : Callee) (cap : Charges) (names : List String) : Prop :=
  ∀ callee ∈ names, ∀ arg result cost, external callee arg result cost → cost ≤ cap callee

def CallTotal (external : Callee) (names : List String) : Prop :=
  ∀ callee ∈ names, ∀ arg, ∃ result cost, external callee arg result cost

private theorem CallBounds.restrict (covers : CallBounds external cap names)
    (included : ∀ name ∈ subset, name ∈ names) : CallBounds external cap subset :=
  fun name member => covers name (included name member)

private theorem CallTotal.restrict (calls : CallTotal external names)
    (included : ∀ name ∈ subset, name ∈ names) : CallTotal external subset :=
  fun name member => calls name (included name member)

private theorem inLeft {name : String} {left right : List String} (member : name ∈ left) :
    name ∈ left ++ right := List.mem_append.mpr (.inl member)

private theorem inRight {name : String} {left right : List String} (member : name ∈ right) :
    name ∈ left ++ right := List.mem_append.mpr (.inr member)

private theorem Eval.bindSound (run : Eval charge external self n env rhs result cost)
    (allowed : rhs.allowed recursive inputs preds = true)
    (current : Knows env n inputs) (known : Knows env (n - 1) preds) :
    Knows (bind env name result) (n - 1) (rhs.afterBind name preds) := by
  cases run <;> try exact forgetSound known
  intro key member
  rcases List.mem_cons.mp member with rfl | present
  · simp [bind, predecessorInput allowed current]
  · exact forgetSound known key present

theorem Eval.pathCost (run : Eval charge external self n env expr result cost)
    (covers : CallBounds external cap expr.callees) (recBound : recursive = true → ∀ r c, self (n - 1) r c → c ≤ previous)
    (allowed : expr.allowed recursive inputs preds = true)
    (current : Knows env n inputs) (known : Knows env (n - 1) preds) :
    CostTree.PathCost (expr.tree charge cap previous) cost := by
  induction run generalizing inputs preds with
  | value | predecessor | add => exact .paid (Nat.le_refl _)
  | letIn before _ rhsIH bodyIH =>
    have parts := Bool.and_eq_true_iff.mp allowed
    exact .seq (.paid (Nat.le_refl _))
      (.seq (rhsIH (covers.restrict (fun _ => inLeft)) parts.1 current known)
        (bodyIH (covers.restrict (fun _ => inRight)) parts.2
          (forgetSound current) (before.bindSound parts.1 current known)))
  | zero _ _ testIH armIH =>
    have ⟨testAllowed, arms⟩ := Bool.and_eq_true_iff.mp allowed
    exact .seq (.paid (Nat.le_refl _)) (.seq
      (testIH (covers.restrict (fun _ => inLeft)) testAllowed current known)
      (.success (armIH (covers.restrict (fun _ h => inRight (inLeft h)))
        (Bool.and_eq_true_iff.mp arms).1 current known)))
  | positive _ _ _ testIH armIH =>
    have ⟨testAllowed, arms⟩ := Bool.and_eq_true_iff.mp allowed
    exact .seq (.paid (Nat.le_refl _)) (.seq
      (testIH (covers.restrict (fun _ => inLeft)) testAllowed current known)
      (.failure (armIH (covers.restrict (fun _ h => inRight (inRight h)))
        (Bool.and_eq_true_iff.mp arms).2 (forgetSound current) (forgetSound known))))
  | call calleeRun => exact .seq (.paid (Nat.le_refl _)) (.paid (covers _ (by simp [Expr.callees]) _ _ _ calleeRun))
  | recur selfRun =>
    have ⟨enabled, atPredecessor⟩ := recurIndex allowed known
    rw [atPredecessor] at selfRun
    exact .seq (.paid (Nat.le_refl _)) (.paid (recBound enabled _ _ selfRun))

theorem Expr.total (expr : Expr) (env : Env) (allowed : expr.allowed recursive inputs preds = true)
    (current : Knows env n inputs) (known : Knows env (n - 1) preds)
    (calls : CallTotal external expr.callees) (recTotal : recursive = true → ∃ r c, self (n - 1) r c) :
    ∃ result cost, Eval charge external self n env expr result cost := by
  induction expr generalizing env inputs preds with
  | value => exact ⟨_, _, .value⟩
  | predecessor => exact ⟨_, _, .predecessor⟩
  | add => exact ⟨_, _, .add⟩
  | call callee argument =>
    obtain ⟨result, cost, run⟩ := calls callee (by simp [Expr.callees]) (argument.read env)
    exact ⟨result, _, .call run⟩
  | recur argument =>
    obtain ⟨enabled, atPredecessor⟩ := recurIndex allowed known
    obtain ⟨result, cost, run⟩ := recTotal enabled
    rw [← atPredecessor] at run
    exact ⟨result, _, .recur run⟩
  | letIn name rhs body rhsIH bodyIH =>
    have parts := Bool.and_eq_true_iff.mp allowed
    obtain ⟨first, firstCost, before⟩ := rhsIH env parts.1 current known (calls.restrict (fun _ => inLeft))
    obtain ⟨result, cost, afterRun⟩ := bodyIH (bind env name first) parts.2 (forgetSound current)
      (before.bindSound parts.1 current known) (calls.restrict (fun _ => inRight))
    exact ⟨result, _, .letIn before afterRun⟩
  | ifZero test zero name positive testIH zeroIH positiveIH =>
    have ⟨testAllowed, arms⟩ := Bool.and_eq_true_iff.mp allowed
    have ⟨zeroAllowed, positiveAllowed⟩ := Bool.and_eq_true_iff.mp arms
    obtain ⟨value, tested, evalTest⟩ := testIH env testAllowed current known (calls.restrict (fun _ => inLeft))
    by_cases isZero : value = 0
    · subst value
      obtain ⟨result, cost, run⟩ := zeroIH env zeroAllowed current known
        (calls.restrict (fun _ h => inRight (inLeft h)))
      exact ⟨result, _, .zero evalTest run⟩
    · obtain ⟨result, cost, run⟩ := positiveIH (bind env name value) positiveAllowed
        (forgetSound current) (forgetSound known) (calls.restrict (fun _ h => inRight (inRight h)))
      exact ⟨result, _, .positive evalTest isZero run⟩

structure Program where
  parameter : String
  defaultBinder : String
  zero : Expr
  positive : Expr

def Program.callees (program : Program) : List String :=
  program.zero.callees ++ program.positive.callees

def Program.inputNames (program : Program) : List String :=
  [program.parameter, program.defaultBinder]

def Program.env (program : Program) (n : Nat) : Env :=
  fun key => if key ∈ program.inputNames then n else 0

private theorem Program.knowsInput (program : Program) (n : Nat) :
    Knows (program.env n) n program.inputNames := by
  intro name member
  simp [Program.env, member]

def Program.valid (program : Program) : Bool :=
  program.zero.allowed false program.inputNames [] &&
    program.positive.allowed true program.inputNames []

def Program.scoped (program : Program) : Bool :=
  program.zero.scoped [program.parameter] && program.positive.scoped program.inputNames

def Program.upper (program : Program) (charge cap : Charges) : Nat → Nat
  | 0 => charge "branch" + (program.zero.tree charge cap 0).upperBound
  | n + 1 => charge "branch" +
      (program.positive.tree charge cap (upper program charge cap n)).upperBound

-- Fuel indexes finite derivations by their maximum call depth. The semantics
-- calls the actual operand at a recursive site, without restricting its size.
def Program.runsAt (program : Program) (charge : Charges) (external : Callee) :
    Nat → Nat → Outcome
  | 0 => fun _ _ _ => False
  | fuel + 1 => fun n result cost =>
    ∃ localCost, Eval charge external (runsAt program charge external fuel) n (program.env n)
        (if n = 0 then program.zero else program.positive) result localCost ∧
      cost = charge "branch" + localCost

def Program.runs (program : Program) (charge : Charges) (external : Callee)
    (n result cost : Nat) : Prop :=
  ∃ fuel, program.runsAt charge external fuel n result cost

private theorem emptyKnowledge : Knows env value [] := by
  simp [Knows]

theorem Program.bounded (program : Program) (charge cap : Charges) (external : Callee)
    (valid : program.valid = true) (contracts : CallBounds external cap program.callees) (n result cost : Nat)
    (execution : program.runs charge external n result cost) :
    cost ≤ program.upper charge cap n := by
  have parts := Bool.and_eq_true_iff.mp valid
  obtain ⟨fuel, run⟩ := execution
  induction fuel generalizing n result cost with
  | zero => contradiction
  | succ fuel ih =>
    obtain ⟨localCost, run, rfl⟩ := run
    cases n with
    | zero =>
      have body : Eval charge external (program.runsAt charge external fuel) 0 (program.env 0)
          program.zero result localCost := by simpa using run
      exact Nat.add_le_add_left (CostTree.pathCostBound
        (body.pathCost (contracts.restrict (fun _ => inLeft)) (fun impossible => by contradiction) parts.1 (program.knowsInput 0) emptyKnowledge)) _
    | succ n =>
      have body : Eval charge external (program.runsAt charge external fuel) (n + 1) (program.env (n + 1))
          program.positive result localCost := by simpa using run
      exact Nat.add_le_add_left (CostTree.pathCostBound
        (body.pathCost (contracts.restrict (fun _ => inRight)) (fun _ => ih n) parts.2 (program.knowsInput (n + 1)) emptyKnowledge)) _

theorem Program.terminates (program : Program) (charge : Charges) (external : Callee)
    (valid : program.valid = true) (contracts : CallTotal external program.callees) (n : Nat) :
    ∃ result cost, program.runsAt charge external (n + 1) n result cost := by
  have parts := Bool.and_eq_true_iff.mp valid
  induction n with
  | zero =>
    obtain ⟨result, cost, run⟩ := program.zero.total (n := 0) (self := program.runsAt charge external 0)
      (program.env 0) parts.1 (program.knowsInput 0) emptyKnowledge (contracts.restrict (fun _ => inLeft))
      (fun impossible => by contradiction)
    exact ⟨result, _, cost, run, rfl⟩
  | succ n ih =>
    obtain ⟨result, cost, run⟩ :=
      program.positive.total (n := n + 1) (self := program.runsAt charge external (n + 1))
        (program.env (n + 1)) parts.2 (program.knowsInput (n + 1)) emptyKnowledge (contracts.restrict (fun _ => inRight)) (fun _ => ih)
    exact ⟨result, _, cost, run, rfl⟩

end ReductionBounds.Execution
