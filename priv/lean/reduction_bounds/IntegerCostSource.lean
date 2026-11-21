namespace ReductionBounds.IntegerCostSource
open ReductionBounds.IntegerSize
open ReductionBounds.IntegerAnalysis (Env bindEnv Binary Unary)
open ReductionBounds.IntegerCost (Expr Runs Charges External)

-- Annotation-free reification of the accepted Core Erlang constructors.
-- Atom spellings and the order of Boolean clauses are retained.
inductive Core where
  | integer (value : Int)
  | variable (index : Nat)
  | letOne (index : Nat) (rhs body : Core)
  | call1 (moduleName functionName : String) (argument : Core)
  | call2 (moduleName functionName : String) (left right : Core)
  | case2 (condition : Core) (firstPattern : Bool) (first : Core) (secondPattern : Bool) (second : Core)
  | apply1 (moduleName functionName : String) (argument : Core)
  | apply2 (functionName : String) (counter accumulator : Core)
  deriving DecidableEq

abbrev Names := Nat → Option (String × String)

def UniqueNames (names : Names) : Prop :=
  ∀ a b pair, names a = some pair → names b = some pair → a = b

def isInteger : Core → Bool
  | .integer _ => true | _ => false

def operationCode (moduleName functionName : String) : Option (Sum Binary Unary) :=
  if moduleName = "erlang" then
    match functionName with
    | "+" => some (.inl .add) | "-" => some (.inl .subtract)
    | "*" => some (.inl .multiply) | "bxor" => some (.inl .bitXor)
    | "bsl" => some (.inr .shiftLeft) | "bsr" => some (.inr .shiftRight)
    | "band" => some (.inr .mask) | _ => none
  else none

def widthArgument (op : Unary) (amount : Nat) : Int :=
  match op with
  | .mask => Int.ofNat (2 ^ amount - 1)
  | _ => Int.ofNat amount

def comparisonCode (moduleName functionName : String) : Option Comparison :=
  if moduleName = "erlang" then
    match functionName with
    | "<" => some .lt | "=<" => some .le | "=:=" | "==" => some .eq
    | "=/=" | "/=" => some .ne | ">=" => some .ge | ">" => some .gt | _ => none
  else none

def reversed : Comparison → Comparison
  | .lt => .gt | .le => .ge | .eq => .eq | .ne => .ne | .ge => .le | .gt => .lt

theorem reversedCorrect (op : Comparison) (a b : Int) :
    (reversed op).test a b = op.test b a := by
  cases op <;> simp [reversed, Comparison.test, eq_comm]

def testCode : Core → Option (Comparison × Nat × Int)
  | .call2 m f (.variable index) (.integer constant) => do
    let op ← comparisonCode m f
    some (op, index, constant)
  | .call2 m f (.integer constant) (.variable index) => do
    let op ← comparisonCode m f
    some (reversed op, index, constant)
  | _ => none

def test (env : Env) (condition : Core) : Option Bool := do
  let (op, index, constant) ← testCode condition
  some (op.test (env index) constant)

def unaryCode (moduleName functionName : String) : Option Bool :=
  if moduleName = "erlang" then
    match functionName with | "+" => some true | "-" => some false | _ => none
  else none

inductive Evaluates (program : Core) (functionName : String) (names : Names) (external : External) :
    Core → Env → Int → Prop where
  | integer : Evaluates program functionName names external (.integer value) env value
  | variable : Evaluates program functionName names external (.variable index) env (env index)
  | letOne : Evaluates program functionName names external rhs env value →
      Evaluates program functionName names external body (bindEnv env index value) result →
      Evaluates program functionName names external (.letOne index rhs body) env result
  | binary : operationCode m f = some (.inl op) →
      Evaluates program functionName names external left env a →
      Evaluates program functionName names external right env b →
      Evaluates program functionName names external (.call2 m f left right) env (op.eval a b)
  | unary : operationCode m f = some (.inr op) → constant = widthArgument op amount →
      Evaluates program functionName names external arg env value →
      Evaluates program functionName names external (.call2 m f arg (.integer constant)) env (op.eval amount value)
  | maskLeft : operationCode m f = some (.inr .mask) → mask = widthArgument .mask width →
      isInteger arg = false → Evaluates program functionName names external arg env value →
      Evaluates program functionName names external (.call2 m f (.integer mask) arg) env (maskValue value width)
  | sign : unaryCode m f = some positive → Evaluates program functionName names external arg env value →
      Evaluates program functionName names external (.call1 m f arg) env (if positive then value else 0 - value)
  | first : firstPattern ≠ secondPattern → test env condition = some firstPattern →
      Evaluates program functionName names external first env value →
      Evaluates program functionName names external (.case2 condition firstPattern first secondPattern second) env value
  | second : firstPattern ≠ secondPattern → test env condition = some secondPattern →
      Evaluates program functionName names external second env value →
      Evaluates program functionName names external (.case2 condition firstPattern first secondPattern second) env value
  | call : names key = some (m, f) → unaryCode m f = none → Evaluates program functionName names external arg env value →
      Evaluates program functionName names external (.call1 m f arg) env (external key value).1
  | localCall : names key = some (m, f) → f ≠ functionName →
      Evaluates program functionName names external arg env value →
      Evaluates program functionName names external (.apply1 m f arg) env (external key value).1
  | recur : name = functionName → Evaluates program functionName names external counter env a →
      Evaluates program functionName names external accumulator env b →
      Evaluates program functionName names external program
        (fun index => if index = 0 then a else if index = 1 then b else 0) value →
      Evaluates program functionName names external (.apply2 name counter accumulator) env value

inductive Translates (names : Names) (functionName : String) : Core → Expr → Prop where
  | integer : Translates names functionName (.integer value) (.literal value)
  | variable : Translates names functionName (.variable index) (.variable index)
  | letOne : Translates names functionName rhs a → Translates names functionName body b →
      Translates names functionName (.letOne index rhs body) (.bind index a b)
  | binary : operationCode m f = some (.inl op) → Translates names functionName left a → Translates names functionName right b →
      Translates names functionName (.call2 m f left right) (.binary op a b)
  | unary : operationCode m f = some (.inr op) → constant = widthArgument op amount →
      Translates names functionName arg a →
      Translates names functionName (.call2 m f arg (.integer constant)) (.unary op amount a)
  | maskLeft : operationCode m f = some (.inr .mask) → mask = widthArgument .mask width →
      isInteger arg = false → Translates names functionName arg a →
      Translates names functionName (.call2 m f (.integer mask) arg) (.unary .mask width a)
  | positive : unaryCode m f = some true → Translates names functionName arg a →
      Translates names functionName (.call1 m f arg) (.binary .add (.literal 0) a)
  | negative : unaryCode m f = some false → Translates names functionName arg a →
      Translates names functionName (.call1 m f arg) (.binary .subtract (.literal 0) a)
  | branchTrue : testCode condition = some (op, index, constant) →
      Translates names functionName yes a → Translates names functionName no b →
      Translates names functionName (.case2 condition true yes false no) (.branch op index constant a b)
  | branchFalse : testCode condition = some (op, index, constant) →
      Translates names functionName yes a → Translates names functionName no b →
      Translates names functionName (.case2 condition false no true yes) (.branch op index constant a b)
  | call : names key = some (m, f) → unaryCode m f = none → Translates names functionName arg a →
      Translates names functionName (.call1 m f arg) (.call key a)
  | localCall : names key = some (m, f) → f ≠ functionName →
      Translates names functionName arg a →
      Translates names functionName (.apply1 m f arg) (.call key a)
  | recur : name = functionName → Translates names functionName counter a → Translates names functionName accumulator b →
      Translates names functionName (.apply2 name counter accumulator) (.recur a b)

-- Both the lowering certificate and the run are checked inductive objects.
theorem sourceAgreement (body : Translates names name sourceProgram program)
    (translated : Translates names name source expr)
    (run : Runs program charge external expr env value cost) :
    Evaluates sourceProgram name names external source env value := by
  induction run generalizing source with
  | literal => cases translated; exact .integer
  | «variable» => cases translated; exact .variable
  | bind ra rb ia ib =>
    cases translated with
    | letOne a b => exact .letOne (ia a) (ib b)
  | binary ra rb ia ib =>
    cases translated with
    | binary code a b => exact .binary code (ia a) (ib b)
    | positive code a => cases ra; simpa [Binary.eval] using Evaluates.sign code (ib a)
    | negative code a => cases ra; exact .sign code (ib a)
  | unary ra ia =>
    cases translated with
    | unary code constant a => exact .unary code constant (ia a)
    | maskLeft code constant shape a => exact .maskLeft code constant shape (ia a)
  | yes h run ih =>
    cases translated with
    | branchTrue code a b => exact .first (by decide) (by simp [test, code, h]) (ih a)
    | branchFalse code a b => exact .second (by decide) (by simp [test, code, h]) (ih a)
  | no h run ih =>
    cases translated with
    | branchTrue code a b => exact .second (by decide) (by simp [test, code, h]) (ih b)
    | branchFalse code a b => exact .first (by decide) (by simp [test, code, h]) (ih b)
  | call ra ia =>
    cases translated with
    | call code primitive a => exact .call code primitive (ia a)
    | localCall code different a => exact .localCall code different (ia a)
  | recur ra rb rc ia ib ic =>
    cases translated with
    | recur code a b => exact .recur code (ia a) (ib b) (ic body)

theorem maskWidthUnique (a b : Nat)
    (same : Int.ofNat (2 ^ a - 1) = Int.ofNat (2 ^ b - 1)) : a = b := by
  have equal := Int.ofNat_inj.mp same
  have ap : 0 < 2 ^ a := Nat.pow_pos (by decide)
  have bp : 0 < 2 ^ b := Nat.pow_pos (by decide)
  exact (Nat.pow_right_inj (by decide : 1 < 2)).mp (by omega)

theorem widthArgumentUnique (op : Unary) (a b : Nat) (same : widthArgument op a = widthArgument op b) : a = b := by
  cases op
  · exact Int.ofNat_inj.mp same
  · exact Int.ofNat_inj.mp same
  · exact maskWidthUnique a b same

-- Every source execution can also be represented by the costed model.
theorem sourceComplete (body : Translates names name sourceProgram program) (unique : UniqueNames names)
    (translated : Translates names name source expr)
    (run : Evaluates sourceProgram name names external source env value) (charge : Charges) :
    ∃ cost, Runs program charge external expr env value cost := by
  induction run generalizing expr with
  | integer => cases translated; exact ⟨_, .literal⟩
  | «variable» => cases translated; exact ⟨_, .variable⟩
  | letOne ra rb ia ib =>
    cases translated with
    | letOne a b =>
      obtain ⟨ca, first⟩ := ia a
      obtain ⟨cb, second⟩ := ib b
      exact ⟨_, .bind first second⟩
  | binary code ra rb ia ib =>
    cases translated with
    | binary other a b =>
      have equal := Sum.inl.inj (Option.some.inj (code.symm.trans other))
      cases equal
      obtain ⟨ca, first⟩ := ia a
      obtain ⟨cb, second⟩ := ib b
      exact ⟨_, .binary first second⟩
    | unary other constant a => cases Option.some.inj (code.symm.trans other)
    | maskLeft other constant shape a => cases Option.some.inj (code.symm.trans other)
  | unary code constant ra ia =>
    cases translated with
    | binary other a b => cases Option.some.inj (code.symm.trans other)
    | unary other argument a =>
      have equal := Sum.inr.inj (Option.some.inj (code.symm.trans other))
      cases equal
      have width := widthArgumentUnique _ _ _ (constant.symm.trans argument)
      cases width
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, .unary first⟩
    | maskLeft other argument shape a => simp [isInteger] at shape
  | maskLeft code constant shape ra ia =>
    cases translated with
    | binary other a b => cases Option.some.inj (code.symm.trans other)
    | maskLeft other argument otherShape a =>
      have width := widthArgumentUnique _ _ _ (constant.symm.trans argument)
      cases width
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, .unary first⟩
    | unary other argument a => simp [isInteger] at shape
  | sign code ra ia =>
    cases translated with
    | positive other a =>
      have equal := Option.some.inj (code.symm.trans other)
      cases equal
      obtain ⟨ca, first⟩ := ia a
      have result := Runs.binary (program := program) (charge := charge) (external := external)
        (operation := Binary.add) (Runs.literal (value := 0)) first
      simp only [Binary.eval, Int.zero_add] at result
      exact ⟨_, result⟩
    | negative other a =>
      have equal := Option.some.inj (code.symm.trans other)
      cases equal
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, Runs.binary (operation := Binary.subtract) Runs.literal first⟩
    | call names none a => rw [code] at none; contradiction
  | first different selected ra ia =>
    cases translated with
    | branchTrue code a b =>
      have h := selected
      simp only [test, code] at h
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, .yes (Option.some.inj h) first⟩
    | branchFalse code a b =>
      have h := selected
      simp only [test, code] at h
      obtain ⟨ca, first⟩ := ia b
      exact ⟨_, .no (Option.some.inj h) first⟩
  | second different selected ra ia =>
    cases translated with
    | branchTrue code a b =>
      have h := selected
      simp only [test, code] at h
      obtain ⟨ca, first⟩ := ia b
      exact ⟨_, .no (Option.some.inj h) first⟩
    | branchFalse code a b =>
      have h := selected
      simp only [test, code] at h
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, .yes (Option.some.inj h) first⟩
  | call callName primitive ra ia =>
    cases translated with
    | positive other a => rw [primitive] at other; contradiction
    | negative other a => rw [primitive] at other; contradiction
    | call other none a =>
      have equal := unique _ _ _ callName other
      cases equal
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, .call first⟩
  | localCall callName different ra ia =>
    cases translated with
    | localCall other none a =>
      have equal := unique _ _ _ callName other
      cases equal
      obtain ⟨ca, first⟩ := ia a
      exact ⟨_, .call first⟩
  | recur same ra rb rc ia ib ic =>
    cases translated with
    | recur other a b =>
      obtain ⟨ca, first⟩ := ia a
      obtain ⟨cb, second⟩ := ib b
      obtain ⟨cc, rest⟩ := ic body
      exact ⟨_, .recur first second rest⟩

end ReductionBounds.IntegerCostSource
