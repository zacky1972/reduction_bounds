namespace ReductionBounds.IntegerAnalysis
open ReductionBounds.IntegerSize

abbrev Env := Nat → Int
abbrev Sizes := Nat → Domain
abbrev State := Option Sizes

def bindEnv (env : Env) (index : Nat) (value : Int) : Env :=
  fun key => if key = index then value else env key

def Covers (state : State) (env : Env) : Prop :=
  match state with
  | none => False
  | some sizes => ∀ index, (sizes index).Holds (env index)

def bindState (state : State) (index : Nat) (size : Domain) : State :=
  match state, size.normalize with
  | some sizes, .bounded bounds => some (fun key => if key = index then .bounded bounds else sizes key)
  | _, _ => none

theorem bindCovers (state : State) (env : Env) (index : Nat) (size : Domain) (value : Int)
    (covered : Covers state env) (held : size.Holds value) :
    Covers (bindState state index size) (bindEnv env index value) := by
  have normalized := (normalizeSound size value).mpr held
  cases state with
  | none => exact False.elim covered
  | some sizes =>
    cases sizeCase : size.normalize with
    | unreachable => simp [sizeCase, Domain.Holds] at normalized
    | bounded bounds =>
      simp only [sizeCase, Domain.Holds] at normalized
      simp only [bindState, sizeCase, Covers]
      intro key
      by_cases same : key = index
      · subst key
        simpa [bindState, sizeCase, bindEnv, Domain.Holds] using normalized
      · simpa [bindState, sizeCase, bindEnv, same] using covered key

def refineState (state : State) (op : Comparison) (index : Nat) (constant : Int) (truth : Bool) : State :=
  match state with
  | none => none
  | some sizes => bindState state index ((sizes index).assume op constant truth)

theorem refineCovers (state : State) (env : Env) (op : Comparison) (index : Nat) (constant : Int) (truth : Bool)
    (covered : Covers state env) (branch : op.test (env index) constant = truth) :
    Covers (refineState state op index constant truth) env := by
  cases state with
  | none => exact False.elim covered
  | some sizes =>
    have narrowed := assumeSound (sizes index) op constant (env index) truth (covered index) branch
    have bound := bindCovers (some sizes) env index _ (env index) covered narrowed
    have unchanged : bindEnv env index (env index) = env := by
      funext key
      by_cases same : key = index <;> simp [bindEnv, same]
    simpa [refineState, unchanged] using bound

inductive Binary where
  | add | subtract | multiply | bitXor
  deriving DecidableEq

def Binary.eval : Binary → Int → Int → Int
  | .add => (· + ·)
  | .subtract => (· - ·)
  | .multiply => (· * ·)
  | .bitXor => xorValue

def Binary.infer : Binary → Domain → Domain → Domain
  | .add => Domain.add
  | .subtract => Domain.subtract
  | .multiply => Domain.multiply
  | .bitXor => Domain.bitXor

theorem binarySound (operation : Binary) (left right : Domain) (u v : Int)
    (hu : left.Holds u) (hv : right.Holds v) :
    (operation.infer left right).Holds (operation.eval u v) := by
  cases operation
  · exact addSound _ _ _ _ hu hv
  · exact subtractSound _ _ _ _ hu hv
  · exact multiplySound _ _ _ _ hu hv
  · exact xorSound _ _ _ _ hu hv

inductive Unary where
  | shiftLeft | shiftRight | mask
  deriving DecidableEq

def Unary.eval (operation : Unary) (amount : Nat) (value : Int) : Int :=
  match operation with
  | .shiftLeft => shiftValue value amount
  | .shiftRight => rightValue value amount
  | .mask => maskValue value amount

def Unary.infer (operation : Unary) (amount : Nat) (size : Domain) : Domain :=
  match operation with
  | .shiftLeft => size.shiftLeft amount
  | .shiftRight => size.shiftRight amount
  | .mask => size.mask amount

theorem unarySound (operation : Unary) (amount : Nat) (size : Domain) (value : Int)
    (held : size.Holds value) : (operation.infer amount size).Holds (operation.eval amount value) := by
  cases operation
  · exact shiftLeftSound _ _ _ held
  · exact shiftRightSound _ _ _ held
  · exact maskSound _ _ _ held

inductive Expr where
  | literal (value : Int)
  | variable (index : Nat)
  | bind (index : Nat) (rhs body : Expr)
  | binary (operation : Binary) (left right : Expr)
  | unary (operation : Unary) (amount : Nat) (value : Expr)
  | branch (comparison : Comparison) (index : Nat) (constant : Int) (yes no : Expr)
  deriving DecidableEq

def Expr.eval (expr : Expr) (env : Env) : Int :=
  match expr with
  | .literal value => value
  | .variable index => env index
  | .bind index rhs body => body.eval (bindEnv env index (rhs.eval env))
  | .binary operation left right => operation.eval (left.eval env) (right.eval env)
  | .unary operation amount value => operation.eval amount (value.eval env)
  | .branch comparison index constant yes no =>
    if comparison.test (env index) constant then yes.eval env else no.eval env

def Expr.infer (expr : Expr) (state : State) : Domain :=
  match state with
  | none => .unreachable
  | some sizes =>
    match expr with
    | .literal value => .bounded (singleton value)
    | .variable index => sizes index
    | .bind index rhs body => body.infer (bindState state index (rhs.infer state))
    | .binary operation left right => operation.infer (left.infer state) (right.infer state)
    | .unary operation amount value => operation.infer amount (value.infer state)
    | .branch comparison index constant yes no =>
      (yes.infer (refineState state comparison index constant true)).join
        (no.infer (refineState state comparison index constant false))

def traceChild (index : Nat) (rows : List (List Nat × Domain)) : List (List Nat × Domain) :=
  rows.map (fun row => (index :: row.1, row.2))

def Expr.trace (expr : Expr) (state : State) : List (List Nat × Domain) :=
  match state with
  | none => [([], .unreachable)]
  | some _ =>
    let root := [([], expr.infer state)]
    match expr with
    | .literal _ | .variable _ => root
    | .bind index rhs body =>
      traceChild 0 (rhs.trace state) ++ traceChild 1 (body.trace (bindState state index (rhs.infer state))) ++ root
    | .binary _ left right => traceChild 0 (left.trace state) ++ traceChild 1 (right.trace state) ++ root
    | .unary _ _ value => traceChild 0 (value.trace state) ++ root
    | .branch comparison index constant yes no =>
      traceChild 0 (yes.trace (refineState state comparison index constant true)) ++
        traceChild 1 (no.trace (refineState state comparison index constant false)) ++ root

theorem inferSound (expr : Expr) (state : State) (env : Env) (covered : Covers state env) :
    (expr.infer state).Holds (expr.eval env) := by
  induction expr generalizing state env with
  | literal value =>
    cases state with
    | none => exact False.elim covered
    | some sizes => exact (singletonExact _ _).mpr rfl
  | «variable» index =>
    cases state with
    | none => exact False.elim covered
    | some sizes => exact covered index
  | bind index rhs body rhsIH bodyIH =>
    cases state with
    | none => exact False.elim covered
    | some sizes =>
      exact bodyIH _ _ (bindCovers _ _ index _ _ covered (rhsIH _ _ covered))
  | binary operation left right leftIH rightIH =>
    cases state with
    | none => exact False.elim covered
    | some sizes => exact binarySound operation _ _ _ _ (leftIH _ _ covered) (rightIH _ _ covered)
  | unary operation amount value valueIH =>
    cases state with
    | none => exact False.elim covered
    | some sizes => exact unarySound operation amount _ _ (valueIH _ _ covered)
  | branch comparison index constant yes no yesIH noIH =>
    cases state with
    | none => exact False.elim covered
    | some sizes =>
      by_cases branch : comparison.test (env index) constant = true
      · simpa [Expr.eval, Expr.infer, branch] using
          joinLeftSound (yes.infer (refineState (some sizes) comparison index constant true))
            (no.infer (refineState (some sizes) comparison index constant false)) (yes.eval env)
            (yesIH _ _ (refineCovers _ _ _ _ _ _ covered branch))
      · have failed : comparison.test (env index) constant = false := by simp [branch]
        simpa [Expr.eval, Expr.infer, branch] using
          joinRightSound (yes.infer (refineState (some sizes) comparison index constant true))
            (no.infer (refineState (some sizes) comparison index constant false)) (no.eval env)
            (noIH _ _ (refineCovers _ _ _ _ _ _ covered failed))

end ReductionBounds.IntegerAnalysis
