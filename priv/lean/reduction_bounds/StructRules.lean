namespace ReductionBounds.Core

theorem envBindRead (env : Env) (name : String) (value : Lynx.Term) :
    (env.bind name value) name = some value := by
  simp [Env.bind]

theorem matchedFieldPresent (entries : List (Lynx.Term × Lynx.Term))
    (fields : List (String × String)) (env bound : Env)
    (matched : bindFields entries fields env = some bound) :
    ∀ pair ∈ fields, ∃ value, fieldLookup entries pair.1 = some value := by
  induction fields generalizing env with
  | nil => simp
  | cons head rest ih =>
    cases lookup : fieldLookup entries head.1 with
    | none => simp [bindFields, lookup] at matched
    | some value =>
      intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨value, lookup⟩
      · exact ih (env.bind head.2 value) (by simpa [bindFields, lookup] using matched) pair member

theorem mapMatchFieldPresent (pat : MapPattern) (entries : List (Lynx.Term × Lynx.Term))
    (env bound : Env) (matched : matchMap pat (.map entries) env = some bound)
    (key name : String) (member : (key, name) ∈ pat.fields) :
    ∃ value, fieldLookup entries key = some value := by
  have fields : bindFields entries pat.fields env = some bound := by
    cases tag : tagMatches entries pat.tag with
    | false => simp [matchMap, tag] at matched
    | true => simpa [matchMap, tag] using matched
  exact matchedFieldPresent entries pat.fields env bound fields (key, name) member

theorem fieldGet (entries : List (Lynx.Term × Lynx.Term)) (key : String)
    (value : Lynx.Term) (present : fieldLookup entries key = some value) :
    Erlang.maps.«get/2» (.atom key) (.map entries) = .ok value := by
  change (match fieldLookup entries key with
    | some found => Except.ok found
    | none => Except.error (Lynx.Exception.error (.tuple #[.atom "badkey", .atom key]))) = .ok value
  rw [present]

theorem exactUpdate (entries : List (Lynx.Term × Lynx.Term)) (key : String)
    (previous value : Lynx.Term) (present : fieldLookup entries key = some previous) :
    Erlang.maps.«update/3» (.atom key) value (.map entries) =
      .ok (.map ((.atom key, value) :: entries)) := by
  have existsKey := congrArg Option.isSome present
  simp [fieldLookup, Lynx.Term.mapLookup] at existsKey
  simp [Erlang.maps.«update/3», existsKey]

theorem lookupUpdated (entries : List (Lynx.Term × Lynx.Term)) (key : String)
    (value : Lynx.Term) :
    fieldLookup ((.atom key, value) :: entries) key = some value := by
  simp [fieldLookup, Lynx.Term.mapLookup]

theorem lookupOther (entries : List (Lynx.Term × Lynx.Term)) (key other : String)
    (value : Lynx.Term) (different : other ≠ key) :
    fieldLookup ((.atom key, value) :: entries) other = fieldLookup entries other := by
  simp [fieldLookup, Lynx.Term.mapLookup, different]

end ReductionBounds.Core

namespace ReductionBounds.Core

inductive CostTree where
  | paid (cost : Nat)
  | seq (left right : CostTree)
  | branch (success failure : CostTree)

def CostTree.upperBound : CostTree → Nat
  | .paid cost => cost
  | .seq left right => left.upperBound + right.upperBound
  | .branch success failure => max success.upperBound failure.upperBound

inductive CostTree.PathCost : CostTree → Nat → Prop where
  | paid : actual ≤ bound → PathCost (.paid bound) actual
  | seq : PathCost left l → PathCost right r → PathCost (.seq left right) (l + r)
  | success : PathCost yes cost → PathCost (.branch yes no) cost
  | failure : PathCost no cost → PathCost (.branch yes no) cost

theorem CostTree.pathCostBound (path : CostTree.PathCost tree cost) :
    cost ≤ tree.upperBound := by
  induction path with
  | paid bound => exact bound
  | seq _ _ left right => exact Nat.add_le_add left right
  | success _ ih => exact Nat.le_trans ih (Nat.le_max_left _ _)
  | failure _ ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

def Expr.costTree (charge opaqueCost : String → Nat) : Expr → CostTree
  | .var _ | .int _ | .atom _ => .paid 0
  | .opaque id => .paid (opaqueCost id)
  | .letIn _ rhs body =>
    .seq (.paid (charge "bind")) (.seq (costTree charge opaqueCost rhs) (costTree charge opaqueCost body))
  | .caseMap subject _ matched fallback =>
    .seq (costTree charge opaqueCost subject) (.seq (.paid (charge "map_match"))
      (.branch (costTree charge opaqueCost matched) (costTree charge opaqueCost fallback)))
  | .caseMapGuarded subject _ condition matched fallback =>
    .seq (costTree charge opaqueCost subject) (.seq (.paid (charge "map_match"))
      (.branch (.seq (costTree charge opaqueCost condition) (.seq (.paid (charge "branch"))
        (.branch (costTree charge opaqueCost matched) (costTree charge opaqueCost fallback))))
        (costTree charge opaqueCost fallback)))
  | .guarded condition success failure =>
    .seq (costTree charge opaqueCost condition) (.seq (.paid (charge "branch"))
      (.branch (costTree charge opaqueCost success) (costTree charge opaqueCost failure)))
  | .isInteger operand =>
    .seq (costTree charge opaqueCost operand) (.paid (charge "is_integer"))
  | .isMap operand =>
    .seq (costTree charge opaqueCost operand) (.paid (charge "is_map"))
  | .field subject _ =>
    .seq (costTree charge opaqueCost subject) (.paid (charge "field"))
  | .update subject _ rhs =>
    .seq (costTree charge opaqueCost subject) (.seq (costTree charge opaqueCost rhs) (.paid (charge "update")))
  | .ge left right =>
    .seq (costTree charge opaqueCost left) (.seq (costTree charge opaqueCost right) (.paid (charge "ge")))
  | .sub left right =>
    .seq (costTree charge opaqueCost left) (.seq (costTree charge opaqueCost right) (.paid (charge "sub")))

end ReductionBounds.Core
