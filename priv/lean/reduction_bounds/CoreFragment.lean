-- Loaded by the Lynx Runner after the Erlang maps and erlang models.
namespace ReductionBounds.Core

abbrev Env := String → Option Lynx.Term
abbrev Result := Option (Except Lynx.Exception Lynx.Term)
abbrev OpaqueEval := String → Env → Result

structure MapPattern where
  tag : Option String
  fields : List (String × String)
  deriving DecidableEq

inductive Expr where
  | var (name : String)
  | int (value : Int)
  | atom (name : String)
  | letIn (name : String) (rhs body : Expr)
  | caseMap (subject : Expr) (pat : MapPattern) (matched fallback : Expr)
  | caseMapGuarded (subject : Expr) (pat : MapPattern) (condition matched fallback : Expr)
  | guarded (condition success failure : Expr)
  | isInteger (operand : Expr)
  | isMap (operand : Expr)
  | field (subject : Expr) (key : String)
  | update (subject : Expr) (key : String) (rhs : Expr)
  | ge (left right : Expr)
  | sub (left right : Expr)
  | opaque (id : String)
  deriving DecidableEq

def Env.bind (env : Env) (name : String) (value : Lynx.Term) : Env :=
  fun key => if key = name then some value else env key

def fieldLookup (entries : List (Lynx.Term × Lynx.Term)) (key : String) : Option Lynx.Term :=
  Lynx.Term.mapLookup entries (.atom key)

def bindFields (entries : List (Lynx.Term × Lynx.Term)) :
    List (String × String) → Env → Option Env
  | [], env => some env
  | (key, name) :: rest, env =>
    (fieldLookup entries key).bind fun value => bindFields entries rest (env.bind name value)

def tagMatches (entries : List (Lynx.Term × Lynx.Term)) : Option String → Bool
  | none => true
  | some tag =>
    match fieldLookup entries "__struct__" with
    | some (.atom actual) => decide (actual = tag)
    | _ => false

def matchMap (pat : MapPattern) (input : Lynx.Term) (env : Env) : Option Env :=
  match input with
  | .map entries =>
    if tagMatches entries pat.tag then bindFields entries pat.fields env else none
  | _ => none

def bindResult (result : Result) (next : Lynx.Term → Result) : Result :=
  match result with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok value) => next value

def eval (external : OpaqueEval) (env : Env) : Expr → Result
  | .var name => (env name).map Except.ok
  | .int value => some (.ok (.integer value))
  | .atom name => some (.ok (.atom name))
  | .letIn name rhs body =>
    bindResult (eval external env rhs) fun value => eval external (env.bind name value) body
  | .caseMap subject pat matched fallback =>
    bindResult (eval external env subject) fun value =>
      match matchMap pat value env with
      | some bindings => eval external bindings matched
      | none => eval external env fallback
  | .caseMapGuarded subject pat condition matched fallback =>
    bindResult (eval external env subject) fun value =>
      match matchMap pat value env with
      | none => eval external env fallback
      | some bindings =>
        match eval external bindings condition with
        | none => none
        | some (.ok (.atom "true")) => eval external bindings matched
        | some _ => eval external env fallback
  | .guarded condition success failure =>
    match eval external env condition with
    | none => none
    | some (.ok (.atom "true")) => eval external env success
    | some _ => eval external env failure
  | .isInteger operand =>
    bindResult (eval external env operand) fun value => some (Erlang.erlang.«is_integer/1» value)
  | .isMap operand =>
    bindResult (eval external env operand) fun value => some (Erlang.erlang.«is_map/1» value)
  | .field subject key =>
    bindResult (eval external env subject) fun input =>
      some (Erlang.maps.«get/2» (.atom key) input)
  | .update subject key rhs =>
    bindResult (eval external env subject) fun input =>
      bindResult (eval external env rhs) fun value =>
        some (Erlang.maps.«update/3» (.atom key) value input)
  | .ge left right =>
    bindResult (eval external env left) fun l =>
      bindResult (eval external env right) fun r => some (Erlang.erlang.«>=/2» l r)
  | .sub left right =>
    bindResult (eval external env left) fun l =>
      bindResult (eval external env right) fun r => some (Erlang.erlang.«-/2» l r)
  | .opaque id => external id env

end ReductionBounds.Core

namespace ReductionBounds.Core

def MapPattern.keeps (pat : MapPattern) (name : String) : Bool :=
  pat.fields.all fun field => field.2 != name

theorem bindFieldsKeeps (entries : List (Lynx.Term × Lynx.Term))
    (fields : List (String × String)) (env bindings : Env) (name : String)
    (matched : bindFields entries fields env = some bindings)
    (keeps : fields.all (fun field => field.2 != name) = true) :
    bindings name = env name := by
  induction fields generalizing env with
  | nil =>
    have same : env = bindings := Option.some.inj matched
    rw [same]
  | cons field rest ih =>
    have headAndRest := Bool.and_eq_true_iff.mp keeps
    cases lookup : fieldLookup entries field.1 with
    | none => simp [bindFields, lookup] at matched
    | some value =>
      have tailMatch : bindFields entries rest (env.bind field.2 value) = some bindings := by
        simpa [bindFields, lookup] using matched
      rw [ih _ tailMatch headAndRest.2]
      have different : field.2 ≠ name := by simpa using headAndRest.1
      simp [Env.bind, Ne.symm different]

theorem mapMatchKeeps (pat : MapPattern) (value : Lynx.Term) (env bindings : Env)
    (name : String) (matched : matchMap pat value env = some bindings)
    (keeps : pat.keeps name = true) :
    bindings name = env name := by
  cases value <;> simp only [matchMap] at matched
  all_goals try contradiction
  split at matched
  · exact bindFieldsKeeps _ _ _ _ _ matched keeps
  · contradiction

-- The reified Core fragment retains aliases on patterns. The analysis expression
-- represents an alias instead by a let in the matched branch.
inductive SourceExpr where
  | var (name : String)
  | int (value : Int)
  | atom (name : String)
  | letIn (name : String) (rhs body : SourceExpr)
  | caseMap (subject : String) (pat : MapPattern) (aliasName : Option String)
      (matched fallback : SourceExpr)
  | opaque (id : String)

def SourceExpr.run (external : OpaqueEval) (env : Env) : SourceExpr → Result
  | .var name => (env name).map Except.ok
  | .int value => some (.ok (.integer value))
  | .atom name => some (.ok (.atom name))
  | .letIn name rhs body =>
    bindResult (run external env rhs) fun value => run external (env.bind name value) body
  | .caseMap subject pat aliasName matched fallback =>
    (env subject).bind fun value =>
      match matchMap pat value env with
      | none => run external env fallback
      | some bindings =>
        match aliasName with
        | none => run external bindings matched
        | some name => run external (bindings.bind name value) matched
  | .opaque id => external id env

def SourceExpr.lower : SourceExpr → Expr
  | .var name => .var name
  | .int value => .int value
  | .atom name => .atom name
  | .letIn name rhs body => .letIn name rhs.lower body.lower
  | .caseMap subject pat aliasName matched fallback =>
    let body := match aliasName with
      | none => matched.lower
      | some name => .letIn name (.var subject) matched.lower
    .caseMap (.var subject) pat body fallback.lower
  | .opaque id => .opaque id

def SourceExpr.scopeSafe : SourceExpr → Bool
  | .letIn _ rhs body => rhs.scopeSafe && body.scopeSafe
  | .caseMap subject pat aliasName matched fallback =>
    (aliasName.isNone || pat.keeps subject) && (matched.scopeSafe && fallback.scopeSafe)
  | _ => true

theorem SourceExpr.lowerSound (external : OpaqueEval) (env : Env) (source : SourceExpr)
    (safe : source.scopeSafe = true) : source.run external env = eval external env source.lower := by
  induction source generalizing env with
  | var | int | atom | «opaque» => rfl
  | letIn name rhs body rhsIH bodyIH =>
    have ⟨rhsSafe, bodySafe⟩ := Bool.and_eq_true_iff.mp safe
    simp only [SourceExpr.run, SourceExpr.lower, eval, rhsIH _ rhsSafe, bodyIH _ bodySafe]
  | caseMap subject pat aliasName matched fallback matchedIH fallbackIH =>
    have ⟨aliasSafe, branchesSafe⟩ := Bool.and_eq_true_iff.mp safe
    have ⟨matchedSafe, fallbackSafe⟩ := Bool.and_eq_true_iff.mp branchesSafe
    cases input : env subject with
    | none => simp [SourceExpr.run, SourceExpr.lower, eval, input, bindResult]
    | some value =>
      cases matchedMap : matchMap pat value env with
      | none =>
        simpa [SourceExpr.run, SourceExpr.lower, eval, input, bindResult, matchedMap]
          using fallbackIH env fallbackSafe
      | some bindings =>
        cases aliasName with
        | none =>
          simpa [SourceExpr.run, SourceExpr.lower, eval, input, bindResult, matchedMap]
            using matchedIH bindings matchedSafe
        | some name =>
          have keeps : pat.keeps subject = true := by simpa using aliasSafe
          have sourceValue := mapMatchKeeps pat value env bindings subject matchedMap keeps
          simpa [SourceExpr.run, SourceExpr.lower, eval, input, bindResult, matchedMap,
            sourceValue] using matchedIH (bindings.bind name value) matchedSafe

end ReductionBounds.Core
