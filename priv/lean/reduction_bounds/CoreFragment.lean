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
