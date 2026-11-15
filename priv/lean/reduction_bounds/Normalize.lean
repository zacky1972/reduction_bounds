namespace ReductionBounds.Core

structure FieldFact where
  subjectName : String
  key : String
  deriving DecidableEq

def FieldFact.holds (env : Env) (fact : FieldFact) : Prop :=
  ∃ entries value, env fact.subjectName = some (.map entries) ∧
    fieldLookup entries fact.key = some value

def FactsHold (env : Env) (facts : List FieldFact) : Prop :=
  ∀ fact ∈ facts, fact.holds env

inductive Rewrite where
  | readField (subjectName key binder : String) (fallback : Expr)
  deriving DecidableEq

def fieldAccessCase (subjectName key binder : String) (fallback : Expr) : Expr :=
  .caseMap (.var subjectName) ⟨none, [(key, binder)]⟩ (.var binder) fallback

def checkRewrite (facts : List FieldFact) (original normalized : Expr) : Rewrite → Bool
  | .readField subjectName key binder fallback =>
    decide ((⟨subjectName, key⟩ : FieldFact) ∈ facts ∧
      original = fieldAccessCase subjectName key binder fallback ∧
      normalized = .field (.var subjectName) key)

theorem fieldAccessCaseSound (external : OpaqueEval) (env : Env)
    (subjectName key binder : String) (fallback : Expr)
    (known : (⟨subjectName, key⟩ : FieldFact).holds env) :
    eval external env (fieldAccessCase subjectName key binder fallback) =
      eval external env (.field (.var subjectName) key) := by
  obtain ⟨entries, value, input, present⟩ := known
  rw [show eval external env (fieldAccessCase subjectName key binder fallback) = some (.ok value) by
    simp [fieldAccessCase, eval, input, bindResult, matchMap, tagMatches, bindFields,
      present, envBindRead]]
  simp [eval, input, bindResult, fieldGet entries key value present]

theorem checkRewriteSound (external : OpaqueEval) (env : Env) (facts : List FieldFact)
    (original normalized : Expr) (rewrite : Rewrite)
    (accepted : checkRewrite facts original normalized rewrite = true)
    (holds : FactsHold env facts) :
    eval external env original = eval external env normalized := by
  cases rewrite with
  | readField subjectName key binder fallback =>
    have conditions := of_decide_eq_true accepted
    rcases conditions with ⟨member, rfl, rfl⟩
    exact fieldAccessCaseSound external env subjectName key binder fallback (holds _ member)

structure Certificate where
  facts : List FieldFact
  original : Expr
  normalized : Expr
  rewrite : Rewrite

def Certificate.check (certificate : Certificate) : Bool :=
  checkRewrite certificate.facts certificate.original certificate.normalized certificate.rewrite

theorem Certificate.sound (certificate : Certificate) (external : OpaqueEval) (env : Env)
    (accepted : certificate.check = true) (holds : FactsHold env certificate.facts) :
    eval external env certificate.original = eval external env certificate.normalized :=
  checkRewriteSound external env certificate.facts certificate.original certificate.normalized
    certificate.rewrite accepted holds

end ReductionBounds.Core
