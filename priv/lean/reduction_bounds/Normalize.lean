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

namespace ReductionBounds.Core

def MapPattern.keys (pat : MapPattern) : List String :=
  (if pat.tag.isSome then ["__struct__"] else []) ++ pat.fields.map Prod.fst

private theorem mapKeyPresent (pat : MapPattern) (entries : List (Lynx.Term × Lynx.Term))
    (env bindings : Env) (matched : matchMap pat (.map entries) env = some bindings)
    (key : String) (member : key ∈ pat.keys) :
    ∃ value, fieldLookup entries key = some value := by
  simp only [MapPattern.keys] at member
  rcases List.mem_append.mp member with tagKey | fieldKey
  · cases tag : pat.tag with
    | none => simp [tag] at tagKey
    | some name =>
      have keyEq : key = "__struct__" := by simpa [tag] using tagKey
      subst key
      cases lookup : fieldLookup entries "__struct__" with
      | none => simp [matchMap, tagMatches, tag, lookup] at matched
      | some value => exact ⟨value, rfl⟩
  · obtain ⟨field, inPattern, rfl⟩ := List.mem_map.mp fieldKey
    exact mapMatchFieldPresent pat entries env bindings matched field.1 field.2 inPattern

def factsAfterMap (subject : String) (pat : MapPattern) (facts : List FieldFact) : List FieldFact :=
  (facts ++ pat.keys.map (fun key => (⟨subject, key⟩ : FieldFact))).filter
    (fun fact => pat.keeps fact.subjectName)

theorem factsAfterMapSound (env bindings : Env) (pat : MapPattern) (subject : String)
    (value : Lynx.Term) (facts : List FieldFact) (holds : FactsHold env facts)
    (input : env subject = some value) (matched : matchMap pat value env = some bindings) :
    FactsHold bindings (factsAfterMap subject pat facts) := by
  intro fact member
  simp only [factsAfterMap] at member
  have ⟨inFacts, keeps⟩ := List.mem_filter.mp member
  have unchanged := mapMatchKeeps pat value env bindings fact.subjectName matched keeps
  have before : fact.holds env := by
    rcases List.mem_append.mp inFacts with known | learned
    · exact holds _ known
    · obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp learned
      cases value <;> simp only [matchMap] at matched
      all_goals try contradiction
      obtain ⟨found, present⟩ := mapKeyPresent pat _ env bindings matched key keyMember
      exact ⟨_, found, input, present⟩
  obtain ⟨entries, found, lookup, present⟩ := before
  exact ⟨entries, found, unchanged.trans lookup, present⟩

def factsAfterAlias (name source : String) (facts : List FieldFact) : List FieldFact :=
  facts.filter (fun fact => fact.subjectName != name) ++
    (facts.filter (fun fact => fact.subjectName == source)).map
      (fun fact => (⟨name, fact.key⟩ : FieldFact))

theorem factsAfterAliasSound (env : Env) (name source : String) (value : Lynx.Term)
    (facts : List FieldFact) (holds : FactsHold env facts) (input : env source = some value) :
    FactsHold (env.bind name value) (factsAfterAlias name source facts) := by
  intro fact member
  simp only [factsAfterAlias] at member
  rcases List.mem_append.mp member with kept | copied
  · have ⟨known, different⟩ := List.mem_filter.mp kept
    obtain ⟨entries, found, lookup, present⟩ := holds _ known
    exact ⟨entries, found, by simpa [Env.bind, show fact.subjectName ≠ name by simpa using different]
      using lookup, present⟩
  · obtain ⟨prior, inFilter, rfl⟩ := List.mem_map.mp copied
    have ⟨known, equal⟩ := List.mem_filter.mp inFilter
    have same : prior.subjectName = source := by simpa using equal
    obtain ⟨entries, found, lookup, present⟩ := holds _ known
    rw [same, input] at lookup
    have valueEq : value = .map entries := Option.some.inj lookup
    exact ⟨entries, found, by simp [Env.bind, valueEq], present⟩

-- A certificate for the entire expression. Each premise is checked in the
-- scope where that expression can be evaluated.
inductive CheckedRewrite : List FieldFact → Expr → Expr → Prop where
  | same : CheckedRewrite facts expr expr
  | readField (known : ⟨subject, key⟩ ∈ facts) :
      CheckedRewrite facts (fieldAccessCase subject key binder fallback) (.field (.var subject) key)
  | caseMap
      (matched : CheckedRewrite (factsAfterMap subject pat facts) yes yes')
      (fallback : CheckedRewrite facts no no') :
      CheckedRewrite facts (.caseMap (.var subject) pat yes no)
        (.caseMap (.var subject) pat yes' no')
  | letAlias
      (body : CheckedRewrite (factsAfterAlias name source facts) expr expr') :
      CheckedRewrite facts (.letIn name (.var source) expr) (.letIn name (.var source) expr')

theorem CheckedRewrite.sound (external : OpaqueEval)
    (proof : CheckedRewrite facts original normalized) (env : Env) (holds : FactsHold env facts) :
    eval external env original = eval external env normalized := by
  induction proof generalizing env with
  | same => rfl
  | readField known => exact fieldAccessCaseSound external env _ _ _ _ (holds _ known)
  | @caseMap subject pat facts yes yes' no no' _ _ matchedIH fallbackIH =>
    cases input : env subject with
    | none => simp [eval, input, bindResult]
    | some value =>
      cases foundMap : matchMap pat value env with
      | none => simpa [eval, input, bindResult, foundMap] using fallbackIH env holds
      | some bindings =>
        simpa [eval, input, bindResult, foundMap]
          using matchedIH bindings (factsAfterMapSound env bindings pat subject value facts holds input foundMap)
  | @letAlias name source facts expr expr' _ ih =>
    cases input : env source with
    | none => simp [eval, input, bindResult]
    | some value =>
      simpa [eval, input, bindResult]
        using ih (env.bind name value) (factsAfterAliasSound env name source value facts holds input)

theorem sourceNormalizationSound (source : SourceExpr) (original normalized : Expr)
    (safe : source.scopeSafe = true) (decoded : source.lower = original)
    (checked : CheckedRewrite [] original normalized) (external : OpaqueEval) (env : Env) :
    source.run external env = eval external env normalized := by
  rw [source.lowerSound external env safe, decoded]
  exact checked.sound external env (by simp [FactsHold])

end ReductionBounds.Core
