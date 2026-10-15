import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: scope-lifetime-finalization R11.
Question: actual registration bodies serve `once_placed_outside_census`.
Consumer: full-source registration sequencing and release custody.
The generated fold retains each existing child beside its local predicate.
It adds no program representation, execution relation or progress claim.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure
open Effect4 Effect4.Machine Effect4.Program

/-- A local predicate can inspect the actual children of each existing code constructor. -/
def correlatedAlg (relation : NCode → Prop) :
    PrimAlgebra EffName EffThunk Val Err Defect FiberId Ann (NCode × Prop) where
  prim_success value := ⟨.success value, relation (.success value)⟩
  prim_failure cause := ⟨.failure cause, relation (.failure cause)⟩
  prim_sync thunk := ⟨.sync thunk, relation (.sync thunk)⟩
  prim_suspend thunk := ⟨.suspend thunk, relation (.suspend thunk)⟩
  prim_withFiber thunk := ⟨.withFiber thunk, relation (.withFiber thunk)⟩
  prim_yieldableError err := ⟨.yieldableError err, relation (.yieldableError err)⟩
  prim_iterator callback value := ⟨.iterator callback value, relation (.iterator callback value)⟩
  prim_onSuccess body callback := ⟨.onSuccess body.1 callback, body.2 ∧ relation (.onSuccess body.1 callback)⟩
  prim_onSuccessConst body next := ⟨.onSuccessConst body.1 next.1,
    body.2 ∧ next.2 ∧ relation (.onSuccessConst body.1 next.1)⟩
  prim_onFailure body callback := ⟨.onFailure body.1 callback, body.2 ∧ relation (.onFailure body.1 callback)⟩
  prim_onSuccessAndFailure body value cause := ⟨.onSuccessAndFailure body.1 value cause,
    body.2 ∧ relation (.onSuccessAndFailure body.1 value cause)⟩
  prim_exitFrame body := ⟨.exitFrame body.1, body.2 ∧ relation (.exitFrame body.1)⟩
  prim_onExit body callback flag := ⟨.onExit body.1 callback flag, body.2 ∧ relation (.onExit body.1 callback flag)⟩
  prim_setInterruptible flag := ⟨.setInterruptible flag, relation (.setInterruptible flag)⟩
  prim_whileLoop callback cursor := ⟨.whileLoop callback cursor, relation (.whileLoop callback cursor)⟩
  prim_yieldNowWith priority := ⟨.yieldNowWith priority, relation (.yieldNowWith priority)⟩
  prim_async register flag cancel := ⟨.async register flag cancel, relation (.async register flag cancel)⟩
  prim_asyncFinalizer callback := ⟨.asyncFinalizer callback, relation (.asyncFinalizer callback)⟩

/-- The code projection of the correlated fold is exactly the existing code. -/
theorem correlated_rebuild (relation : NCode → Prop) (code : NCode) :
    (cata_prim (correlatedAlg relation) code).1 = code := by
  let hom : PrimHom (PrimAlgebra.id EffName EffThunk Val Err Defect FiberId Ann) := by
    refine ⟨(fun code => (cata_prim (correlatedAlg relation) code).1),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; rfl
  exact (hom_eq_cata_prim hom code).trans (cata_id_prim code)

/-- Every existing code node satisfies the supplied local constructor relation. -/
def Correlated (relation : NCode → Prop) (code : NCode) : Prop :=
  (cata_prim (correlatedAlg relation) code).2

/-- Registration keeps the exact operation which produces its callback answer. -/
def RegistrationBody : NCode → Prop
  | .onSuccess body callback => ∀ acquired fin, callback = .afterScopeAdd acquired fin →
      ∃ scope, body = .sync (.op (.scopeAdd scope fin))
  | _ => True

abbrev RegistrationCode := Correlated RegistrationBody

/-- The body-callback relation is available at the actual selected registration node. -/
theorem registration_body (body : NCode) (acquired : Val) (fin : FinName)
    (held : RegistrationCode (.onSuccess body (.afterScopeAdd acquired fin))) :
    ∃ scope, body = .sync (.op (.scopeAdd scope fin)) := by
  have related := held.2 acquired fin rfl
  rw [correlated_rebuild] at related
  exact related

/-- Ordinary success callbacks add no registration-body requirement. -/
theorem registration_success (body : NCode) (callback : EffName)
    (held : RegistrationCode body)
    (ordinary : ∀ acquired fin, callback ≠ .afterScopeAdd acquired fin) :
    RegistrationCode (.onSuccess body callback) := by
  refine ⟨held, ?_⟩
  intro acquired fin same
  exact False.elim (ordinary acquired fin same)

/-- An actual scope-add callback carries exactly its own operation body. -/
theorem registration_add (scope : Nat) (acquired : Val) (fin : FinName) :
    RegistrationCode (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd acquired fin)) := by
  refine ⟨True.intro, ?_⟩
  intro value other same
  cases same
  exact ⟨scope, rfl⟩

end Effect4.Program.CodeClosure
