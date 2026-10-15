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
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
def RegistrationBody : NCode → Prop
  | .onSuccess body callback => ∀ acquired fin, callback = .afterScopeAdd acquired fin →
      ∃ scope, body = .sync (.op (.scopeAdd scope fin))
  | _ => True

abbrev RegistrationCode := Correlated RegistrationBody

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_success (relation : NCode → Prop) (value : Val) :
    Correlated relation (.success value) = relation (.success value) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_failure (relation : NCode → Prop) (cause : CauseV) :
    Correlated relation (.failure cause) = relation (.failure cause) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_sync (relation : NCode → Prop) (thunk : EffThunk) :
    Correlated relation (.sync thunk) = relation (.sync thunk) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_suspend (relation : NCode → Prop) (thunk : EffThunk) :
    Correlated relation (.suspend thunk) = relation (.suspend thunk) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_withFiber (relation : NCode → Prop) (thunk : EffThunk) :
    Correlated relation (.withFiber thunk) = relation (.withFiber thunk) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_yieldableError (relation : NCode → Prop) (error : Err) :
    Correlated relation (.yieldableError error) = relation (.yieldableError error) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_iterator (relation : NCode → Prop) (callback : EffName) (cursor : Val) :
    Correlated relation (.iterator callback cursor) = relation (.iterator callback cursor) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_whileLoop (relation : NCode → Prop) (callback : EffName) (cursor : Val) :
    Correlated relation (.whileLoop callback cursor) = relation (.whileLoop callback cursor) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_setInterruptible (relation : NCode → Prop) (flag : Bool) :
    Correlated relation (.setInterruptible flag) = relation (.setInterruptible flag) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_yieldNowWith (relation : NCode → Prop) (priority : Nat) :
    Correlated relation (.yieldNowWith priority) = relation (.yieldNowWith priority) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_async (relation : NCode → Prop) (callback : EffName) (flag : Bool) (cancel : Option EffName) :
    Correlated relation (.async callback flag cancel) = relation (.async callback flag cancel) := rfl

/-- The existing code fold exposes its local constructor relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_asyncFinalizer (relation : NCode → Prop) (callback : EffName) :
    Correlated relation (.asyncFinalizer callback) = relation (.asyncFinalizer callback) := rfl

/-- The existing code fold retains the actual child beside its local relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_onSuccess (relation : NCode → Prop) (body : NCode) (callback : EffName) :
    Correlated relation (.onSuccess body callback) =
      (Correlated relation body ∧ relation (.onSuccess body callback)) := by
  change (Correlated relation body ∧ relation (.onSuccess (cata_prim (correlatedAlg relation) body).1 callback)) = _
  rw [correlated_rebuild]

/-- The existing code fold retains the actual child beside its local relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_onFailure (relation : NCode → Prop) (body : NCode) (callback : EffName) :
    Correlated relation (.onFailure body callback) =
      (Correlated relation body ∧ relation (.onFailure body callback)) := by
  change (Correlated relation body ∧ relation (.onFailure (cata_prim (correlatedAlg relation) body).1 callback)) = _
  rw [correlated_rebuild]

/-- The existing code fold retains the actual child beside its local relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_onSuccessAndFailure (relation : NCode → Prop) (body : NCode) (value cause : EffName) :
    Correlated relation (.onSuccessAndFailure body value cause) =
      (Correlated relation body ∧ relation (.onSuccessAndFailure body value cause)) := by
  change (Correlated relation body ∧ relation (.onSuccessAndFailure (cata_prim (correlatedAlg relation) body).1 value cause)) = _
  rw [correlated_rebuild]

/-- The existing code fold retains the actual child beside its local relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_onExit (relation : NCode → Prop) (body : NCode) (callback : EffName) (flag : Bool) :
    Correlated relation (.onExit body callback flag) =
      (Correlated relation body ∧ relation (.onExit body callback flag)) := by
  change (Correlated relation body ∧ relation (.onExit (cata_prim (correlatedAlg relation) body).1 callback flag)) = _
  rw [correlated_rebuild]

/-- The existing code fold retains the actual child beside its local relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_exitFrame (relation : NCode → Prop) (body : NCode)  :
    Correlated relation (.exitFrame body) =
      (Correlated relation body ∧ relation (.exitFrame body)) := by
  change (Correlated relation body ∧ relation (.exitFrame (cata_prim (correlatedAlg relation) body).1)) = _
  rw [correlated_rebuild]

/-- The existing code fold retains both actual children beside their local relation. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem correlated_onSuccessConst (relation : NCode → Prop) (body next : NCode) :
    Correlated relation (.onSuccessConst body next) =
      (Correlated relation body ∧ Correlated relation next ∧ relation (.onSuccessConst body next)) := by
  change (Correlated relation body ∧ Correlated relation next ∧
    relation (.onSuccessConst (cata_prim (correlatedAlg relation) body).1
      (cata_prim (correlatedAlg relation) next).1)) = _
  rw [correlated_rebuild, correlated_rebuild]

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
