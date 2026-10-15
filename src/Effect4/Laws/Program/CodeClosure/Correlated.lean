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

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_success (value : Val) :
    RegistrationCode (.success value) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_failure (cause : CauseV) :
    RegistrationCode (.failure cause) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_sync (thunk : EffThunk) :
    RegistrationCode (.sync thunk) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_suspend (thunk : EffThunk) :
    RegistrationCode (.suspend thunk) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_withFiber (thunk : EffThunk) :
    RegistrationCode (.withFiber thunk) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_yieldableError (error : Err) :
    RegistrationCode (.yieldableError error) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_iterator (callback : EffName) (cursor : Val) :
    RegistrationCode (.iterator callback cursor) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_whileLoop (callback : EffName) (cursor : Val) :
    RegistrationCode (.whileLoop callback cursor) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_setInterruptible (flag : Bool) :
    RegistrationCode (.setInterruptible flag) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_yieldNowWith (priority : Nat) :
    RegistrationCode (.yieldNowWith priority) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_async (callback : EffName) (flag : Bool) (cancel : Option EffName) :
    RegistrationCode (.async callback flag cancel) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_asyncFinalizer (callback : EffName) :
    RegistrationCode (.asyncFinalizer callback) = (True) := rfl

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_onSuccess (body : NCode) (callback : EffName) :
    RegistrationCode (.onSuccess body callback) = (RegistrationCode body ∧ RegistrationBody (.onSuccess body callback)) := by
  change (RegistrationCode body ∧ RegistrationBody (.onSuccess (cata_prim (correlatedAlg RegistrationBody) body).1 callback)) = _
  rw [correlated_rebuild]

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_onFailure (body : NCode) (callback : EffName) :
    RegistrationCode (.onFailure body callback) = (RegistrationCode body) := by
  change (RegistrationCode body ∧ True) = _
  exact and_true _

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_onSuccessAndFailure (body : NCode) (value cause : EffName) :
    RegistrationCode (.onSuccessAndFailure body value cause) = (RegistrationCode body) := by
  change (RegistrationCode body ∧ True) = _
  exact and_true _

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_onExit (body : NCode) (callback : EffName) (flag : Bool) :
    RegistrationCode (.onExit body callback flag) = (RegistrationCode body) := by
  change (RegistrationCode body ∧ True) = _
  exact and_true _

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_exitFrame (body : NCode) :
    RegistrationCode (.exitFrame body) = (RegistrationCode body) := by
  change (RegistrationCode body ∧ True) = _
  exact and_true _

/-- Constructor normalization for the exact registration template. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem registration_code_onSuccessConst (body next : NCode) :
    RegistrationCode (.onSuccessConst body next) = (RegistrationCode body ∧ RegistrationCode next) := by
  change (RegistrationCode body ∧ RegistrationCode next ∧ True) = _
  rw [and_true]

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
