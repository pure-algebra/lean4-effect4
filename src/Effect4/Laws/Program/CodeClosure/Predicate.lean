import Effect4.Program.Compile
import Effect4.Machine.Fold
import Effect4.Laws.Auto.RuleSets

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the shared compiler and callback closure of Atomic, Timeout and both crews.
The generated runtime-code fold lifts name and thunk predicates.
This reading establishes no initialization, reachability or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure
open Effect4 Effect4.Machine Effect4.Program

/-- The code-graph lifting of a name predicate and a thunk predicate, as one algebra. -/
def codeAlg (name : EffName → Prop) (thunk : EffThunk → Prop) :
    PrimAlgebra EffName EffThunk Val Err Defect FiberId Ann Prop where
  prim_success _ := True
  prim_failure _ := True
  prim_sync suspended := thunk suspended
  prim_suspend suspended := thunk suspended
  prim_withFiber suspended := thunk suspended
  prim_yieldableError _ := True
  prim_iterator callback _ := name callback
  prim_onSuccess body callback := body ∧ name callback
  prim_onSuccessConst body next := body ∧ next
  prim_onFailure body callback := body ∧ name callback
  prim_onSuccessAndFailure body success failure := body ∧ name success ∧ name failure
  prim_exitFrame body := body
  prim_onExit body callback _ := body ∧ name callback
  prim_setInterruptible _ := True
  prim_whileLoop callback _ := name callback
  prim_yieldNowWith _ := True
  prim_async register _ cancel := name register ∧ ∀ callback ∈ cancel, name callback
  prim_asyncFinalizer callback := name callback

/-- A stable head for the generated predicate fold.
Consumer: local constructor normalization and the compiler contract. -/
def Code (name : EffName → Prop) (thunk : EffThunk → Prop) (code : NCode) : Prop :=
  cata_prim (codeAlg name thunk) code

variable (name : EffName → Prop) (thunk : EffThunk → Prop)

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_success (value : Val) :
    Code name thunk (.success value) = (True) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_failure (cause : CauseV) :
    Code name thunk (.failure cause) = (True) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_sync (value : EffThunk) :
    Code name thunk (.sync value) = (thunk value) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_suspend (value : EffThunk) :
    Code name thunk (.suspend value) = (thunk value) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_withFiber (value : EffThunk) :
    Code name thunk (.withFiber value) = (thunk value) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_yieldableError (err : Err) :
    Code name thunk (.yieldableError err) = (True) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_iterator (callback : EffName) (value : Val) :
    Code name thunk (.iterator callback value) = (name callback) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_onSuccess (body : NCode) (callback : EffName) :
    Code name thunk (.onSuccess body callback) = (Code name thunk body ∧ name callback) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_onSuccessConst (body next : NCode) :
    Code name thunk (.onSuccessConst body next) = (Code name thunk body ∧ Code name thunk next) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_onFailure (body : NCode) (callback : EffName) :
    Code name thunk (.onFailure body callback) = (Code name thunk body ∧ name callback) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_onSuccessAndFailure (body : NCode) (success failure : EffName) :
    Code name thunk (.onSuccessAndFailure body success failure) = (Code name thunk body ∧ name success ∧ name failure) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_exitFrame (body : NCode) :
    Code name thunk (.exitFrame body) = (Code name thunk body) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_onExit (body : NCode) (callback : EffName) (flag : Bool) :
    Code name thunk (.onExit body callback flag) = (Code name thunk body ∧ name callback) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_setInterruptible (flag : Bool) :
    Code name thunk (.setInterruptible flag) = (True) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_whileLoop (callback : EffName) (value : Val) :
    Code name thunk (.whileLoop callback value) = (name callback) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_yieldNowWith (priority : Nat) :
    Code name thunk (.yieldNowWith priority) = (True) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_async (callback : EffName) (flag : Bool) (cancel : Option EffName) :
    Code name thunk (.async callback flag cancel) = (name callback ∧ ∀ next ∈ cancel, name next) := rfl

@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
theorem code_asyncFinalizer (callback : EffName) :
    Code name thunk (.asyncFinalizer callback) = (name callback) := rfl

/-- A certified thunk supplies a runtime sync leaf.
Consumer: the compiler contract's synchronous-operation case. -/
theorem sync_closed (suspended : EffThunk) (held : thunk suspended) :
    Code name thunk (.sync suspended) := by
  aesop (rule_sets := [Effect4.CodeClosure])

/-- A conjunction of two liftings is the lifting of the pointwise conjunction. -/
theorem fold_and (name₁ name₂ : EffName → Prop) (thunk₁ thunk₂ : EffThunk → Prop) (code : NCode) :
    cata_prim (codeAlg (fun n => name₁ n ∧ name₂ n) (fun t => thunk₁ t ∧ thunk₂ t)) code ↔
      cata_prim (codeAlg name₁ thunk₁) code ∧ cata_prim (codeAlg name₂ thunk₂) code := by
  let hom : PrimHom (codeAlg (fun n => name₁ n ∧ name₂ n) (fun t => thunk₁ t ∧ thunk₂ t)) := by
    refine ⟨(fun body => Code name₁ thunk₁ body ∧ Code name₂ thunk₂ body),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [codeAlg])
  exact Iff.of_eq (hom_eq_cata_prim hom code).symm

/-- Pointwise leaf implications lift through the generated runtime-code fold.
Consumer: unrestricted finalizer annotations reuse the stored callback closure. -/
theorem code_mono {name₁ name₂ : EffName → Prop} {thunk₁ thunk₂ : EffThunk → Prop}
    (names : ∀ n, name₁ n → name₂ n) (thunks : ∀ t, thunk₁ t → thunk₂ t)
    (code : NCode) (held : Code name₁ thunk₁ code) : Code name₂ thunk₂ code := by
  induction code with
  | success | failure | yieldableError | setInterruptible | yieldNowWith => trivial
  | sync t | suspend t | withFiber t => exact thunks t held
  | iterator n value | whileLoop n value | asyncFinalizer n => exact names n held
  | onSuccess body n ih | onFailure body n ih | onExit body n flag ih =>
    exact ⟨ih held.1, names n held.2⟩
  | onSuccessConst body next ihBody ihNext => exact ⟨ihBody held.1, ihNext held.2⟩
  | onSuccessAndFailure body success failure ih =>
    exact ⟨ih held.1, names success held.2.1, names failure held.2.2⟩
  | exitFrame body ih => exact ih held
  | async register flag cancel =>
    exact ⟨names register held.1, fun n member => names n (held.2 n member)⟩

end Effect4.Program.CodeClosure
