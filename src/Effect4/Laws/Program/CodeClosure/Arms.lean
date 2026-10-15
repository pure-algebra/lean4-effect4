import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: actual callback arms retain a supplied code predicate.
Consumers: source leaf annotations and full finalizer registration correlations.
The constructor contract supplies local callbacks; one proof reads the actual primitive arms.
These local facts establish no native history or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Arms
open Effect4 Effect4.Machine Effect4.Program

/-- The actual iterator result retains its body and its concrete continuation frame. -/
def Iteration (P : NCode → Prop) : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Prop
  | .resume body next => P body ∧ ∀ cursor, P (.iterator next cursor)
  | _ => True

/-- The actual loop result retains its body and its concrete next cursor. -/
def Loop (P : NCode → Prop) (callback : EffName) : LoopNext Val NCode → Prop
  | .continue cursor body => P body ∧ P (.whileLoop callback cursor)
  | .finish body => P body

/-- Local callback and constructor facts supply the actual primitive answer arms. -/
structure Rules (P : NCode → Prop) (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) : Prop where
  success : ∀ value, P (.success value)
  failure : ∀ cause, P (.failure cause)
  value : ∀ body callback value, P (.onSuccess body callback) → P (interp.contA callback value)
  constant : ∀ body next, P (.onSuccessConst body next) → P next
  bothValue : ∀ body callback other value, P (.onSuccessAndFailure body callback other) → P (interp.contA callback value)
  cause : ∀ body callback cause, P (.onFailure body callback) → P (interp.contE callback cause)
  bothCause : ∀ body other callback cause, P (.onSuccessAndFailure body other callback) → P (interp.contE callback cause)
  cancel : ∀ callback cause, P (.asyncFinalizer callback) → P (interp.cancelThenFail callback cause)
  iterator : ∀ callback cursor value, P (.iterator callback cursor) → Iteration P (interp.iterNext callback value).2
  loop : ∀ callback cursor value, P (.whileLoop callback cursor) → Loop P callback (interp.loopResume callback cursor value)

/-- Every exit constructor obeys the supplied leaf rules. -/
theorem ofExit (P : NCode → Prop) (interp) (rules : Rules P interp) (exit : ExitV) : P (Prim.ofExit exit) := by
  cases exit
  · exact rules.success _
  · exact rules.failure _

/-- The actual value arm preserves the predicate on its output and every pushed frame. -/
theorem value (P : NCode → Prop) (interp) (rules : Rules P interp)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (held : P frame) (actual : frame.armA interp value provided = some (next, pushed)) :
    P next ∧ ∀ code ∈ pushed, P code := by
  fun_cases Prim.armA interp frame value provided
  case case10 generator cursor body next selected =>
    have closed := rules.iterator generator cursor value held
    rw [selected] at closed
    aesop (add norm simp [Prim.armA, Iteration])
  all_goals aesop (add norm simp [Prim.armA, Loop]) (add safe apply [(ofExit P interp rules), rules.success, rules.failure]) (add safe forward [rules.loop, rules.value, rules.constant, rules.bothValue])

/-- The actual cause arm preserves the predicate on its output and every pushed frame. -/
theorem cause (P : NCode → Prop) (interp) (rules : Rules P interp)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (held : P frame) (actual : frame.armE interp cause provided = some (next, pushed)) :
    P next ∧ ∀ code ∈ pushed, P code := by
  fun_cases Prim.armE interp frame cause provided
  all_goals aesop (add norm simp [Prim.armE]) (add safe apply [(ofExit P interp rules), rules.success, rules.failure]) (add safe forward [rules.cause, rules.bothCause, rules.cancel])

end Effect4.Program.CodeClosure.Arms
