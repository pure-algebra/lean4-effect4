import Effect4.Modules.Step.Elab.Inputs
import Effect4.Laws.Modules.Step.Scope

/-! Named input and fold authoring readers and controls.
The interface elaborates to existing Step data.
The shared reading, typing, and scope laws remain its semantic boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Test.Program.StepInputs
open Effect4 Effect4.Program Effect4.Modules Effect4.Program.Authoring

step_context% IdFirst (id : .nat, hint : .nat)
step_context% HintFirst (hint : .nat, id : .nat)
def first := step_inputs% IdFirst => id
def reordered := step_inputs% HintFirst => id
example : first = (Step.var (.here .nat [.nat])) := by rfl
example : reordered = (Step.var (.there .nat (.here .nat []))) := by rfl
#guard first.term (input_sources% (IdFirst) {hint := nat 9, id := nat 3}) {} [] == .ok (.lit (.nat 3))
#guard reordered.term (input_sources% (HintFirst) {id := nat 3, hint := nat 9}) {} [] == .ok (.lit (.nat 3))

step_context% Payload (A : Ty) where (value : A, count : .nat)
def generic (A : Ty) := step_inputs% (Payload A) => value
example (A : Ty) : generic A = (Step.var (.here A [.nat])) := by rfl
#guard (generic .nat).term (input_sources% (Payload .nat) {count := nat 2, value := nat 5}) {} [] == .ok (.lit (.nat 5))

step_context% FoldInputs (xs : .list .nat, n : .nat)
def nested := step_inputs% FoldInputs =>
  let derived : Step _ .nat := .add n (.nat 1)
  fold_step% xs from total := .nat 0 with element =>
    fold_step% xs from innerTotal := total with innerElement =>
      .add innerTotal (.add derived (.add element innerElement))
def nestedResult : Nat := Step.eval (Γ := [.list .nat, .nat]) Schema.Model.Leaves.deferredKeys
  (([1, 2] : List Nat), ((2 : Nat), ())) nested
#guard nestedResult == 24
example : (nested.term (input_sources% (FoldInputs) {
    xs := app "cons" [nat 1, app "nil" []], n := nat 2})).Scoped :=
  Step.«scoped» nested (Input.source_scoped
    (TermSrc.Scoped_cons
      (app_scoped "cons" (TermSrc.Scoped_cons (nat_scoped 1)
        (TermSrc.Scoped_cons (app_scoped "nil" TermSrc.Scoped_nil) TermSrc.Scoped_nil)))
      (TermSrc.Scoped_cons (nat_scoped 2) TermSrc.Scoped_nil)))
/-- error: step_context%: repeated name same -/
#guard_msgs in
step_context% Repeated (same : .nat, same : .nat)

/-- error: input_sources%: repeated name id -/
#guard_msgs in
#check input_sources% (IdFirst) {id := nat 1, id := nat 2, hint := nat 3}

/-- error: input_sources%: missing input hint -/
#guard_msgs in
#check input_sources% (IdFirst) {id := nat 1}

/-- error: input_sources%: unknown input other -/
#guard_msgs in
#check input_sources% (IdFirst) {id := nat 1, hint := nat 2, other := nat 3}

/-- error: Unknown identifier `absent` -/
#guard_msgs in
#check step_inputs% IdFirst => absent

/-- error: fold_step%: accumulator and item names must differ -/
#guard_msgs in
#check step_inputs% FoldInputs => fold_step% xs from same := .nat 0 with same => same

/-- error: fold_step%: binder n shadows an existing local -/
#guard_msgs in
#check step_inputs% FoldInputs => fold_step% xs from n := .nat 0 with element => element

def repeatedMetadata : InputContext := [("id", .nat), ("id", .nat)]
/-- error: step inputs: declaration repeats id -/
#guard_msgs in
#check step_inputs% repeatedMetadata => id

/-- error: step_inputs%: input id shadows an existing local -/
#guard_msgs in
#check step_inputs% IdFirst => step_inputs% IdFirst => id

end Test.Program.StepInputs
