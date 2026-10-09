import Effect4.Step.Elab.Inputs
import Effect4.Laws.Step.Scope
import Effect4.Step.Lists

/-! Named input and fold authoring readers and controls.
The interface elaborates to existing Step data.
The shared reading, typing, and scope laws remain its semantic boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Test.Program.StepInputs
open Effect4 Effect4.Program Effect4.Modules Effect4.Program.Authoring

/-- Same-typed inputs with distinct roles. -/
step_context% IdFirst (id : .nat, hint : .nat)
step_context% HintFirst (hint : .nat, id : .nat)
def first := step_inputs% IdFirst => id
def reordered := step_inputs% HintFirst => id
example : first = (Step.var (.here .nat [.nat])) := by rfl
example : reordered = (Step.var (.there .nat (.here .nat []))) := by rfl
#guard first.term (input_sources% (IdFirst) {hint := nat 9, id := nat 3}) {} [] == .ok (.lit (.nat 3))
#guard reordered.term (input_sources% (HintFirst) {id := nat 3, hint := nat 9}) {} [] == .ok (.lit (.nat 3))

/-- A documented context may retain a type parameter. -/
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

def itemPass := step_inputs% FoldInputs =>
  let derived : Step _ .nat := .add n (.nat 1)
  Step.Lists.map xs (item_step% xs with element => .add derived element)
def itemResult : List Nat := Step.eval (Γ := [.list .nat, .nat]) Schema.Model.Leaves.deferredKeys
  (([1, 2] : List Nat), ((2 : Nat), ())) itemPass
#guard itemResult == [4, 5]
example : (input_ref% (IdFirst) id) = Input.here .nat [.nat] := by rfl
example : (input_ref% (HintFirst) id) = Input.there .nat (Input.here .nat []) := by rfl
/-- error: item_step%: binder n shadows an existing local -/
#guard_msgs in
#check step_inputs% FoldInputs => item_step% xs with n => n
/-- error: input_ref%: unknown input other -/
#guard_msgs in
#check input_ref% (IdFirst) other

def repeatedMetadata : InputContext := [("id", .nat), ("id", .nat)]
/-- error: step inputs: declaration repeats id -/
#guard_msgs in
#check step_inputs% repeatedMetadata => id

/-- error: step_inputs%: input id shadows an existing local -/
#guard_msgs in
#check step_inputs% IdFirst => step_inputs% IdFirst => id

open Effect4.Schema.Model

-- Value callers use the same declaration and names as the source callers.
def firstValue : Nat := first.eval (Γ := IdFirst.types) Leaves.refused
  (input_values% (IdFirst) (Leaves.refused) {hint := 9, id := 3})
def reorderedValue : Nat := reordered.eval (Γ := HintFirst.types) Leaves.refused
  (input_values% (HintFirst) (Leaves.refused) {id := 3, hint := 9})
#guard firstValue == 3
#guard reorderedValue == 3

def payloadValues (L : Leaves) (A : Ty) (a : CarrierAt L A) : Inputs L (Payload A).types :=
  input_values% (Payload A) (L) {count := 2, value := a}
def payloadValue : String := (generic .string).eval (Γ := (Payload .string).types) Leaves.refused
  (payloadValues Leaves.refused .string "payload")
#guard payloadValue == "payload"

step_context% NoInputs ()
#guard (input_values% (NoInputs) (Leaves.refused) {}) == ()

step_context% IdentityInputs (waiter : .deferredOf .nat .never, amount : .nat)
def identityInput := step_inputs% IdentityInputs => waiter
def identityValues := input_values% (IdentityInputs) (Leaves.deferredKeys) {
  amount := 4, waiter := (⟨7⟩ : Machine.DeferredKey)}
#guard (identityInput.eval (Γ := IdentityInputs.types) Leaves.deferredKeys identityValues).index == 7

/-- error: input_values%: repeated name id -/
#guard_msgs in
#check input_values% (IdFirst) (Leaves.refused) {id := 1, id := 2, hint := 3}

/-- error: input_values%: missing input hint -/
#guard_msgs in
#check input_values% (IdFirst) (Leaves.refused) {id := 1}

/-- error: input_values%: unknown input other -/
#guard_msgs in
#check input_values% (IdFirst) (Leaves.refused) {id := 1, hint := 2, other := 3}

/-- error: step inputs: declaration repeats id -/
#guard_msgs in
#check input_values% (repeatedMetadata) (Leaves.refused) {id := 1}

/-- error: Type mismatch
  "wrong"
has type
  String
but is expected to have type
  Nat -/
#guard_msgs (error, drop info) in
#check input_values% (IdFirst) (Leaves.refused) {id := "wrong", hint := 2}

/-- error: Type mismatch
  7
has type
  Nat
but is expected to have type
  Machine.DeferredKey -/
#guard_msgs (error, drop info) in
#check input_values% (IdentityInputs) (Leaves.deferredKeys) {waiter := (7 : Nat), amount := 4}

/-- error: input_values%: declared inputs differ from expected type -/
#guard_msgs (error, drop info) in
#check (input_values% (IdFirst) (Leaves.refused) {id := 1, hint := 2} : Inputs Leaves.refused [.bool])

end Test.Program.StepInputs
