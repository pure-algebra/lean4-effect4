import Effect4.Laws.Program.NativeScope

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: immutable root bindings serve Workers and QueueWorkers cleanup log claims.
Reach: existing source points, captures and lexical environment extensions.
Limit: these laws establish no initialization or history premise.
Consumer: the stable answer-flow code and saved callback graph.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The immutable leading bindings of an environment. -/
def Prefix (bindings env : List Val) : Prop := env.take bindings.length = bindings

/-- A stable source point retains lexical scope and its initialized leading bindings. -/
def At (root : NativeEff) (bindings : List Val) (p : Point) : Prop :=
  SourceScope.At root p ∧ Prefix bindings p.env

/-- A prefix supplies enough environment entries. -/
theorem Prefix.length {bindings env : List Val} (held : Prefix bindings env) :
    bindings.length ≤ env.length := by
  have measured := congrArg List.length held
  rw [List.length_take] at measured
  omega

/-- Appending arguments keeps every initialized leading binding. -/
theorem Prefix.append {bindings env : List Val} (held : Prefix bindings env) (tail : List Val) :
    Prefix bindings (env ++ tail) := by
  unfold Prefix
  rw [List.take_append_of_le_length held.length]
  exact held

/-- Reading a leading slot yields its initialized value. -/
theorem Prefix.read {bindings env : List Val} (held : Prefix bindings env)
    (index : Nat) (inside : index < bindings.length) : env[index]? = bindings[index]? := by
  have selected := congrArg (fun values : List Val => values[index]?) held
  rw [List.getElem?_take, if_pos inside] at selected
  exact selected

/-- The point's child has the same leading environment. -/
theorem child {bindings : List Val} {p : Point} (held : Prefix bindings p.env) (index : Nat) :
    Prefix bindings (p.child index).env := held

/-- A bound answer follows the leading environment. -/
theorem childWith {bindings : List Val} {p : Point} (held : Prefix bindings p.env)
    (index : Nat) (value : Val) : Prefix bindings (p.childWith index value).env :=
  held.append [value]

/-- Two bound answers follow the leading environment. -/
theorem childWith2 {bindings : List Val} {p : Point} (held : Prefix bindings p.env)
    (index : Nat) (first second : Val) : Prefix bindings (p.childWith2 index first second).env :=
  held.append [first, second]

/-- A selected arm optionally binds one answer after the leading environment. -/
theorem childBind {bindings : List Val} {p : Point} (held : Prefix bindings p.env)
    (index : Nat) (value : Option Val) : Prefix bindings (p.childBind index value).env := by
  cases value with
  | none => exact child held index
  | some value => exact childWith held index value

/-- Registering a finalizer appends its acquired answer after the leading environment. -/
theorem capture {bindings : List Val} {p : Point} (held : Prefix bindings p.env)
    (value : Val) (context : Ctx) : Prefix bindings (p.capture value context).env := held.append [value]

/-- A finalizer capture retains its bindings under every completed-fiber view. -/
theorem ofCapture {bindings : List Val} {captured : Capture} (held : Prefix bindings captured.env)
    (completed : List (FiberId × ExitV)) : Prefix bindings (Point.ofCapture captured completed).env := held

/-- Existing child scope and immutable leading bindings travel together. -/
theorem At.child {root : NativeEff} {bindings : List Val} {p : Point} (held : At root bindings p)
    (index : Nat) (scope : SourceScope.NextAt root p index 0) : At root bindings (p.child index) :=
  ⟨SourceScope.child_at root p index scope, AnswerSlots.child held.2 index⟩

/-- Existing answer-binding scope and immutable leading bindings travel together. -/
theorem At.childWith {root : NativeEff} {bindings : List Val} {p : Point} (held : At root bindings p)
    (index : Nat) (value : Val) (scope : SourceScope.NextAt root p index 1) :
    At root bindings (p.childWith index value) :=
  ⟨SourceScope.childWith_at root p index value scope, AnswerSlots.childWith held.2 index value⟩
end Effect4.Program.AnswerSlots
