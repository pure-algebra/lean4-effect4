import Effect4.Author
import Effect4.Run

/-! Finite authoring controls through the public entries at C1, 96e3fd10.
Consumer: decisions row 332's entry-module cutover.
Reach: deriving, construction, captures, elaboration refusals, and tape visibility.
No semantic theorem, whole-module compatibility, or host execution claim follows. -/

set_option backward.isDefEq.respectTransparency false

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules
namespace EntryProbe

structure Counter where
  count : Nat
  ready : Bool
  deriving Modeled

def fields : List (String × Bool × Ty) := [("count", false, .nat), ("ready", false, .bool)]
#guard Modeled.ty (α := Counter) == .record fields

def made : Step [] (.record fields) := record_step% { ready := .bool true, count := .nat 7 }
def countField : FieldRef fields .nat := field_ref% "count"
def readCount : Step [] .nat := .get made countField
#guard made.normal && made.canonical
def countResult : Nat := Step.eval (Γ := []) Model.Leaves.opaque () readCount
#guard countResult == 7

step_context% BumpInputs (amount : .nat, values : .list .nat)
def bump := step_inputs% BumpInputs =>
  Step.Lists.map values (item_step% values with value => .add value amount)
def sumBumped := step_inputs% BumpInputs =>
  fold_step% values from total := .nat 0 with value => .add total (.add value amount)
def bumpSource (amount values : TermSrc) : TermSrc :=
  bump.term (input_sources% (BumpInputs) {values := values, amount := amount})
def bumpResult : List Nat := Step.eval (Γ := [.nat, .list .nat]) Model.Leaves.deferredKeys ((2 : Nat), (([1,2] : List Nat), ())) bump
#guard bumpResult == [3,4]
def sumResult : Nat := Step.eval (Γ := [.nat, .list .nat]) Model.Leaves.deferredKeys ((2 : Nat), (([1,2] : List Nat), ())) sumBumped
#guard sumResult == 7

/-- error: input_sources%: missing input values -/
#guard_msgs in
#check input_sources% (BumpInputs) {amount := nat 2}

/-- error: fold_step%: binder amount shadows an existing local -/
#guard_msgs in
#check step_inputs% BumpInputs => fold_step% values from amount := .nat 0 with value => value

/-- error: record_step%: the required field ready is missing -/
#guard_msgs in
example : Step [] (.record fields) := record_step% { count := .nat 7 }

#check Effect4.Run.tapeOf
#eval "C1 public entries expose deriving, named records, captured folds, refusals, and the tape."
end EntryProbe
