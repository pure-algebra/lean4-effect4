import Tools.Explain

/-!
Controls of `#explain` and `#obligations` (`tools/Tools/Explain.lean`), on steps and theorems
declared here, so no later theorem of the tree changes the expected answers. Each line is a finite
evaluation of the tool:

1. a fold-free step over a record: both checks pass, the footprint and the spine are read, and
   the three shared laws are named;
2. a theorem about the step is listed with its standing;
3. a red control: a record whose names are out of order fails both checks, and no law is named;
4. the namespace's obligations count what is proved.
-/

set_option autoImplicit false
open Effect4.Program Effect4.Modules

namespace Test.Audit.Explain

def fields : List (String × Bool × Ty) := [("count", false, .nat), ("ready", false, .bool)]
def countF : Effect4.Schema.FieldRef fields .nat := .here _ _ _
def bump : Step [.record fields] (.record fields) :=
  .set (.var (.here _ _)) countF (.add (.get (.var (.here _ _)) countF) (.nat 1))

theorem bump_writes : bump.writes = ["count"] := rfl

/--
info: Test.Audit.Explain.bump (definition, Test.Audit.Explain)
  type: Step [Ty.record fields] (Ty.record fields)
step: inputs [{count: nat, ready: bool}]; answers {count: nat, ready: bool}
  checks: normal true, canonical true
  writes: [count]; spine: 0
  law: typing: the normality check closes by `rfl`; `Step.typed_of_normal` also requires native atom typing, typed inputs and fold scope alignment where used
  law: reading: the canonicality check closes by `rfl`; `Step.sound` also requires input readings, fold scope alignment and deferred identity interpretation where used
  law: frame: `Step.frame` applies on input 0, outside the writing footprint
theorems that state something about it (1):
  Test.Audit.Explain.bump_writes: proved
-/
#guard_msgs in
#explain bump

def unsorted : List (String × Bool × Ty) := [("ready", false, .bool), ("count", false, .nat)]
def readyF : Effect4.Schema.FieldRef unsorted .bool := .here _ _ _
def flip : Step [.record unsorted] (.record unsorted) :=
  .set (.var (.here _ _)) readyF (.not (.get (.var (.here _ _)) readyF))

/--
info: Test.Audit.Explain.flip (definition, Test.Audit.Explain)
  type: Step [Ty.record unsorted] (Ty.record unsorted)
step: inputs [{ready: bool, count: nat}]; answers {ready: bool, count: nat}
  checks: normal false, canonical false
  writes: [ready]; spine: 0
  law: frame: `Step.frame` applies on input 0, outside the writing footprint
-/
#guard_msgs in
#explain flip

/--
info: Test.Audit.Explain: 1 theorems; 1 proved, 0 modulo goals, 0 planned goals
  Test.Audit.Explain.bump_writes: proved
-/
#guard_msgs in
#obligations Test.Audit.Explain

end Test.Audit.Explain
