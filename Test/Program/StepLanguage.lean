import Effect4.Laws.Modules.Step
import Effect4.Modules.Semaphore.Steps
import Effect4.Schema.FieldRef.Elab

/-! The battery of the step language (decisions row 330, slice L2): Latch's cell and its release
written as steps over `Ty`, the three laws read at them, Semaphore's take-if-available written
as a step over its own cell, and one red control for each check. -/

set_option autoImplicit false

open Effect4.Program Effect4.Program.Authoring Effect4.Store Effect4.Schema Effect4.Schema.Model
open Effect4.Modules

namespace Test.Program.StepLanguage

/-! ## Latch's cell -/

def waiterTy : Ty := .record [("hint", false, .nat), ("id", false, .nat)]

def cellFields : List (String × Bool × Ty) := [("open", false, .bool), ("waiters", false, .list waiterTy)]

def cellTy : Ty := .record cellFields

def openF : FieldRef cellFields .bool := field_ref% "open"
def waitersF : FieldRef cellFields (.list waiterTy) := field_ref% "waiters"

def cell : Input [cellTy] cellTy := .here _ _

/-- The cell with no waiter: the clearing update that `release` and its next cell share. -/
def cleared : Step [cellTy] cellTy := .set (.var cell) waitersF (.emptyLike (.get (.var cell) waitersF))

/-- `release`: the reply (whether it was open, the woken waiters), and the next cell. -/
def release : Step [cellTy] (.prod (.prod .bool (.list waiterTy)) cellTy) :=
  .ite (.get (.var cell) openF)
    (.pair (.pair (.bool false) (.emptyLike (.get (.var cell) waitersF))) (.var cell))
    (.pair (.pair (.bool true) (.get (.var cell) waitersF)) cleared)

/-- `release`'s next cell alone: an update spine of the cell. -/
def releaseNext : Step [cellTy] cellTy := .ite (.get (.var cell) openF) (.var cell) cleared

/-- The fault "release opens", as data: it overwrites `open`. -/
def releaseOpens : Step [cellTy] cellTy :=
  .ite (.get (.var cell) openF) (.var cell)
    (.set cleared openF (.bool true))

-- Both checks pass: the records are canonical, and every type the checker needs is normal.
#guard release.canonical && release.normal && releaseNext.normal && releaseOpens.normal

-- Reader: the release's term reads its value, at every scope and identity context.
example (L : Leaves) (vs : Inputs L [cellTy]) {src : {t : Ty} → Input [cellTy] t → TermSrc}
    {env : Env} {path : List Nat} {vals : List Val}
    (hin : ∀ {t : Ty} (x : Input [cellTy] t),
      Reads (src x) env path vals ((imageAt L t).toVal (x.get vs))) :
    Reads (release.term src) env path vals ((imageAt L _).toVal (release.eval L vs)) :=
  Step.sound L vs hin release rfl

-- Reader: the release's term types at the release's type, at every scope.
example {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {src : {t : Ty} → Input [cellTy] t → TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (hin : ∀ {t : Ty} (x : Input [cellTy] t), TypesEach sig (src x) env path types t) :
    TypesEach sig (release.term src) env path types (.prod (.prod .bool (.list waiterTy)) cellTy) :=
  Step.typed_of_normal sig atoms hin release rfl

-- Reader: the release keeps `open`, on carriers and on the machine's record frame.
example (L : Leaves) (vs : Inputs L [cellTy]) :
    openF.get (releaseNext.eval L vs) = openF.get (cell.get vs) :=
  Step.frame L vs cell openF releaseNext rfl (by decide)

example (L : Leaves) (vs : Inputs L [cellTy]) :
    Effect4.Machine.Record.read false ((imageAt L cellTy).toVal (releaseNext.eval L vs)) "open" =
      Effect4.Machine.Record.read false ((imageAt L cellTy).toVal (cell.get vs)) "open" :=
  Step.frame_read L vs (by decide) cell openF releaseNext rfl (by decide)

-- The release's term is the hand term of probe MODS-1, at a scope.
#guard release.term (fun x => Input.source [var "s"] x) { names := ["s"] } [] ==
  (ifT (field (var "s") "open")
    (app "pair" [app "pair" [bool false, noneOf (field (var "s") "waiters")], var "s"])
    (app "pair" [app "pair" [bool true, field (var "s") "waiters"],
      recordSet (var "s") "waiters" (noneOf (field (var "s") "waiters"))])) { names := ["s"] } []

/-! ## A field by name follows its field

`Effect4.Semaphore.cellRecord` is Semaphore's own schema. A field inserted before `taken` moves
its position, and the reference by name moves with it (overwatch finding OW-03). -/

def withAvailable : List (String × Bool × Ty) := ("available", false, .nat) :: Effect4.Semaphore.cellRecord

#guard (field_ref% "taken" : FieldRef Effect4.Semaphore.cellRecord .nat).index == 2 &&
  (field_ref% "taken" : FieldRef withAvailable .nat).index == 3

/-! ## Red controls -/

-- The fault overwrites `open`, so the frame law's premise fails for it.
#guard releaseOpens.writes.contains openF.name

-- A field read that yields a record is no update spine.
#guard (Step.get (.var (.here (.record [("inner", false, cellTy)]) [])) (.here "inner" cellTy [])
  : Step [.record [("inner", false, cellTy)]] cellTy).spine == none

-- A record whose names are out of order fails both checks: the machine's overwrite would sort
-- its fields, so the read and write laws do not apply.
#guard
  let unsorted : List (String × Bool × Ty) := [("z", false, .bool), ("a", false, .bool)]
  let read : Step [.record unsorted] .bool := .get (.var (.here _ _)) (.here _ _ _)
  !read.canonical && !read.normal

-- A selection at a type that is not its own normal form passes the reading check and fails the
-- typing check: the checker answers the normal form, a union in canonical order.
#guard
  let both : Ty := .union .bool .nat
  let pick : Step [both] both := .ite (.bool true) (.var (.here _ _)) (.var (.here _ _))
  pick.canonical && !pick.normal && both.normalize != both

-- A reference by name refuses a missing field, a field of another type, an optional field,
-- two fields of one name, and a schema it cannot read.
/-- error: field_ref%: the schema has no field takn -/
#guard_msgs in
example : FieldRef Effect4.Semaphore.cellRecord .nat := field_ref% "takn"

/-- error: field_ref%: the field taken has type Ty.nat, not Ty.bool -/
#guard_msgs in
example : FieldRef Effect4.Semaphore.cellRecord .bool := field_ref% "taken"

/-- error: field_ref%: the field a is optional; a reference names a required field -/
#guard_msgs in
example : FieldRef [("a", true, .nat)] .nat := field_ref% "a"

/-- error: field_ref%: two fields of the schema are named a -/
#guard_msgs in
example : FieldRef [("a", false, .nat), ("a", false, .nat)] .nat := field_ref% "a"

/-- error: field_ref%: the schema fs does not reduce to a list of literal fields -/
#guard_msgs in
example (fs : List (String × Bool × Ty)) : FieldRef fs .nat := field_ref% "a"

end Test.Program.StepLanguage
