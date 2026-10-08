module

public import Effect4.Modules.Step.Inputs
meta import Effect4.Modules.Step.Elab.Inputs
meta import Effect4.Schema.FieldRef.Elab

/-!
# Modules.Latch.Steps — the Latch's steps, written natively as data

The first module whose steps are written in the step language from the start
(`src/Effect4/Modules/Step.lean`; decisions row 330, slice L3). Each step is data over the one
input, the cell. Its term is the step's term (`Step.term`), so no hand term exists, and its laws
are the language's.

The cell is rc.112's `class Latch` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`): its
`_isOpen`, its `waiters`, and its `scheduled` batch. The batch is two fields here: `pending`, the
waiters of the batch, and `scheduled`, whether a flush is scheduled. rc.112's `scheduled` is
`undefined` exactly when `scheduled` is false. A waiter is its hint and its identity, both
`Deferred` identities (`idTy`).

| Step | rc.112 | Reply |
| --- | --- | --- |
| `isOpenStep` | `isOpen()` | whether the latch is open |
| `wakeStep true` | `open`, then `scheduleUnsafe` | `[the answer, whether a flush is posted]` |
| `wakeStep false` | `release`, then `scheduleUnsafe` | `[the answer, whether a flush is posted]` |
| `flushStep` | `flushScheduled` | the batch, in order |
| `closeStep` | `closeUnsafe` | whether the step closed the latch |

A wake moves the waiters into the batch. It posts one flush only when no flush is scheduled,
and otherwise it appends to the batch already scheduled, as `scheduleUnsafe` does. So two wakes
before a flush resume their waiters in one batch, in the order of enrolment (probe MODS-10).

Registration, cleanup, and the initial cell are in `Modules.Latch.Registration`.
The wrapper owns the posted flush and each waiter's suspension.
The laws are in `src/Effect4/Laws/Modules/Latch/`.
-/

@[expose] public section

namespace Effect4.Latch

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

/-- A waiter's record: its hint, then its identity. -/
def waiterRecord : List (String × Bool × Ty) := [("hint", false, idTy), ("id", false, idTy)]

/-- A waiter uses the one declared field list. -/
def waiterTy : Ty := .record waiterRecord

/-- The cell's fields in the canonical order. -/
def cellRecord : List (String × Bool × Ty) :=
  [("open", false, .bool), ("pending", false, .list waiterTy), ("scheduled", false, .bool),
   ("waiters", false, .list waiterTy)]

/-- **The cell's type.** -/
def cellTy : Ty := .record cellRecord

namespace Data

def openF : FieldRef cellRecord .bool := field_ref% "open"
def pendingF : FieldRef cellRecord (.list waiterTy) := field_ref% "pending"
def scheduledF : FieldRef cellRecord .bool := field_ref% "scheduled"
def waitersF : FieldRef cellRecord (.list waiterTy) := field_ref% "waiters"

/-- The cell input has one declaration for both stored steps and source applications. -/
step_context% CellInputs (cell : cellTy)
abbrev Γ : List Ty := CellInputs.types

abbrev cell : Input Γ (.record cellRecord) := input_ref% (CellInputs) cell

/-- The cell, as a step. -/
abbrev c : Step Γ (.record cellRecord) := .var cell

/-- **`isOpen()`**. -/
def isOpen : Step Γ .bool := .get c openF

/-- The cell after a wake: opened for `open`, as it is for `release`. -/
def opened (setOpen : Bool) (r : Step Γ (.record cellRecord)) : Step Γ (.record cellRecord) :=
  if setOpen then .set r openF (.bool true) else r

/-- **`open` (`setOpen` true) and `release` (`setOpen` false), each with `scheduleUnsafe`.**
Reply: `[the answer, whether a flush is posted]`. An open latch answers false and changes
nothing. With no waiter the answer is true and nothing is posted. Otherwise the waiters join
the batch: a new batch posts a flush, and a scheduled batch takes them at its end. -/
def wake (setOpen : Bool) : Step Γ (.prod (.prod .bool .bool) (.record cellRecord)) :=
  .ite (.get c openF) (.pair (.tuple2 (.bool false) (.bool false)) c)
    (.ite (.isZero (.len (.get c waitersF)))
      (.pair (.tuple2 (.bool true) (.bool false)) (opened setOpen c))
      (.ite (.get c scheduledF)
        (.pair (.tuple2 (.bool true) (.bool false))
          (opened setOpen (.set (.set c pendingF (.append (.get c pendingF) (.get c waitersF)))
            waitersF (.emptyLike (.get c waitersF)))))
        (.pair (.tuple2 (.bool true) (.bool true))
          (opened setOpen (.set (.set (.set c pendingF (.get c waitersF)) scheduledF (.bool true))
            waitersF (.emptyLike (.get c waitersF)))))))

/-- **`flushScheduled`**: the batch, and the cell with no batch scheduled. With no batch
scheduled it answers nothing and changes nothing. -/
def flush : Step Γ (.prod (.list waiterTy) (.record cellRecord)) :=
  .ite (.get c scheduledF)
    (.pair (.get c pendingF)
      (.set (.set c pendingF (.emptyLike (.get c pendingF))) scheduledF (.bool false)))
    (.pair (.emptyLike (.get c pendingF)) c)

/-- **`closeUnsafe`**: whether the step closed the latch. -/
def close : Step Γ (.prod .bool (.record cellRecord)) :=
  .ite (.get c openF) (.pair (.bool true) (.set c openF (.bool false))) (.pair (.bool false) c)

end Data

/-! ## The terms: each the step's term -/

def isOpenStep (s : TermSrc) : TermSrc := Data.isOpen.term (input_sources% (Data.CellInputs) {cell := s})
def wakeStep (setOpen : Bool) (s : TermSrc) : TermSrc := (Data.wake setOpen).term (input_sources% (Data.CellInputs) {cell := s})
def flushStep (s : TermSrc) : TermSrc := Data.flush.term (input_sources% (Data.CellInputs) {cell := s})
def closeStep (s : TermSrc) : TermSrc := Data.close.term (input_sources% (Data.CellInputs) {cell := s})

end Effect4.Latch
