module

public import Effect4.Modules.Semaphore.Steps
public import Effect4.Modules.Step
meta import Effect4.Schema.FieldRef.Elab

/-!
# Modules.Semaphore.Data — Semaphore's fold-free steps, written as data

Two of Semaphore's five steps fold nothing: `takeIfAvailable` and `release`. Each is written here
as a step over the inputs `[count, cell]` (`src/Effect4/Modules/Step.lean`), and its term is the
module's own term, by definition (`takeIfAvailableStep_eq`, `releaseStep_eq`). So the step
language's laws give the two steps' agreement and typing
(`src/Effect4/Laws/Modules/Semaphore/Data.lean`; decisions row 330, slice L3).

The other three steps fold over the waiters (`removeWaiter`, `fromFirst`), and wait for folds in
the step language.
-/

@[expose] public section

namespace Effect4.Semaphore.Data

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq : cellTy = .record cellRecord := rfl

def permitsF : FieldRef cellRecord .nat := field_ref% "permits"
def takenF : FieldRef cellRecord .nat := field_ref% "taken"
def waitersF : FieldRef cellRecord (.list waiterTy) := field_ref% "waiters"

/-- A step's two inputs: the request's count, then the cell. -/
abbrev Γ : List Ty := [.nat, .record cellRecord]

def count : Input Γ .nat := .here _ _
def cell : Input Γ (.record cellRecord) := .there _ (.here _ _)

/-- The free count: the total less what is taken. -/
def free : Step Γ .nat := .sub (.get (.var cell) permitsF) (.get (.var cell) takenF)

/-- **The model's `takeIfAvailable`.** Reply: whether the request took. -/
def takeIfAvailable : Step Γ (.prod .bool (.record cellRecord)) :=
  .ite (.not (.lt free (.var count)))
    (.pair (.bool true) (.set (.var cell) takenF (.add (.get (.var cell) takenF) (.var count))))
    (.pair (.bool false) (.var cell))

/-- What a release leaves taken: `taken` less the count, truncated. -/
def left : Step Γ .nat := .sub (.get (.var cell) takenF) (.var count)

/-- **The model's `release`.** Reply: `[the free count, whether a waiter is enrolled]`. -/
def release : Step Γ (.prod (.prod .nat .bool) (.record cellRecord)) :=
  .pair (.tuple2 (.sub (.get (.var cell) permitsF) left) (.not (.isZero (.len (.get (.var cell) waitersF)))))
    (.set (.var cell) takenF left)

/-- The take-if-available step's term is the module's term. -/
theorem takeIfAvailableStep_eq (need s : TermSrc) :
    takeIfAvailableStep need s = takeIfAvailable.term (Input.source [need, s]) := rfl

/-- The release step's term is the module's term. -/
theorem releaseStep_eq (n s : TermSrc) : releaseStep n s = release.term (Input.source [n, s]) := rfl

end Effect4.Semaphore.Data
