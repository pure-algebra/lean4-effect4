module

public import Effect4.Modules.Pool.Steps
public import Effect4.Modules.Step
meta import Effect4.Schema.FieldRef.Elab

/-!
# Modules.Pool.Data — Pool's fold-free steps, written as data

Two of Pool's six steps fold nothing: `select` and `close`. Each is written here as a step over
the cell at the resource type `A` (`src/Effect4/Modules/Step.lean`), and its term is the
module's own term, by definition, at every `A` (`selectStep_eq`, `closeStep_eq`). The step
language's laws then give the two steps' agreement and typing
(`src/Effect4/Laws/Modules/Pool/Data.lean`; decisions row 330, slice L3).

The lease, the return, the withdrawal and the closer's step fold over the items or the waiters,
and they build records: they wait for folds and record construction in the step language.
-/

@[expose] public section

namespace Effect4.Pool.Data

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq (A : Ty) : cellTy A = .record (cellRecord A) := rfl

def closingF (A : Ty) : FieldRef (cellRecord A) .bool := field_ref% "closing"
def waitersF (A : Ty) : FieldRef (cellRecord A) (.list waiterTy) := field_ref% "waiters"

/-- The select step's inputs: the count, then the cell. -/
abbrev Γ (A : Ty) : List Ty := [.nat, .record (cellRecord A)]

def count (A : Ty) : Input (Γ A) .nat := .here _ _
def cell (A : Ty) : Input (Γ A) (.record (cellRecord A)) := .there _ (.here _ _)

/-- **The model's `select`.** Reply: the first `count` waiters. -/
def select (A : Ty) : Step (Γ A) (.prod (.list waiterTy) (.record (cellRecord A))) :=
  .pair (.take (.get (.var (cell A)) (waitersF A)) (.var (count A)))
    (.set (.var (cell A)) (waitersF A) (.drop (.get (.var (cell A)) (waitersF A)) (.var (count A))))

/-- The close's one input: the cell. -/
def only (A : Ty) : Input [.record (cellRecord A)] (.record (cellRecord A)) := .here _ _

/-- **The model's `close`.** Reply: `[this step began the close, the count of the waiters]`. -/
def close (A : Ty) : Step [.record (cellRecord A)] (.prod (.prod .bool .nat) (.record (cellRecord A))) :=
  .pair (.tuple2 (.not (.get (.var (only A)) (closingF A))) (.len (.get (.var (only A)) (waitersF A))))
    (.set (.var (only A)) (closingF A) (.bool true))

theorem selectStep_eq (A : Ty) (count s : TermSrc) :
    selectStep count s = (select A).term (Input.source [count, s]) := rfl

theorem closeStep_eq (A : Ty) (s : TermSrc) : closeStep s = (close A).term (Input.source [s]) := rfl

end Effect4.Pool.Data
