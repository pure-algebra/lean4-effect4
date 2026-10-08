module

public import Effect4.Modules.Queue.Steps
public import Effect4.Modules.Step
meta import Effect4.Schema.FieldRef.Elab

/-!
# Modules.Queue.Data — the Queue's fold-free step, written as data

One of the Queue's steps folds nothing: `size`, a read of the buffer's length. It is written
here as a step over the cell at the message type `A` (`src/Effect4/Modules/Step.lean`), and its
term is the module's own term, by definition, at every `A` (`sizeStep_eq`). The step language's
laws then give its agreement and typing (`src/Effect4/Laws/Modules/Queue/Data.lean`; decisions
row 330, slice L3).

The take, the offer, the poll and the two withdrawals fold over the takers or the offers, build
records, and use the empty constants `noneT` and `nilT`: they wait for folds, record
construction and typed empty constants in the step language.
-/

@[expose] public section

namespace Effect4.Queue.Data

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq (A : Ty) : cellTy A = .record (cellRecord A) := rfl

def msgsF (A : Ty) : FieldRef (cellRecord A) (.list A) := field_ref% "msgs"

def cell (A : Ty) : Input [.record (cellRecord A)] (.record (cellRecord A)) := .here _ _

/-- **The model's `size` in an opened queue**: the buffer's length. -/
def size (A : Ty) : Step [.record (cellRecord A)] .nat := .len (.get (.var (cell A)) (msgsF A))

theorem sizeStep_eq (A : Ty) (s : TermSrc) : sizeStep A s = (size A).term (Input.source [s]) := rfl

end Effect4.Queue.Data
