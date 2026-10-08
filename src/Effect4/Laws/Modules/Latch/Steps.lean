import Effect4.Modules.Latch.Steps
import Effect4.Laws.Modules.Latch.Model
import Effect4.Laws.Modules.Step
import Effect4.Laws.Auto.Semantics

/-!
# The Latch's steps agree with its model, and are typed

The Latch is written natively in the step language (`src/Effect4/Modules/Latch/Steps.lean`), so
its relation to the model is native too: **the cell's value is the image of the model state's
carrier** (`cellVal`), by definition. The agreement of each step is then the step language's
reading law (`Step.sound`) and one equation of Lean values: the step's value on the carrier is
the model's transition (`wake_eval`, `flush_eval`, `close_eval`, `isOpen_eval`). Each typing
statement is the step language's typing law, by its check, with no premise.

Placement: concept `translation-simulation`, requirement R10: the claim `latch-steps-agree`
(`latch_steps_agree`). The typing statements are concept `store-typing`, requirement R4.
Reach: every model state and table, every scope, every caller's term that reads the cell. The
statements say nothing of `await`, of interruption, of the posted flush's fiber, or of
liveness.
-/

set_option autoImplicit false

namespace Effect4.Latch.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Schema
open Effect4.Schema.Model Effect4.Modules
open Effect4.Latch.Data (Γ)

/-! ## The relation: the carrier's image -/

/-- A waiter on the carrier of the opaque context: its hint and its identity through the table. -/
def waiterC (tb : Table) (i : Nat) : CarrierAt Leaves.opaque waiterTy :=
  (Val.promise (tb.hint i), (Val.promise (tb.handle i), ()))

/-- **A model state on the carrier of the opaque context.** -/
def cellC (tb : Table) (s : State) : CarrierAt Leaves.opaque cellTy :=
  (s.isOpen, (s.pending.map (waiterC tb), (s.scheduled, (s.waiters.map (waiterC tb), ()))))

/-- **The cell's value for a model state**: its carrier's image. -/
def cellVal (tb : Table) (s : State) : Val := (imageAt Leaves.opaque cellTy).toVal (cellC tb s)

/-- A batch as the flush answers it: each waiter's record through the table. -/
def batchVal (tb : Table) (batch : List Nat) : Val :=
  (imageAt Leaves.opaque (.list waiterTy)).toVal (batch.map (waiterC tb))

/-- The step's one input at a model state. -/
abbrev inputsAt (tb : Table) (s : State) : Inputs Leaves.opaque Γ := (cellC tb s, ())

/-! ## Each step's value is the model's transition -/

theorem isOpen_eval (tb : Table) (s : State) :
    Data.isOpen.eval Leaves.opaque (inputsAt tb s) = s.isOpen := rfl

theorem wake_eval (tb : Table) (setOpen : Bool) (s : State) :
    (Data.wake setOpen).eval Leaves.opaque (inputsAt tb s) =
      (((wake setOpen s).2.1, (wake setOpen s).2.2), cellC tb (wake setOpen s).1) := by
  obtain ⟨isOpen, waiters, pending, scheduled⟩ := s
  cases isOpen
  · cases waiters with
    | nil => cases setOpen <;> rfl
    | cons w ws =>
      cases scheduled
      · cases setOpen <;> rfl
      · cases setOpen
        · show ((true, false), (false, (pending.map (waiterC tb) ++ (w :: ws).map (waiterC tb),
            (true, (([] : List _), ()))))) =
            ((true, false), (false, ((pending ++ w :: ws).map (waiterC tb), (true, ([], ())))))
          rw [List.map_append]
        · show ((true, false), (true, (pending.map (waiterC tb) ++ (w :: ws).map (waiterC tb),
            (true, (([] : List _), ()))))) =
            ((true, false), (true, ((pending ++ w :: ws).map (waiterC tb), (true, ([], ())))))
          rw [List.map_append]
  · rfl

theorem flush_eval (tb : Table) (s : State) :
    Data.flush.eval Leaves.opaque (inputsAt tb s) =
      ((flush s).2.map (waiterC tb), cellC tb (flush s).1) := by
  obtain ⟨isOpen, waiters, pending, scheduled⟩ := s
  cases scheduled <;> rfl

theorem close_eval (tb : Table) (s : State) :
    Data.close.eval Leaves.opaque (inputsAt tb s) = ((close s).2, cellC tb (close s).1) := by
  obtain ⟨isOpen, waiters, pending, scheduled⟩ := s
  cases isOpen <;> rfl

/-! ## The four steps agree with the model -/

section Agree

variable (tb : Table) (s : State) {cellSrc : TermSrc} {env : Env} {path : List Nat}
  {vals : List Val} (readsCell : Reads cellSrc env path vals (cellVal tb s))
include readsCell

/-- `isOpen()` reads whether the model is open. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem isOpenStep_agrees : Reads (Latch.isOpenStep cellSrc) env path vals (Val.bool s.isOpen) :=
  Step.sound Leaves.opaque (inputsAt tb s) (Input.reads_cons readsCell Input.reads_nil)
    Data.isOpen rfl

/-- **A wake agrees with the model's `wake`**: the reply, whether a flush is posted, and the
model's next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem wakeStep_agrees (setOpen : Bool) :
    Reads (Latch.wakeStep setOpen cellSrc) env path vals
      (Val.tuple [Val.tuple [.bool (wake setOpen s).2.1, .bool (wake setOpen s).2.2],
        cellVal tb (wake setOpen s).1]) := by
  have reads := Step.sound Leaves.opaque (inputsAt tb s)
    (Input.reads_cons readsCell Input.reads_nil) (Data.wake setOpen) (by cases setOpen <;> rfl)
  rw [wake_eval] at reads
  exact reads

/-- **The flush agrees with the model's `flush`**: the batch in order, and the next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem flushStep_agrees :
    Reads (Latch.flushStep cellSrc) env path vals
      (Val.tuple [batchVal tb (flush s).2, cellVal tb (flush s).1]) := by
  have reads := Step.sound Leaves.opaque (inputsAt tb s)
    (Input.reads_cons readsCell Input.reads_nil) Data.flush rfl
  rw [flush_eval] at reads
  exact reads

/-- **The close agrees with the model's `close`.** -/
@[semantics "translation-simulation" (requirement := R10)]
theorem closeStep_agrees :
    Reads (Latch.closeStep cellSrc) env path vals
      (Val.tuple [.bool (close s).2, cellVal tb (close s).1]) := by
  have reads := Step.sound Leaves.opaque (inputsAt tb s)
    (Input.reads_cons readsCell Input.reads_nil) Data.close rfl
  rw [close_eval] at reads
  exact reads

end Agree

/-- **The Latch's four steps agree with its model**: one field per step, at its statement. -/
structure StepsAgree : Prop where
  isOpen : ∀ (tb : Table) (s : State) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val}, Reads cellSrc env path vals (cellVal tb s) →
      Reads (Latch.isOpenStep cellSrc) env path vals (Val.bool s.isOpen)
  wake : ∀ (tb : Table) (s : State) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val}, Reads cellSrc env path vals (cellVal tb s) → ∀ setOpen : Bool,
      Reads (Latch.wakeStep setOpen cellSrc) env path vals
        (Val.tuple [Val.tuple [.bool (wake setOpen s).2.1, .bool (wake setOpen s).2.2],
          cellVal tb (wake setOpen s).1])
  flush : ∀ (tb : Table) (s : State) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val}, Reads cellSrc env path vals (cellVal tb s) →
      Reads (Latch.flushStep cellSrc) env path vals
        (Val.tuple [batchVal tb (flush s).2, cellVal tb (flush s).1])
  close : ∀ (tb : Table) (s : State) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val}, Reads cellSrc env path vals (cellVal tb s) →
      Reads (Latch.closeStep cellSrc) env path vals
        (Val.tuple [.bool (close s).2, cellVal tb (close s).1])

/-- **The Latch's steps agree with its model** (claim `latch-steps-agree`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem latch_steps_agree : StepsAgree where
  isOpen tb s _ _ _ _ readsCell := isOpenStep_agrees tb s readsCell
  wake tb s _ _ _ _ readsCell setOpen := wakeStep_agrees tb s readsCell setOpen
  flush tb s _ _ _ _ readsCell := flushStep_agrees tb s readsCell
  close tb s _ _ _ _ readsCell := closeStep_agrees tb s readsCell

/-! ## The four steps are typed -/

section Typed

variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy) {cellSrc : TermSrc}
  {env : Env} {path : List Nat} {types : List Ty}
  (typesCell : TypesEach sig cellSrc env path types cellTy)
include atoms typesCell

@[semantics "store-typing" (requirement := R4)]
theorem isOpenStep_types : TypesEach sig (Latch.isOpenStep cellSrc) env path types .bool :=
  Step.typed_of_normal sig atoms (Input.types_cons typesCell Input.types_nil) Data.isOpen rfl

@[semantics "store-typing" (requirement := R4)]
theorem wakeStep_types (setOpen : Bool) :
    TypesEach sig (Latch.wakeStep setOpen cellSrc) env path types
      (.prod (.prod .bool .bool) cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons typesCell Input.types_nil) (Data.wake setOpen)
    (by cases setOpen <;> rfl)

@[semantics "store-typing" (requirement := R4)]
theorem flushStep_types :
    TypesEach sig (Latch.flushStep cellSrc) env path types (.prod (.list waiterTy) cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons typesCell Input.types_nil) Data.flush rfl

@[semantics "store-typing" (requirement := R4)]
theorem closeStep_types :
    TypesEach sig (Latch.closeStep cellSrc) env path types (.prod .bool cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons typesCell Input.types_nil) Data.close rfl

end Typed

end Effect4.Latch.Model
