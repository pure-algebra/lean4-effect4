module

public import Effect4.Library.Latch.Steps
public import Effect4.Step.Inputs
public import Effect4.Step.Lists
meta import Effect4.Step.Elab
meta import Effect4.Step.Elab.Inputs

/-!
# Latch registration and cleanup

The independent model is in `Laws.Modules.Latch.Model`.
These steps transcribe rc.112 `internal/effect.ts`, lines 5624–5639.
Cleanup removes the first matching registration, searching waiters before the scheduled batch.
It leaves the scheduled flag unchanged, including when the batch becomes empty.
The wrapper still owns suspension, interruption delivery, and posting the flush.
-/

@[expose] public section
set_option autoImplicit false

namespace Effect4.Latch
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

namespace Data

/-- The identity of a registration, through the canonical waiter schema. -/
def waiterIdF : FieldRef waiterRecord idTy := field_ref% "id"

step_context% InitialInputs (opened : .bool)
step_context% AwaitInputs (id : idTy, hint : idTy, cell : cellTy)
step_context% WithdrawInputs (id : idTy, cell : cellTy)

/-- A cell with the supplied open flag and no registrations or scheduled batch. -/
def initial : Step InitialInputs.types cellTy := step_inputs% InitialInputs => record_step% {
  «open» := opened, pending := .nil, scheduled := .bool false, waiters := .nil }

/-- The callback answers immediately when open, or appends one registration when closed. -/
def awaitLatch : Step AwaitInputs.types (.prod .bool cellTy) := step_inputs% AwaitInputs =>
  let waiter : Step _ waiterTy := record_step% { id := id, hint := hint }
  .ite (.get cell openF) (.pair (.bool true) cell)
    (.pair (.bool false) (.set cell waitersF (.snoc (.get cell waitersF) waiter)))

/-- A single pass removes the first matching registration and reports whether it found one. -/
def removeFirst {Γ : List Ty} (id : Step Γ idTy) (xs : Step Γ (.list waiterTy)) :
    Step Γ (.prod .bool (.list waiterTy)) :=
  Step.Lists.removeFirst xs (item_step% xs with waiter =>
    .sameDeferred (.get waiter waiterIdF) id)

/-- Cleanup searches waiters first, then the still-attached scheduled batch. -/
def withdraw : Step WithdrawInputs.types (.prod .unit cellTy) := step_inputs% WithdrawInputs =>
  let removed := removeFirst id (.get cell waitersF)
  .ite (.fst removed) (.pair .unit (.set cell waitersF (.snd removed)))
    (.ite (.get cell scheduledF)
      (.pair .unit (.set cell pendingF (.snd (removeFirst id (.get cell pendingF)))))
      (.pair .unit cell))

end Data

/-- Construct the initial cell through the shared step translation. -/
def initialStep (isOpen : TermSrc) : TermSrc := Data.initial.term (input_sources% (Data.InitialInputs) {opened := isOpen})
/-- Register a callback through the shared step translation. -/
def awaitStep (id hint cell : TermSrc) : TermSrc := Data.awaitLatch.term (input_sources% (Data.AwaitInputs) {id := id, hint := hint, cell := cell})
/-- Remove one registration through the shared step translation. -/
def withdrawStep (id cell : TermSrc) : TermSrc := Data.withdraw.term (input_sources% (Data.WithdrawInputs) {id := id, cell := cell})

end Effect4.Latch
