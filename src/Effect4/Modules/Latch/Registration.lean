module

public import Effect4.Modules.Latch.Steps
meta import Effect4.Modules.Step.Elab

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

/-- A cell with the supplied open flag and no registrations or scheduled batch. -/
def initial : Step [.bool] cellTy := record_step% {
  «open» := .var (.here _ _), pending := .nil, scheduled := .bool false, waiters := .nil }

/-- The callback answers immediately when open, or appends one registration when closed. -/
def awaitLatch : Step [idTy, idTy, cellTy] (.prod .bool cellTy) :=
  let c := Step.var (.there _ (.there _ (.here _ _)))
  let waiter : Step [idTy, idTy, cellTy] waiterTy := record_step% {
    id := .var (.here _ _), hint := .var (.there _ (.here _ _)) }
  .ite (.get c openF) (.pair (.bool true) c)
    (.pair (.bool false) (.set c waitersF (.snoc (.get c waitersF) waiter)))

/-- A single pass removes the first matching registration and reports whether it found one. -/
def removeFirst {Γ : List Ty} (id : Input Γ idTy) (xs : Step Γ (.list waiterTy)) :
    Step Γ (.prod .bool (.list waiterTy)) :=
  .fold xs (.pair (.bool false) (.emptyLike xs))
    (.ite (.fst (.var (.here _ _)))
      (.pair (.bool true) (.snoc (.snd (.var (.here _ _))) (.var (.there _ (.here _ _)))))
      (.ite (.sameDeferred (.get (.var (.there _ (.here _ _))) waiterIdF)
          (.var (.there _ (.there _ id))))
        (.pair (.bool true) (.snd (.var (.here _ _))))
        (.pair (.bool false) (.snoc (.snd (.var (.here _ _))) (.var (.there _ (.here _ _)))))))

/-- Cleanup searches waiters first, then the still-attached scheduled batch. -/
def withdraw : Step [idTy, cellTy] (.prod .unit cellTy) :=
  let c := Step.var (.there _ (.here _ _))
  let removed := removeFirst (.here _ _) (.get c waitersF)
  .ite (.fst removed) (.pair .unit (.set c waitersF (.snd removed)))
    (.ite (.get c scheduledF)
      (.pair .unit (.set c pendingF (.snd (removeFirst (.here _ _) (.get c pendingF)))))
      (.pair .unit c))

end Data

/-- Construct the initial cell through the shared step translation. -/
def initialStep (isOpen : TermSrc) : TermSrc := Data.initial.term (Input.source [isOpen])
/-- Register a callback through the shared step translation. -/
def awaitStep (id hint cell : TermSrc) : TermSrc := Data.awaitLatch.term (Input.source [id, hint, cell])
/-- Remove one registration through the shared step translation. -/
def withdrawStep (id cell : TermSrc) : TermSrc := Data.withdraw.term (Input.source [id, cell])

end Effect4.Latch
