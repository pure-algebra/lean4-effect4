import Effect4.Laws.Program.Typed.Assembly

/-!
# Formal pass, seat PROOFS — red control: the typed state does not exclude a halted machine

Base `efd67af1`. Reading aid for `note.md` §3 G4. `RunMachine.halt` sets only `stuck`
(`Machine/Fibers.lean:665-667`); `TypedState` (`Typed/Assembly.lean:67-72`) reads `fibers`,
`races`, `state` and `nextToken`, never `stuck`. So halting keeps the typed state, a halting
command with an empty residue meets `StepPreserves`'s conclusion at the same world, and M6's
capstone cannot yield "a reachable machine is never stuck" (row 52, system map R9) without a
clause that reads `stuck`.
-/

set_option autoImplicit false

namespace FormalPass.Proofs.HaltTyped
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-- Halting changes no field the typed state reads. -/
theorem typedState_halt (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : TypedState root rootTy w m) : TypedState root rootTy w (m.halt why) := by
  obtain ⟨valid, ok, deliv⟩ := h
  exact ⟨{ ids := valid.ids, fibers := valid.fibers, heap := valid.heap,
           promises := valid.promises, tokens := valid.tokens, tokenBound := valid.tokenBound,
           tokenTargets := valid.tokenTargets, state := valid.state, wf := valid.wf,
           cells := valid.cells, fiberClosed := valid.fiberClosed, heapClosed := valid.heapClosed,
           promiseClosed := valid.promiseClosed, tokenClosed := valid.tokenClosed,
           root := valid.root },
         ⟨ok.c0, ok.c1, ok.c2⟩, deliv⟩

/-- The empty residue is typed. -/
theorem queueOk_nil (root : ProgramSource) (w : W) : QueueOk root w [] := by
  intro c hc
  cases hc

/-- A command whose result is `(m.halt why, [])` (for example `linkScope` on an unknown scope,
`Machine/Fibers.lean:1010`) satisfies the conclusion `StepPreserves` asks for, at the same world. -/
theorem halting_result_typed (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : TypedState root rootTy w m) :
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' (m.halt why) ∧ QueueOk root w' [] :=
  ⟨w, leHost_refl w, typedState_halt root rootTy w m why h, queueOk_nil root w⟩

/-- Hence the typed state does not imply that the machine is not stuck: whenever some machine
is typed, a stuck one is typed at the same world. -/
theorem typed_not_imply_running (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : TypedState root rootTy w m) :
    ∃ m', TypedState root rootTy w m' ∧ m'.stuck = some why :=
  ⟨m.halt why, typedState_halt root rootTy w m why h, rfl⟩

end FormalPass.Proofs.HaltTyped

open FormalPass.Proofs.HaltTyped in
#print axioms typedState_halt
open FormalPass.Proofs.HaltTyped in
#print axioms queueOk_nil
open FormalPass.Proofs.HaltTyped in
#print axioms halting_result_typed
open FormalPass.Proofs.HaltTyped in
#print axioms typed_not_imply_running
