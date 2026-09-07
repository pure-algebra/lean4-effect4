import Effect4.Program.RuntimeR
import Test.Program.RuntimeRReference
import Test.Program.RuntimeRContract

/-!
# Simulation contract — the P3 judgment and the P4 corollary, pinned

Packet: `Test/contracts/program-runtime-r.contract.md` (P3 and P4, 2026-09-07).
`run_eq_ref` (`Program/RuntimeR.lean`) is universal: on every program, every compile
budget, every command budget, every `Completion` tape and every choice list the frame
machine's replay and the term reference's replay end the same way and observe the same
exits and stores. The theorems below instantiate it on the reference battery's programs
and tapes, so the finite `agrees` guards of `RuntimeRContract` are consequences of one
proof; each receipt has a `#guard` beside it that evaluates the same statement, so a
statement that stopped reading what it names would be caught at once. The P4 receipts
instantiate the straight corollary on the compile contract's programs with the side
conditions discharged by `decide`, at the fixed budget of `run_eq_meaning`.

The proof receipts compare Lean machines only (`RSTEP-FB-HOST`). The final section
retains a known host discrepancy, E4-CHECK-CE-016, without asserting its repair.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.SimulationContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Sched
open Effect4.Program.Agreement (depth steps)
open Test.Program.RuntimeRReference
open Test.Syntax.CompileContract (fuel pSucceed pBindSync pFail pCatch pOnExit pRefSet)

/-! ## P3 on the reference tapes: classification and the whole observation -/

/-- The judgment on one reference program and tape. -/
def RefAgrees (e : NativeEff) (tape : List Api.Decision) : Prop :=
  (run e tape).outcome = classify (replayR e budget tape) ∧
    obs (run e tape).machine = obsR (replayR e budget tape).machine

/-- Every reference program on every tape, as one instance of `run_eq_ref`. -/
theorem ref_agrees (e : NativeEff) (tape : List Api.Decision) : RefAgrees e tape :=
  run_eq_ref e budget tape

theorem ref_waiting_failure : RefAgrees waiting failureTape := ref_agrees _ _
theorem ref_waiting_wrongToken : RefAgrees waiting wrongTokenTape := ref_agrees _ _
theorem ref_suspended_fire : RefAgrees suspendedBind fireTape := ref_agrees _ _
theorem ref_deferred_join : RefAgrees deferredJoin fireTape := ref_agrees _ _
theorem ref_scoped_context : RefAgrees scopedContext startTape := ref_agrees _ _
theorem ref_race_winner : RefAgrees raceWinner startTape := ref_agrees _ _
theorem ref_interrupt_live : RefAgrees interruptLive startTape := ref_agrees _ _
theorem ref_ensured_interrupt : RefAgrees ensured interruptTape := ref_agrees _ _
theorem ref_par_two : RefAgrees parTwo fireTape := ref_agrees _ _

-- The same statements, evaluated: the reference battery reads what the theorem names.
#guard decide (obs (run waiting failureTape).machine = obsR (replayR waiting budget failureTape).machine)
#guard decide ((run waiting failureTape).outcome = classify (replayR waiting budget failureTape))
#guard decide (obs (run suspendedBind fireTape).machine = obsR (replayR suspendedBind budget fireTape).machine)
#guard decide (obs (run scopedContext startTape).machine = obsR (replayR scopedContext budget startTape).machine)
#guard decide (obs (run raceWinner startTape).machine = obsR (replayR raceWinner budget startTape).machine)
#guard decide ((run raceWinner startTape).outcome = classify (replayR raceWinner budget startTape))
#guard decide (obs (run ensured interruptTape).machine = obsR (replayR ensured budget interruptTape).machine)
#guard decide (obs (run parTwo fireTape).machine = obsR (replayR parTwo budget fireTape).machine)

/-- The root's exit, read on both machines. -/
theorem ref_exit_waiting :
    (run waiting failureTape).exit =
      ((replayR waiting budget failureTape).machine.fiber? Api.root).bind RunFiber.exit :=
  run_eq_ref_exit waiting budget failureTape

#guard decide ((run waiting failureTape).exit =
  ((replayR waiting budget failureTape).machine.fiber? Api.root).bind RunFiber.exit)

/-- Both sufficiency receipts, with the loaded code fixed at the reference budget and the
command budget varied: the term's receipt is the frame's. -/
theorem ref_suffices (n : Nat) :
    letI := evaluatorFor waiting
    Suffices (interpOf waiting) n failureTape (Api.load waiting budget) =
      SufficientR waiting n (loadR waiting budget) failureTape :=
  suffices_eq_ref waiting budget n failureTape []

-- The receipts at three command budgets: short of the tape, at it, and past it.
#guard decide (SufficientR waiting 1 (loadR waiting budget) failureTape =
  (letI := evaluatorFor waiting; Suffices (interpOf waiting) 1 failureTape (Api.load waiting budget)))
#guard decide (SufficientR waiting budget (loadR waiting budget) failureTape =
  (letI := evaluatorFor waiting; Suffices (interpOf waiting) budget failureTape (Api.load waiting budget)))
#guard decide (SufficientR raceWinner 3 (loadR raceWinner budget) startTape =
  (letI := evaluatorFor raceWinner; Suffices (interpOf raceWinner) 3 startTape (Api.load raceWinner budget)))

/-- The loaded machines are in the book (the introduction lemma at the root). -/
theorem ref_load_related : BMeans waiting (Api.load waiting budget) (loadR waiting budget) :=
  load_rel waiting budget []

/-! ## P4 on the compile contract's straight programs, at the fixed budget -/

/-- The straight corollary on one program: finished, the root's exit is the meaning's, the
stores are the meaning's, and no other fiber exists. -/
def StraightAgrees (e : NativeEff) : Prop :=
  classify (replayR e fuel [Api.evaluate, Api.flush]) = .finished ∧
    obsR (replayR e fuel [Api.evaluate, Api.flush]).machine =
      ⟨[(Api.root, some (meaning e [] Stores.empty).1)], (meaning e [] Stores.empty).2⟩

theorem straight_pSucceed : StraightAgrees pSucceed :=
  straight_ref pSucceed fuel (by decide) (by decide) (by decide)
theorem straight_pBindSync : StraightAgrees pBindSync :=
  straight_ref pBindSync fuel (by decide) (by decide) (by decide)
theorem straight_pFail : StraightAgrees pFail :=
  straight_ref pFail fuel (by decide) (by decide) (by decide)
theorem straight_pCatch : StraightAgrees pCatch :=
  straight_ref pCatch fuel (by decide) (by decide) (by decide)
theorem straight_pOnExit : StraightAgrees pOnExit :=
  straight_ref pOnExit fuel (by decide) (by decide) (by decide)
theorem straight_pRefSet : StraightAgrees pRefSet :=
  straight_ref pRefSet fuel (by decide) (by decide) (by decide)

-- The fixed budget is sufficient on the reference: the receipt, not an existential budget.
theorem straight_pOnExit_sufficient :
    SufficientR pOnExit fuel (loadR pOnExit fuel) [Api.evaluate, Api.flush] = true :=
  straight_sufficient pOnExit fuel (by decide) (by decide) (by decide)
theorem straight_pRefSet_sufficient :
    SufficientR pRefSet fuel (loadR pRefSet fuel) [Api.evaluate, Api.flush] = true :=
  straight_sufficient pRefSet fuel (by decide) (by decide) (by decide)

-- The same, evaluated on the term reference alone.
#guard decide (classify (replayR pOnExit fuel [Api.evaluate, Api.flush]) = .finished)
#guard decide (obsR (replayR pOnExit fuel [Api.evaluate, Api.flush]).machine =
  ⟨[(Api.root, some (meaning pOnExit [] Stores.empty).1)], (meaning pOnExit [] Stores.empty).2⟩)
#guard decide (obsR (replayR pRefSet fuel [Api.evaluate, Api.flush]).machine =
  ⟨[(Api.root, some (meaning pRefSet [] Stores.empty).1)], (meaning pRefSet [] Stores.empty).2⟩)
#guard SufficientR pOnExit fuel (loadR pOnExit fuel) [Api.evaluate, Api.flush]
#guard SufficientR pCatch fuel (loadR pCatch fuel) [Api.evaluate, Api.flush]

-- The domain is the theorem's: past the budget the receipt is what the frame's is, and
-- `straight_ref` is not applicable (the side condition fails), so nothing is claimed.
#guard decide (SufficientR pOnExit 1 (loadR pOnExit fuel) [Api.evaluate, Api.flush] =
  (letI := evaluatorFor pOnExit; Suffices (interpOf pOnExit) 1 [Api.evaluate, Api.flush] (Api.load pOnExit fuel)))
#guard !(decide (2 * steps pOnExit + 6 ≤ 1))

/-! ## E4-CHECK-CE-016: every executed scope registration has its own identity

The defect this witness recorded: the same `forkScoped` ran twice in a loop under one
`Point.fuel`, so its second scope registration replaced the first, and the first child kept
running past the scope's close — `[true, false, true]` on both Lean machines against
`[true, true, true]` on pinned rc.112.

Repaired 2026-09-07. The registration identity is allocated by the store at each executed
registration, as `internal/effect.ts:5366-5372` (`forkIn`/`forkScoped`) and `:5457-5460`
(`fiberRunIn`) allocate `const key = {}`; the compile no longer mints one from a point.
The general laws are `Machine.scopeLinkFiber_allocates`, `_fresh`, `_keysFresh`, `_appends`
and `Machine.dropFinalizer_removes_its_own` over the reachable-state invariant
`Stores.ScopeKeysFresh`, which `Sched.StoresOk` carries through the whole replay; the
ground receipts are `Machine.Witnesses.w6_two_links_have_two_keys` and its siblings.

The guards below are the repaired result at compile fuel 40, command fuel 400, scheduler
budget 2048 and `[evaluate, flush]`, with the command fuel receipt still true. These compare
Lean machines only (`RSTEP-FB-HOST`); the host half is the audit record's emitted witness.
-/

namespace ScopeRegistrationCollision
open Test.Program.RuntimeRContract

def repeated (n : Nat) : NativeEff :=
  .scoped (.bind (.perform .deferredMake (.lit .unit))
    (.whileLoop (.lit (.nat 0))
      (.app "lt" (.cons (.var 1) (.cons (.lit (.nat n)) .nil)))
      (.app "succ" (.cons (.var 1) .nil))
      (.withFiber (.forkScoped (.callback .deferredAwait (.var 0))
        ⟨true, true, .inherit⟩))))

theorem typed_one : Api.wellTyped (repeated 1) = true := by decide
theorem typed_two : Api.wellTyped (repeated 2) = true := by decide
theorem typed_three : Api.wellTyped (repeated 3) = true := by decide

#guard (Api.print (repeated 2)).isOk
#guard (Api.print (repeated 3)).isOk
#guard (frameRun (repeated 1) [Api.evaluate, Api.flush]).machine.fibers.map
  (fun f => f.exit.isSome) == [true, true]
#guard (frameRun (repeated 2) [Api.evaluate, Api.flush]).machine.fibers.map
  (fun f => f.exit.isSome) == [true, true, true]
#guard (termRun (repeated 2) [Api.evaluate, Api.flush]).machine.fibers.map
  (fun f => f.exit.isSome) == [true, true, true]
-- three iterations, so the repair is not a two-registration special case
#guard (frameRun (repeated 3) [Api.evaluate, Api.flush]).machine.fibers.map
  (fun f => f.exit.isSome) == [true, true, true, true]
#guard (termRun (repeated 3) [Api.evaluate, Api.flush]).machine.fibers.map
  (fun f => f.exit.isSome) == [true, true, true, true]
#guard (letI := evaluatorFor (repeated 3);
  Suffices (interpOf (repeated 3)) 400 [Api.evaluate, Api.flush]
    (frameLoad (repeated 3) 40 2048))
#guard (letI := evaluatorFor (repeated 2);
  Suffices (interpOf (repeated 2)) 400 [Api.evaluate, Api.flush]
    (frameLoad (repeated 2) 40 2048))

end ScopeRegistrationCollision

end Test.Program.SimulationContract
