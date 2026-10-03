import Test.Counterexamples.Machine.Semantics.FitsOrder

/-!
# `E4-TYPED-CE-009` against M5 and the capstone restated over `J` (history since row 137)

TY-01 (decisions row 137): before row 137, `Fits`' fiber arm compared a declaration with the
checker's certificate in the raw order while the checker normalizes, so a checked program whose
forked child is certified at a non-normal type loaded into no typed state. Seat C restated the
synthesis seat's tracked port (`docs/research/2026-10-01-landing/ports-at-dceae006/HeadM5Fits.lean`)
here against `J` (`m5_false`), M5's proposition (`loadsTyped_false`) and the capstone's
(`capstone_false`) before seat A's checker-order `Fits` merged.

Row 137 repairs it. At the production judgment the program loads into `J`
(`FitsOrder.prog3_loads_typed`), so M5's and the capstone's propositions hold there
(`FitsOrder.loadsTyped`, `FitsOrder.capstone_at_load`). The three refutations are kept as
history under `FitsOrder.RawLeaf` (the production leaf implied the raw one before row 137;
`FitsOrder.rawLeaf_false` refutes the hypothesis now), as one-line uses of FitsOrder's
`Reviewed` theorems, which carry the same argument over `J` once (integration seat I2). The
program, its checked premises and the leaf are FitsOrder's; this file's copies of them, its local
`fiber_inv` (seat B's `TypedProg.fiber_inv`) and its `leaf_false` (`FitsOrder.Reviewed.leaf_false`
over the pre-137 judgment, and FitsOrder's `#guard_msgs` fixture pinning this file's proof failing
against the production judgment) are deleted.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Machine.Semantics.RawOrderLoad

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Test.Counterexamples.Machine.Semantics.FitsOrder (src rootTy3 prog3 RawLeaf)

/-- **Historical: `J` failed at every world of the load** (before row 137). -/
theorem m5_false (raw : RawLeaf) : ¬ ∃ w, MachineTyped src rootTy3 w (loadR prog3 100 100) :=
  FitsOrder.Reviewed.m5_false raw

/-- **Historical: M5 restated over `J` was false here.** -/
theorem loadsTyped_false (raw : RawLeaf) : ¬ LoadsTyped src rootTy3 100 100 :=
  FitsOrder.Reviewed.loadsTyped_false raw

/-- **Historical: the capstone restated over `J` was false here**, at the loaded machine. -/
theorem capstone_false (raw : RawLeaf) : ¬ ReachableTyped src rootTy3 100 (loadR prog3 100 100) :=
  fun cap => m5_false raw
    (cap src.lawful FitsOrder.prog3_typed rfl (rreachable_load src 100))

end Test.Counterexamples.Machine.Semantics.RawOrderLoad
