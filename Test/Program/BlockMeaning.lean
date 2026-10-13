import Effect4.Laws.Program.Block
import Test.Program.DefinitionsControls

/-!
# The meaning of a definition block (slice PROC-5, goal G5): readers and controls

`Laws/Program/Block.lean` gives a program with a block its meaning at a budget: invocations read
as rows appended after the host's, the block a recursive handler (`mrecB`). Its laws are
theorems: `denoteDefs_refines`, `denoteDefs_noBlock`, `invoke_unfolds_at_limit`, with
`Mrec.conv_unique`. The programs are `DefinitionsControls`' blocks.

* **Finite evaluations (tested), which no theorem covers yet.** At a budget past the nesting the
  meaning gives the frame machine's exit (`Api.run`): one invocation, and mutual recursion eight
  deep. The machine's agreement with the meaning is G4's, unstated.
* **Control (tested): the frontier, never a failure.** Below the nesting the meaning is the
  frontier, and a body that invokes itself without end is the frontier at every budget tried,
  as the machine's run is.
* **Red control (proved): no single budget solves the unfolding equation**
  (`budget_not_unfolding`), so the law holds only at the limit.
-/

set_option autoImplicit false

namespace Test.Program.BlockMeaning

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Laws.Effects.Mrec
open Test.Program.DefinitionsControls (twiceProg evenOdd spinProg successVal)

/-- The exit at a budget under the empty reply tape, at the empty table: `some none` is the
frontier. -/
def exitAt (e : NativeEff) (k : Nat) : Option (Option ExitV) :=
  (meaningDefs (tapeHandler []) k e [] Stores.empty []).map (·.1.1)

-- tested: past the nesting, the meaning's exit is the machine's
#guard (exitAt twiceProg 1).join == (Api.run twiceProg 200).exit
#guard (exitAt (evenOdd 7) 8).join == (Api.run (evenOdd 7) 400).exit
#guard (exitAt (evenOdd 6) 7).join == (Api.run (evenOdd 6) 400).exit
#guard successVal (exitAt (evenOdd 7) 8).join == some (.bool false)
-- control (tested): below the nesting, the frontier
#guard exitAt (evenOdd 7) 7 == some none
#guard exitAt twiceProg 0 == some none
-- control (tested): recursion without end is the frontier at every budget tried, as the machine's run is
#guard (List.range 20).all fun k => exitAt spinProg k == some none
#guard (Api.run spinProg 60).outcome == .frontier

/-! ## The red control: no single budget solves the unfolding equation -/

/-- A signature with no operation of the program's own. -/
abbrev Empty : Effects.Signature.{0, 0} := ⟨PEmpty, fun _ => PUnit⟩

/-- One definition, answering a natural number. -/
abbrev One : Effects.Signature.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- The definition's body answers `7` and invokes nothing. -/
def seven : (d : One.Op) → Effects.Program (Effects.Signature.sum Empty One) (One.Answer d) :=
  fun _ => .pure (7 : Nat)

/-- At budget `0` the invocation is the frontier, while its unfolding finishes with `7`. -/
theorem budget_not_unfolding :
    ¬ ∀ k, mrecB seven k
        (.vis (.inr ()) (fun n => .pure n) : Effects.Program (Effects.Signature.sum Empty One) Nat) =
      mrecB seven k ((seven ()).bind (fun n => .pure n)) := by
  intro h
  have h0 := h 0
  simp only [mrecB, mrecStep, seven, Effects.Program.bind] at h0
  cases h0

end Test.Program.BlockMeaning
