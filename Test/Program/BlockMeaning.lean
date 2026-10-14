import Effect4.Laws.Program.BlockMeaning
import Test.Program.DefinitionsControls

/-!
# Finite controls for the budgeted block meaning

Concept: translation-simulation. Claims: rows-block-host and block-handler-unfolds.
These evaluations compare selected definition blocks with the machine at stated budgets.
They check call-depth cuts and recursive examples; they establish no general machine agreement.
The zero-budget control distinguishes a call from its body at the same budget.
-/

set_option autoImplicit false

namespace Test.Program.BlockMeaning

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Test.Program.DefinitionsControls (twiceProg evenOdd spinProg successVal)

/-- The exit at a budget under the empty reply tape, at the empty table: `some none` is the
frontier. -/
def exitAt (e : NativeEff) (k : Nat) : Option (Option ExitV) :=
  (hostRunBlockB (tapeHost []) (bodiesOf e) k [] e emptyCtx [] Stores.empty []).map (·.1)

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

/-! ## A call and its unfolding can differ at the same budget -/

-- control: a valid call at budget zero is a cut, while its nonrecursive body finishes.
#guard (hostRunBlockB (tapeHost []) [.succeed (.lit (.nat 7))] 0 []
    (.perform (.call 0) (.lit .unit)) emptyCtx [] Stores.empty []).map (·.1) = some none
#guard (hostRunBlockB (tapeHost []) [.succeed (.lit (.nat 7))] 0 []
    (.succeed (.lit (.nat 7))) emptyCtx [.unit] Stores.empty []).map (·.1) =
  some (some (.success (.nat 7)))

end Test.Program.BlockMeaning
