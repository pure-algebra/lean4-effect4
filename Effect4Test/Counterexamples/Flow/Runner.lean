/-
Counterexamples for the Flow runner (`test/counterexamples/REGISTER.md`,
`E4-FLOW-CE-017` and `E4-FLOW-CE-018`). Each attack names a reading the runner
must refuse; the executable witness is a `#guard` over the actual runner.
-/

import Effect4.Semantics.Runs
import Effect4.Target.TypeScript.ScriptFlow

namespace Effect4Test.Counterexamples.Flow.Runner

open Effects Effect4 Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)

/-- One decision at site 1, then a return. -/
def once : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def noOps : FlowService (tableAlphabet ⟨0⟩ []) Id :=
  tableService ⟨0⟩ [] (fun _ v => pure v) (fun _ v => v)

def runWith (fuel : Nat) (tape : Tape) : Option (RunResult × Effect4.Trace.Log) :=
  match admit (tableAlphabet ⟨0⟩ []) once with
  | .ok flow => some ((Flow.run fuel flow noOps (tableNameOf ⟨0⟩ []) tape (.nat 5)).run [])
  | .error _ => none

/-! ## E4-FLOW-CE-017: fuel exhaustion is a failure

Attack: report an exhausted run as `done (failure _)`, giving a finite
approximation a denotation it does not have. Repair: DB-04, the run ends at
the frontier `fuel block` with a trailing `frontier` row and no `done` row. -/

-- With no fuel the run is a fuel frontier at the entry.
#guard runWith 0 [⟨⟨1⟩, true⟩] =
  some (RunResult.frontier (.fuel ⟨0⟩), [Effects.Trace.Event.frontier])

-- No `done` row of any kind is written.
#guard (runWith 0 [⟨⟨1⟩, true⟩]).map (fun r => r.2.any fun event =>
  match event with | .done _ => true | _ => false) = some false

-- The same run with enough fuel finishes: fuel was the only frontier.
#guard runWith 2 [⟨⟨1⟩, true⟩] =
  some (RunResult.done (.nat 5), [.decide 1 true, .done (.success (.nat 5))])

/-! ## E4-FLOW-CE-018: a foreign tape entry answers this site

Attack: consume the head entry whatever site it names. Repair: R6, the tape
is consumed by occurrence with a site check; a mismatch is `refusedSite expected
actual`, logs nothing, and consumes nothing. -/

#guard runWith 2 [⟨⟨2⟩, true⟩] = some (RunResult.refusedSite ⟨1⟩ ⟨2⟩, [])

-- Exhaustion, by contrast, is a live frontier: the run is unanswered, not refused.
#guard runWith 2 [] =
  some (RunResult.frontier (.unansweredDecision ⟨1⟩), [Effects.Trace.Event.frontier])

end Effect4Test.Counterexamples.Flow.Runner
