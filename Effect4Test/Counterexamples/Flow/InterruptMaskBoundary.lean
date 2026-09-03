import Effect4Test.Flow.InterruptContract

/-!
Independent M2 boundary amendment: E4-FLOW-CE-024 and E4-FLOW-CE-025.
These are finite executable expectations over the existing runner. The final
three guards are intentionally red before the restoration-boundary repair.
The original InterruptContract remains unchanged; its extra outside decision
is superseded by the append-only M2 amendment in flow-regions-runner.contract.md.
The companion host reproducer makes a real request under rc.112's mask.
No new semantic carrier, runtime claim, or library declaration is introduced.
-/

namespace Effect4Test.Counterexamples.Flow.InterruptMaskBoundary

open Effects Effect4 Effect4.Flow
open Effect4Test.Flow.InterruptContract
  (masked finalizer run rblock deliverAtPerform)

-- Reuse the canonical resource-bearing fixture. Only its outside continuation
-- changes: returning has no fresh interrupt point at which to rescue a request.
private def maskedReturn : RegionFlow String :=
  { masked with blocks := masked.blocks.take 4 ++
      [rblock 4 none ["number"] (.plain (.ret ⟨0⟩))] }

private def delivered : Tape := [deliverAtPerform 2]

private def successfulCleanup : Effect4.Trace.Log :=
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .decide 1000005 true
  , .op "put" (.nat 5), .answer "put" .unit
  , .decide 1000002 false
  , .leave 1 (.success (.nat 5))
  , .finalizer 1 (.success (.nat 5))
  , .op "release" (.nat 5), .answer "release" .unit ]

private def restoredInterrupt : Option (InterruptResult × Effect4.Trace.Log) :=
  some (.interrupted, successfulCleanup ++ [.done .interrupted])

/-! Positive controls: admitted data, uninterrupted return, and genuinely
unmasked delivery. These pass before and after the boundary correction. -/

#guard (run maskedReturn [⟨1⟩] []).isSome
#guard sitesSeparated maskedReturn

#guard run maskedReturn [⟨1⟩] [] =
  some (.done (.nat 5),
    [ .enter 1
    , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
    , .decide 1000005 false
    , .op "put" (.nat 5), .answer "put" .unit
    , .decide 1000002 false
    , .leave 1 (.success (.nat 5))
    , .finalizer 1 (.success (.nat 5))
    , .op "release" (.nat 5), .answer "release" .unit
    , .done (.success (.nat 5)) ])

#guard run maskedReturn [] delivered =
  some (.interrupted,
    [ .enter 1
    , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
    , .decide 1000005 true
    , .leave 1 .interrupted, .finalizer 1 .interrupted
    , .op "release" (.nat 5), .answer "release" .unit
    , .done .interrupted ])

-- E4-FLOW-CE-023's nested interrupted finalizers remain a positive control.
#guard ((run finalizer [] [deliverAtPerform 4]).map fun result =>
    result.2.filterMap fun event => match event with
      | .finalizer region outcome => some (region, outcome)
      | _ => none) = some [(2, .interrupted), (1, .interrupted)]

/-! Corrected expectations. At the historical baseline, the first and third
guards expose an extra outside point; the second exposes an incorrect success.
Restoration is internal delivery, not a fresh question or a dropped request.
Successful cleanup precedes that delivery and keeps its successful exit. -/

-- E4-FLOW-CE-024/025: all M2 rows are retained, without decide 1000009.
#guard run masked [⟨1⟩] delivered = restoredInterrupt

-- E4-FLOW-CE-025: even an immediate return must observe the pending interrupt.
#guard run maskedReturn [⟨1⟩] delivered = restoredInterrupt

-- No later tape answer is consulted or logged during restoration. An explicit
-- true answer at the outside site cannot create a second delivery decision.
#guard run masked [⟨1⟩] (delivered ++ [deliverAtPerform 4]) = restoredInterrupt

end Effect4Test.Counterexamples.Flow.InterruptMaskBoundary
