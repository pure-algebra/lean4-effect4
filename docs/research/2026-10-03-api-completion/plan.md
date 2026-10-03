# Authoring, session work and proof reuse

Base: `8913519b`, 2026-10-03. The owner authorized implementation and landing of the next
priorities, stronger proof infrastructure, useful host-session and authoring/composition APIs,
and whichever remaining T obligations can be closed on their settled contracts. Slice A is
already integrated. This continuation implements concrete consumers before expanding APIs.

Finishing criteria for this tranche:

1. General path replacement lands with lookup/update/restore laws and the existing layer
   authoring consumers migrated through its compatible wrapper (seat program-path-editing).
2. Existing store-frame proof infrastructure gains a missing useful primitive law, with
   repeated invariant reconstruction removed from a real caller (seat store-frame-laws).
3. Host-session users can see runnable fibers and queued dispatcher work and opt into one
   documented internal scheduling step; host input, pending replies and clock waits remain
   visible without a claim of global progress (seat session-work).
4. A scoped composition relation has a real runtime comparison consumer and a concrete
   transformation law, including state after failure and finalization (coordinator, below).
5. Each slice is independently built, probed, axiom-inspected and committed. The combined
   tree builds affected modules and tests, and added modules are connected to existing roots.
   Existing dirty main-checkout documents remain outside the integration. Nothing is pushed.
6. Remaining T items receive a fresh source-grounded disposition: proved at their actual
   stated scope, a named partial contribution, or an explicit dependency/semantic ruling.
   Conditional results are not reported as closing general progress or liveness.

This is a research work record. It does not amend frozen contracts, decide the captured-service
policy, or authorize a second program representation. Per-seat briefs record exact file fences
and proof placement before implementation. The coordinator owns root import anchors; the
existing dirty authorities and generated semantics files are not edited by these slices.

## Coordinator slice D: straight-fragment composition with an execution consumer

The existing straight-fragment denotation observes both exit and complete stores for every
environment/store input. `run_eq_meaning` already connects it to ordinary machine runs with
explicit compilation and execution bounds. A convenience theorem computes sufficient bounds
from those existing measures, so callers need not discharge arithmetic premises by hand. Add a proof-side `StraightEq` relation containing
both fragment witnesses and equality of those meanings. It stores no program implementation.

Immediate consumers: composition congruence for the constructors admitted by `Straight`,
suspension insertion/removal in those contexts, and a theorem transporting the relation to
equal machine exits/stores at independently sufficient source and target budgets. This is the
first bounded T5 application; no claim is made that it supplies T5's general scheduled relation.

Five-part placement, before proof work:

1. Concept 10 (Translation and Simulation), required program-transformation preservation
   under a named observation; concept 7's compositional representation laws support it.
   Proposed registry claim `straight-composition-agreement`, role simulation.
2. A local `StraightEqWanted` goal for the execution connector precedes its proof. Relation
   laws and constructor congruences serve that goal and its suspension-rewrite consumers.
3. Reach: two programs in existing `Straight`, all semantic environments and stores for the
   relation; machine comparison starts at the existing empty environment/stores and empty
   host table, as `run_eq_meaning` states. Observation is finished outcome, exit and full
   stores, with separate computable sufficient fuel bounds on both runs. It is not `Obs`,
   trace equality or full-machine equality. Use the existing denotation contract and its
   E4-DEN-CE-003/004/005 boundaries; decision 138/DI-57 keep host agreement separate.
4. Does not establish general T5, equal finite-fuel frontiers, traces, scheduling, loops,
   layers, lexical substitution, typing preservation, host behavior or target execution.
   No code transformation is applied silently to user programs.
5. Serves R8 and future authoring/lowering proofs: a changed source shape can reuse the
   existing execution agreement through a compositional semantic argument. M5-M7 stay
   unchanged and are not prerequisites of this connection.

Coordinator source fence: new `src/Effect4/Laws/Program/MeaningEq.lean`, new
`Test/Program/MeaningEqContract.lean`; import the former after
`Effect4.Laws.Program.Agreement.Machine` in `src/Effect4/Laws.lean`, the latter after
`Test.Program.AgreementContract` in `Test/All.lean`. No existing runtime definitions change.
Proofs use existing meaning equations and fragment definitions, without a new traversal.
Focused build and retained axiom/positive/negative fixture checks precede commit.
