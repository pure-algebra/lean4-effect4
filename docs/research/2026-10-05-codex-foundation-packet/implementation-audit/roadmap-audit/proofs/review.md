# Roadmap priorities 1 and 2

Evidence status: frozen source inspection, primary-literature verification, and finite Python mirrors.
No Lean proof or repository change occurs in this audit.

## Disposition

Both priorities are sensible small proof slices. Neither should be described as closing runtime suspension.
Priority 1 removes a redundant admission condition once its exact finite bound is proved.
Priority 2 connects completed journal prefixes and recorded positions to the existing machine replay.
Keep the module work and row 226's driver design separate.

The source cut is `d3a3e558`.
The observed later checkout is `0acec081735277287cad1ce342059d1600b4ee3f`.
The inspected reference and tape owners have no changes between those cuts.
`sources.json` records the full frozen commit and every retained source hash.

## Priority 1: the goal is right; the finite-domain proof needs more detail

`Eff.expandRefs` in `Program/Refs.lean` uses the original root for every lookup.
It performs exactly `refSites.length + 1` rounds of the existing expansion algebra.
A newly inserted target is not recursively expanded during the same fold call.
The implementation comment already states the intended bound; the general theorem remains missing.

The useful dependency edge runs from an original reference occurrence to each original reference inside its target.
It does not merely run from one target path to another.
A target may contain another referenced definition, so target paths alone need not decrease.
For each edge, prove that the nested reference's original path precedes the caller's original path.
This uses both the prior-target check and the prohibition on an enclosing target.
Then rank the finite set of original reference occurrences, or count their predecessors.
Copies retain the rank of their original occurrence; their new expanded paths are not the ranking domain.

Lexicographic descent over arbitrary paths is insufficient.
Paths such as `[1]`, `[0,1]`, and `[0,0,1]` give an infinite descending pattern.
The finite original-site domain is therefore an indispensable premise of the proof construction.
Copy multiplicity can grow while the maximum dependency rank decreases.

Reuse `Path.lt_trans`, `lt_irrefl`, and the existing path sorting facts in `Laws/Program/PathOrder.lean`.
Reuse `Node.yieldAt_subset_of_at`, `mem_refSites_of_at`, and `layerRefsWF_at` in `Laws/Program/PathFold.lean`.
The inverse collection/address fact and the descendant-before-caller fact need explicit proof where required.
Use the generated family fold to establish the one-round rank decrease across all seven syntax sorts.
Do not write a second expander or a generic graph library.
The exact `length + 1` implementation bound must follow, including the zero-reference case.

The roadmap overstates the current caller burden.
`TypedProgram.expanded_refSites` already extracts the evidence from a successful whole-program check.
`TypedProgram.hasTy` uses that evidence without asking its caller for another premise.
`checkTypedProgram_of_hasTy` is the useful converse consumer whose separate `expanded` premise can disappear.
`typeOfProgram_expandRefs` is another direct consumer.
No frozen-source caller of that theorem beyond its local type pin was found.

First prove the helper, then derive checker equivalence.
Removing the executable guard is optional and follows the equivalence proof.
If it is removed, migrate `Api.explain` and `explain_none_iff` together to preserve refusal agreement.
A well-formed reference graph alone does not imply type formation, scoping, or successful typing.

The runtime compiler redirects references to preserve shared layer identity and memo keys.
This theorem does not justify executing the expanded tree in its place.
It does not establish R5's open `lower_refines_build` or any R8 equal-observation claim.

## Priority 2: useful prefix laws, with a narrower consequence

The proposed append formula agrees with the recursive definition of `tapeFrom`.
Strengthen the cut's intermediate fact to preserve the exact position list: `tapeFrom s done = (positions, [])`.
Then the machine equality follows from existing `tape_replays`.
Add one position-prefix law for `Position.after`; it directly serves the list of views in `Lowered.shown`.
The full corrected signatures are in `proposals.md` and are uncompiled.

The existing helpers already expose all cases: `tapeFrom_frontier`, `skip`, `take`, and `stop`.
`Run.play_append`, `play_cons`, `step_built`, and `step_budget` supply the state bookkeeping.
The stopping condition is a frontier phase or a decision that raw replay cannot read past.
An outstanding external call alone is not the definition of an unread tape.

The cut ends before the first stopped row.
Executing that row may already mutate the machine before reporting insufficient command fuel.
Therefore its post-state is not the cut's replay result.
A second command on that changed machine is not a continuation of the first command.

The first `Lowered.shown` consumer needs a fresh-open premise.
`Lowered.opened` is structurally any `Run`, but `shown` calls `Api.replay` from a new load.
It also feeds the entire accumulated journal to `tapeFrom` starting at `opened`.
Current fixtures use fresh opens, so this is a limit on a new universal theorem, not a demonstrated fixture defect.
For arbitrary progressed runs, retain the initial machine in `Run.replayFrom` and consume only newly added rows.
The engine's finite prefix comparisons remain necessary; a Lean prefix law does not certify generated execution.

## Driver suspension already has a different starting point

`driveState_add` in `Laws/Machine/Approximation.lean` already splits command-loop fuel additively.
Its result retains both the machine and the remaining commands.
`driveState_lift` is the existing invariant-lifting consumer.
The missing driver state is outside that local loop.
`fireStep` and `stepDecisionState` project remaining work to a sufficiency Boolean.
They do not retain all dispatcher tasks, flush or clock phases, and atomic ownership required by row 226.
The tape-cut result cannot reconstruct this erased continuation.
Use the existing split law when implementing the full suspension; do not make Priority 2 its theoretical prerequisite.

## Placement in the existing proof graph

| Work | Placement and consumer | Scope excluded |
| --- | --- | --- |
| Reference completeness | Proposed claim `reference-expansion-complete` in the existing registry, under `initial-algebras-folds`; R5 with a typing consumer under R4. Add the required property before its goal. Consumer: `checkTypedProgram_of_hasTy` and `typeOfProgram_expandRefs` | No runtime sharing or R8 simulation |
| Tape append and cut | Helpers of existing `run-tape-replay`, under `translation-simulation`, R8. Consumer: the position views of `Lowered.shown` | No session-ledger or engine equality |
| Journal bookkeeping | Reuse `Run.journal_replays`, R13; equal recorded rows replay the run | No host-choice agreement or missing load inputs |
| Full driver continuation | Existing proposed `driver-continuation-split` and `driver-suspension-keeps-typed`, under `reactive-scheduling`, R12; reuse `drivestate-lift` and `driveState_add` | No fairness or eventual completion |

No parallel ledger is needed. The reference-completeness claim is not already named in the frozen registry.
A generic fold-uniqueness theorem does not itself prove completeness of this reference resolver.
No R1–R13 requirement closes solely from either proposed slice.

## Evidence and falsifiers

`probe.py` is a standalone pure Python model, not the project's runtime or a Lean proof.
It checks 8,403 finite journal cases and 40,617 append splits.
It checks the cut equation and every retained position against raw replay.
Its red controls reject a stopped command's post-state and omission of a reply receipt before application.

Five finite tree fixtures cover empty trees, one reference, nested chains, diamonds, and nested sibling targets.
The diamond grows from six references to nine, then reaches zero.
A nested chain takes three rounds; the zero-reference case needs zero.
The controls reject enclosing self-reference, forward references, reference-valued targets, and missing targets.
They support the proposed proof shape without proving its universal bound.

The roadmap's citation needs correction.
Lynch–Vaandrager §3.2, Lemma 3.8 lifts finite moves through a forward simulation.
Proposition 3.9 proves that forward simulation is reflexive and transitive.
Neither directly proves this project's exact journal cut or its reachability invariant.
Gambino–Hyland supplies conceptual support for indexed well-founded induction, not the reference-rank theorem.
See `literature/review.md` for the verified primary-source pages and URLs.
