# 2026-10-13 graph separation receipt

**The one thing to know before merging:** apply `fallback` to the whole scene during integration, including routes, marks and regions.
The module's separation law concerns visible node envelopes, not those other shapes.

## Base and head

Base: `26436e79195664380bf7861c307395e093e91e48`.
Source head: `06adfec52ef472c2cdc6c14bfed77ae1bc19e1f7`.
Branch: `codex/graph-separation`.
Worktree: `C:/Users/kokok/Dev/lean4-effect4-graph-separation`.
The receipt commit follows the source head and changes no Lean declaration.

## Changed files

- `tools/Tools/View/GraphSeparation.lean`: finite separation queries, conservative movement envelopes and explicit relocation phases.
- `tools/view/GraphSeparationProbe.lean`: finite controls and readers at the concrete swap's boxes.
- `docs/research/2026-10-13-graph-separation-plan.md`: design, consumer, scope and placement written before proofs.
- This receipt: commands, evidence and integration limits.

No existing producer, library root, test root, manifest or coordinator file changes.
No commit is pushed.

## Commands and results

Each command runs from the worktree above.

```powershell
robocopy C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4/.lake/packages C:/Users/kokok/Dev/lean4-effect4-graph-separation/.lake/packages /E /XD research /R:1 /W:1 /NFL /NDL /NP /NJH /NJS
```

Result: exit 1, files copied.
The copy excludes research directories and makes no build-directory link.
The copied kit remains at `e51195721f47fa767fb84f918dc439e76d83071f`.
Lake reports its tracked research files as deleted because that directory is deliberately excluded.
Lake also reports the existing lakefile/manifest revision mismatch.
The module and its imported kit sources remain unchanged.
The coordinator owns any pin repair; this slice changes no dependency declaration.

```powershell
$env:LEAN_NUM_THREADS='3'; lake build Tools.View.GraphSeparation
$env:LEAN_NUM_THREADS='3'; lake build ProofGraph.AxiomAudit
$env:LEAN_NUM_THREADS='3'; lake env lean -DwarningAsError=true --run tools/view/GraphSeparationProbe.lean
lake env lean -DwarningAsError=true --root=tools/view -o .lake/build/lib/lean/GraphSeparationProbe.olean tools/view/GraphSeparationProbe.lean
lake env lean -DwarningAsError=true C:/Users/kokok/AppData/Local/Temp/effect4-graph-separation-audit.lean
python scripts/check-language.py --show docs/research/2026-10-13-graph-separation-plan.md
git diff --check
```

Results: narrow build succeeds, 5 jobs; audit imports build succeeds, 15 jobs.
The final probe and the compiled-probe audit each exit 0.
The language report emits no finding for the plan.
The whitespace check exits 0.
One Lake process runs at a time.

The temporary audit source is:

```lean
import GraphSeparationProbe
import ProofGraph.AxiomAudit
#axiom_audit checked Tools.View.GraphSeparation GraphSeparationProbe
```

## Axiom output

```text
#axiom_audit: 156 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals; checked: the walk's answers at 1837 constants agree with their captured graph, over the labels [propext, Quot.sound]
```

The probe's own imported-module audit separately checks 152 declarations of `Tools.View.GraphSeparation`.
No rendering exemption or trust ceiling changes.

## Evidence

Evidence: **Lean theorems**, under their stated premises.

`checkClear_iff` observes kit `IBox.Disjoint` over every supplied ordered box pair.
`firstFrameOverlap_none_iff` extends that observation to exactly the supplied finite profile.
`movingEnvelope_contains` assumes current origins between endpoint origins and dimensions bounded by the endpoint maxima.
It proves containment under those conditions, without asserting a particular easing meets them.
`fallback_growth_le` bounds the per-mille factor by the rest size.
`fallback_endpoint_family` selects no mixture of endpoint envelope families.
`fallback_clear` assumes each endpoint family is already pairwise disjoint.
It establishes separation of the selected envelopes, not unrestricted painted scene geometry.

Evidence: **finite controls**, not universal behavior claims.

```text
graph-separation: touching, first refusal, swap, translation, size change controls pass
graph-separation: sparse-sample miss, conservative false positive, overshoot controls pass
graph-separation: hidden relocation and endpoint-family fallback controls pass
```

The sparse profile contains only the separated endpoints and misses the swap's midpoint collision.
The swept-envelope selector detects that possibility without sampling the midpoint.
Another control shows a wider target at the old origin outside the plain endpoint hull.
The maximum-size envelope contains that box.
A separate control retains a conservative false positive.
An overshooting origin demonstrates where the envelope premise stops.

## Landed theorems and their placement

The five-field placement in `docs/research/2026-10-13-graph-separation-plan.md` applies to this table.
Concept: `initial-algebras-folds`; proposed observation: `graph-transition-box-separation`, role decidability, serving R14 under row 334 (3).
The coordinator's graph transition policy consumes the detection and fallback metadata.

| Theorem | Consumer and scope |
| --- | --- |
| `checkClear_iff` | Conservative policy selection on supplied allocated box occurrences |
| `firstFrameOverlap_none_iff` | Finite transition inspection, with no between-sample conclusion |
| `movingEnvelope_contains` | The policy selector's explicit bounded-origin and bounded-size premise |
| `fallback_growth_le` | Endpoint growth that cannot exceed its allocated envelope |
| `fallback_endpoint_family` | Whole-scene old/hidden/new selection; visible node envelopes belong to one family |
| `fallback_clear` | Endpoint-family separation under both endpoint separation premises |

Private query helpers serve `checkClear_iff` and `firstFrameOverlap_none_iff`.
They have no independent universal geometry claim.

## Open obligations

The integration must select whole old, hidden or new scene families.
Hiding only boxes leaves routes and marks visible.
The renderer must keep each grown node inside its selected envelope and suppress zero-size nodes.
The endpoint families must pass the separation check before using its conclusion.
The direct-motion selector must account for easing overshoot and growth beyond the endpoint dimensions.
The broad-phase selector may conservatively reject a safe direct motion.
The integration must expose that policy choice and its reason.
No law concerns route intersections, stroke halos, port identity, scheduler behavior or interruption continuity.
No outside runtime behavior gate is reached by this pure tooling slice.

## Proposed decisions rows, proposals only

Expose the old/hidden/new relocation policy explicitly when broad-phase node envelopes intersect.
Keep the endpoint-family premises and direct-motion bounds separate from finite rendered controls.
The module adds no second program IR and changes no current graph or connector construction.
