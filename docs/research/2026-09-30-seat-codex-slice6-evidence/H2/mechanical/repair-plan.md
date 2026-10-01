# H2 part one: mechanical probe and predicted repair cost

Status: **static predictions only**. No candidate here has been compiled by this seat. No
existing proof body has been repaired. The input is the four E cutover candidates, not active
source; their hashes and exact replacement counts are in `source-manifest.json`.

The mechanical pass changes 59 standalone `FitsExit` uses to `ExitOk`, then adds the two
part-one definitions in Admission. `ExitOk w ty ex` is base `FitsExit w ty ex` conjoined with
`NoShapeDefect ex`. That clause excludes only `badName` and `notImplemented` die reasons and
is independent of the effect type. Membership and `FitsExit` are untouched. Missing service
is intentionally not excluded in this part.

All typed exit positions move: BodyTyped.fin; residual pure, control payloads and protocol
posts; frame hooks and stack predicates; completion exits; generated predicate exits and,
through them, queued result payloads and stored promise/due completions. There are no M5–M7
proof additions. H1 remains the coordinator's separate candidate.

## Predicted existing-body failures and local repair plan

Line numbers before the arrow refer to E/cutover, after it to H2/mechanical. A failure is not
measured until a compiler log identifies the body. These are eight predicted affected bodies
on the E baseline, of which seven predate E and one is E's new weakening adapter.

| Body | Location | Why the unchanged body is predicted to fail | Narrow repair after measurement |
| --- | --- | --- | --- |
| `strongExit_success` | Admission 57 → 69 | A membership proof is not the new conjunction. | Pair the old membership with the vacuous success exclusion. |
| `strongExit_of_clean` | Admission 62 → 74 | The statement itself becomes false: cleanExit permits die badName and die notImplemented. | Add an explicit NoShapeDefect premise and pair it with `fitsExit_of_clean`; do not silently claim cleanExit excludes those defects. |
| `cleanExit_of_never` | Admission 76 → 88 | The old body uses the new conjunction as base failure membership. | Apply the existing Membership helper to the first projection. |
| `strongExit_bool` | Residual 321 → 321 | A boolean membership proof is not the new conjunction. | Pair it with vacuous success exclusion, or call the repaired success wrapper. |
| `settling_fork` | Residual 352 → 352 | The direct allocated-fiber witness must now inhabit the first conjunct. | Pair the same declaration witness with vacuous success exclusion. |
| `strongExit_mono` | Residual 412 → 412 | The E adapter passes ExitOk to the base FitsExit transport law. | Transport its first projection and retain its second unchanged. This adapter was added in E; report separately from the seven legacy bodies. |
| `strongExit_failure_of_error` | Stack 87 → 87 | Rewriting only the base failure membership no longer produces the whole goal. | Apply the existing Membership error-column helper to the first projection, retain type-independent exclusion. |
| `popR_typed` | Stack 105 → 105 | The two success arms pass ExitOk where hooks require Fits; clean-failure call sites need exclusion evidence, and the local preempt function currently admits an arbitrary cause. | Pass `hex.1` at iterator/loop; use interrupt provenance for the three injected interrupt causes; require the original cause's `NoShapeDefect` at preempt and obtain it from the branch's `hex.2`; transport it through stripFail/combine. Count this as one body regardless of site count. |

The helper `strongExit_of_clean` is a contract change, not merely a proof trick. Its present
statement is refuted by `c = Cause.die .badName`: cleanExit reduces to true, while the new
exclusion would require badName ≠ badName. Retaining the base Membership helper unchanged is
correct; only the strengthened typed-exit wrapper needs the added premise.

Expected unchanged proof bodies include `walk_saved`, `walk_done`, `hookLaws_interpR`,
`popR_typed_interpR`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale`, the residual
inversions, and the Assembly capture laws: they pass the parameterized exit judgment without
unpacking its old representation. These are predictions, not positive compiler results.

## New local helpers proposed, not yet written

- Shape exclusion for a cause whose reasons are all interrupts; specialize to recorded and
  pending interrupt causes using `InterruptProvenance`.
- Exclusion under stripFail, using `Cause.mem_stripFail` (Machine/Cause.lean:835).
- Exclusion under combine, using `Cause.mem_combine` (Machine/Cause.lean:879).
- Exclusion under sanitize from exclusion of the original cause and interrupt provenance of
  the recorded cause (`sanitize` is combine after stripFail, Machine/Cause.lean:831).
- Optionally a local ExitOk success and world-weakening wrapper to avoid repeating pairs.

These are new helper proofs, not edits to existing slice-five bodies. The compiler's first
failure list and the final diff of named existing bodies must be retained separately. The
stop rule is **at least eight actual existing proof-body edits across the current post-E
tree**, excluding mechanical judgment substitutions and the count of newly introduced helper
declarations. Report both the total and its split: seven legacy slice-five bodies plus the E
adapter are predicted. The adapter is not hidden in mechanical renames. If compilation and
the required repairs confirm all eight, stop H2 and report that measured cost. There is no
inferred stop from this prediction, and no proof repair is authorized by this document.

## Smallest amendment options if the measured cost reaches eight

1. Keep H2 parked and retain the recorded limitation. E and H1 remain separately reviewable;
   do not mark the shared-exit defect repaired or claim the M6 capstone excludes it.
2. Ask the owner to authorize exactly the measured named bodies, with no additional scope.
   For the currently predicted set, the amendment would allow eight existing-body edits
   (seven legacy plus one E adapter), the explicit clean-failure premise repair, and only
   local exclusion lemmas. It would retain the prohibition on M5–M7 proofs and keep part two
   separate. This is a proposed future amendment, not current authorization.

Do not evade the cap by renaming existing wrappers as newly introduced helpers, by hiding
proof changes inside a mechanical script, or by editing Membership's base FitsExit semantics.
For part two, the smallest direct helper amendment is a matching requirement-row premise
(or explicit evidence that missingService is absent when the destination requires nothing).
Whether actual saved frames provide that evidence is a separate measured question.

## Part-two isolated diagnostic

`../diagnostics/MissingServiceTransport.lean` tests only the direct error-column transport
statement. Two types have the same unit answer and never error columns, but one requires the
native scope service and the other requires nothing. The exit die missingService satisfies
the proposed full exclusion inside and is refused outside. The file contains the direct
refutation and axiom-print commands; none has yet been compiled. It constructs no saved frame
or reachable execution and therefore makes no claim that the full walk is false.
