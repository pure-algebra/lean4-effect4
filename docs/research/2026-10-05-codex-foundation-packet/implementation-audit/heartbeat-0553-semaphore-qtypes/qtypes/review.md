# QTYPES acceptance delta at the 05:53 heartbeat

## Disposition and integration boundary

No new actionable defect found in the reviewed delta.
The previously reviewed five proofs now have completed acceptance evidence, not only a narrow build log.

Main is frozen at `21b9722976b0339db1c58973015af06f0697e126`.
Part 1 is landed there through merge `0b048da4` and state/report update `835696c1`.
The clean seat is frozen at `541fbb2e490fb6369665b3e56b1553234e77bd77`.
Its follow-up and receipt are staged on main at this observation, not committed at the main review cut.
Every inspected index copy equals its seat-commit copy; `snapshot.json` records the comparisons.
No later main state enters this verdict.

## Delta from the prior review

The five original proposition texts still match `2f22ad7b` byte for byte.
`verified-summary.json` retains the comparison and each proposition's hash.
No premise was added to those statements. Their checker and message-type domain are unchanged.
The agreement and executable step definitions are not edited by the slice.

Part 1 adds the dedicated acceptance fixture and repairs two local hypothesis names reserved by the audit environment.
Part 2 adds only focused connectors: same-stem minting at distinct depths, written-name distinction, positional reply reads, and reply normal forms.
The two unused helpers are removed. The existing node and caller judgments remain the owners.

The expanded fixture now uses an actual authoring program with three `bindWith` calls followed by `Ref.modify`.
Its checked step term equals the term used in the capture examples, and the guard separately requires that term to exist.
The examples discharge identity and hint capture at that exact scope through `captured_answer` and `capturedTy_answer`.
The same-stem theorem does not claim arbitrary stem/depth injectivity; the prose retains the known collision between different stems.

The arbitrary-scope `withdrawTake_keeps_cell` obtains one term from `Reads`, then applies `Types.tree` to that same elaboration equation.
It retains `EnvTyped`, cell lookup, existing cell membership, exact evaluation, and typed-capture premises.
This is a useful connector without a second elaboration or a new store invariant.
The positional-read helper retains the tuple checker's own success premise and has out-of-range and list controls.

## Retained acceptance evidence

No Lean or build ran during this review. These results come from copied logs and retained tool-result records.

| Evidence | Result |
| --- | --- |
| `qtyping-6.log` | focused fixture build succeeds: 459 jobs, exit 0 |
| `build-5.log` | default build succeeds: 956 jobs, exit 0 |
| final default library-root gate | 167 API/utility modules; 287 Laws-only modules; every source reachable; API root never reaches Laws |
| final default module and axiom gate | 706 modules; 86047 declarations; semantic/test ceiling `[propext, Quot.sound]` |
| final default goal gate | 24 planned goals; 11 declarations depend on goals; no other declaration reaches `sorryAx` |
| `final2/axioms.out` | 168 queried public declarations: 164 use `[propext, Quot.sound]`, three use `[propext]`, one uses no axioms |
| fixture status pins | five original and five general typing theorems are proved, with no next goal; passes, captures, and the two store connectors have pinned checks |
| `red3/red.out` | exactly 12 errors at the deliberately falsified controls; no other error header |

The broad gate retains its explicitly reported implementation exceptions for `Classical.choice`.
Those exceptions do not appear in the 168 individually queried public theorem outputs.
The fixture's zero brought-in counts are scoped to its Test-root walk, not a count of all proof dependencies.
The fixture and retained output explain that boundary.

The twelve falsifiers cover invalid typing, capture collision, same-depth name shadowing, exchanged identity/hint syntax, a changed goal status, and a changed axiom list.
The ordinary fixture's successful build supplies their positive controls.
These are finite controls. The symbolic theorems remain conditional on their stated type, environment, and capture premises.

`retained-tool-evidence.json` contains exact commands, tool IDs, source locations, timestamps, and result excerpts.
The default-build result is at task output line 536; the final axiom distribution is at line 548.
The task file is `a89d3ddaa261cf123.output` in the retained Claude task directory.
Each line hash excludes its newline. Log copies have independent whole-file hashes.

## Requirement accounting and remaining boundary

The receipt correctly separates the five newly proved original R4 nodes from the five general R4 caller nodes.
The generated report at `835696c1` confirms their proved status and leaves R4 open.
Its reported next-goal list falls from 15 to 10; the default goal gate's count is a different population.
`requirement-evidence.json` retains the exact report rows and source hashes for both revisions.

R10's Queue wrapper agreement stays open. The other R rows remain open and are not claimed as advances of this slice.
The receipt keeps cell membership, full wrapper typing, cleanup, scheduling, target execution, and host behavior outside the proved result.
It also retains the string-literal and narrower-message caller limitations.
Its existing-typed-store observation does not prove initialization of a model-encoded cell.

The receipt explicitly asks the coordinator to regenerate semantics evidence after the follow-up.
The added helpers and changed proof dependencies can change measured counts, even without changing the ten tagged statements.
This is a disclosed integration action, not an unreported acceptance failure.
No generator or target/host lane was run by this review.

## Verification of this packet

The review compared the frozen source with the earlier goal statements and the observed main index.
It counted the actual axiom lines and red-error headers, inspected the fixture changes, and checked the report's R rows.
All copied sources, logs, and review artifacts have SHA-256 records in the receipt.
The repository was not changed.
