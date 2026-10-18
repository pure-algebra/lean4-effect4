# Self-review of the seams interfaces

Status: adversarial review (history, not authority), at `774ddc3d7` on `refactor/phase1-phase3`.
New evidence: `self-review-probes/SelfReviewControls.lean`, finite evaluations that prove no theorem.

## The most serious problem

`interfaces.md` supersedes `README.md` v2, but it reverts five of v2's reviewed refinements without
saying so. Each revert reopens a Codex finding.

1. The state carrier keeps the action list only inside `reached : ∃ as, …`. `State.transcript`
   cannot be read from an erased witness (SR-1). v2 kept `transcript` as data.
2. `replay : Raw → List Action → Raw` is total, so loading cannot refuse a hostile chain. Loading
   never compares `after`, and the origin's engine has no migration or refusal (SR-1). v2 had
   `replayAccepted` returning `Except` and a six-step load.
3. Stored edges are raw `Digest`s, which the store's edge traversal does not see (SR-2). v2
   required typed `Ref`s.
4. `Move.record` returns. With `interrupt` it gives result nodes two entry paths that disagree
   after a crash (SR-3). v2 removed it.
5. The retry rule flips from stale-first to duplicate-first, unrecorded (SR-17).

Cause 3 then holds only for a session's own chain under an unchanged engine. Cause 4's "one entry
path" fails after an interrupted commit.

## Findings

| ID | Place | Problem | Evidence | Severity | Smallest fix |
| --- | --- | --- | --- | --- | --- |
| SR-1 | §4.3 `State`, `transcript`, persistence | The persisted transcript exists only inside `∃`. Total replay loads a chain with a refused action silently changed. Loading never compares `after`. The origin's engine names no migration rule. | probe `transcriptOf`: `cases` fails on the erased witness; `review-probes/TranscriptCarrierControl.lean`; README v2 §3.2 | blocks implementation | Restore v2's carrier, `replayAccepted : … → Except (Nat × Refusal) Raw`, its six-step load and origin versions. |
| SR-2 | probe `SessionEntry.parent`/`after`, `Job.program`, `Tape.job`/`parent`, `Answered.query`, `Move.record` | A `Digest` encodes as bytes, so `Node.checkedEdges` and closure reads skip it. A `Job`'s closure omits its program; an `after` can dangle. | probe: `(Canonical.toVal zeroDigest).refs = []`, while an `AnyRef` frame is seen | fix in its slice (ST3, ST4) | Typed `Ref` fields (v2 §3.2). |
| SR-3 | §4.4 `record`, interruption; §1 row SM-C-14 | `interrupt` keeps fresh nodes and no moves, so a result node enters without `record`. Reopening derives a record from it, which the model lacks. A later result for the same query commits in the model and leaves two on disk. `record_once` fails, or the ST2 differential diverges. | reading §4.4, §4.5, §1 | blocks implementation | Drop `Move.record`; check the association at node admission on every path (v2 §5.3). |
| SR-4 | §4.4 `Cas.interrupt` | Total over every `t`. "Closed since `t` is children first" holds only for a `t` that node admission accepts. | reading §4.4 order | fix in its slice (ST1b) | Keep the longest prefix that passes node admission. |
| SR-5 | §3 diagram; §4.1 `Memo.import`; §7 dune row; loop 5 | `import` recomputes every entry and loading replays every check, so a stored checker result never saves a check across processes. §7's sampled rerun is a trust assumption. In OCaml `agrees` and `learn`'s premise erase: cause 1 holds in Lean only. | ledger row "Persistent cache speed"; Codex P log `int -> bool` | fix in its slice (S0, ST3, S6) | Drop the checker arm of the store memo, or state the native trust assumption beside `Oracle.eq_uncached`. |
| SR-6 | §4.4 `poisoned`; ST3 | A wrong first result from a far store takes the query. The correct one refuses `poisoned` forever. A gate whose output bytes vary poisons on rerun. | reading §4.4, §6 | fix in its slice (ST3) | Recompute checker results before `record`; key nondeterministic actions per run. |
| SR-7 | §6 acceptance of V1, S1, S2, S4 | SM-C-26 recurs. S1 rows 1–4, S2 loop 2 and S4 rows 5–7 are `Tool.serve` requests, which land at S3a. `Doc.step` takes no snapshot, so row 4's `stale` exists only in `serve`. V1's five-request trace needs S1's commits and S3a's `suggest`. | reading §4.2 `Doc.step`, §6 | blocks implementation | State `Doc.step` rows in S1, `FillSet.add` rows in S2, `Live` rows in S4; move the loops to S3a. |
| SR-8 | §4.2 `feed_keepExact`, `kept_eq_certified`, certification; loop 4 | The edit engine always rechecks at `[]`, so "spliced unless the expanded edit disagreed" fails there. Keep-exact accepts a root edit that `certifiedB` refuses on a reference-free base. The fill set refuses the root first, so "certified exactly when the same commit would be accepted" fails. Loop 4's root hole rechecks. A root part key is not the module check (SM-C-13). | probe "root edits": `.rechecked`; `commit` ok; `certifiedB … [] = false`; `[.refused [] .root]`; `occurrences rootHole 0 = [[]]` | fix in its slice (S1, S2) | Check `[]` through the `module` key; restrict both laws and the sentence to non-root addresses. |
| SR-9 | §4.3 `Action.edit (at_) (a : DocAction)` | `edit _ (.publish fills)` publishes with no fill set, anchor or certification. Materialization gains a second owner in `Doc.step`. | probe `Tool.Action`, `Edit2.DocAction` | fix in its slice (S1, S3a) | Restrict `edit` to `commit`, `draft`, `revert`; publish calls `Program.materialize`. |
| SR-10 | §4.2 revert | A forward per-address check refuses any batch whose later item edits inside an earlier item's product. No checking policy is named. | probe "nested batch": forward check false, reverse order matches | fix in its slice (S1) | Undo items in reverse order on a temporary document; name the policy. |
| SR-11 | §4.2 refusal order; probe `FeedRefusal` | Today's `noFocus` has no constructor. `refused` is listed after `typeChanged`, whose `new : EffTy` needs a type. | `Doc.commit` in `SourceDocument.lean`; probe | fix in its slice (S1) | Add `noFocus`; put `refused` before `typeChanged`. |
| SR-12 | §4.1 `Memo.oracle`; §2.2 | Exact key equality drops today's prefix-extension hit. `SigData.holes` sits in every part key, so each new hole row misses every entry. §2.2 omits the cut. | probe: `extendsB` true, keys differ, old `lookup` hits; `Test/Program/CheckCacheControls.lean` control 3 | fix in its slice (V1) | Keep the extension rule with its law and R10's premise, or list the cut. |
| SR-13 | §4.1 `Checked`; §4.3 laws | `Checked` has a public constructor, so traces are not valid by construction. No `serve_valid` exists, so a host cannot supply `Memo.learn`'s premise. | probe `Checked`; law tables | fix in its slice (V1) | Give `Checked` a private constructor with validity; `learn` takes a `Checked α`. |
| SR-14 | §2.1, §4.3 exchange; loops 5–6 | `Exchange.apply`, `Base` and `staleBase` have no declaration, in the note or the probe. No reply carries the new `Head`. An act at `Base.state` names a non-head parent and refuses `fork`. | probe namespaces; §4.4 step 6 | fix in its slice (ST4) | Declare `apply` returning reply and new `Head`; make `Base.state` query-only or a fork to a new root. |
| SR-15 | §4.4 `Cas` | `Except Admission Cas` cannot answer §4.6's fresh, duplicate, created or recorded. `Cas.get` and the new refusals are unelaborated; today's `staleRoot` carries versions. `RootKind`'s five planes have no place beside `RootPolicy`. `interrupt` is an event, not a disk operation. | probe `Cas.Spec`; `Admission`, `RootKind` in `Store/Domain/Store.lean` | fix in its slice (ST1a, ST1b) | Return per-node and per-move outcomes; move `interrupt` to the event model; rule on `RootKind`. |
| SR-16 | §4.5 abstraction | "Create and advance each root" cannot reach a swap root's generation without targets the image lacks. | reading `advance_head` | fix in its slice (ST2) | Make the abstraction a relation, or restore generations as data. |
| SR-17 | §4.4 `advance` order | An obsolete expectation answers duplicate. README v2 §5.2 chose stale-first. Codex allows either. | probe `#guard (advance r2 ⟨2, 1⟩ 1).2 = .duplicate` | nice to have | Record the choice in §1. |
| SR-18 | §4.3; loop 5 | Load costs the whole history: every check, admission, play and discarded document, with a cold memo. Unstated. | reading | fix in its slice (ST4) | State the cost and the engine-change rule. |
| SR-19 | §4.3 `negotiate`; §7 | An inert query keeps no selection, so it is discovery with an intersection. | `serve_query` | nice to have | Keep the selection in the driver; refuse unselected methods. |
| SR-20 | §2.1 `Check` | The feed builds `.part` keys (`SigData`, environment, rebase), so part decomposition stays with the caller. `deps` and `combine` are public. | probe `CheckInput`, `Check.Spec` | nice to have | `Check` builds part keys from session, address and filling. |
| SR-21 | several | "Three seats" contradicts S0 → V1. Loop 3's `.hole 1` does not exist at loop 1's `n1`. `Answer.fills` has no anchor. `RunForm.view` answers a `LiveRecord`. The probe's `keepExact` docstring omits the layer recheck. | reading | nice to have | Edit the text. |

### Checked and holding

- `keepExact`'s refusal without a whole recheck does not conflict with SM-C-10. Refusal follows from
  the kept test, and acceptance keeps the whole-expansion comparison.
- Loop 1's spellings elaborate, with `.nat 7` for `7`: `Sel.row`, `Sel.key`, `.ofExit`,
  `.control .flush` and `Run.Verdict.played [.refused .noCall]` (probe and Codex P). Row 3 splices
  `[[1]]`. Row 2 is a `term` refusal at the part's root.

### Keep and cut

§6's K0 row carries all eighteen rows of `cuts.md`. Gaps: SR-12's silent cut; `Move.record` kept
after v2 removed it; `RootKind` unruled. §2.2 omits the survey's slice cuts `Kit_serve` request
execution, `E4_host.serve` (both S6) and the run entries `Run.runPure`, `Api.Runner.load`,
`Api.Typed.replay` and `Live.start` (S4). `Doc.history` duplicates the transcript.

### Deep modules

`Tool` and `FillSet` are deep. Leaks: `Check` (SR-20), `Cas.interrupt` (SR-15), `Action.edit`
(SR-9) and `Exchange` (SR-14). `Doc.session` exposes the whole `SourceSession`, and `Checked`
enters every consumer's type.

## Each Codex finding

| Finding | Verdict | Reason |
| --- | --- | --- |
| SM-C-1 | moved | Proved in Lean; `agrees` erases in OCaml, trust unstated (SR-5). |
| SM-C-2 | resolved at cause | Two operations; the certification sentence is false at the root (SR-8). |
| SM-C-3 | resolved at cause | `Place.resolve` with its probe control. |
| SM-C-4 | resolved at cause | `dry` nests in the types; atomicity is a planned law, not a type. |
| SM-C-5 | resolved at cause | Loop 1 elaborates (probe). |
| SM-C-6 | resolved at cause | Replay rebuilds the anchor, given SR-1's carrier. |
| SM-C-7 | moved | To an undeclared load contract (SR-1). |
| SM-C-8 | resolved at cause | `DepRole` carries the projection; `combine_deps` unproved. |
| SM-C-9 | resolved at cause | Contextual feed; laws re-frozen in S2; root case wrong (SR-8). |
| SM-C-10 | resolved at cause | The comparison stays inside the feed. |
| SM-C-11 | moved | Learning needs `serve_valid` (SR-13) and gives nothing across processes (SR-5). |
| SM-C-12 | resolved at cause | No answer type mentions a cache. |
| SM-C-13 | resolved at cause | `Explanation.part` with the restricted law. |
| SM-C-14 | moved | `interrupt` admits a result without `record` (SR-3). |
| SM-C-15 | moved | The store keeps a wrong first result (SR-6); native `learn` is unchecked (SR-5). |
| SM-C-16 | resolved at cause | `Head` with generation; probe control. |
| SM-C-17 | resolved at cause | Journal chain, though its parent is a raw digest (SR-2). |
| SM-C-18 | moved | An event, but unchecked and against the record gate (SR-3, SR-4). |
| SM-C-19 | prose only | §4.5 is a table; its abstraction cannot rebuild generations (SR-16). |
| SM-C-20 | resolved at cause | Three domains; answers exceed `Cas.commit`'s type (SR-15). |
| SM-C-21 | prose only | `Job` holds; `Cas.get` is not declared (SR-15). |
| SM-C-22 | resolved at cause | Claim corrected. |
| SM-C-23 | resolved at cause | `cuts.md` K-08. |
| SM-C-24 | resolved at cause | `cuts.md` K-07. |
| SM-C-25 | resolved at cause | `cuts.md` K-11. |
| SM-C-26 | moved | Acceptance still precedes its consumer (SR-7). |
| SM-C-27 | resolved at cause | Narrowed; `negotiate` remains discovery (SR-19). |

## Commands and limits

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true \
  docs/research/2026-10-17-seams/self-review-probes/SelfReviewControls.lean
```

Exit 0 (log beside it). The interface probe elaborates with the same command. No production file
changed. SR-3 to SR-6, SR-14 and SR-16 are readings of the declared text, not executions.
