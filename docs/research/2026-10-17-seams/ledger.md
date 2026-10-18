# Seams amendment ledger and handoff

The current [implementation proposal](README.md) incorporates every finding in the [Codex review](codex-review.md).
It replaces the unsafe checker parameter and digest-only root comparison with explicit checked contracts.
The next work is to align the concurrent interface draft, then run S0, V1 contract finalization, and ST1a.
Implementation and new proofs remain outstanding.

The owner authorizes these planning amendments for Claude to finalize.
Base and head remain `774ddc3d784c0e0a04bd0d1e0bf6556c630074b2`, on `refactor/phase1-phase3`.
No production implementation changes or commits form part of this amendment.
The review's numbered references still refer to [README-v1.md](README-v1.md) and [cuts-v1.md](cuts-v1.md).
Those copies retain the reviewed bytes.

## Disposition of every finding

“Adopted” means the plan now specifies the correction.
It does not mean its acceptance checks have run against a new implementation.
Evidence labels P, C, S, M, and H keep their meanings from the review.

| Finding | Disposition | Current location | Implementation owner | Required acceptance |
| --- | --- | --- | --- | --- |
| SM-C-1 | Adopted: certify the checker function with pointwise agreement | README §§2, 4.3 | S0, V1, S3a | Actual OCaml closure and sealing checks, followed by `serve_ask` under its stated premise |
| SM-C-2 | Adopted: pending additions and immediate commits remain distinct | README §3.1 | S1, S2 | Compare revisions, history, root restrictions, and partial item outcomes |
| SM-C-3 | Adopted: hole selection requires one source occurrence | README §3.1 | S1 | In-range row with zero, one, and repeated occurrences |
| SM-C-4 | Adopted: atomic temporary folds, nested `dry`, one revision, empty-batch refusal | README §3.1 | S1, S3a | Late edit failure, late unresolved event, refused command phase, simulated refusal, and empty batch |
| SM-C-5 | Adopted: correct start and reply events | README §3.3 | S1 rows 1–3′, S3a full trace | Distinguish unresolved `h0` from resolved `ask` with `noCall`. Receive, apply, and flush produce the expected journal. |
| SM-C-6 | Adopted through accepted-action persistence | README §3.2 | S2, ST4 | Replay the actual pending additions at their original prefix. Old and fresh anchors retain their different publication behavior. |
| SM-C-7 | Adopted and simplified: retain the accepted transcript as data | README §3.2 | S3a, ST4 | Replay historical opens, starts, restores, publications, and plays in their stored order. Reject refused stored actions and false projections. |
| SM-C-8 | Adopted: dependency roles and address projections | README §4.1 | V1 | Owner equations, source filtering, synthetic layer addresses, wrapper removal, empty layers, aggregate entries, and refusal precedence |
| SM-C-9 | Adopted: contextual expansion and coordinated law changes | README §4.2 | V1, S2 | Filling beside a reference and filling with external reference targets. Re-freeze D4/D5/D9 and dependent premises. |
| SM-C-10 | Adopted: retain the whole-expansion splice guard | README §4.2 | V1, S1 | A layer edit changes a copy outside the target and forces fallback |
| SM-C-11 | Adopted: validated writer trace, memo learning, and full suggestion inputs | README §§3.1, 4.3–4.4 | V1, S3a, S6 | Candidate/limit/cursor behavior and miss→hit only with retained learning state |
| SM-C-12 | Adopted: project cache diagnostics out of semantic replies | README §4.3 | V1, S3a, S6 | Cached and uncached semantic transcripts agree while hit counters may differ |
| SM-C-13 | Adopted: restrict local explanation replay | README §4.4 | V1 | A successful body check followed by aggregate failure uses the whole key or aggregate evidence |
| SM-C-14 | Adopted and simplified: universal result checks replace `Move.record` | README §5.3 | ST3, ST4 integration | Empty moves, raw imports, recovery, malformed envelopes, and conflicting results cannot bypass the `Cas` rule |
| SM-C-15 | Adopted: recompute imported checker results | README §§4.3, 5.3 | ST3, S6 | An incorrect first result cannot construct a valid memo entry |
| SM-C-16 | Adopted: digest plus generation and immutable root policy/target kind | README §§3.2, 5.1–5.2 | ST1b | A→B→A, policy mismatch, target-kind mismatch, and stale-first precedence |
| SM-C-17 | Adopted through session entries with designated parents | README §§3.2, 5.2 | ST1b, ST4 | Session and tape journal append, fork refusal, and incidental-reference rejection. A Tree image is no longer the persisted session. |
| SM-C-18 | Adopted: interruption starts inside a transaction | README §5.4 | ST1b, ST2 | Internal cuts and actual write/sync/publication kills. Every previously durable node remains. |
| SM-C-19 | Adopted: explicit image, ownership, and limited Rocq reuse | README §5.4 | ST1a, ST1b, ST2 | New-to-old node connector, regenerated Rocq, retained snapshots, and named capacity/fault observations |
| SM-C-20 | Adopted: separate ordinary, damaged, and interrupted executions | README §5.5 | ST1b, ST2, ST3 | Defined R/r, strict retry rule, dual-fault order, and no collision claim for a forged occupant |
| SM-C-21 | Adopted: checked typed reads and all saved-run fields | README §§3.2, 5.1, 5.6 | ST1a, S4, ST4 | Wrong version/spec/kind/payload, untrusted bytes, session names, budgets, row names, and record versions |
| SM-C-22 | Adopted: correct gate-cache rationale | README §5.6 | ST3 | Different commands receive different keys. Existing command equality remains during migration. |
| SM-C-23 | Adopted: repair parser grammar before mirror keys | cuts K-08 | K0 | M's standalone-function and qualified-name controls. Keep unreadable type-block rows visible. |
| SM-C-24 | Adopted: move the test reader and retain faithful-prefix premises | cuts K-07 | K0 | `WordContract` builds and G6 names the actual `wfFrom_apply` premises |
| SM-C-25 | Adopted: one vector owner with capacity fallback | cuts K-10–K-11 | K0 | Value equality, carrier/size allocation results, and an exercised oversized fallback |
| SM-C-26 | Adopted: move checks to consumers and require disk comparison first | README §9 | Each slice | S0 before V1 landing, full trace and `serve_ask` at S3a, ST2 before persistent use |
| SM-C-27 | Adopted: narrow source claims and select concrete patterns | README §6 | S3b, ST2, S6, later Incremental | Version selection, cached/uncached comparison, finite fixtures, explicit observer lifetime and cutoff |

## Refinements made while integrating the review

Three GPT-6.1 specialists support the original review.
The amendment reuses those specialists for focused consistency checks.
The following choices remove ambiguities without adding another program representation.

| Question | Selected refinement | Why it matters |
| --- | --- | --- |
| Obsolete retry with equal target | Refuse before the duplicate branch. Only a fresh expectation can return duplicate. | A caller can rely on its root generation check even after A→B→A. |
| Separate result recording | Remove `Move.record`. Inserting a checked `Answered` node establishes its derived association. | Nodes-before-moves would make the first record operation redundant. |
| Generic result payloads | Reserve one versioned envelope grammar. Keep output references traversable and include output format in action identity. | Every insertion path reads the same query field, and legitimate format changes use distinct queries. |
| Recovery prefix | Retain all old durable nodes plus an allowed prefix of newly appended fresh records. | Damage in committed content cannot authorize truncation. |
| Root publication | Recover the entire old or entire new root table. | Per-root mixtures would violate atomic transaction observations. |
| Session storage | Adopt the concurrent draft's accepted-action chain at kind 7, with runtime transcript data and a replay equation. | It removes allocation reconstruction and synthetic histories. It retains superseded actions. |
| Learning | Adopt the concurrent draft's writer trace, with a sealed validity-bearing package consumed by `Memo.learn`. | Pure and native drivers can retain learned entries without an unrestricted mutable callback. |
| Persistent cache speed | Recompute imported results before certification, then retain validated hits in process. | The plan does not trade correctness for an unproved cold-cache shortcut. |

## Earlier constraints retained

| Constraint | Current treatment |
| --- | --- |
| One program owner | `Eff` remains program syntax. Requests, checker inputs, and stored records are data about operations. |
| No core-to-Laws dependency | Core holds computation witnesses. Laws derives the cross-field properties. |
| No hand-written native semantic shims | Generate codecs, wrappers, key operations, and core dispatch. Hand code owns the physical boundary. |
| Base in generated libraries | Permit qualified operations with a declared target contract. No blanket ban. |
| Full program admission | Start and restoration use `admitProgram`, beyond a partial kit check. |
| Canonical bytes | Retain the existing exact codecs, explicit versions, and hostile byte fixtures. |
| C4 shape pin | Keep blocked until the separate tag/reference-kind issue is addressed. No rendering-injectivity claim follows from adding one field. |
| R12 `Option Unit` | Select an explicit field profile distinguishing absence from a present unit. |
| Tier reuse | Keep proved `Word.Layered` and `LocalFirst` until a real consumer and connectors justify replacement. |
| Proof placement | Register each required property and planned goal before proof work in its owning slice. |

## Files and verification

Changed planning documents:

- `README.md`: version 2 of the seams implementation proposal.
- `cuts.md`: corrected scope and acceptance for all original cut rows.
- `ledger.md`: this disposition and handoff.

Added historical copies:

- `README-v1.md`: the exact proposal bytes used by the review.
- `cuts-v1.md`: the exact cut-list bytes used by the review.

Added verification records live under `review-probes/`.
The amendment checker compares the current tree with the earlier recorded baseline.
It reports concurrently created interface files separately from this amendment's outputs.
It allows the named planning amendments and checks the retained review evidence by digest.

```sh
python3 scripts/check-language.py --strict \
  docs/research/2026-10-17-seams/README.md \
  docs/research/2026-10-17-seams/cuts.md \
  docs/research/2026-10-17-seams/ledger.md
python3 docs/research/2026-10-17-seams/review-probes/check_amendment.py
```

The result records are `review-probes/amendment-language.log` and `review-probes/amendment-checks.json`.
The checker verifies finding coverage, cut coverage, local links, dependency order, historical copies, retained evidence, and unchanged production bytes.
It does not execute the new interfaces or prove their laws.

The original `results.json` and `host-probes.log` remain the finite-probe evidence.
A new finite representation control checks the erased-history obstruction and the retained-data correction.
It runs through `scratch/lean-slot.sh` with `LEAN_NUM_THREADS=3` and warnings treated as errors.
The command and result appear in `review-probes/amendment-probe.json`.
It does not compile the concurrent interface probe or the proposed application.
No production change requires a new behavior-gate run in this amendment.
No axiom output is claimed for new obligations because this amendment states no Lean theorem.
The new slices still owe their narrow builds, axiom gate, and reached behavior gates.

## Concurrent interface draft: alignment required

`interfaces.md`, `interface-probe/SeamsInterfaces.lean`, and `implementation-brief.md` appear during this amendment.
They are another author's work and remain untouched.
`review-probes/concurrent-inputs.json` records the versions read here.
Their supersession sentence does not incorporate this later amendment.
Treat `README.md` version 2 and this ledger as the selected recommendations for reconciling that draft.
The coordinator finalizes one consistent interface before implementation.
The concurrent implementation brief calls the draft settled, so its dispatch must incorporate this alignment first.
Use this ledger to integrate the following amendments before dispatch.

| Interface topic | Selected integration instruction | Evidence or reason |
| --- | --- | --- |
| Accepted-action persistence | Adopt the session chain. Keep document/run histories as replayed projections. | Simpler than reconstructing a transcript from a Tree. It directly retains anchors, origins, and allocation order. |
| `StateOf` and `Spec.transcript` | Add runtime transcript data and its validating replay equation. Derive existential reachability from them. | A field proposing `transcript` does not implement extraction from `reached : ∃ …`. The new Lean red control rejects that extraction. |
| Accepted replay | Use `Except` replay or an accepted-prefix predicate. Reject a failed action in stored history. | A total replay that ignores refusals cannot certify a log of accepted actions. |
| Writer trace | Keep the pure writer and driver learning. Seal the whole `Checked` package with erased validity and let `Memo.learn` consume that package. | A native raw list must not acquire memo validity merely because a proof argument erases. |
| Stored references | Use typed `Ref` fields for parent, query, program, job, and tape edges. Use `AnyRef` only when the target sort varies. | The new finite control confirms that `Canonical.toVal` of a digest has no reference edge, while `AnyRef` does. |
| Root retry | Compare generation and digest before duplicate target. Change the stale-token/equal-target control accordingly. | The concurrent probe currently accepts that obsolete retry. This plan chooses strict compare-and-set. |
| Result association | Reserve the common envelope and remove redundant `Move.record`. | Universal insertion checks close the bypass with one operation. Keep output references visible. |
| Interrupted publication | Include cuts before and after atomic root publication, with entire old/new root tables. | A model whose interrupt always leaves roots old omits an interrupted acknowledgement after publication. |
| New laws | Keep full owner connectors, source filtering, and the stated Rocq premises. | Lean type checking of specification fields does not prove their required implementations exist. |

The concurrent draft's proof and build claims are not rerun or adopted as evidence here.
Its full Lean type signatures remain for Claude to align with these selected contracts.
In particular, its probe's public memo and erased validity premises do not test the newly required abstract OCaml package boundaries.

## Claude finalization

Use `README.md` as the current seams proposal and this ledger as the review disposition.
Do not merge conflicting choices from the historical drafts back into the full Lean type signatures.
Finalize the accepted-action grammar, dependency roles, refusal constructors, and common result envelope within the selected contracts.
Record required authority changes at the coordinator-owned anchors.
Then dispatch S0, V1 contract work, and ST1a, with K0 alongside them.

The handoff ends at a reviewed implementation plan.
No production fix, general refinement proof, or native agreement theorem is claimed by these document changes.

## Finalization

[interfaces.md](interfaces.md) version 2 finalizes the plan and adopts every row of the alignment table.
It replaces `Memo.import` with no stored checker results (its decision D1).
Its §9 records each other choice beside this ledger's.
