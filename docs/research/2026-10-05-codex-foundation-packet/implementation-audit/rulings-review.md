# Foundation ruling acceptance review

The rulings retain the accepted contracts. Correct one proposed claim before stating it: retain the winning-cancellation premise.

Proof role: acceptance review of decisions and proposed obligations.
Evidence status: source comparison and retained receipt inspection; no new runtime execution or proof.
Scope: commit `5ebacecc8631b9897652a86f67b7f1d3097dcffc`, decisions 214–237, the foundation note, and the registry's open parts.

## Finding: retain cancellation arbitration in the proposed claim

`waiting-request-obligation-preserved`, under R11 in `tools/Tools/SemanticsRegistry.lean`, says:

> a cancellation before consumption withdraws the request and consumes nothing

The accepted packet and decision 222 instead require cancellation to **win** before consumption.
The omitted premise matters: an interruption request can remain pending while a protected operation commits.
Arrival, winning withdrawal, commitment, and later interruption are different observations.

Smallest correction:

> When cancellation wins and withdraws the request before consumption, the operation consumes nothing. A completed commit remains committed.

Keep the four observations from row 222: commitment, operation exit, caller-continuation entry, and fiber exit.
Place this correction in the proposed R11 claim before its owning slice states a goal.
The waiting wrapper and Queue agreement consume the claim.
Its immediate prerequisites remain the request arbitration rule and the selected delivery profile.
It establishes neither successful return of every committed value nor resource lifetime outside a protected use.

Classification: proposed-claim scope drift, not a change to row 222 or an existing theorem defect.
The F1 and STATE summaries use similar shortened wording; their references still lead to the correct ruling.
Align those summaries when correcting the semantics registry, without treating them as independent contract changes.

The retained five-control probe separates commitment from return and cancellation while waiting.
It does not directly test an interruption requested before consumption while the operation remains masked.
This review does not claim a new runtime counterexample for that ordering.

## Accepted contracts retained

| Area | What remains explicit |
| --- | --- |
| Queue | Row 219 retains strict request order, nonblocking consumption, taker-side commitment, head-batch blocking, and the declared difference from native 4.0.1. |
| Waiting | Row 221 retains checked dynamic accesses, atomic wait registration, notification ownership, distinct request/token/batch identities, and stale-delivery controls. |
| Transactions | Row 223 retains the restricted `Eff` fragment, flat nesting, exclusions, dynamic access order, and completion of bookkeeping before receiver execution. |
| Transaction agreement | Row 223 leaves version erasure and target agreement open. R10 explicitly requires a named release and immutable payloads. |
| Alternatives | Row 224 retains retry-only fallback, abandoned left writes, retained enclosing writes, combined dependencies on double retry, and propagated failure. |
| Work limits | Row 226 retains an embedded budget first and full driver suspension before resumable ownership. Reissuing a command remains insufficient. |
| Observations | Rows 222 and 230 retain separate operation outcomes, public observations before hiding state, future handle correspondence, and separate progress claims. |
| Time and versions | Rows 231–232 retain old millisecond meaning, separate clock meanings, the numeric boundary, and an audit before moving the pin. |

The transaction exclusions prevent a claim that arbitrary Effect code rolls back.
The separate ticket-composition exclusion retains the opposing-ticket witness's scope.
The R12 progress clauses retain fairness, body-progress, and budget premises.

The consolidation absorbs `tx_body_access_frame` into `atomic-attempt-isolation`.
Its future statement must show that every executed access is recorded.
The atomic body profile requires this for resolved calls too.
Rows 221 and 223 retain this restriction; the shorter table does not repeal it.
The tracking of every dependency remains a design prerequisite, not a theorem established by the model's function type.

## Open work and placement are represented honestly

The foundation note records eighteen proposed obligations and an exclusion, rather than claiming eighteen Lean goals or proofs.
The semantics registry keeps them in requirement open parts until their definitions permit statements.
This follows the authority's allowance for required parts without goals.
Each owning slice still owes a placed claim and goal before proof work.

The whole Queue transition packet and design W remain explicitly owed before the Queue implementation slice.
Starting the separate bounded T3b work does not close either prerequisite.
The clock's placement under R13 is disclosed and retains its translation-simulation concept.
Rows 235–237 record additional owner decisions; they are not unexplained changes to the earlier packet.
In particular, row 237 delays clock work until T3b merges because their generated outputs overlap.
The earlier foundation note's parallel clock schedule is superseded planning text.

## Verification and limits

Read the current operating rules, the named authorities, and both accepted packet notes.
Compared the accepted notes with their tracked copies; both pairs are byte-identical.

| Input pair | SHA-256 |
| --- | --- |
| `contracts-and-literature.md` | `2c4aa82918ff4ed8b4d0413fd17813dc06fa42ae34adf5400dce368e4a15d89f` |
| `foundation-audit.md` | `01f1e527f380842d543ed8110eadbfcbf9adedaf06189c0ddaa37a8d11723c93` |

The original directory is `/private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/`.
The tracked copies are in `docs/research/2026-10-05-codex-foundation-packet/`.
The companion `rulings-verification.json` records the checked commit, input hashes, assertion outcomes, and working-tree status.

Commands: `git rev-parse HEAD`, `git status --short`, targeted `sed` and `rg` reads, and the retained verification script.
All source-read commands completed successfully.
No build, generator, install, runtime probe, or active-repository write ran.
This review accepts the recorded design boundaries; it establishes no implementation agreement or new theorem.
