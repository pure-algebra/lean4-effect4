# Promoting the design into the authority documents: plan, and a one-page system map

Status: **executed 2026-09-30 in the documentation cut-over commit; kept as history.** The one-page map is now `docs/core/system-map.md`, the boundary `docs/core/host-boundary.md`, the storage interfaces `machine-state.md` §7, the stages `lcnf-route.md` §8, the decisions rows 91–103. Originally: An authority document states what
is settled and names what is open, so the promotion follows the owner's rulings on the decisions
in §3. Base `be15b062` on `refactor/phase1-phase3`.

The sources are four notes from 2026-09-30:
- the [origin-ledger plan](2026-09-30-origin-ledger-and-step-invariants-plan.md);
- [host answers and the typed guarantee](2026-09-30-host-answers-and-typed-guarantee.md);
- the [external runtime contract](2026-09-30-external-runtime-contract.md);
- the [plan review](2026-09-30-origin-plan-review.md) and its
  [ratification conditions](2026-09-30-origin-plan-review/RemediationReview.md).

## 1. The system in one page (draft)

This is the page the owner asked for: what the system is for, how it works, how it is organized,
and where it is going. Each layer names its owner document and its status. **Proved** means a
theorem at the trust ceiling; **exists** means code without that theorem; **open** means planned.

**The goal.** An agent-first language of algebraic effects whose programs are first-order data.
An agent writes a program, a checker certifies its type, and a machine defined in Lean runs it
with every choice explicit, so runs replay exactly. The machine's meaning is Effect's own: each
behavior it models cites the line of the pinned Effect rc.112 source it transcribes. The same
program reads from and writes to Effect TypeScript, and the same machine compiles to native
OCaml. Proofs connect each of these to the others, or the gap is named.

| Layer | What it is | Owner | Status |
| --- | --- | --- | --- |
| 1. Programs as data | One program representation, `Eff`: a first-order tree with a digest, stored by content, printed and read back. Names are data; no closures or runtime objects in program syntax. | `AGENTS.md` vocabulary, `docs/core/ontology.md` §5 | exists; one free object per sort |
| 2. Types and certificates | `Ty`/`EffTy` and one checker (a fold) that either certifies a type or refuses with a located reason. | `docs/core/ontology.md`, `Program/Checker.lean` | proved sound and complete against `HasTy` at every path |
| 3. Meaning | One denotation; a reference machine; the native (frame) machine. | `docs/core/machine-state.md` | proved: meaning soundness, `run_eq_meaning` (straight fragment), `loopAgreement` (looped), `run_eq_ref` (the two machines, **empty host table only**) |
| 4. Choices as data | Every scheduling, timing and host-answer choice is a decision on a tape; a run's journal replays it. | `Run.lean`, `Api/Runner.lean` | proved: `replay_unique`, `journal_replays` |
| 5. The typed-state guarantee | A checked program never reaches a malformed state, and every fiber finishes at its type. | `docs/core/post-phase-c-synthesis.md`, `Laws/Program/Typed/` | slices 1–5 proved (world, admission, protocols, stack walk, delivery, assembly); M5–M7 open; statement repair and value-predicate amendment pending |
| 6. The host boundary | Host services are rows in a table. A program's call parks a fiber; the host answers through one keyed session that checks each reply against the row's type and the declared types of any handles in it, then prepares the answer. | proposed `docs/core/host-boundary.md` | exists: session, envelope, admission, preparation. Open: handle types (a live hole today), the registry, lifecycle and cleanup, the reference connection (DI-57) |
| 7. Runtime state and storage | The machine's state is a set of families (fibers, frames, cells, deferreds, scopes, memo, timers, external resources, sessions). Each is owned by one of six storage interfaces with laws: dense arena, keyed table, ordered work, append-only sequence, persistent path/environment, derived view. Facts fixed at creation live in append-only ledgers; derived views (such as a handle's declared type) are computed from ledgers and the checker. | `docs/core/machine-state.md` | arena laws and `Projects`/`Refines` proved; the interfaces and the fork ledger planned |
| 8. Compilation | Three distinct compilations: a program to the machine's first-order runtime code (`compileEff`); the Lean machine itself to OCaml through Lean's LCNF (OCaml is made only from LCNF); a program to and from Effect TypeScript (printer and reader). Each stage is a named connection with its own evidence. | `docs/core/lcnf-route.md` | printer/reader laws and completeness over the template table proved; the OCaml engine checked by differential runs (finite evidence); number policy mixed; rows 28/29/31 open |
| 9. Faithfulness to Effect | The pinned vendor source, the runtime census with its coverage report, the truth harness against real Effect runs, and signed divergences (`U-01`). | `docs/RUNTIME-COVERAGE.md`, `docs/UPSTREAM-BACKLOG.md` | exists; coverage quoted only from the report |
| 10. Authoring and use | A named authoring surface elaborated once into `Eff`, a certificate-first API, and later the MCP face (after LCNF, by the owner's order). | `docs/core/api-surface.md` | exists in part; the agent authoring surface is the stated purpose |

**Evidence discipline.**
- Every claim names its theorem or its finite probe.
- The trust ceiling is `[propext, Quot.sound]`.
- Coverage is quoted only from its report.
- A refusal is located.
- A gap is written down, not hidden behind a `True`.

**How the pieces connect.** A program comes in, from the authoring surface or read from
TypeScript. The checker certifies it. The machine runs it, reference for proofs and native for
execution, with explicit choices and with host calls through the keyed session. The same machine,
compiled through LCNF, runs natively in OCaml. The printer writes the program back as Effect
TypeScript. Each arrow is an exact embedding, a simulation on a named observation, or a located
refusal, or it is listed as open.

**Where it is going, in order:**
1. Slice 6 (the fork ledger).
2. The M6 statement repair and the value-predicate amendment.
3. M5–M7, the typed-state guarantee on programs without host answers.
4. The external lane, fiber slice first, then the Ref slice after generic cells.
5. The first storage replacement (row 85).
6. The first real target closure (rows 28/29/31).
7. Composing them.

The authoring surface and reading go alongside, and the MCP face comes after LCNF.

## 2. Where each fact goes (one owner each)

| Fact | Authority | Source |
| --- | --- | --- |
| The one-page map above | new `docs/core/system-map.md` (recommended), with `ontology.md` trimmed to its formal frame (§5) and its dated 2026-09-17 sections moved to `docs/research/`. Alternative: `ontology.md` §0. | this note |
| The six storage interfaces and the runtime-family inventory | `docs/core/machine-state.md` | contract §7 |
| The fork ledger as an append-only sequence, and the registry as a derived view over creation ledgers plus the checker | `docs/core/machine-state.md` | ledger plan §3, host-answers note §8 |
| The host boundary: lifecycle, receipt versus application, capability environment, the 20-constructor acceptance matrix, entry paths, required controls | new `docs/core/host-boundary.md` | contract §§2–6, host-answers note |
| The compilation stages as named connections, the number policy, validation certificates | `docs/core/lcnf-route.md` | contract §8 |
| The M6 statement, and the value-predicate amendment | `docs/core/post-phase-c-synthesis.md` §H, and the M6 declarations | host-answers note §4, B3 |
| Every ruling | `docs/core/decisions.md` rows, written by the coordinator | §3 below |
| The pointer | `docs/STATE.md` | |

New core files need a line each in `AGENTS.md`'s authority map. That is the owner's governance
call.

## 3. What has to be ruled first

The three notes ask overlapping questions. One list, de-duplicated:

| # | Decision | Source | Recommendation |
| --- | --- | --- | --- |
| 1 | Fork ledger: forks only; record the creating construct's kind if the registry is ratified | ledger plan §9.1, §3 | yes |
| 2 | Reader switch rests on bounded evidence (census, local lookup facts, runner) | ledger plan §9.2 | yes |
| 3 | Trace agreement stays a proof obligation; `forkedOf` moves to `Test/` after | ledger plan §9.3 | yes |
| 4 | Automation decided after three hand proofs | ledger plan §9.4 | yes |
| 5 | M6's capstone counts only runs with no applied host answer (current scope) | host-answers §4 | yes |
| 6 | Constructor-complete membership judgment before M6 proof work | host-answers B3; contract ruling 4 | yes |
| 7 | Interim boundary profile refuses internal handle kinds in host rows; the registry of declarations derived from creation sites is the route to supporting them (extends row 44; touches row 7) | host-answers B1; contract ruling 2 | yes, both, in that order |
| 8 | One public typed host replay route over the keyed session journal, both budgets | host-answers B2; contract ruling 6 | yes |
| 9 | External completion required before the public guarantee is claimed | host-answers §6.5; contract ruling 1 | yes |
| 10 | Stable host resource identity, recursive preparation, cleanup ownership at every cancellation point | contract ruling 3 | yes |
| 11 | Storage and compiler stages compose only through named semantic connections | contract ruling 5 (reaffirmed) | yes |
| 12 | The system map's home (new `system-map.md`, `ontology.md` trimmed) | this note §2 | yes |
| 13 | The host boundary's home (new `host-boundary.md`) | this note §2 | yes |

## 4. Order of writing, after the rulings

1. `decisions.md`: the rulings as rows (coordinator).
2. `system-map.md`, from §1, with each status re-checked against the tree on the day it lands.
   Trim `ontology.md`.
3. `machine-state.md`: the six interfaces, the inventory, the ledger and the registry.
4. `host-boundary.md`: the contract's boundary sections, with the interim profile stated.
5. `lcnf-route.md`: the stage table and the number policy.
6. The synthesis §H and the M6 declarations: the statement repair (its counterexample registered
   as `E4-SCHED-CE-015`).
7. `STATE.md` and `AGENTS.md`'s authority map; `make gen-architecture`.

Each is its own commit by explicit paths; research notes are force-added when their authority
lands. The probes stay in `docs/research/` as evidence, cited by the authority documents, never
copied into them.

## 5. Probes still worth running before the rulings

- **The static environment at a path.** A small fold, checked against the checker on the
  corpus's fork sites: it removes path B's one real gap.
- **The fiber vertical slice end to end** on the live session, with the derived declaration: the
  forged reply refused, the honest one applied, the program's exit typed.
- **The number policy.** A program whose intermediate sum passes the largest integer, run on
  both engines, to see the wrap the translation table predicts.
- ~~A handle inside a pair, reached internally.~~ Done: a checked program with no host table
  stores a fiber handle in a pair, projects it and awaits it, and runs to 7
  ([path probes](2026-09-30-host-answers-evidence/PathProbes.lean) §D). Decision 6 is needed
  for M6 itself.
