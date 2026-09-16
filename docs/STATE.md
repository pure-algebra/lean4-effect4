# State of the work

One page: what is true at HEAD, the ratified plan, what is next, what the owner must decide. Replaced at every landing. The review log and `COORDINATION.md` are history; this file is the entry point.

## What this is

An agent-first language of algebraic effects whose engine is reified in Lean. One machine, three faces: Lean proves it (the reference, the machine, the certificates), OCaml runs it natively (the same machine compiled through LCNF, the reified Effect runtime as a fast, low-level platform outside any JavaScript host), TypeScript interoperates with the Effect ecosystem (the printer and readers). Programs are data: a canonical `Eff` tree with a digest, a computed typing certificate, folds, a tape-driven run with replay, and a printed image that reads back. Any Effect code the profile covers reads into `Eff`; coverage grows by data (generated rows, proved forms), and an unregistered head refuses by name.

## True at `670f76ab` (2026-09-16)

- Branch `refactor/phase1-phase3`. `make check` green: 308 modules, 53,998 declarations at `[propext, Quot.sound]`; the `Classical.choice` boundary is 2 modules, 29 declarations. The reader lane matches Lean's oracle on all 416 programs. The host lanes (`make check-host`) were last run by Codex before `1a97c37`.
- Landed today: the typed surface (one typing certificate `TypedProgram`, certified emission `ModuleEmission`, certified reading `ModuleReading` and `Api.admitModule`, hoisting and reconstruction proofs, typed derived forms, the lexical certificate, one owner each for binding names and the declaration annotation), and seat 2's deletion of the profile module (net −246 lines, seven axiom exemptions gone).
- Of the language's four halves, the engine, the interop boundary and program-as-data exist; the agent-facing authoring surface has no commits. It is the focus now.

## The ratified plan (owner, 2026-09-16 evening; rulings DI-79 to DI-90 in `docs/DESIGN-ISSUES.md`)

**M1, the solid core.** Authoring first, then the alphabet:
1. The authoring elaborator (DI-83): a named source tree `Src`, `elaborate` by nearest-binder resolution, layers by name through `restoreAll`, located refusals; the authoring profile of the alphabet as data (DI-84); the checker's refusal projection `blame`/`explain` (DI-86); the additive facade (DI-85: `Api.check`, `Typed.*`, budgets with defaults, `Api.digest`, `Api.author`). Packet: `docs/research/2026-09-16-authoring-ready-packet.md`.
2. The three step-0 refactors of the constructs packet: promote `childLevel` to `Node.binders`, delete `Plain`, `suspendDecided`.
3. S1 stable wire tags (constructor tags are declaration positions today, `Program/Wire.lean:16`).
4. The `Eff` series (DI-79): `select`, `iterate`, the `Decision` family; retire `branch`, `whileLoop`, `callback`, `yieldError`; `catchIf` stays (DI-82). Every step regenerates the OCaml engine and runs `check-ocaml`. Packet: `docs/research/2026-09-16-select-and-iterate-ready-packet.md`. One baseline promotion at the end.

**M2, the semantic repairs.** The `Ty` series (`scopeExit`, `fiberId`; DI-81, DI-87), `refSet` answers unit (DI-80), unit spelling and the type-oracle gap (DI-87), full-key service identity, the one keyed route with the facade deletions and the session generated into the OCaml engine (S6), layers (S5), B18's strings off the wire, package rows generated from the pinned package's declarations (DI-89), then the ingest packet: style inverse as data, the canonical reader generated from `Read.lean`, the two engines cut to normalizers, the ingest census back on (DI-88).

**M3, the proofs and the rest.** Straight and loop safety (S8a, S8a-L), observation and clocks (S7), the combinators and compact iteration (S9b, S9c) with the higher-order forms by named list (DI-89), reference typing (S8b), the `Effects` package in-tree (DI-90). `Stream` and `Channel` are the next reification packet after M3.

**Cut from the plan by the rulings:** the §3.6 substitution machinery, the §3.1 at-most-one summary, the §3.8 annotation grammar's parse round trip, per-packet alphabet edits, seat 2's structural-type-argument step (its stash is dropped).

## Next, in order

1. Commit this record. Drop seat 2's step-2 stash.
2. The authoring elaborator, the profile table and the refusal projection, in the main session, one Lean process at a time, each as its own commit after `make check`.
3. The facade's additive half.
4. Step 0 of the constructs packet, then S1, then the `Eff` series.

## Owner decisions open

None blocking. Standing asks 1 (the `Effects` package) and 2 (DI-39's amendment) are ruled by DI-90 and DI-82.

## Process (ratified)

- Speed over ceremony: edit with whatever is fastest, including shell edits; build what you touch; `make check` once per step; `make check-host` per slice; nothing pushed without the owner.
- One Lean process at a time. A parallel seat runs only in its own worktree on disjoint files, with a brief the owner has seen. Fable seats need the owner's word each time.
- Generated modules stay self-contained on `effect` alone unless the `select .tag` narrowing probe fails (DI-85).
- The current authorities under `docs/research/` are tracked (the plan, the two open packets, the obligations note, the algebraic-reading ruling, the review log); the rest of the directory stays untracked.

## Where things are

- Plan: `docs/research/2026-09-16-foundational-language-implementation-plan.md` (S0 to S9; its header says the register rows win where they differ). Obligations: `docs/research/2026-09-16-strict-proof-obligations.md`. Register B1 to B21: the top of `docs/research/2026-09-16-implementation-review-log.md`. The algebraic reading and the order ruling: `docs/research/2026-09-16-algebraic-reading-assessment-and-order-ruling.md`.
- Checks: `make check` after every change, `make check-host` per slice, `make check-full` before a release. Lanes are incremental: a lane whose inputs have not changed since its `.lake/check/<lane>` marker is skipped, so the marker's time is the receipt.
