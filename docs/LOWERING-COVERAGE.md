# Lowering coverage

Status: vocabulary adopted 2026-09-02 with the trace lane; the ledger itself lands
with P-T5 of the plan.

This document owns the vocabulary of `generated/lowering-coverage.tsv`: what a
lowering rule is, which evidence classes exist, what the states mean, and what
the ledger refuses to claim. It is disjoint from `docs/RUNTIME-COVERAGE.md`: a
lowering row may cite runtime-census row ids it rests on, and the join checks only
that those ids exist. Nothing here ever adds a witness to a census row, and a host
trace never turns a census row green.

## Rules

A lowering rule is one named Lean definition in `Effect4/Target/TypeScript/` whose
docstring carries the tag `lowering: rule.<name>`. One definition per rule, so
that evidence for a rule is evidence for exactly the code that implements it. The
denominator is `Effect4.Target.EffectV4.Rule.all` in
`Effect4/Target/TypeScript/Lower.lean`; the tag set and the denominator must agree
in both directions.

Rules today (straight-line scripts): `service-acquire`, `nullary-value`,
`perform-call`, `perform-bind`, `perform-discard`, `atom-call`, `ret`,
`error-abort`. The data reading of an error (`Except E A` spelled
`Result.Result<A, E>`) is an answer type, not a rule. Later: `choose`,
`jump-dispatch`, `loop-labelled`, `merge-block`, `dispatch-fallback`,
`region-onExit`, `region-scoped`.

## Evidence classes

| Column | Meaning | Produced by | Never filled by |
| --- | --- | --- | --- |
| `golden` | pinned expected traces under `generated/traces/` that exercise the rule (paths with digests) | `harness/trace/Emit.lean` through the traced service | a host run |
| `host` | a receipt under `harness/trace/receipts/` whose pin equals the current `harness/trace/host-pin.json` and whose comparison passed under the named mask | `effect4-trace` | a Lean theorem |
| `property` | a batch record in `generated/lowering-property.tsv`: seed, generated, admitted, agreed, and zero surviving lowering mutants | `harness/trace/Property.lean` and `scripts/test-lowering-mutations.sh` | a golden alone |
| `typeReceipt` | the declaration line the pinned `tsc.original` emits for the program (`--declaration --emitDeclarationOnly`) is byte-equal to `Script.declarationLine`, the Lean-rendered A, E and R channels; the receipt records the line and the digest of the emitted file | `scripts/check-lowering-types.sh` | the skewed TypeScript 5.9.3 extractor (auxiliary only) |
| `proof` | a named theorem about the Lean side (traced service versus Flow runner, dispatch versus structured form) with an axiom receipt inside `propext`/`Quot.sound` | `Effect4Test/Target/TypeScript/LoweringCoverage.lean` | any host observation |

## States

| State | Requires |
| --- | --- |
| `absent` | nothing |
| `pinned` | at least one golden |
| `checked` | `pinned` and a host receipt at the current pin |
| `covered` | `checked` and a property batch with zero surviving mutants |
| `proved-lean-side` | a `proof` entry (independent of the host columns) |

A rule ships in a published module when it is at least `checked` with a type
receipt. The report prints the counts per state and never a percentage.

## Gate

`scripts/check-lowering-coverage.sh` regenerates the ledger and fails on: a tag
without a row or a row without a tag; a golden path that is missing or whose
digest drifted; a host receipt whose pin differs from the current pin; a `proof`
entry that is not a theorem or reaches an axiom outside the ceiling; a declared
state above the derived one; `frames.jsonl` cited as evidence.
`scripts/test-lowering-coverage-gate.sh` plants each of those and requires the
named detector signal.

## Refusals

Agreement under a mask on a corpus does not establish: semantic preservation
beyond that corpus; any property of primitives, frames, or the pop loop;
interruption; concurrency or scheduler order; the module's types (see
`typeReceipt`); layer build, memoization, or provided-scope semantics; host error
identity, stack annotations, or defect payloads; termination (frontiers compare as
frontiers); byte identity of the program (see `check.sh`); any statement about
the host from a Lean theorem. Wording in reports follows `AGENTS.md`: no
"sound", "equivalent", "preserves" or "complete" without the mask, corpus and
receipt named.
