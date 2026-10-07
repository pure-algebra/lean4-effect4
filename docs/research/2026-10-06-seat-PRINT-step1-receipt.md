# Receipt: Step B (probe of the TypeScript printer)

This receipt records Step B of chunk 2 (PRINT step 1).
It changes no file of the Lean source tree.

## What the probe ran

The probe exercised tsgo 7.0.0-dev.20260629.1 across 44 TypeScript test cases.
The eliminator forms and binder term forms ran in two variants.
The green variant carries type arguments at the join of two union members.
The red variant carries one member too few and fails.
All evidence files stand in `docs/research/2026-10-06-print-probe-evidence/`.

## Key findings

Six forms have no place for type arguments in target syntax:
1. Boolean test of `select` (`s ? a0 : a1`): ternary conditional has no type argument syntax.
2. Record field access (`field`): member access `r.name` has no type argument syntax.
3. Record field update (`recordSet`): spread syntax `{ ...r, name: v }` has no type argument syntax.
4. Tuple element indexing (`tupleAt`): indexing `t[index]` has no type argument syntax.
5. Atom `length`: prelude exports `length` with 0 type parameters.
6. Atom `isSome`: prelude exports `isSome` with 0 type parameters.

All other 38 forms accept explicit type arguments at the join and reject the red control.

## Files added

- `docs/research/2026-10-06-print-probe.md`
- `docs/research/2026-10-06-print-probe-evidence/*.ts.txt` (88 evidence files)
