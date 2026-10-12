# Numeric target and dispatcher acceptance

The target checks pass, but the compiler tool audit does not satisfy the library axiom allowlist.
Its one additional finding is metadata lookup through Lean.Environment.
The proof libraries retain their existing trust boundary.

Base: `9d7d4e5ef12528985a78f19352004fa2ef6e427f`.
The source commit containing this receipt is the accepted target landing.
`target/AcceptedEvidence.json` records the exact changed paths and their hashes.

## Placement

Concept: translation-simulation, R8 and M7.
Proof role: target boundary maintenance and finite controls.
Evidence status: checked generation, target typechecking, and bounded executions.
Scope: the current profile multiplication atom, numeric ingress, and dispatcher representation.
The [numeric plan](PLAN.md) and [dispatcher plan](DispatcherPlan.md) record the design.
No theorem statement or program meaning changes in this target slice.
The host remains outside the Lean proof boundary.

## Changes

`OCaml5.Lcnf.Builtins` lowers Profile.scale through exact multiplication and the existing profile check.
Raw Nat.mul retains its previous bounded implementation.
`Effect4Gen.PreludeAtoms` emits the marked multiplication row into the TypeScript prelude.
The prelude refuses a product before exposing its rounded result.

The dispatcher type substitution remains explicit.
`Externs.fieldCarrierIn?` reads a field override first, then its declared external type.
The constructor conversion uses the declared empty operation only for a tracked empty list.
The generated constructor keeps its surrounding record and every other field.
The engine table names the actual insert, spawn, and dropToken declarations.
Old substitutions that lowering no longer reaches are removed.

The existing engine adapters read the list-shaped dispatcher.
Their queue observation uses nonempty buckets.
The private host dispatcher's independent flag remains outside this representation claim.

`LcnfGen` restores warning 8 in both generated headers.
The generator rewrites all four roots and their closure reports.
No generated output is edited by hand.

## Checks

Exact commands and raw output are retained under `target/`.
The retained runners record the original integration checkout and temporary control paths.

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws Effect4Gen.PreludeAtoms OCaml5.Tools.LcnfGen Test.Machine.NaturalProfile
LEAN_NUM_THREADS=3 lake env lean --run tools/Effect4Gen/Driver.lean --group PreludeAtoms
LEAN_NUM_THREADS=3 python3 scripts/generate.py --only lcnf
python3 /private/tmp/check-numeric-typescript.py
python3 /private/tmp/check-numeric-ocaml.py
python3 /private/tmp/check-carrier-fixture.py
python3 /private/tmp/compare-profile-tool-audit.py
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Counterexamples/Machine/Semantics/MulOutsideProfile.lean
```

The combined laws build passes 1,065 jobs.
The final compiler repair build passes 22 jobs.
All four generated roots report zero holes, successful module checks, and successful name checks.

The pinned tsgo version is 7.0.0-dev.20260629.1.
Its prelude typecheck passes; all 86 atom controls pass.
The retained pre-repair probe detects rounded and out-of-profile multiplication.

OCaml 5.1.1 builds the engine, both instances, comparison driver, benchmark, dispatcher controls, and API controls.
All 206 engine checks pass.
Both engine instances check ordinary, zero, boundary, rounded, and machine-integer-exceeding products.
Refusal retains the input observation and the unread decisions.
The dispatcher and API controls pass.
All four generated roots compile with warning 8 enabled.
A missing-constructor control fails specifically with fatal warning 8 under the generated header.

The carrier fixture keeps the surrounding record and an existing carrier field.
A missing empty operation fails OCaml's abstract carrier typecheck.
A nonempty list leaves the empty operation unused, which the generator rejects.
The actual dispatcher-field lookup control also passes.

The retained stale-table, nominal-field, and dropped-record failures precede the accepted output.
They remain rejection evidence, not accepted artifacts.

## Tool audit

`ProfileToolAudit.lean` audits the five changed compiler and generator modules.
The baseline has 114 outside-allowlist findings among 806 declarations.
The current source has 115 among 808 declarations.
All 114 old findings remain unchanged.
The added finding is `OCaml5.Lcnf.Externs.fieldCarrierIn?`, which reaches Classical.choice through Lean.Environment.
These metaprogramming modules sit outside the Effect4 and Test library roots.
No library axiom exception changes.

The comparison compiles baseline sources in a separate module tree.
It checks that the baseline lacks the new helper and the current audit finds it.
`target/profile-target-tool-audit-comparison.json` retains the exact difference.

## Size and remaining work

The source and generated diff is measured by `target/DiffStat.txt`.
Most changed lines are deterministic generated targets after the shared machine edits.
No scenario proof machinery is added.

E4-RUN-CE-047 becomes a repaired regression with exact reference answers and finite target refusals.
The general compiler simulation, the raw natural rows, and the behavior sweep remain open.
The original scenario goals remain open.
The sweep must regenerate later context changes before comparing those targets.
