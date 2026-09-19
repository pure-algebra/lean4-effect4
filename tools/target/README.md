# Independent target type diagnostics

`make check-target` (`bun tools/target/cli.ts --repo .`) checks the actual printed programs and adapter members
against type metadata generated from Lean. It writes `.lake/target/report.json` and exits
0 only when every selected comparison agrees, 1 on mismatch/refusal, and 2 on an unreadable
or invalid top-level tool input. It neither runs Lean nor regenerates inputs.

The independent finite selection in `Test/fixtures/target/selection.json` lists the truth
programs and adapter rows. The tests compare exact program identities with the corpus,
and retain exact selected row identities, rather than relying on a count. `corpus.ts` runs the
same comparison over every well-typed program of a corpus manifest, for `make check-corpus`. It contains identities
and explicit target symbol bindings, never expected signatures. Additions/removals in the
source inventories require a reviewed selection change; selected missing entries are refused.
Expected program A/E strings and full requirement keys come from `harness/truth/corpus.json`.
The hand selection reads annotated generated exports. The corpus lane reads separate
unannotated modules so its actual columns come from initializer inference; the hand
selection alone is not that independent inference check.
Expected adapter types come from `generated/row-types.tsv`, which `tools/Tools/RowTypes.lean`
writes with `Ty.renderRaw` and each row's own `RowShape`: the tool has no type printer of its
own, and `make check-target` refuses a stale table rather than reading it.
The full `scopeKey` maps to `Scope.Scope`; a matching service code alone is insufficient.
Other requirement keys need explicit bindings before this profile can admit them.

`oracle.ts` is the diagnostic library's face: the types, the query sources, and a `query` that
runs `checker.ts`. `checker.ts` is the only thing in the repository that drives a type checker;
it runs under node because the compiler's synchronous client reads a node-internal pipe handle,
the same reason `harness/tsdiag/run-tsdiag.mjs` is node. `profile.ts` projects existing
generated metadata into its queries. `input.ts` decodes optional local query selections.
`cli.ts` is the thin driver. The compiler is the one compiler of decisions row 57, tsgo
(`@typescript/native-preview`, pinned in `ts/eff/package.json`; the oracle refuses an install
that is not the manifest's), with the package's own compiler options (and its pinned Bun type
root made explicit); imported values are never executed. The query modules are never written to
disk: the compiler reads them through its virtual filesystem callbacks, beside
`ts/eff/tsconfig.json`. Expected types and actual compiler types meet only in two ordinary
assignment statements per column. There are no assertions converting actual values to the
expected type and no private compiler assignability APIs. Type strings are display data.

A handle target binding (`Host.Resource` → `Adapter.HostResource`) is a *declaration* in the
query source — a namespace with a type member — so the expected column is the string Lean
rendered and the compiler does the binding by name resolution. Two names on one target are one
host type and are refused at the binding (DI-24, DI-76).

Queries explicitly distinguish `program`, effect-valued primitive (`effect`), and callable
primitive (`function`) claims. Only a program's error column accepts an actual type contained
in its declared bound. Answer and requirement columns, primitive errors, requests, receivers,
and nested reply payloads still require both assignments. This policy follows the query's
kind, never its ID or the presence of an Effect result. Both program producers set that kind;
an explicit local query must request it.

Each report retains expected, attempted, resolved, mismatching and refused IDs separately,
compiler diagnostics, source hashes, compiler/package versions, explicit bindings, full
requirement metadata, query kind, both assignment directions, and optional/rest parameter
information. Each checked column records `exact`, `strict-containment`, or `mismatch`;
unavailable evidence stays null. A program's strict containment retains the failed reverse
assignment diagnostic in its report. Reversed containment is a mismatch. Only the pinned
compiler's recognized assignment-incompatibility diagnostics participate in this relation;
other diagnostics still refuse the query.
A Boolean tag predicate does not establish a narrower host error type. If the core proves
an all-caught residual but the printer still emits ordinary `catchIf`, that target mismatch
remains visible; the comparison does not excuse it.
A method's actual receiver is derived from the selected indexed member type. Arguments are
projected by call shape, including the printer's one-level binary-product split — in Lean,
beside the shape it reads. Return answer, error, and requirements are separate columns. Missing fields or unbound symbols do
not become `unknown`; a non-Effect value cannot pass through `never` extraction results.

Any in compared roots, generic payloads, or local record data is refused. Unknown requires
an explicit per-column policy. Library implementation fields and adapter class internals are
opaque to this contamination walk; their generic payloads and public types still participate
in compiler assignment checks. This prevents the SQL client's internal `any` or Effect's
internal `unknown` from being misreported as an unresolved handle result. It does not certify
host implementation bodies. Single, non-generic call signatures are supported. All overloads
are listed; overloaded/generic members and rows with trailing/explicit type arguments are
refused pending an explicit instantiation model. These assignment checks are finite TypeScript
judgments, not Lean semantic theorems, runtime cause agreement, or proof of distinct Lean
service-key identity.

`assignability.ts` is the second query kind (plan 1.10): a bare pair of rendered types, both
readings of both directions (the checker's own `isTypeAssignableTo` and one ordinary assignment
statement), against `Ty.sub` on the pairs `tools/Tools/TyVectors.lean` writes. Every row is
`agree`, a named `cut`, `incomplete` (the order refuses what the target accepts) or `defect`
(the order accepts what the target refuses, which fails the lane). The committed table is
`generated/assignability.tsv`; `make gen-assignability` promotes a fresh run. Its own control
travels with the questions: each pair also carries `Ty.sub` under one swapped arm (`refOf` read
covariantly), and the lane fails if no pair catches it.

Run `bun test tools/target` for independent positive and negative controls. These tests pass
by detecting the specified failures; they do not turn a production mismatch into conformance.
One of them is the ruling itself: no file of this tree constructs a second checker
(`createProgram`, `getTypeChecker`, `transpileModule`), so "assignable" has one meaning.
Run `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tools/target/tsconfig.json`
for the tool's own type check. A reproducible command control is:

```sh
bun tools/target/cli.ts --repo . --queries Test/fixtures/target/positive.json --out .lake/target/positive.json
bun tools/target/cli.ts --repo . --queries Test/fixtures/target/negative.json --out .lake/target/negative.json
```

The first exits 0, the second exits 1. Explicit queries are reported under a separate profile;
they never replace the default repository selection. Fatal malformed inputs exit 2. Reports
contain no elapsed time or machine-local absolute paths; timing belongs in delivery receipts.
No report is a historical baseline, and no report regeneration mutates one.

The tool's positive typecheck excludes only `catch-if-predicate-bad.ts`, a deliberately
ill-typed compiler control. The oracle tests still require that file to produce a named
source refusal with `TS2769`; excluding it from the tool build does not suppress that check.
