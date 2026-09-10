# Independent target type diagnostics

`python3 scripts/check-target.py` checks the actual printed programs and adapter members
against type metadata generated from Lean. It writes `.lake/target/report.json` and exits
0 only when every selected comparison agrees, 1 on mismatch/refusal, and 2 on an unreadable
or invalid top-level tool input. It neither runs Lean nor regenerates inputs.

The independent finite selection in `Test/fixtures/target/selection.json` lists 31 truth
programs and 11 adapter rows (8 package rows plus 3 truth Host rows). It contains identities
and explicit target symbol bindings, never expected signatures. Additions/removals in the
source inventories require a reviewed selection change; selected missing entries are refused.
Expected program A/E strings and full requirement keys come from `harness/truth/corpus.json`.
Expected adapter types come from the generated `Row` schema and package/Host row data.
The full `scopeKey` maps to `Scope.Scope`; a matching service code alone is insufficient.
Other requirement keys need explicit bindings before this profile can admit them.

`oracle.ts` is the diagnostic library. `profile.ts` projects existing generated metadata
into its queries. `input.ts` decodes optional local query selections. `cli.ts` and
`scripts/check-target.py` are thin drivers. The tool uses the repository's pinned TypeScript
compiler and compiler options (with its pinned Bun type root made explicit); imported values
are never executed. Expected types and actual compiler types meet only in two ordinary
assignment statements per column. There are no assertions converting actual values to the
expected type and no private compiler assignability APIs. Type strings are display data.

Each report retains expected, attempted, resolved, mismatching and refused IDs separately,
compiler diagnostics, source hashes, compiler/package versions, explicit bindings, full
requirement metadata, both assignment directions, and optional/rest parameter information.
A method's actual receiver is derived from the selected indexed member type. Arguments are
projected by call shape, including the printer's one-level binary-product split. Return
answer, error, and requirements are separate columns. Missing fields or unbound symbols do
not become `unknown`; a non-Effect value cannot pass through `never` extraction results.

Any in compared roots, generic payloads, or local record data is refused. Unknown requires
an explicit per-column policy. Library implementation fields and adapter class internals are
opaque to this contamination walk; their generic payloads and public types still participate
in compiler assignment checks. This prevents the SQL client's internal `any` or Effect's
internal `unknown` from being misreported as an unresolved handle result. It does not certify
host implementation bodies. Single, non-generic call signatures are supported. All overloads
are listed; overloaded/generic members and rows with trailing/explicit type arguments are
refused pending an explicit instantiation model. Mutual assignability is a finite TypeScript
judgment, not a Lean semantic theorem or proof of distinct Lean service-key identity.

Run `bun test tools/target` for independent positive and negative controls. These tests pass
by detecting the specified failures; they do not turn a production mismatch into conformance.
Run `bun ts/eff/node_modules/typescript/bin/tsc --noEmit -p tools/target/tsconfig.json` for the
tool's own type check. A reproducible command control is:

```sh
python3 scripts/check-target.py --queries Test/fixtures/target/positive.json --out .lake/target/positive.json
python3 scripts/check-target.py --queries Test/fixtures/target/negative.json --out .lake/target/negative.json
```

The first exits 0, the second exits 1. Explicit queries are reported under a separate profile;
they never replace the default repository selection. Fatal malformed inputs exit 2. Reports
contain no elapsed time or machine-local absolute paths; timing belongs in delivery receipts.
No report is a historical baseline, and no report regeneration mutates one.
