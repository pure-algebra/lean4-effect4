# Typed-context design and type signature receipt

The canonical type must gain a row; the current context type is only a handle alias.
The checked plan retains the actual merge and restoration producers.
The B6 proof must cover installation and restoration phases as well as saved frames.

Base: `6b1693e753a73410e03ea3726ae8dbe7480f56c2`.
This base merges root `b39d89388` into the clean L3 fold branch.
The commit containing this receipt is the research slice head.
Only this research folder changes; no core source changes.

## Evidence

`Signatures.lean` records the proposed reader's answer row and requirement row.
It uses existing `EffTy` columns for provision.
Its universal row-discharge proof establishes coverage under ambient and supplied key union.
Its context weakening reader uses the existing satisfaction theorem.
Finite controls show empty capture discharges no required key.
The existing address census excludes both retained CE001 sources from the proposed migration profile.
That profile is not a new program admission implementation.
Actual native equations check right-biased merge, `updateThenK`, `bodyThen` and the `restoreCtx` finalizer program.
They do not establish a whole-history context invariant.

`Signatures.ts` checks the proposed public types against Effect rc.112.
Two expected errors reject empty-context evidence and an incorrectly closed requirement row.
The callback region checks `Exclude<R, "Db">`.
The captured-empty-context replacement merges inside provision; it does not perform a raw reset.
No runtime TypeScript observation is claimed.

## Commands and results

All Lean commands use `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Test.Counterexamples.Program.ContextReset Effect4.Laws.Auto.KernelRfl` | passed, 153 jobs |
| `lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/Signatures.lean` | passed; imported-module audit 1230 declarations, zero goals and modulo goals |
| export and import audit below | passed; 1253 declarations within `[propext, Quot.sound]`, zero goals and modulo goals |
| `python3 docs/research/2026-10-11-machine-models/codex/context/check-signatures.py --truth /Users/pooks/Dev/lean4-effect4/harness/truth` | passed with Effect 4.0.0-rc.112 and tsgo 7.0.0-dev.20260629.1 |
| `git diff --check` | passed |
| `python3 scripts/check-language.py --show` over plan and receipt | no findings |

The audit exports a temporary module, so it includes every declaration of the research probe:

```sh
mkdir -p /private/tmp/context-signature-audit
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true \
  -R docs/research/2026-10-11-machine-models/codex/context \
  -o /private/tmp/context-signature-audit/Signatures.olean \
  docs/research/2026-10-11-machine-models/codex/context/Signatures.lean
LEAN_PATH=/private/tmp/context-signature-audit LEAN_NUM_THREADS=3 lake env lean \
  -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/Audit.lean
```

`PLAN.md` places reader, region, B6 and parameter-transformer obligations before implementation.
It records exact constructor/tag retirement and generated, LCNF, OCaml and target migration.
It proposes the next file partition without editing those files.
The ordinary proof declarations serve the proposed provide-context-row and typed-context-read claims.
No new planned goal or private evaluator pass enters the tree.
No source lines are removed in this design slice.
The source repair, dynamic B6 invariant, transformer inference and behaviour sweep remain open.
No push occurs.
