# ST1b — root policies and atomic transactions

Version-2 roots use complete heads and generated policy bytes.
Version-1 roots retain their generations; Pin maps to pin and every other former plane maps to swap.
ST2 must connect reopened images without inventing an old transaction history.

Base: `0bb42e37d4fa99fd84979df03beb3dd0391a4e98`.
Implementation head: `79acf8fbbd74a8cee46c0dc919a8b16ff77aa959`.
The implementation and this receipt remain on `codex/seams`.
The coordinator merges; this work pushes nothing.

## Placement

`evidence/ST1b/PLACEMENT.md` records each obligation before proof work.
The registry and `docs/core/semantics.md` place nine properties under exact-codecs and R13.
Their pointers live in `src/Effect4/Store/Domain/Cas.lean`.

| Pointer | Role | Reach and hypotheses | Exclusions | Consumer |
| --- | --- | --- | --- | --- |
| `advance_stale` | compatibility | A differing complete expected head refuses before target and policy checks. | Host races and persistence. | ST4 requests. |
| `advance_duplicate` | compatibility | The identical complete target retains the exact store and generation. | Changed targets. | Retry controls and ST4. |
| `advance_head` | compatibility | An accepted changed advance installs exactly the next generation. | Duplicate targets and host publication. | ST4 root movement. |
| `journal_ff` | preservation | An accepted changed journal target reaches the previous head through designated parents. | Incidental edges and host storage. | Session and checkpoint chains. |
| `commit_grows`, `bytes_never_change` | preservation | An accepted transaction retains earlier residents and their node values. | Hash injectivity and disk durability. | ST2 and ST4. |
| `commit_reads` | compatibility | Every submitted node reads back after an accepted transaction; conflicts refuse. | Rejected transactions and host execution. | ST2 comparison. |
| `interrupted_closed` | preservation | A fully accepted transaction cut from a closed store remains closed. | Filesystem correctness and progress. | ST2 recovery. |
| `interrupted_roots` | compatibility | An accepted cut retains the old roots or the exact committed store. | Host publication atomicity. | ST2 recovery. |
| `replay_append` and staging helpers | helper | Canonical event replay composes with the accepted operation. | Arbitrary replay parameters. | Checked Cas construction and these claims. |

All nine registry pointers are proved.
No ST1b proof goal remains open.

## Acceptance and controls

| Plan row | Positive observation | Red control | Current evidence |
| --- | --- | --- | --- |
| Ordinary 1–6 | Nodes enter fresh or duplicate; a new root starts at generation one. | Repeated creation and stale expectations refuse before wrong target kinds. | `Test/Store/SeamsTransactions.lean`. |
| A→B→A | Each changed target increases the generation. | The original complete head refuses after the address returns. | Transaction fixture and native control fixture. |
| Pins | An identical target remains a duplicate. | Changed targets refuse; stale expectations refuse first. | Both fixtures. |
| Journal and fork | Designated parent chains permit advancement. | Incidental references cannot establish ancestry. A new root name creates a separate chain. | Both fixtures and checkpoint controls. |
| Atomic rollback | Validated nodes and moves publish together. | A late missing root refuses commit and every cut. | Transaction fixture. |
| Node interruption | The retained count measures fresh nodes; earlier durable nodes remain. | Duplicates consume no count. A dependent second fresh node is absent at cut one. | Transaction fixture. |
| Published interruption | The cut returns exactly the committed store. | Node cuts retain the old complete root table. | Transaction fixture and `interrupted_roots`. |
| Root bytes | Version 2 reads generated policy bytes and exact names. | Version-1 Journal byte one remains swap; case and space differences remain distinct in version 2. | Native control fixture. |
| Generated policies | Native control delegates to the Lean-produced policy table. | A disposable journal-to-swap mutation fails the actual shared-facts fixture. | Retained mutation run and production OCaml gate. |
| Rocq export | Current StoreCode compiles with the existing five-file proof group. | Value parameters refuse; the earlier generic Head and type/projection collision failures remain retained. | HeadPrinter fixture, retained failures, production Rocq run. |

Ordinary row seven belongs to ST3.
The damaged-segment and owned-writer comparisons belong to ST2.
The native checks here do not claim atomic disk transactions.

## Deleted owners and moved callers

Lean `RootKind`, `Root.version`, `nextVersion`, `putRoot`, and `putRootOr` are deleted.
Native `root_kind` is deleted.
Roots retain a fixed policy, target kind, and complete head.
The store, goldens, checkpoint publication, and root fixtures use those fields and moves.
Native control delegates policy data to the generated `E4_root_policy` module.
The legacy byte mapping remains only in the version-1 decoder.

## Corrections and controls

The plan's unconditional generation-increase wording excludes duplicates in its own ordinary row five.
`advance_head` therefore states the changed-target law; `advance_duplicate` proves exact retention.
The duplicate control prevents an unconditional increase claim.

Native root names previously folded case and rejected spaces.
Version 2 retains exact UTF-8 names within its wire capacity, matching Lean equality.
Version 1 retains its former lowercase ASCII domain.

Checkpoint roots use journal policy because their existing publication checks require predecessor ancestry.
Their designated parent occupies the canonical constructor's fourth field.
An incidental reference cannot replace that field.

The Gallina printer previously refused the polymorphic Head field.
The correction prints explicit type parameters and refuses value parameters.
The generated type name avoids the root_policy projection's existing name.
The retained failures and the HeadPrinter fixture bound this correction.

The standalone audit input stays in the receipt evidence rather than becoming a permanent battery.
The two acceptance fixtures remain reachable from `Test/All.lean`.

## Evidence limits

Lean proves the stated transaction observations at the required axiom ceiling.
Rocq retains its existing primitive and codec premises for node laws.
It proves no root, result, transaction, or crash theorem here.
Native controls provide finite host evidence.
The disk writer and reopened-image connector remain ST2 obligations.

## Proposed decisions rows

Adopt complete expected heads and generated root policies.
Keep duplicate generations unchanged and test staleness before target or policy checks.
Retain explicit version-1 root-byte mapping and exact version-2 names.
Define interrupted node counts over fresh nodes after full transaction validation.
Keep native crash observations separate from the proved model's cuts.

## Production evidence

`landed-source-paths.txt` lists every implementation path.
`landed-source-hashes.json` pins their bytes at the implementation commit.
`generated-hashes.json` verifies that production producers reproduce the reviewed output hashes.
The earlier preparation reports retain their exact scope; these production commands establish the landing.

```text
#axiom_audit: 1404 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [narrow](evidence/ST1b/narrow.json) | 0 | 7.66 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Store.Domain.Cas Effect4.Store.Domain.Word Effect4.Store.Domain.Traits Effect4.Store.Domain.Genesis Effect4.Store.Domain.Pin Effect4.Store.Domain.ProgramWire OCaml5.Tools.CasGoldens OCaml5.Tools.CasFacts OCaml5.Tools.GallinaGen Test.Store.SeamsTransactions Test.Store.SeamsHeadPrinter Test.Store.WordContract` |
| [audit](evidence/ST1b/audit.json) | 0 | 2.918 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-st1b-audit.lean` |
| [generate-cas](evidence/ST1b/generate-cas.json) | 0 | 6.363 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only cas` |
| [generate-store-rocq](evidence/ST1b/generate-store-rocq.json) | 0 | 6.452 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only store-rocq` |
| [rocq](evidence/ST1b/rocq.json) | 0 | 3.604 | `python3 /private/tmp/seams-st1b-rocq-production.py` |
| [batteries](evidence/ST1b/batteries.json) | 0 | 197.055 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=0bb42e37d4fa99fd84979df03beb3dd0391a4e98` |
| [check-ocaml](evidence/ST1b/check-ocaml.json) | 0 | 177.46 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
| [generate-semantics](evidence/ST1b/generate-semantics.json) | 0 | 386.411 | `python3 /private/tmp/seams-lean-one.py make gen-semantics` |
| [native-versions](evidence/ST1b/native-versions.json) | 0 | 0.366 | `opam exec --switch=effect4 -- sh -c 'ocamlc -version; dune --version; python3 --version'` |
| [rocq-version](evidence/ST1b/rocq-version.json) | 0 | 0.93 | `opam exec --switch=rocq -- rocq --version` |
