# Every check and test, with a verdict (2026-09-13)

Companion to `2026-09-13-ci-refactor-proposals.md`. That note said how to run checks; this
one says which checks are worth running. Facts come from a read of every script header, test
file docstring, and the git history of real catches at `259d00d`; the verdicts are mine, for
the owner to accept or overrule.

## 1. How each one was judged

A check earns its place by protecting one of these, and by having no cheaper check that
protects the same thing:

- **Lean core**: the constructs, the checker, the runtime, the proofs. Protected by the build,
  the axiom audit, and the Lean batteries. The cheapest checks in the repository, because Lake
  rebuilds only what changed.
- **Projections are faithful**: the OCaml and TypeScript files Lean generates are what Lean
  says. Protected by regenerate-and-diff.
- **The printed language means what the real runtime does**: the printed programs run the
  same on Effect rc.112 (truth) and type the same under the TypeScript compiler (T0). The
  only outside oracles the repository has.
- **The OCaml engine agrees with Lean on bytes and exits**: the differentials over Lean-cut
  goldens. A genuine independent implementation of the wire format.
- **Tools built on the language** (the foreign-code readers, the ingest census, the streams
  census, the schema host harnesses): worth testing, but not on every change to the language.

Against that: runtime, what a construct change forces someone to edit by hand, and whether it
duplicates another check. A check that is red by declaration for weeks, or that tests a hand
copy of Lean code, counts as confusion.

Tiers used below. **Every change**: runs with the build, target under five minutes after it.
**Per slice**: the host oracles, a few minutes more. **On its inputs**: a Make prerequisite
runs it only when the files it reads change (vendored sources, the schema modules, a checker
script). **Nightly**: the long censuses. **Drop** and **merge** as written.

## 2. The eighteen sweep checks

| check | protects | catch on record | s | verdict | why |
| --- | --- | --- | --- | --- | --- |
| generated-stale | provenance labels on 615 generated files | none; its only red is the declared LCNF one | 1 | **merge** into one drift check | with real Make rules and `git diff --exit-code` the label concept goes; the LCNF red goes with item 16 |
| library-roots | every module reachable from a root, `Effect4` never imports the proofs, the axiom ceiling over 52,590 declarations | yes: the closure walk found 26 unreachable modules and three collisions (`f42162c`) | 24 | **keep, every change**, minus its second elaboration | `lake build Test` already runs the axiom audit; the script elaborates `Test/All.lean` a second time. Keep the orphan walk, drop the repeat |
| source-citations | every cited path exists | yes: DI-51 found two dangling citations | 1 | **keep, every change** | one second, real catches |
| internal-citations | no line-numbered citation into seven mutable docs | none by the gate | 78 | **merge** into the citation scanner above | same tokens, second regex, 78 seconds for a text scan; one pass does both in about two |
| effect-runtime-census | the 137-row behaviour census still matches the vendored rc.112 sources; the coverage rows in `RuntimeCoverage.lean` line up | none | 10 | **keep, on its inputs** (`vendor/`, `RuntimeCoverage.lean`) | its inputs are pinned files; on any other change it cannot fail |
| ts-eff | seven generated TypeScript tables are byte-equal to Lean's | none | 35 | **merge** into the drift check | `check-generated.sh` already compares the same seven files |
| conform `cases` | no catch-all `match` arm on a core type without a declared cover | (the rule's value is in what it prevents) | in 28 | **keep, every change**, as a site attribute | see the proposals note; the JSON edit goes, the rule stays |
| conform `native` | the compiler's own memory layout of every core type is covered, injective, coherent | yes: found `decodeAt` missing its `bigintK` arm (`137afdd`) | in 28 | **keep, every change** | cheap, real catch, protects the wire |
| conform `types` | six `Ty` examples normalize to a fixed point; three laws exist by name | none | in 28 | **drop as a gate** | the laws are theorems the build checks; the examples belong in `TypeAlgebraContract` as guards |
| conform `models` | 28 proved laws exist by name; value-model plans resolve | none | in 28 | **out of the per-change lane** | `lake build Conform` fails if a named theorem vanishes; the report is documentation |
| generated | regenerate the derived Lean, specs, OCaml files and goldens, wire and CAS goldens, TypeScript tables; compare bytes | none recorded | (regenerates six groups) | **keep, every change**, as `make check-gen` | this is the projection-faithfulness check; it absorbs items 1 and 6 |
| schema-typescript | three Lean-emitted Schema documents compile under TypeScript 7 and tsgo and revive on rc.112 | none | 48 | **on its inputs** (`src/Effect4/Schema`, the three fixtures); decide DI-08 first | depends on a sibling checkout; nothing about `Eff` changes it |
| schema-codec | 17 `Ty` encodings agree with rc.112's `Schema.toCodecJson` and round-trip on the host | none | 3 | **keep, per slice** | three seconds, and `Ty` is what the freeze is about |
| ts-eff-corpus | the TypeScript reader reproduces Lean's JSON for 408 printed programs; 295 bun tests | yes: the printed-module type check found `pKv.ts` declaring a wrong error type for months | 10 | **keep, every change**, minus its truth-module type check | the reader is the TypeScript face of the language; the type check of truth modules is also done by `truth` |
| ingest | two foreign-TypeScript readers agree with each other and Lean over 408 printed and 22,986 constructed modules, six rewrites, an OCaml decode of 23,394 programs | a design finding (DI-37), no code defect | 486 | **split**: the 408 printed programs, both readers, the bun tests and the README check per slice (about a minute); the 22,986-module census, the rewrites and the OCaml decode **nightly** | it tests a tool built on the language; a Lean change rarely reaches it, and the smoke half catches what would |
| host-protocol | the keyed session protocol: 57 recorded rc.112 runs replay in Lean, 29 negative controls | none since landing | 68 | **on its inputs** (`Api`, `HostSession`, `HostProtocol`, the session harness); nightly otherwise | it is the oracle of the P4 lane and must be green there; it cannot change from a typing edit |
| truth | 34 printed programs exit and schedule as rc.112 does; the printed modules type-check | yes: the lane's first runs found `pScope` disagreeing on everything and an ill-typed `pLoop`; `8e6988e` corrected a sqlite error row | 72 | **keep, per slice**; its deterministic halves into `make gen` | the outside oracle for the language's meaning; one gap: no timer program (`pSleep` exists only in the OCaml corpus) |
| streams | 799 documentation examples of the vendored rc.112 stream modules still produce their documented output | none | 6 (cached) | **on its inputs** (`vendor/`) | a self-consistency check of the pinned host; no Lean claim, by its own docs |
| gen-check | the LCNF-generated OCaml builds; `gen_check.ml` compares the generated machine dispatcher against a hand copy of the archived avatar | none | 18 | **drop `gen_check.ml` and its avatar copy; regenerate the two frozen LCNF files; fold the "engine builds, prelude verbatim" steps into engine-tests** | this file is the sole reason a gate has been red by declaration for weeks; it tests against something the repository archived |
| dune-tests | the 48 Lean-cut goldens decode, re-encode, print and type in OCaml; the wire kernel; the hand-written typing mirror | drift only (the atom-count pin) | 5 | **keep the differentials, drop the mirror tests** (§4) | the golden byte round trips are a real second implementation; the typing tests test a hand copy |
| engine-tests | the OCaml engine runs the 48 goldens, the truth corpus and 500 generated programs identically on three engines; CAS bytes and control against Lean's cut; the engine's own store tests | yes: the engine refused every load when the wire gained the timer rows | 8 | **keep, per slice** | true differentials; the OCaml-only store tests are the engine product's own unit tests and stay in the OCaml lane |

## 3. Off the sweep today

| check | protects | verdict | why |
| --- | --- | --- | --- |
| `check-compatibility.py` | the constructor shapes of every stored type against a saved snapshot | **add, every change**, with a re-promoted snapshot | the freeze has no teeth without it; the snapshot still lists `choose` |
| `check-target.py` (T0 over 45 programs) | the printed programs' answer, error and requirement types agree with the TypeScript compiler | **add, per slice** | the typing oracle of the language; today it runs only when someone remembers |
| conform `compiler` | Lean-emitted OCaml for `normalize` and friends agrees with Lean on a fixture list | **keep, OCaml lane** | this is the generated direction, and it replaces the hand mirror's normalization test |
| conform `layouts` | inspection of four layout targets with retained counterexamples | **manual**, unchanged | an inspection profile by its own README |
| `check-known-red.sh` | the declared-red list | **keep the mechanism, aim for an empty list** | consolidate its four readers into one |
| `check-schema-annotations`, `-effectful-field`, `-payload-surface`, `-structural-assurance` | the Schema slice's host harnesses and its 2,682-line assurance projection | **on its inputs** (`src/Effect4/Schema`); un-defer or drop the assurance projection | an owner-deferred stamp that refuses its own fingerprint is permanent confusion; DI-08 decides whether the slice is in the release at all |
| `check-schema-census`, `check-schema-fields` | the 22 tag spellings and field order of the pinned rc.112 schema source | **on its inputs** (`vendor/`) | cannot change otherwise |
| `report-effect-runtime-coverage.sh` | a report | unchanged | not a check |
| `test-trust-gate.sh` (CI, 105 s every run) | the axiom audit rejects eleven planted defects | **on its inputs** (`AxiomGate.lean`, the trust fixtures, the script) | it tests the checker, not the language |
| the other twelve `test-*` self-tests | each tests one checker script | **on its inputs** (the script it tests) | none belongs in the per-change lane; several are run by nobody today, which "on its inputs" fixes |

## 4. The OCaml tests, file by file

| file | checks | kind | verdict |
| --- | --- | --- | --- |
| `test_eff.ml` golden section | 48 Lean-cut programs decode, re-encode, print in OCaml | Lean-vs-OCaml differential | **keep** |
| `test_eff.ml` typing and GADT sections, constructor and atom pins | the hand-written `eff_typing.ml` types the goldens as Lean did; `eff_typed` embeds them; pins transcribed by hand from Lean | hand copy | **drop with the mirror**; the pins become a Lean-generated expected file |
| `test_lean_wire.ml` | Lean's eight wire goldens decode exactly and re-encode byte for byte | differential, independent encoder | **keep** |
| `test_metadata.ml` | Lean metadata bytes decode and re-encode | differential | **keep** |
| `test_val_frames.ml` | the `ref` and `handle` frames | hand-derived goldens | **keep**; generate the goldens from Lean |
| `prop_wire.ml` | five wire properties over 400 random programs | OCaml-only, cheap | **keep** |
| `test_scoped_typing.ml`, `test_error_typing.ml`, `test_native_queries.ml`, `test_type_normalization.ml` (864 controls) | re-derive DI-63, DI-62, the native query typing and DI-53 normalization by hand in OCaml | hand copy of Lean rules | **drop with the mirror**; the conform `compiler` profile keeps the generated normalization check |
| `gen/gen_check.ml`, `gen/api_check.ml` | the generated machine dispatcher against the archived avatar's hand copy; a three-program smoke | hand copy of an archived thing | **drop `gen_check`**, keep the smoke |
| engine `test_engine`, `test_diff`, `test_query`; cas `test_bytes`, `test_cas`, `test_control`, `test_cache` | Lean-cut goldens through three engines; CAS bytes, control and cache slices against Lean's cut | differential | **keep** |
| engine `test_host`, `test_math`, `test_buckets`, `test_due`, `test_wake`, `test_whatwg`, `test_timers`, `test_sched`, `test_log`, `test_replay_steps`, the `prop_*` files; cas `test_wal`, `test_pack`, `test_crash`, `test_index`, `test_checkpoint` | the OCaml engine's own components against list twins transcribed by hand from Lean | product unit tests | **keep in the OCaml lane**; the hand-transcribed twins become Lean-generated expected files |

Net: `eff_typing.ml` (654 lines), `eff_typed.ml/.mli` (916), `gen_check.ml` (306) and four test files go; every remaining OCaml test either consumes bytes Lean cut or tests OCaml code that is a product in its own right.

## 5. The TypeScript tests

| surface | verdict | why |
| --- | --- | --- |
| `ts/eff/test/*` (metadata, read, tables, wire: 4 files) | **keep, every change** inside `ts-eff-corpus` | the reader against Lean's bytes |
| `ts/eff/ingest/test/*` (14 files) | **keep, per slice**, run once (today both `ingest` and `ts-eff-corpus` run the whole `bun test`) | the foreign readers' own tests |
| `ts/eff/check.ts` | **keep** | the JSON oracle of the reader |
| `harness/truth/*.test.ts` (prelude inventory, catch-if, native queries) | **keep, per slice** with truth | the prelude inventory is what tells you a new atom needs a host definition |
| `harness/truth/session/*` tests (26) | **on its inputs** with host-protocol | |
| `tools/target` tests (3) | **per slice** with T0 | |
| `harness/schema-*` | **on its inputs**, after DI-08 | |

## 6. The Lean test tree

Everything under `Test/` is a must-compile battery, rebuilt only when its imports change,
and it is the cheapest checking the repository has. Keep it whole, with five adjustments.

| item | verdict | why |
| --- | --- | --- |
| the 34 `*AxiomReport.lean` files, 1,706 `#print axioms` lines | **replace** with one generated manifest `generated/axioms.tsv` (theorem, axioms) that the drift check compares | nothing compares the printed lines today; the whole-tree audit already enforces the ceiling; every theorem rename touches a report |
| `Test/Audit/RuntimeCoverage.lean`, 7,379 lines | **keep the 137-row census; generate the 625 statement snapshots** or drop them | the snapshots re-transcribe `#check` lines that the contract batteries already freeze (`CauseExitContract` and `RuntimeCoverage` hold the same statements twice) |
| the 170 numeric pins (`wellTypedCount = 129`, `totalNodes = 1993`, `runs = 160384`, …) | **move** to an expected file per battery; keep the property guards | DI-60's report becomes the diff; no rebuild to accept a count |
| `Test/Program/LayerSharingContract.lean` (106 s to build, kernel-checked certificates) | **keep**, but flag it | more build time than every other test module combined; if it slows the layer lane, it moves to the nightly build root |
| `Test/Machine/Fuzz.lean` (160,384 replays per build) | **keep** | it found and closed a real scope defect the day it landed (S1-1) |
| `Test/Counterexamples/REGISTER.md` (398 rows: 331 seeded with no executable witness on `main`, 21 pinned, 20 reserved, 8 moved, 2 retired) | **generate** the register from the executable refusal files (`tests/refuse/`), and move the seeded and moved rows to a history document | the table is history maintained by hand; the 21 executable rows are the tests |
| `Test/contracts/`: `machine-completion`, `machine-scheduling`, `schema-authoring`, `schema-typescript-generation` (no references) and `schema-codec` (unlinked from its gate) | **archive** the four; link or archive the fifth | |
| the 13 retired `archive/surface-*` packets | already archived; leave | |

## 7. Overlaps removed by the verdicts above

- The seven TypeScript tables: compared by `ts-eff` and by `generated`. One drift check.
- The truth modules' type check: `check-truth.py` and `check-ts-eff-corpus.sh`. Once.
- Citations: two scanners over the same tokens. One.
- The axiom ceiling: the whole-tree audit, 34 report files, and a second elaboration in
  `library-roots`. The audit plus a generated manifest.
- The `Gen.lean` corpus printed twice (`ts-eff-corpus` and `ingest`). Once, shared.
- `bun test` run twice. Once.
- The known-red list read by four programs. One reader.
- The typing rules stated in Lean (`effTy`), Lean (`HasTy`, proved equal), OCaml by hand
  (`eff_typing.ml`), OCaml by hand again (`eff_typed`), and checked against TypeScript (T0).
  Two Lean statements proved equal, plus the outside oracle.

## 8. What the lanes look like afterwards

**Every change** (`make check`): the build with the axiom audit; the orphan walk; the drift
check over every generated group; the catch-all attribute check; the native layout check;
the compatibility snapshot; the citation scan; the TypeScript reader over the 408 printed
programs with its bun tests. About three to four minutes after the build, most of it the
regeneration.

**Per slice** (`make check-host`): truth (72 s); T0 (about a minute); schema-codec (3 s);
the OCaml differentials and engine tests (13 s); the ingest smoke (about a minute). About
three minutes more.

**On its inputs** (Make prerequisites, otherwise skipped): host-protocol; the runtime census
and the streams census on a vendor re-pin; the schema harnesses on a schema change; every
checker self-test on its checker.

**Nightly** (`make check-full`): the full ingest census; everything above regardless of
inputs; a no-cache proof replay weekly.

**Gone**: the label files and their stamp check, the second citation scanner, the second
elaboration, conform `types`, the hand-written OCaml checker and its five test files,
`gen_check.ml`, the 34 axiom reports, the hand-maintained register and count pins, the
declared-red entry, and the duplicate runs.

## 9. Decisions this asks of the owner

1. Retire the hand-written OCaml checker and its tests (§4); the wire differentials stay.
2. Drop `gen_check.ml` and regenerate the two frozen LCNF files, clearing the declared red.
3. DI-08: is the Schema slice in the release? Its six host harnesses and the deferred
   assurance projection follow that answer.
4. The ingest census to nightly, with a one-minute smoke per slice.
5. Replace the 34 axiom report files with a generated manifest.
6. Add a timer program to the truth corpus (the only construct family with no host oracle).
