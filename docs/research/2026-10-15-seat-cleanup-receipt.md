# 2026-10-15 seat CLEANUP receipt: P0 of the interop plan, and the census of gates and graft

**The one thing to know before merging:** S3 lands as one commit, but no route gate ran on it.
The wind-down stopped `check-compiler`, `check-native` and `check-ocaml` in the slot's queue, so
they are yours at the merge. Each byte S3 moves in the nine regenerated OCaml files is layout:
the parse trees are equal once locations are removed (tested, with four controls). S4 was not
started: nothing is cut, and the `Makefile` is unchanged. `check-native`'s marker still omits 11
files of its driver's import closure, 8 of them under `src/OCaml5`.

## Base and head

Branch `claude/cleanup` in `/Users/pooks/Dev/lean4-effect4-cleanup`. The brief's base is
`439155600` (the brief's commit on `28abb73c6`). The coordinator merged S1 and S2 into
`refactor/phase1-phase3` at `68765c384`, and this branch fast-forwarded to it. S3 is one commit on
`68765c384`; this receipt is the next one. The handback names both hashes.

## Changed files

### S1 (`5b1180aae`)

- `src/OCaml5/Lcnf/Types.lean`: `finiteIndexIn`, `ParamSlot`, `familyIndex?`,
  `typeParameterSlots` (it replaces `typeParameterIndices`), `typeParameterWidth`, `ParamVars`;
  `kernelTy` and `typeInfo?` read a family parameter as one OCaml parameter per constructor.
- `src/OCaml5/Lcnf/Translate.lean`: `monoTy` and `tyOfInd` spell a family's parameters as
  anonymous types.
- `src/OCaml5/Lcnf/TypeRows.lean`: a docstring names `typeParameterSlots`.
- `tools/Conform/Effect4/CompilerControls.lean`: the parameter rule's controls move to
  `typeParameterSlots`; F3's controls join them.

### S2 (`ea5371129`)

- `src/OCaml5/Lcnf/ClockFlow.lean`: `Flow.paramTypes`; the `ingress` origin; `Context` (the mono
  index and the reactor template); `isReactorType`; `globalArity` reads the mono declaration; the
  fact bound counts the new origin.
- `src/OCaml5/Lcnf/Translate.lean`: `reactorMonoType?` and `clockContext`, passed to both calls
  of `ClockFlow.refusals`.
- `Test/Audit/ClockLiteralFixtures.lean`, `Test/Audit/ClockLowering.lean`: six fixtures and their
  controls.
- `ocaml/engine/e4_engine.ml`, `ocaml/engine/e4_engine.mli`: `check_answer` (EN9).
- `ocaml/engine/test/test_engine.ml`: `answer_ingress_check`.

### S3 (the commit after `68765c384`)

- `src/OCaml5/Ml/Syntax.lean`: the forms `Ty.labelled`, `Pat.int`, `Expr.fnMatch`, `Expr.seq`,
  `Expr.letPat`, `Expr.ifUnit`, `Expr.commented`, `Expr.pack`, `TypeDecl.isPrivate`, `SigItem`,
  `Decl.openD` and `Decl.moduleTypeD`; `Expr.raw` is removed.
- `src/OCaml5/Ml/Fold.lean`: regenerated (`python3 scripts/generate.py --only derived`, the group
  `MlFold`).
- `src/OCaml5/Ml/Render.lean`: the new forms, each with a `#guard`; an application in the head of
  an application prints in its parentheses (`(f x) y`), so the print parses back to its tree.
- `src/OCaml5/Ml/Check.lean`: `Interface` and `Env.withInterface` (an `open` reads as the opened
  unit's scope); patterns are checked (`checkPat`), and so are signatures (`checkSigItems`); the
  codes `unbound-module`, `unbound-module-type`, `duplicate-module-type` and `private-abstract`;
  a `rawD` opens the scope of the structure that holds it, and no other scope.
- `src/OCaml5/Lcnf/Builtins.lean`: `preludePrimitives`, the three primitives as structured
  bindings (they replace `rawPrimitives`); the fragment rule refuses each new form.
- `src/OCaml5/Lcnf/Externs.lean`: `carrierSignatures`, the seven carrier signatures as module
  types (`List Ml.Decl`).
- `src/OCaml5/Lcnf/Gen.lean`: the structured `open`; the opened unit's interface is handed to
  `Ml.checkModule`; `generateInFull` in place of the renaming loop.
- `src/OCaml5/Lcnf/Types.lean`: `generateInFull`, the renaming loop that `Gen` and `EffGen` share.
- `src/OCaml5/Eff/Emit.lean`: rewritten over `OCaml5.Ml` (527 lines at the base, 627 now); each
  `eff/` file is an `Ml.Module`.
- `src/OCaml5/Tools/EffGen.lean`: it checks every module with the interface of `Eff_types`, then
  renders it.
- `tools/Conform/Effect4/LcnfMl.lean`: the target evaluator reads `Pat.int` and
  `Expr.commented`, and refuses the other new forms by name.
- `tools/Conform/Effect4/CompilerControls.lean`: a control's support body is `.seq` in place of
  verbatim text.
- `ocaml/README.md`: the rows `Ml/*` and `Eff/*`.
- Regenerated: `ocaml/eff/eff_{ctors,wire,json,native,subterm,layout}.ml`, `ocaml/gen/api_gen.ml`,
  `ocaml/engine/api_engine.ml`.

One production `Decl.rawD` remains: the engine's hand prelude (`Gen.lean`, `--prelude
ocaml/engine/tools/api_engine_prelude.ml`). It is hand OCaml until the carriers are Lean data
(LC-8). No `Expr.raw` remains: the constructor is gone.

### The receipt's commit

- This receipt.
- `docs/research/2026-10-15-seat-cleanup-wind-down/`: `compare.sh` (the parse-tree comparison) with
  its controls; `reach.py` (the reach census) with its two outputs; `probes/`, the S1 and S2 probe
  scripts and logs; `s3-logs/`, S3's build scripts and logs. The probes ran in this worktree, and
  their paths name it.

## Commands and results

Every Lean command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. A probe or
log cited below as `scratch/probe/…` or `scratch/s3/…` is copied into
`docs/research/2026-10-15-seat-cleanup-wind-down/` (`probes/`, `s3-logs/`).

### S1

| Command | Result |
| --- | --- |
| `lake build OCaml5` (restore, at the base) | 135 jobs, from the cache |
| `lake build Test.Dogfood.Scenario.Todo.Host` (the probe's input) | 1,198 jobs, from the cache |
| `scratch/probe/run-host-probe.sh` at the base | closure 1,330; 0 todos; 4 clock refusals; 82 fields not spelled: 68 of `EffAlgebra`, 10 of `TermAlgebra`, 4 of `CauseTermAlgebra` |
| `lake env lean --run scratch/probe/AlgReach.lean` (roots as the probe's) | the algebras are reached by the folds `cata_*`, `EffAlgebra.id`, `EffAlgebra.onRef`, `expandAlgebra`, `TermRefusal.algebra` and `causeAlgebra`; `ArgF` and `superAlg` are not in the closure |
| `lake build OCaml5`, after the edit | PASS, 135 jobs |
| `lake build Conform`, after the edit | PASS, 354 jobs; every F3 control holds |
| `scratch/probe/run-host-probe.sh`, after the edit | `field types not spelled: #[]`; the 4 clock refusals remain |
| `python3 scripts/generate.py --only lcnf` | PASS; `git status` shows no generated file changed |
| `make -o build check-compiler` | `conform compiler: PASS, exit 0` |
| `make -o build check-native` | `conform native: PASS, exit 0` |
| `make -o build check-ocaml` | exit 0; `gen-check: PASS`; its chain re-ran the corpus, `fixtures`, `variances`, `derived` and `lcnf`, and no committed file changed |

### S2

| Command | Result |
| --- | --- |
| `lake env lean --run scratch/probe/ClockDebug.lean` (an instrumented copy of the base's `ClockFlow`) on the probe's roots | 89 local calls are unknown production; none is the reactor call in `Run.driveFrom`. 82 are the `op` of the program folds `foldMapAt_*` and `foldMap_*`, 6 are instance parameters, 1 is a pair's field in `namedHasTy` |
| `lake env lean --run scratch/probe/Dump2.lean Effect4.Program.Node.addresses._redArg` | the folds' `op` is `List.appendTR._redArg`, a builtin twin with no kernel constant |
| the same copy with each global's arity read off its mono declaration | the probe's refusals are `#[]`; one unknown call remains (`namedHasTy`) and it reaches no clock |
| `lake build OCaml5`, after the edit | PASS, 135 jobs |
| `scratch/probe/run-host-probe.sh`, after the edit | `clock refusals (0)`, `field types not spelled: #[]`, `Ml.checkModule: PASS`, `name hygiene: PASS`; wrote `scratch/probe/todo_host.ml` (26,784 lines) |
| `scratch/probe/run-runwith-probe.sh` (root `Effect4.Run.runWith`, its reactor a root parameter) | `clock refusals (0)`; without the ingress rule (the scratch copy) the reactor call in `driveFrom._redArg` refuses |
| `lake build Test.Audit.ClockLowering` | PASS, 148 jobs: every old clock control and the six new ones |
| `lake env lean --run scratch/probe/ClockDiff2.lean` (the base's analysis against the library's) | the 23 root sets of `ClockDiff` AGREE; of the 6 new roots, the two green controls DIFFER as designed (refused at the base, admitted now) and the four red ones AGREE |
| `lake build Conform Test.Audit.LetReturn` | PASS, 355 jobs |
| `opam exec --switch=effect4 -- dune build engine`, then `_build/default/engine/test/test_engine.exe` | `ALL PASS: 0 failure(s) in 175 checks`, 16 of them `answer_ingress_check` |
| `python3 scripts/generate.py --only lcnf` | PASS; no generated file changed; the three artifacts report `clock refusals (0)` |
| `make -o build check-compiler` | `conform compiler: PASS, exit 0` |
| `make -o build check-native` | skipped by its marker (its inputs omit `src/OCaml5`, which its driver imports); `make -B -o build check-native`: `conform native: PASS, exit 0` |

A finite probe beyond the gates (tested, scratch only): `ocamlopt` on `scratch/probe/todo_host.ml`
against copies of `eff_types.ml` and `E4_clock`. It stops at three gaps outside F3 and the
clock boundary, each patched in the scratch copy only to reach the next (`probes/compile/`):
1. `Char.ofNat` builds `UInt32.ofBitVec 0` as a record `{ to_bit_vec = … } : uint32`; the type
   rows spell `UInt32` as `int`.
2. A `String` is built as a record `{ to_byte_array = … } : string_`; the rows spell `String` as
   `string`.
3. `Node.addresses` passes one lambda, applied to `()` for an erased type, at seven types;
   OCaml's value restriction refuses it (`'a eff` against `'a stmt`).
These are two of 729 record constructions, and one shared polymorphic closure. Later errors are
not measured.

### S3

In the order they ran:

| Command | Result |
| --- | --- |
| `lake build OCaml5`, after the emitter's rewrite | PASS, 135 jobs |
| `python3 scripts/generate.py --only eff`, first run | FAIL: `EffGen: pBind uses OCaml5.Eff.bind, not a constructor of the closed world`. The emitter's public helper `bind` captured the corpus's double-backtick name `` ``bind ``; the four helpers became private, and `lake build OCaml5` passed again |
| `python3 scripts/generate.py --only eff` | PASS: 31 families, 89 corpus programs; the goldens and `eff_manifest.txt` unchanged |
| `lake build OCaml5 Conform Test.Audit.ClockLowering Test.Audit.LetReturn Drivers.Corpus Drivers.ForeignCorpus Drivers.ProgramStructureCheck Drivers.Styles Drivers.TsGen` (every direct dependent) | PASS, 790 jobs, 21.67 s |
| `lake env lean Test/fixtures/ty-rule/CensusMirrorsOCaml5.lean`, then `…/CensusMirrorsConformLcnfMl.lean`, after `lake build Effect4.Laws.Auto.Traversals Effect4.Laws.Auto.Exhaustive` | exit 0 each (11.3 s, 11.1 s). Under `OCaml5`: 2 structural rows, `OCaml5.Eff.tyO` and `OCaml5.Eff.tyV`; under `Conform`: 1, `Conform.Effect4.LcnfMl.tyT` |
| `python3 scripts/generate.py --only lcnf`, first run | FAIL on `ocaml/engine/api_engine.ml`: `Ml.checkModule (fatal): 222 diagnostic(s)`, each an `unbound-value` of a `sh_*` name of the hand prelude. The cause is below |
| `lake build OCaml5`, after the checker's scope rule | PASS, 135 jobs, 14.24 s |
| `python3 scripts/generate.py --only lcnf` | PASS, 17.91 s; each of the three artifacts `Ml.checkModule: PASS (0 diagnostics)`; `eff_types.ml` and the closure manifests unchanged |
| `python3 scripts/generate.py --only eff` | PASS, 3.82 s; the goldens and `eff_manifest.txt` unchanged |
| `compare.sh` over the nine regenerated files | for each file, the same parse tree and the same comments (table below) |
| `compare.sh --pair` on its four controls (`controls/`) | a nested application, a changed comment and a parse failure each refuse; a layout change passes |
| the same `lake build` of every direct dependent, after the scope rule | (written at the commit; see the wind-down handoff) |
| `make -o build check-docs` | 0.61 s; FAIL with one finding outside this seat's edits: `docs/core/decisions.md:494` cites `tools/view/make_videos.py`, the owner's untracked file in the main checkout. `ocaml/README.md` has no finding |
| `make -o build check-compiler`, `check-native`, `check-ocaml` | not run: stopped in the slot's queue at the wind-down |

`compare.sh` parses the committed file and the regenerated one with `ocamlc -stop-after parsing
-dparsetree`, removes every source location and compares the two trees. It compares the comments,
which the parser drops, as ordered lists. `COMPARE_BASE=68765c384` compares against the merge.

| File | Structure items | Lines moved | What moved |
| --- | --- | --- | --- |
| `ocaml/eff/eff_types.ml` | 2 | none | nothing |
| `ocaml/gen/api_gen.ml` | 873 | +2 −1 | the prelude's `let b = … in` breaks its line |
| `ocaml/engine/api_engine.ml` | 10 | +41 −33 | the signatures' `val` lines lose their aligned columns; a blank line follows each module type; the prelude's `let … in` |
| `ocaml/eff/eff_ctors.ml` | 158 | +1096 −865 | the printer's layout: a binding's body on its own line, a blank line between items, `function` arms indented |
| `ocaml/eff/eff_wire.ml` | 116 | +1060 −1381 | the same |
| `ocaml/eff/eff_json.ml` | 56 | +260 −200 | the same |
| `ocaml/eff/eff_native.ml` | 8 | +22 −30 | the same |
| `ocaml/eff/eff_subterm.ml` | 12 | +232 −283 | the same |
| `ocaml/eff/eff_layout.ml` | 2 | +8 −58 | the same |

The `open` line is the same bytes in every file: `Decl.openD` prints what the verbatim `open`
printed. No committed byte moved for the parenthesized application head: no regenerated file
holds an application in the head of an application. The builtin guard of an over-applied
`Prod.fst` now reads `(fst p) x`.

**The cause of the first lcnf failure.** At the base the `open` line of `api_gen.ml` and
`api_engine.ml` was a verbatim item, and so were the engine's carrier signatures. A top-level
verbatim item opened the value scope of the whole module, so no value name of either module was
checked. Structured, they leave one verbatim item, the hand prelude inside the engine's functor
`Make`. The rule opened the scope only for a top-level item, so the prelude's names went unseen.
Now a `rawD` opens the scope of the structure that holds it, and no other (`checkDeclAlg`; a
control in `Check.lean`). So `api_gen.ml` is checked whole for the first time (873 structure
items, 0 diagnostics), the top level of `api_engine.ml` is checked, and the body of `Make` stays
open until the prelude is Lean data (LC-8).

## S4: not started

The wind-down came before any S4 edit. Nothing is cut and no `Makefile` line moved. What follows
is what the seat read and measured before the stop. Every verdict is a proposal.

Reach is measured by `docs/research/2026-10-15-seat-cleanup-wind-down/reach.py` (K4's method):
a runner is a library root, `Test/All.lean`, `Test/Slow.lean`, a `lean_exe` root, or a Lean file
that the `Makefile`, a script, CI, a host program or an authority document names. Its outputs
are `reach-tools.txt` (`tools/` and `src/OCaml5`) and `reach-hosts.txt` (`harness/`, `apps/`,
`ocaml/`). A time names its source; "not run here" marks a gate this seat did not run.

### The `make` targets

| Target | What it checks | The fault it catches | Time | Also caught by | Proposal |
| --- | --- | --- | --- | --- | --- |
| `check` (`build`) | the core and the law graph build | a broken proof or definition | not run here | none | keep (the proofs) |
| `check-roots` | `lake build Test`, then `Test/All.lean` elaborated | an unreachable battery, a source no root reaches, an axiom past `[propext, Quot.sound]` | not run here | none | keep (the three gates) |
| `check-native` | the native profile: Lean's native layout of the reflected values | a value whose native layout differs from the conformance model | passed on S1 and S2 (unmeasured) | none | keep; fix its marker (open item 1) |
| `check-compiler` | the compiler checkpoint: the route's OCaml for normalization, compiled and run, with three mutations | a lowered definition or a builtin row that answers other than Lean on the fixtures | passed on S1 and S2 (unmeasured) | the OCaml lane's differential, in part | keep (`check-full`) |
| `check-ocaml` | `dune build`, `dune test eff gen clock`, `dune test engine`, `gen-check.sh` | a codec that disagrees with Lean's bytes; an engine that disagrees with the generated one; a seam with a hole | 29.4 s with no input changed, 368.4 s with the reruns (state note §2) | none for the three-engine differential | keep (`check-full`) |
| `check-schema-codec` | Lean's `Ty.encode` and Schema code against rc.112's `Schema.toCodecJson` | a codec value rc.112 decodes otherwise | not run here | none | keep (outside oracle) |
| `check-schema-ts` | Schema TypeScript generation on the pinned host | generated Schema code the pinned compiler or runtime refuses | not run here | none | keep (outside oracle) |
| `check-truth` | Lean's exits against rc.112's over the program corpus | a meaning that differs from the Effect runtime | 17 s (`d3b702102`) | none | keep (outside oracle) |
| `check-target` | the printed programs' types under tsgo 7 | a printed type tsgo infers otherwise | not run here | none | keep (outside oracle) |
| `check-ts-reader` | the TypeScript reader against Lean's reader on the corpus | a TypeScript reading that differs from Lean's | not run here | none | keep (outside oracle) |
| `check-host-protocol` | the keyed lane, the scenarios' scripts, the to-do service and application | a host session that differs from the Effect runtime's | not run here | none | keep (outside oracle) |
| `check-corpus` | the generated corpus on rc.112: exits, schedules, types | a corpus program whose run or type differs | 63 s (`d3b702102`) | none | keep (outside oracle) |
| `check-tsdiag` | the corpus under tsgo against the checker's refusals | a program this checker types that tsgo refuses | not run here | none | keep (outside oracle) |
| `check-ingest-smoke` | the printed corpus through the ingest's printed contract | a printed module the ingest reads otherwise | not run here | `check-ingest` | keep (`check-full`) |
| `check-ingest` | the ingest census: foreign corpus, both recognizers, OCaml decode | a foreign program the recognizers or the decoder read otherwise | about 8 min (its script's header) | none | keep (a sweep) |
| `check-truth-release` | the truth lane on `effect@4.0.1` against the build ledger | a meaning that differs on the release build | not run here | none | keep (row 248; needs a named install) |
| `check-census` | the runtime census against the vendored sources, and its witness join | a stale census or a witness that names no row | not run here | none | keep (`AGENTS.md` states coverage only after it) |
| `check-schema-pins` | rc.112's Schema tag spellings against `Representation.tagName` | a Schema kind rc.112 adds or renames | not run here | none | keep (outside oracle, cheap) |
| `check-gen`, `check-gen-full` | every generated file against a fresh producer run | drift of a committed generated file | not run here | none | keep |
| `check-docs` | every path, link, citation and target the authority documents name | a dangling reference | 0.61 s (S3) | none | keep (`AGENTS.md`) |
| `check-language` | the controlled English checker's controls, then the specification and `AGENTS.md` | a rule violation in the two strict documents | not run here | none | keep (`AGENTS.md`) |
| `check-tsgo` | no `typescript` below 7 under `ts/`, `harness/`, `tools/` | a second compiler installed | not run here | none | keep (`AGENTS.md` names it) |
| `check-tools` | the axiom gate's admissions against compiled declarations, with a `Classical.choice` that must be refused | an admission that is not exact; a gate that admits a choice it should refuse | not run here | none | keep: the axiom gate's own red control |
| `check-semantics` | the semantics report's refusals of a broken registry | a report that renders a broken registry | not run here | none | keep: the report is an authority document |
| `check-slow` | the slow batteries | a long finite run or a trace law that fails | not run here | none | keep |
| `check-kernel` | every compiled declaration replayed through the kernel | a declaration the kernel refuses | not run here | none | keep (a sweep) |
| `check-conservativity` | an alphabet append's five clauses (its controls by default) | an append that moves a golden, a tag or a verdict unnamed | not run here | none | keep (row 172's instrument) |
| `check-ty-rule` | the `Ty` rule checker's controls | a hand case analysis on `Ty` outside the folds | not run here | none | keep (row 182's instrument) |

### The scripts

Every script a target above runs is in that row. These have no caller in the `Makefile`, the
scripts, CI or a tracked document outside `docs/research/` (`git grep`):

| Script | The fault it covers | Proposal |
| --- | --- | --- |
| `scripts/check-generator-bootstrap.py` | the early generator's answer to a changed constructor (needs `effect4gen` built) | cut (no caller) |
| `scripts/test-derived-plan.py` | a wrong dependency order of the derived generation (`scripts/lib/derived_plan.py`) | cut (no caller) |
| `scripts/test-lean-imports.py` | a header form the shared reader misses (HC-R8). Every closure-keyed marker rests on the reader, and no gate checks it after a cut | cut (no caller), or key it to the reader as the owner rules |
| `scripts/test-conform-runner.py` | the conformance runner's own report validation | cut (a test of a test). Decisions row 263 left it run by hand and its fate "a separate decision". Its two mentions go with it (`scripts/check-conform.py`'s docstring, `tools/Conform/README.md`) |
| `scripts/check-service-identity.py` | a service requirement or a provision that the emitted module and tsgo 7 or the pinned runtime disagree on (two TS2375 red controls, four runtime outcomes) | wire it into `check-full`, or cut it if `check-target` already compares the service-keyed programs (DI-76's remedy). The seat did not measure which |
| `scripts/build-progress.sh` | none: a live view of a running build | keep: the owner reads it from Bash (memory `visible-build-progress`) |

### The audit batteries (`Test/Audit/`)

All 27 are reached from `Test/All.lean` or `Test/Slow.lean`. Each is a battery of controls of
one tool, gate or rule:

| Module | The fault it catches |
| --- | --- |
| `AxiomGate` | the three gates: an axiom past the ceiling, an unreached battery, a source no root reaches |
| `AnswerGate` | a `SyncOp` or `FiberOp` row missing from the manifest |
| `ClockLiteralFixtures`, `ClockLowering` | a clock literal that loses its value; a saturated or unknown natural that reaches clock ingress; a builtin callback read as unknown; a host's reactor at a root refused, or a non-reactor admitted |
| `ClosureAudit` | a table bound before a returned closure |
| `ExhaustiveFixture`, `TraversalFixture`, `TraversalCensus` | a wrong row of the exhaustiveness or traversal census |
| `Explain`, `Obligations`, `ProofGraph`, `ProofGraphPlan`, `ProofGraphSearch`, `StatementCensusControls`, `SummaryControls`, `SemanticsCensus` | a proof-graph tool that answers wrong on a fixture |
| `FrameRules`, `PositionAnalysis`, `IndexedColumns`, `IndexedColumnActual`, `TypedStateDecl` | a frame rule, a position analysis or an indexed column generated wrong |
| `GlyphControls`, `SiteControls` | a mark table or a site page that the view's or the site's checks pass wrongly |
| `LandingPlanControls` | a landing plan counted wrong |
| `LetReturn` | the `let x = e in x` law broken on the evaluator, or the route's rewrite of it |
| `RuntimeCoverage` | a census row with no witness, or a witness that is no theorem |
| `ScenarioGate` | a scenario record that the proof graph does not back |

### The dune tests

The 34 tests and `api_check` (the G0 smoke of `ocaml/gen`) are LC-5's census
(`docs/research/2026-10-15-lowering-state/README.md` §6.6), each with its fault there, plus
`test_clock` (an exact clock value or refusal). Their times are that note's `probes/test-times.txt`:
43 s together, `prop_fibers_view` 15.45 s of it. S2 adds `answer_ingress_check` to `test_engine`.
No test is a cut candidate: each names its own fault, and the hand-carrier properties retire with
LC-8 (K5).

### The Conform lanes

| Lane | Run by | Proposal |
| --- | --- | --- |
| the `compiler` profile (`Conform.Effect4.Normalization`) | `check-compiler` | keep |
| the `native` profile (`Conform.Effect4.NativeMain`) | `check-native` | keep; fix its marker |
| the mirror census (`Conform.Cli.Audit`) | by hand (`AGENTS.md` names it as the baseline's reader) | keep; red until the next promotion (state note §6.3) |

### Graft: what no runner reaches

`reach-tools.txt`: 47 of 237 tool modules are unreached. The 18 files of
`tools/Effect4Gen/guards/` are text the derived generator appends (`--append`), so they are
inputs. The other 29:

| Files | What they are | Proposal |
| --- | --- | --- |
| `tools/conform-red/Probe2Neg.lean` | a red control that must fail to compile, run by no lane. It names `termTy_reflect`, `effTy_reflect` and `EffTy.joinAnswer_reflect`, which left the tree at `b08f3b580` (2026-09-18). So it fails at an unknown name, not at the failure it states (assumed from the source and that commit; not run) | cut. Its mentions: `RulesNeg.lean`'s docstring, `Test/Counterexamples/Archive/REGISTER.md` (`E4-CONFORM-CE-008`, which `check-docs` reads), `docs/core/traversal-census.md` §7 |
| `tools/conform-red/RulesNeg.lean` | the red control of `HasTy.select`'s requirement column: a wrong rule that `effTy_sound`'s arm and the checker's equation must refuse (not run; its state is unknown) | keep it as the rule's red control. Run it, then wire it as a `Test` fixture under `#guard_msgs (error)` at an anchor the coordinator names. `HasTy.lean`'s docstring names it, so a cut edits a law module's docstring and rebuilds the law graph |
| `tools/Tools/Session/Snapshot.lean` | snapshot previews; its consumer is the live-graph research driver (`docs/research/2026-10-10-live-graph-support/mcp/Preview.lean`, `Controls.lean`), which no runner reaches | keep until the live-graph plan is ruled, or move it beside its consumer |
| `tools/Drivers/ProgramStructureCheck.lean` | six negative controls of `Tools.ProgramStructure` (a missing family, a wrong parameter, a function field, an unknown nominal, the depth budget, an unsupported row) | make it a battery at an anchor the coordinator names, or fold the controls into `EffGen`'s cross-checks |
| `tools/view/*.lean` (18) and 7 modules of `tools/Tools/View/` (`FlowOrder`, `FlowPath`, `GraphContact`, `GraphContent`, `GraphPacking`, `GraphRegions`, `GraphRegionsView`) | the owner's visual probes of the 2026-10-13 receipts, run by hand | keep (the owner's) |

`reach-hosts.txt`: 10 of 23 host-side Lean files. Five are the engine's fixture writers
(`ocaml/engine/test/*/write.lean`), which the `Makefile` reaches by a wildcard
(`ENGINE_FIXTURE_WRITERS`), so they are reached. The other five are packets:

| Files | What they are | Proposal |
| --- | --- | --- |
| `harness/{authoring-branches,channel-transforms,module-catalogue,partitioned-bookkeeping,pull-protocol}/` (`Produce.lean`, `observe.ts`, `run.py`, `README.md`) | finite outside-oracle packets against an installed Effect 4.0.1 and tsgo 7, each run by hand for a landing's receipt | keep. Recommendation: one lane beside `check-truth-release`, which needs the same named install, so they do not rot as `conform-red` did |

Fixtures and generated files:

| File | Reader | Proposal |
| --- | --- | --- |
| `Test/fixtures/schema-census/reference.ts` | none: a synthetic fixture of the census's drift test, `git:c407ab7:scripts/test-schema-census-gate.sh`, which left the tree | cut (no caller) |
| every other folder of `Test/fixtures/` | a script, the `Makefile`, a contract or a battery | keep |
| the 8 files of `generated/` | each has a reader in the `Makefile`, a script, a battery or a document | keep |

## Axiom output

S1 and S3 change no declaration of an `Effect4.*` or `Test.*` module. Their declarations are in
the tool libraries `OCaml5` and `Conform`, which the axiom gate does not audit
(`Test/Audit/AxiomGate.lean`). S2 adds fixtures and controls to two `Test.Audit` modules. This
seat ran no `#axiom_audit` on them; the whole-tree gate runs in the coordinator's `lake build
Test`.

## Evidence

- F3 holds on the probe's closure (tested): the host-run probe spells every field.
- F3 moves no committed byte (reproduced, in place): the LCNF group regenerates identically.
- The F3 rule's controls (tested, finite): `Conform.Effect4.CompilerControls`, built by
  `check-compiler`.
- The F3 rule stops at a family applied to a variable (tested): `ArgF.r : R fam` stays unknown.
- The clock refusals came from a builtin callback's arity, not the reactor call (reproduced, on
  the base's analysis): this corrects the lowering state note's §6.9.
- S3 moves only layout in the nine regenerated files (tested, finite): the comparison and its
  four controls. It is a check of these files, not a theorem about the printer.
- `api_gen.ml`'s value names all resolve (tested): `Ml.checkModule`, 0 diagnostics, a syntactic
  check. It is not `ocamlc`.

## Landed theorems and their placement

None. Row 391 holds: the lowering carries no proof obligation.

## Open obligations

1. The route gates on S3 (`check-compiler`, `check-native`, `check-ocaml`), at the merge.
   `check-native` runs by its marker, since S3 touches `tools/Conform`.
2. The three lowering gaps of S2's `ocamlopt` probe (a `UInt32` record, a `String` record, the
   value restriction on a shared closure). P1 needs them.
3. The engine's functor body is checked with its scope open while the hand prelude is verbatim
   text (LC-8).
4. `OCaml5.Eff.tyO` is a hand structural traversal of `Ty`, carried from the base. A fold over
   `TyAlgebra` removes its census row (row 182's rule R4); `tyV` in `Goldens.lean` is the same.
5. Each `eff/` file opens with two "GENERATED" comment lines (the stamp and the module's header),
   as at the base.
6. Everything in S4 (the wind-down handoff lists it).

## Proposed decisions rows (proposals only)

1. **The clock boundary as built (row 394 (1), S2).** A root's reactor answer is host ingress,
   checked by `E4_engine.check_answer` (EN9). A global's arity is read off its mono declaration,
   so a builtin callback's call is resolved.
2. **The printer and the checker (S3).** The printer prints an application in an application's
   head in its parentheses, so a print parses back to its tree. `Expr.raw` is removed. `Decl.rawD`
   stays for the engine's hand prelude only, and it opens the scope of its own structure only.
3. **S4's census.** The cuts, the marker fix and the debatable items below, for the coordinator to
   rule.

## Wind-down handoff

**The one thing to know.** S3 is committed after its narrow build, and its three route gates are
yours: none ran on it. S4 holds no edit; its census and proposals are in this receipt.

**Base and head.** Base `68765c384`, the coordinator's merge of S1 and S2. S3 is the next commit,
and this receipt's commit follows it. The handback names both hashes.

**Landed since `68765c384`.** S3 (K3 widened): `eff/` and the three LCNF artifacts printed through
`OCaml5.Ml` and checked by `Ml.checkModule` with the opened unit's interface; the module language
(`open`, module types, packed modules, private type bodies), each printed under `#guard` and
read by the checker; `Expr.raw` removed; the carrier signatures and the prelude's primitives
structured.

**In flight.** Nothing: no patch is needed, since S3 is committed whole and S4 has no edit. The
seat's tools are tracked in `docs/research/2026-10-15-seat-cleanup-wind-down/`.

**Open items.**
1. `check-native`'s marker (`$(CHK)/native` in the `Makefile`) depends on `CORE_SOURCES` and every
   `tools/Conform` source. It omits 11 files of its driver's import closure
   (`scripts/lean-imports.py --closure tools/Conform/Effect4/NativeMain.lean`, measured):
   `src/OCaml5/Eff/World.lean`, `src/OCaml5/Lcnf/{Externs,Index,Naming,TypeRows,Types}.lean`,
   `src/OCaml5/Ml/{Identifier,Syntax}.lean`, `tools/ProofGraph/Axioms.lean`,
   `tools/Tools/ProgramStructure.lean` and `tools/Tools/WireTags.lean`. So the gate can report
   green on a stale route. `check-compiler`'s marker covers its closure (0 omitted, 20 files
   beyond it).
2. The fix, as designed and not made: each profile in `scripts/check-conform.py` names its driver;
   `--inputs PROFILE` prints the driver's closure and the runner's files; the markers read it, with
   `$(BUILD_PINS)`; the runner builds exactly the driver's imports. Today it builds `Conform
   Effect4 Effect4.Laws.Program.Typing.Check`. The narrower build leaves the mirror census
   (`Conform.Cli.Audit`, `Conform.Manifest.Mirror`, `Conform.Manifest.Readers`) built by no gate.
   `Conform.Lcnf.TargetLaws` stays built by `lake build Test`. The closure walk moves from
   `scripts/lean-imports.py` into `scripts/lib/lean_imports.py`, so both scripts share it.
3. The evident cuts, none made: the four scripts and `Test/fixtures/schema-census/reference.ts`
   above, and `tools/conform-red/Probe2Neg.lean` with its three mentions.
4. The debatable items: `check-service-identity.py`; `RulesNeg.lean`; `ProgramStructureCheck`;
   `Session/Snapshot.lean`; the five `harness/` packets; the view probes (the owner's). Each row
   above gives a recommendation.
5. From S3: the open obligations 2 to 5 above.
6. A tooling note: once, when the tool's 600 s limit stopped a foreground slot command, the slot's
   lock vanished, since `lean-slot.sh`'s trap removes it on a signal. Whether its `lake` child
   kept running was not measured. The seat ran every later slot command in the background.

**Gates run and not run.**
- Run by this seat on S3: the narrow build of every touched module and direct dependent; the two
  `ty-rule` mirror fixtures; `generate.py --only lcnf` and `--only eff`; `compare.sh` with its
  controls; `make -o build check-docs` (one finding outside the seat's edits).
- Run on S1 and S2 (above): `check-compiler`, `check-native`, `check-ocaml` (S1), and
  `check-compiler`, `check-native` (S2).
- Not run on S3: `check-compiler`, `check-native`, `check-ocaml`.
- Not run by this seat at all (the brief's list): `check-gen`, `check-slow`, `check-corpus`,
  `check-target`, `check-truth`, the conservativity script; and every other gate of `check-full`.
