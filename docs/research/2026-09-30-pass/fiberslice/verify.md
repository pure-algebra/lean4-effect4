Every fiberslice probe reruns identically (all exit 0, axiom lines byte-identical), but the slice cannot be promoted as "refuses the forged reply and applies the honest one" yet: a fiber's declaration is only as right as the checker, and for a fork inside a layer body provided under a binder it is wrong, so the prototype's keyed session admits a host reply that makes a `nat`-checked program return a string (reproduced, `verify-LayerEnv.lean`). The registry seat's layer gap 1 has to be fixed first or with the slice.

Two more things the coordinator needs before merging any of this:
- At a host row whose answer is a template (`fiberOf (var 0) (var 1)`, decisions row 42), the prototype refuses the honest reply that production applies (reproduced, `verify-Template.lean`). Codex's contract already says templates must be instantiated, or open variables refused, before admission (§4 matrix, `var` row). The prototype does neither.
- P0's premise "path A breaks no in-tree row" is false. `Test/Api/ExternalContract.lean:15` defines a host row answering the internal cell spelling `Ref<number>`, and the tree uses it to test host-returned cells (`:55-57`, `:65-68`). No test admits that table today, so no test would fail, but the rule removes a tested behaviour. That is the owner's call (row 7, authority), not a free move.

# Verification of seat fiberslice

Verifier for seat fiberslice. Base `be15b062`, branch `refactor/phase1-phase3`. HEAD is `48cd1de1`.
`git diff --stat be15b062..HEAD -- src/ Test/ ocaml/ tools/` shows one changed file,
`tools/Tools/ArchitectureRoles.lean`, which no probe reads. So the code under test is the base's.
I wrote only `verify.md` and `verify-*.lean` in this folder. I did not edit the seat's files.
The seat's `.build/` directory was gone, so I built the two modules into my scratch folder. The
seat's `logs/` are untouched.

Evidence words. **Proved**: a kernel-checked theorem; its axioms are quoted. **Reproduced**: I
reran a probe or built a new one, and the behaviour happened. **Tested**: a finite `#guard` over
named inputs; it says nothing beyond those inputs. **Read**: read from the source, not executed.
**Assumed**: taken without a check.

## 1. Reruns

Every command went through the one-compiler lock. The commands are in §5.

| File | Exit | Time | Compared with the seat |
| --- | --- | --- | --- |
| `Research/Pass/FiberSlice/Core.lean` (module) | 0 | 80 s | built into my scratch `.build/` |
| `Research/Pass/FiberSlice/Proofs.lean` (module) | 0 | 2 s | 31 axiom lines, identical to `logs/Proofs.log` |
| `LivePath.lean` | 0 | 1 s | no output, as the seat's |
| `Sites.lean` | 0 | 3 s | 17 axiom lines, identical |
| `Typed.lean` | 0 | 2 s | 2 axiom lines, identical |
| `Replays.lean` | 0 | 16 s | no output, as the seat's |
| `Holes.lean` | 0 | 1 s | no output, as the seat's |
| `DeclLane.lean` | 0 | 22 s | printed line identical: 8584 programs, 34336 runs, 35744 forks, 28918 declared, 2626 layer builds, 4200 with no site, 28034 exited, 0 violations |

The axioms: 44 theorems at `[propext, Quot.sound]`, 5 at `[propext]`, and
`firstRefusal_of_all_none` at none. Counts match the note: 31 + 17 + 2 = 50 theorems. LivePath
has 44 `#guard` lines and 1 `#guard_msgs`, Replays 25, Holes 23. No `sorry`, `axiom`,
`native_decide`, `partial`, `unsafe` or `implemented_by` in any file.

## 2. Verdicts, claim by claim

**C1. The forged reply is refused on the live keyed session; the honest one is applied.**
Confirmed (reproduced, tested). `LivePath.lean:72-126` reran. Production's phases are
`[preflight, applied, progressed]` and the root ends with `"wrong"`. The prototype's are
`[refused envelope, refused noCall, progressed]` with the located refusal at value path `[]`.
The honest run ends with 7 on both routes. The tape route refuses at decision 1. This holds
for this program and a closed row. It does not hold at a template row (M2) or for a fork in a
layer body (M1).

**C2. Every nesting gap of the old predicate is closed at the admission.** Confirmed for
success-value positions (reproduced, tested). The eight rows reran. I added the error arm of a
Result and a three-deep nesting `list (option (prod unit fiber))` (`verify-Nesting.lean`): both
are refused at their exact paths (`[0]`, `[1, 0, 1]`), and the honest values pass. Failure
payloads cannot carry a handle: `Err` is a closed alphabet (`Machine/Alphabets.lean:34-40`,
`valOfErr_keys`), and the cause image is handle-free (`causeImage_handleFree`,
`Alphabets.lean:183`). Oracle answers cannot either (`externalAdmits` wants a handle-free
value, `Program/Compile.lean:1387-1393`). Contexts, cells and deferreds are the separate holes
the seat names.

**C3. `envAt` is the checker's environment, and `siteDecl` is the checker's type at every source
fork site.** Confirmed (proved). I read all 17 statements. `envStep_checks` splits on
`Node.child`'s own arms: 52 child positions plus the no-child arm, so the case list is complete
by construction. `NodeChecks` quantifies over `inLoop`/`afterRet` for statements and drops the
environment for layers. That is a fair reading of the checker. The siteDecl theorems are about
nodes of `root.expandRefs`. One limit matters: these theorems are about the **checker**. They say
nothing about the runtime. At a layer body the runtime environment differs (M1), so "the
declaration is right" does not follow from them.

**C4. The declaration needs the site's environment (nine binder programs; the naive reading fails
seven; red control).** Confirmed (tested). `LivePath.lean:248-374` reran. The matchCause probe
covers the value arm only; the cause arm and `catchIf`/`acquireRelease` are covered by the proof,
not by a run.

**C5. Nothing else changes (proved).** Confirmed (proved). `admitD_eq_of_fiberFree`,
`acceptReply_of_acceptReplyD`, `fitsAt_hasTy`, `fitsAt_none_of_hasTy` say what the note says.
The hypothesis `AnswerFiberFree` is not vacuous. `noFiber` reads `Store.Val.handles`, which walks
every container frame (`Store/Carrier/Val.lean:301-312`). Read the scope exactly: nothing
changes for answers **without** a fiber handle. For an answer with one, the verdict can change on
an honest reply (M2).

**C6. 96,556 journals agree.** Confirmed (tested). The sum is right: 30,941 + 22,621 +
2 × 1,885 + 2 × 19,608 + 8 battery runs. `sameMachine` compares all ten `RunMachine` fields
(`Machine/Fibers.lean:436-449`), races by key. `sameSession` compares every data field of
`Session` (`Api/HostSession.lean:84-93`). One note: the three batteries' rows answer `nat`, `unit`
or an external handle, and no submitted value holds a fiber. So on 57,340 of the journals (all but the
fiber row's) the declaration clause never fires. Those runs show that the copied session steps match
production. They do not test the clause. Only the fiber row's 2 × 19,608 do.

**C7. The declaration lane: every exited source fork fits its declaration, 0 violations.**
Confirmed as a finite check (reproduced; identical output). Three limits:
- The invariant is false outside the corpus. `verify-LayerEnv.lean` builds a three-line program
  whose only fork is declared `nat` and returns `"s"`. The lane's layer bodies bind nothing, so
  it cannot reach this (the registry seat says the same, its note §5).
- The arity check (`DeclLane.lean:92-102`) runs the first tape only, not the four.
- The `never` control (`:123-135`) is a separate function. It shows the corpus has declared
  forks that succeed. It does not run `checkRun`'s violation branch.

**C8. Three kinds of internal fork, told apart by the node at the site.** Confirmed (read,
tested). Finalizer forks record `[]` (`Machine/Fibers.lean:969`). Source-less races record
`race.nextSite.getD []` (`:1864`). `merge`/`mergeAll` layer builds record the layer's path
(`Program/Compile.lean:1453-1455`). The origin plan names only the first two
(`2026-09-30-origin-ledger-and-step-invariants-plan.md:79-82`). `verify-Top.lean` adds a run: the
two layer builds of a `merge` have no declaration. Both admissions accept them at
`fiberOf unknown unknown`, and the prototype refuses them at `fiberOf nat never`.

**C9. The OCaml engine has no answer admission; the slice regenerates no group.** Partly.
- Confirmed (read): the closure lists `ocaml/gen/closure-api_engine.tsv` and
  `closure-api_gen.tsv` contain no `admit`, `admitAnswer`, `acceptReply`, `HostSession`,
  `Program.Refusal` or `oracleRefusal`. They do contain `Val.hasTy`, `externalValue`,
  `prepareExternalAnswer`, `externalAdmits`, `requestOf`, `awaits`. The engine calls
  `api_run p fuel [] [] fuel` (`api_engine_inst.ml:77`, `api_engine_ref.ml:60`).
  `Program.Refusal` is in no derived manifest (`tools/Effect4Gen/manifest.json:143-148` lists
  `TableRefusal`, `AdmitRefusal`, `HostSession.Refusal`).
- Not shown: the OCaml engine depends **by name** on a specialization the Lean compiler made
  while compiling `replayCheckedFrom`. The name is
  `step_decision_state_at_program_replay_checked_from_spec_1` (`ocaml/gen/api_gen.ml:16285`,
  `ocaml/engine/api_engine.ml:14148`). Two hand-written files call it (`api_engine_inst.ml:74`,
  `api_engine_ref.ml:57`), and about 40 closure rows carry the same prefix. Step 3 edits
  `replayCheckedFrom`. Swapping one plain call probably keeps the name, but nothing here shows it.
  The check is cheap and AGENTS.md owes it anyway: `python3 scripts/generate.py --only lcnf`
  byte-identical, then `dune build`. I did not run either (the brief forbids it).

**C10. Contexts are a live hole.** Confirmed (reproduced). See also M5: the proposed static
clause, as written, refuses an honest context.

**C11. Deferreds are a live hole at `Deferred<number, number>`.** Confirmed (reproduced). The
cited lines read as stated (`Machine/Stores.lean:2003-2023`, `Program/Typed.lean:62-65`).

**C12. Cells, scopes, `unknown`.** Confirmed (reproduced, read). For `unknown` I widened the test
from one consumer to eleven (`verify-Top.lean` §2): `awaitFiber`, `interrupt`, `interruptScoped`,
`awaitAll`, `awaitNewChildren`, `setContext`, `runIn`, `forkIn`, `closeScope`, `refGet`,
`deferredAwait`. The checker refuses every one at `unknown`, and accepts the controls at their
proper types. The reason is in the rules: `fiberTy` matches `fiberOf` exactly
(`Typing/Rules.lean:184-186`), and the scope and context rules compare types with `=`
(`Checker.lean:327, 337, 374, 381`).

**C13. Two law sites would silently break if `admit` changed in place.** Partly (read). The sites
are right: `Reactor.Envelops` is defined by `admit` (`Laws/Run.lean:625-633`), `drive_envelope`
concludes no envelope refusal (`:636-639`), and `preflight_ok`, `submit_accepted`,
`applyReply_accepted` take `Envelope` (`:404`, `:421`, `:442`). But "silently" is wrong. The
clause needs the program, and the machine does not store it, so `admit` cannot gain the clause
without a new argument; every caller then fails to elaborate. And if only `preflight` moved,
the stale proofs fail the build. Either way the build reports it.

**C14. The case-site policy reaches the slice.** Confirmed (read).
`tools/Conform/Effect4/cases-policy.json` sets `unlisted: refuse` for `Ty`, `Eff` and `NativeOp`.
`admit` has a `NativeOp` entry. `fitsAt`'s default arm covers exactly the 13 constructors the seat
lists. The policy pins compiled case sites, so the exact cover is decided by the scan after a
build.

**C15. The runtime check transfers to any narrower table; an admitted value is a strong value
(fiber part); "the boundary owes nothing more for fibers once M6 supplies T1".** Partly.
- Confirmed (proved): `declFits_narrower`, `fitsAt_narrower`, `fits_narrower`,
  `envelopeD_fits_table`, `fiberDeclOf_native` are real and non-vacuous (`Narrower` is
  reflexive, so it can hold).
- `admitted_value_strong` is proved, but it says little. It does not mention the admission. Two
  of its three conclusions are its own hypotheses (`hty`, `hlive`); the third is
  `fits_narrower`. And `StrongValueFibers` is the seat's own definition, not the tree's.
- The chain is not closed. The admission checks the **prepared** value in the **extended**
  allocation table (`envelopeD_fits`). `admitted_value_strong` needs fits at the **world's**
  table on the **unprepared** value. No theorem joins the two.
- `HandlesLive` (`Laws/Program/Typed/Admission.lean:21-26`, the fiber arm at `:25`) needs `Γ id` for **every** fiber handle.
  The top rule admits internal fibers with no declaration (`verify-Top.lean`), and
  `ForkSource.lean` leaves internal forks out of `Γ`. So either M6 declares internal fibers, or
  the admission must refuse undeclared ones. The seat's open question 2 is a real fork in the
  design, not a nicety.
- The keyed session steps the native machine; `RState` is the reference machine (DI-57). The
  seat's own table says so; the summary claim drops it.
- T1 is declared, not proved. By the registry seat's layer gaps it cannot hold until gap 1 is
  fixed. P5 makes this sharper: typing a source point at `envAt`'s environment makes `EnvTyped`
  fail on length at a layer-body point under a binder (the runtime environment is longer). So
  P5 needs gap 1 fixed first.

**The one-thing claim.** Partly. Small, beside, regenerates nothing derived, refuses the forged
reply at closed rows: confirmed on the seat's probes. Not shown, or false: the honest reply at a
template row (M2), the declaration of a layer-body fork (M1), and the lcnf group (C9).

**P0, "path A breaks no in-tree row".** Refuted (tested, read). `verify-PathA.lean` applies the
path probe's own `mentionsInternal` to `Test/Api/ExternalContract.lean`'s table: it refuses the
second row, `row "cell" NativeOp.refTy`. The path probe's list of "every host row the tree
defines" (`host-answers-evidence/PathProbes.lean:51-58`, 15 rows) leaves this file out. The row
is a deliberate fixture: it tests that a host may return a cell (`deadHandle` at `:55-57`, the
delayed read at `:65-68`). It also sits in the typed corpus (`Test/Program/TypedCorpus.lean:119`).
No in-tree test admits that table (grep: only `typeOf`, `replayChecked`, raw `replay`,
`Checker.check`, `PointTyped`), so no test fails. But P0 includes `Ref<number>` in the refused
spellings, while the seat's own table (§6) says that spelling is aliasing only, an authority
question for the owner (row 7).

## 3. What the seat missed

**M1. The layer environment gap reaches the boundary through the prototype (reproduced).** The
checker types a layer's effect body closed (`envStep` gives `[]` at `Core.lean:49-50`; the binder
table agrees, `Program/Binders.lean:40-41`). The runtime builds the body at a point derived from
the providing site (`innerLayerAt`, `constructionAt`, `Program/Compile.lean:715-749`), and
`Point.child` keeps the environment (`:80`). Variables are read by level (`env[index]?`,
`Machine/Term.lean:427`). `verify-LayerEnv.lean`:
- `bind "s" (provideLayer (effect natKey (bind 5 (bind (fork (succeed (var 0))) 7))) (service
  natKey))` checks at `nat`. Its one fork is declared `nat` and returns `"s"`.
- Add a host row `fiberOf nat never`, ask, and join. The host names that fork. `admit` and
  `admitD` both accept. Through `submitD`/`applyReplyD` the phases are
  `[preflight, applied, progressed]`, and the `nat`-checked program finishes with `"s"`.
- A red control is pinned under `#guard_msgs`.

The registry seat proved gap 1 itself (`registry/LayerGap.lean`, its `forkLeak_*`). The seat
lists it as open question 4. What is new here is the step through the slice: the prototype
admits the reply. The slice's guarantee is relative to the checker, and here the checker and the
runtime disagree.

**M2. Template host rows (reproduced).** The checker instantiates every row's columns from the
request's static type (`rowTy`, `Typing/Rules.lean:114-117`). `checkTable` does not refuse
template parameters (`Program/Native.lean:345-352`). The admission compares against the
uninstantiated column. `verify-Template.lean`:
- The row `request := fiberOf (var 0) (var 1)`, `answer := fiberOf (var 0) (var 1)` admits. A
  program that passes its `nat` fiber and joins the answer checks at `nat`, and the session
  starts.
- The honest reply names the same fiber. Production accepts and finishes with 7. The prototype
  refuses with `handleDecl … ⟨[], fiberDecl ⟨1⟩ (some nat) (fiberOf (var 0) (var 1))⟩`, on the
  admission and on the tape route.
- A forged reply at the same row: production accepts it (the same hole), and the prototype
  refuses it. So at template fiber rows the prototype refuses everything.
- For context: a bare template data column is unanswerable today, before any slice. `Val.hasTy`
  at `var` is false, so `admit` refuses even the value the checker typed.

No in-tree host row uses a template (grep), so this is latent. Path A also covers it while
fibers stay refused. When the slice lifts fibers out of path A, template fiber rows need a rule:
instantiate from the call site's static request type, or refuse open variables at table
admission, as the contract says.

**M3. P0's premise** (see the P0 verdict above).

**M4. The OCaml engine's name coupling to `replayCheckedFrom`** (see C9).

**M5. The proposed context clause refuses honest contexts (reproduced).** `verify-Context.lean`
runs the seat's own `servicesFit`. A context read under `scoped` carries keys (0,0) and (4,4),
both statically typed, and passes. A context read under a provided layer also carries
`currentMemoMapKey` (3,3) (`Machine/ContextMap.lean:670`), which has no static type, so
`servicesFit` answers `false`. `ServicesOk` leaves such keys unconstrained
(`Admission.lean:32-34`). Relaxing the clause to skip untyped keys would let a host plant a
memo map in a context the program installs. That is a decision for the owner (contract §3,
capabilities), not a detail.

**M6. Undeclared fibers and the typed world** (see C15). A host can name a runtime layer build at
the top today and after the slice (`verify-Top.lean`). The world's `HandlesLive` needs a `Γ`
entry for it.

**M7. Raw certified routes stay open (tested).** The slice wires the two checked routes. The
certified entry points `replayAdmitted` (`Api.lean:425-433`) and the certificate-first
`Api.Typed.replay` (`Api.lean:471`) replay the caller's tape without decision admission, by design
("Raw", `Api.lean:278-284`). `verify-Raw.lean`: both finish the seat's forged program with
`"wrong"`. The contract's entry-path list (§5) should say which routes a host may use.

**M8. Smaller points.** The batteries never fire the clause (C6). The lane's arity check runs one
tape, and its `never` control does not exercise `checkRun` (C7). "Silently" in C13 is wrong.

## 4. My probes

All are finite checks, not proofs. No theorems, so no axiom output.

| File | What it shows | Exit |
| --- | --- | --- |
| `verify-Template.lean` | template fiber row: production applies the honest reply (7), the prototype refuses it; forged also refused; template data column unanswerable today; red control pinned | 0 |
| `verify-LayerEnv.lean` | layer-body fork declared `nat` returns `"s"`; the prototype's keyed session applies the host's reply naming it, and the `nat` program ends with `"s"`; red control pinned | 0 |
| `verify-Top.lean` | `merge` layer builds have no declaration, are admitted at the top only; eleven handle consumers refused at `unknown`, controls accepted | 0 |
| `verify-Nesting.lean` | Result error arm and three-deep nesting refused at `[0]` and `[1, 0, 1]`, honest accepted; a union of two fiber types admits the `string` fiber, and no rule can join a union | 0 |
| `verify-PathA.lean` | path A's own predicate refuses `ExternalContract`'s `cell` row (`Ref<number>`) | 0 |
| `verify-Context.lean` | the proposed `servicesFit` passes a scoped context and refuses a context read under a layer (key (3,3), the memo map) | 0 |
| `verify-Raw.lean` | `replayAdmitted` and `Typed.replay` finish the forged program with `"wrong"` | 0 |

## 5. Commands and results

`<lock>` is `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh`.
`<scratch>` is `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/verify-fiberslice`.
I ran the seat's `run.sh` steps through my copy, `<scratch>/rerun.sh`, which writes oleans and logs
to `<scratch>` instead of the seat's folder:

```
bash <lock> lake env lean -M6144 -DwarningAsError=true -R docs/research/2026-09-30-pass/fiberslice \
  -o <scratch>/.build/Research/Pass/FiberSlice/Core.olean \
  docs/research/2026-09-30-pass/fiberslice/Research/Pass/FiberSlice/Core.lean          # exit 0
bash <lock> env LEAN_PATH=<scratch>/.build lake env lean -M6144 -DwarningAsError=true \
  -R docs/research/2026-09-30-pass/fiberslice -o <scratch>/.build/Research/Pass/FiberSlice/Proofs.olean \
  docs/research/2026-09-30-pass/fiberslice/Research/Pass/FiberSlice/Proofs.lean        # exit 0
LEAN_PATH=<scratch>/.build bash <lock> lake env lean -M6144 -DwarningAsError=true \
  docs/research/2026-09-30-pass/fiberslice/<Probe>.lean
  # LivePath, Sites, Typed, Replays, Holes, DeclLane: exit 0 each
diff <(grep -v '^exit' <scratch>/logs/Proofs.log) <(grep -v '^exit' docs/research/2026-09-30-pass/fiberslice/logs/Proofs.log)
  # and the same for Sites, Typed, DeclLane: no difference
LEAN_PATH=<scratch>/.build bash <lock> lake env lean -M6144 -DwarningAsError=true \
  docs/research/2026-09-30-pass/fiberslice/verify-{Template,LayerEnv,Top,Nesting,Context}.lean   # exit 0 each
bash <lock> lake env lean -M6144 -DwarningAsError=true \
  docs/research/2026-09-30-pass/fiberslice/verify-{PathA,Raw}.lean                     # exit 0 each
```

`verify-Context.lean` prints `[(0, 0, true), (4, 4, true)]`, `some true`, and
`[(4, 4, true), (3, 3, false)]`. The other probes print nothing.

Read-only commands: `git log`, `git diff --stat be15b062..HEAD -- src/ Test/ ocaml/ tools/`, `grep`
and `sed` over `src/`, `Test/`, `ocaml/`, `tools/`, `harness/`, `generated/`, and `python3` reads of
`ocaml/gen/roots.json` and `tools/Conform/Effect4/cases-policy.json`. No build of the library, no
generator, no `make`, no git writes.
