The fiber slice is small and regenerates no generated file: a declaration read from the fork site with the existing checker (proved to be the checker's own type there) plus one shape-and-fiber recursion refuse the forged fiber reply on the keyed session, apply the honest one, and change nothing else (proved for answers without fiber handles; 96,556 journals compared) — but refusing internal handle kinds in host rows (path A) must still land now, because contexts and deferreds are live holes today that no fiber declaration closes.

# Fiber slice of the external lane: derived declarations and one membership recursion

Seat: fiberslice. Base `be15b062`, branch `refactor/phase1-phase3`, 2026-09-30. HEAD moved to
`5e1ced00` during the pass; that commit changed only documents (`git diff --stat be15b062..HEAD --
src/ Test/` is empty). Research only: every file I wrote is in
`docs/research/2026-09-30-pass/fiberslice/`. No commit, no build of the library, no edit elsewhere.

Evidence words. **Proved**: a kernel-checked theorem; its `#print axioms` output is quoted.
**Tested**: a finite `#guard` over named inputs; it shows what happens on those inputs only.
**Reading**: read from the source, not executed.

## 1. The slice in short

- **A declaration for every live fiber, derived, never stored.** Fiber 0 (the loaded root) is
  declared at the certified program type. A forked fiber is declared at the checker's type of
  the forked body, typed in the environment the checker reaches the fork site with. The site is
  the one the machine already records (`RunFiber.origin`; the fork ledger when it lands).
  Functions: `envStep`/`envAt` (the environment at a path), `siteDecl`, `fiberDecl`.
- **One recursion for shape and fiber declarations**, `fitsAt`, over the encoding `Val.hasTy`
  reads (products as two-cell lists, Results and exits as constructors, snapshots decoded, a
  union by one whole branch). It returns a located refusal: a value path and a reason.
- **Admission** is today's `admit` (row, shape, allocation, liveness), then `fitsAt` on the
  prepared value in the extended allocation table. A refusal is
  `handleDecl fiber token ⟨path, reason⟩`.
- **Wiring**: one call in `HostSession.preflight` (`Api/HostSession.lean:171`) and one in
  `replayCheckedFrom` (`Program/Admit.lean:118`). `submit`, `applyReply`, `Runner.step` and
  `Run.drive` all go through `preflight`, and `applyReply` re-runs it at application, so the
  check holds at receipt and again at application.
- **Nothing generated changes.** The OCaml engine has no answer admission and runs with the
  empty table; the slice leaves `Val.hasTy`, `externalValue` and `prepareExternalAnswer`, the
  functions the engine does contain, untouched.

The prototype is `Research/Pass/FiberSlice/Core.lean` (copies of `admit`, the envelope,
`acceptReply`, the session steps and the tape route, one call changed in each).

## 2. Findings

**F1. The live hole is closed on the keyed session (tested).** `LivePath.lean` §1 drives
start → evaluate → `bindCall` → submit → apply → flush for a program checked at `nat` that
forks a child and joins the fiber the host names (the host-answers probe's program).
- Production, forged reply (child returns `"wrong"`): phases `[preflight, applied, progressed]`,
  root exit `success "wrong"` (lines 76-77).
- Prototype, forged reply: `[refused envelope, refused noCall, progressed]`, no exit
  (lines 80-82). The admission's refusal is located: `handleDecl root 0 ⟨[], fiberDecl ⟨1⟩ (some
  string) (fiberOf nat never)⟩` (lines 101-104); production's `admit` accepts the same decision
  (106-108).
- Honest reply (child returns 7): applied on both routes, exit 7, identical results (85-87).
- A fiber that does not exist is still `deadHandle` (liveness runs before the declaration,
  110-112).
- Tape route: `replayChecked` finishes with `"wrong"`; the prototype's tape route refuses at
  decision 1 with the located reason, and the honest tape finishes with 7 (115-126).

**F2. Every nesting gap of the old predicate is closed at the admission (tested).**
`LivePath.lean` §2, eight rows each answering a `nat` fiber somewhere inside: a bare handle,
a product (two-cell list), an option, a list, a snapshot, a Result, a successful exit, a union.
The old admission accepts all eight forged values. The prototype refuses each at its value
path (`[]`, `[0]`, `[0]`, `[0]`, `[0, 0]`, `[0]`, `[0]`, `[]`) with the same reason, and accepts
all eight honest values. Through the whole session, production finishes with `"wrong"` for the
three programs that consume the fiber (bare, `fst` of the pair, `select` on the option) and
reports `[exitOk "wrong"]` for the two that `awaitAll`; the prototype refuses at submit; the
honest runs are identical on both routes (lines 194-244).

**F3. The declaration needs the site's environment, and `envAt` is exactly the checker's
(proved, tested).**
- Proved (`Sites.lean`): `envAt_checks` — from a checked node, the node at every path is
  checked, at the environment `envAt` computes and at its own path. `siteDecl_fork`,
  `siteDecl_forkIn`, `siteDecl_forkScoped`, `siteDecl_race` — at every source fork site of a
  program `typeOfProgram` accepts, `siteDecl` answers the checker's type of the forked body
  there, and the fork expression's own static answer is `fiberOf` of exactly that type. So the
  registry agrees, by proof, with the type the program itself gave the handle.
- Tested (`LivePath.lean` §3): nine programs fork under `bind`, `catchCause`, `matchCause`,
  `onExit`, a generator `bindYield`, an option `select`, `iterate`, `forkScoped` and `raceAll`
  (two entrants, sites `[0, 0]` and `[0, 0, 1]`). Every fork's derived declaration is the expected
  type. The path probe's reading (empty environment) has no declaration for the seven forks that
  read a bound variable. Red control: with that reading, an honest reply naming a fiber forked
  under a binder is refused (lines 356-374).
- Tested (`DeclLane.lean`): at every source fork site the corpus reaches, `envAt`'s length is
  the binder level of the generated binder table (`Node.childLevel`, cut from
  `tools/Effect4Gen/binders.json`). The hand table `envStep` and the generated one agree there.

**F4. Nothing else changes (proved, tested).**
- Proved: `admitD_eq_of_fiberFree` — on an answer with no fiber handle (success value, or the
  delayed cell's contents) the prototype's verdict is the old one, refusal reason included.
  `acceptReply_of_acceptReplyD` — whatever the prototype accepts, the old check accepts, with
  the same decision. `fitsAt_hasTy` — the combined judgment implies the old shape judgment;
  `fitsAt_none_of_hasTy` — on fiber-free values they agree exactly.
- Tested (`Replays.lean`), every phase and every session field compared. The machine is compared
  field by field; a race by its identity, host, token, flags, next site and number of entrants
  left, because its race state and pending programs have no equality instance:
  - `HostSpecContract`: the ten records at the parked and the answered machine, their refusal
    reasons, and the frontier, finished and refused tapes.
  - `KeyedHostContract`: its four paths at fuel 1000 and 0, and all 30,941 journals of length at
    most 4 over its 13 commands.
  - `HostSessionContract`: all 22,621 journals of length at most 4 over its 12 commands at fuel
    100, and all 1,885 of length at most 3 at fuel 1 and at fuel 0.
  - The fiber row: all 19,608 journals of length at most 5 over 7 commands agree for the honest
    program. For the forged program, wherever the phases differ, the first difference is the
    forged submit (production `preflight`, prototype `refused envelope`), and some journal does
    differ.
  In total 96,556 journal comparisons.

**F5. The declaration lane: every source fork's exit fits its declaration (tested).**
`DeclLane.lean` reruns the exit-type lane (8,584 programs × 4 tapes = 34,336 runs; the lane
itself checks only the root, `ExitTypeLane.lean:14-15`). 35,744 forks: 28,918 source forks, every
one declared; 28,034 exited source forks checked, each success fitting its declaration with the
registry reading nested fiber handles, each failure's typed reasons admitted by the declared
error. 0 violations. Control: declarations replaced by `never` are caught.

**F6. The runtime makes three kinds of internal fork, told apart by the node at the site
(tested, reading).** Finalizer forks and races without a source Point record `[]`
(`Machine/Fibers.lean:969`, `:1864`). A layer build forked by `merge`/`mergeAll` records the
layer's own path (`Program/Compile.lean:1453-1455`), a non-empty site naming a layer node. The
lane saw 4,200 of the first and 2,626 of the second. The origin plan (§3) lists only the first
kind; the layer builds are a third kind it does not name. The ledger still needs no
construct-kind field for this slice, because a fork node, a race cell and a layer node are
different nodes. The slice
reads internal forks at the top: a host may name one only at a type above every type
(`fiberOf unknown unknown`), which is exact, since every fiber fits the top.

**F7. The admission is not in the OCaml engine; nothing generated changes (reading).** The
LCNF roots are `Api.run`, `Api.replay`, `stepDecisionState`, `driveState` and helpers
(`ocaml/gen/roots.json`). The generated `api_gen.ml` and `api_engine.ml` contain `Val.hasTy`,
`externalValue`, `prepareExternalAnswer`, `requestOf` and `awaits` (preparation and inspection)
and none of `admit`, `admitAnswer`, `acceptReply` or `HostSession`. The engine calls
`api_run p fuel [] [] fuel`, the empty table (`ocaml/engine/api_engine_inst.ml:77`,
`api_engine_ref.ml:60`); this settles the contract's claim the host-answers note left unchecked.
`ocaml/engine/e4_admit.ml` is mailbox back-pressure, unrelated.

**F8. Contexts are a live hole today (tested).** A row answering `Ty.context`; the host sends a
context that binds a free key whose static type is `nat` (type code 4, `Native.lean:277-294`) to
`"forged"`; the program installs it (`setContext`) and reads the service. Checked at `nat`, it
finishes with `"forged"` on production and on the prototype (`Holes.lean`). `Val.hasTy v
Ty.context` only decodes the value (`Program/Typed.lean:54`); the proof world requires
`ServicesOk` (`Laws/Program/Typed/Admission.lean:32-34`). A static clause — every service fits
its key's type — refuses it and needs no registry (`servicesFit`, tested).

**F9. Deferreds are a live hole today, at the native spelling (tested).** `memoBuild` allocates
a deferred for a layer's build and `memoComplete` completes it with the build's exit
(`Machine/Stores.lean:2003-2023`). A host answering `Deferred<number, number>` names that
deferred; `deferredAwait`, typed to answer a number, returns the layer's built service context
(`ctor 5 [...]`) on both routes. The honest counterpart (the program's own deferred, completed
with 3) returns 3. At `deferredOf a e` any promise is accepted whatever `a` and `e`
(`Program/Typed.lean:62-65`).

**F10. Cells: no wrong read today, but the certified type can be wrong (tested, reading).**
Every cell is made by `refMake` at a number (`syncOpOf`, `Native.lean:232`). At `refOf string`
a host can name the program's own number cell; both routes apply it and the program's certified
`Ref<string>` result is a number cell, which breaks `HandlesFit (refOf t)`
(`Admission.lean:41`). At the native spelling `Ref<number>` a host can alias the program's own
cell: the program writes 9 through "the host's" cell and reads 9 from its own. That is type-safe;
it is an authority question.

**F11. Scopes have no type parameter (tested, reading).** `Val.hasTy` checks the kind and the
spelling exactly (`Program/Typed.lean:51`) and the typed world has no scope table. A host can
hand back the program's own scope and the program can close it (`Holes.lean`): authority, not
typing. **F12. `unknown` (tested).** Any handle passes `Val.hasTy` at `unknown`, but no rule reads
a handle there: the checker refuses `awaitFiber` at `unknown`.

**F13. Two law sites would go wrong if `admit` changed in place (reading).**
`Reactor.Envelops` (`Laws/Run.lean:625-633`) defines "a host inside the envelope" by today's
`admit`. With the declaration clause, a reactor that answers a forged fiber is inside by that
definition yet refused, so `drive_envelope` (`:636`, "a host inside the envelope is never
refused") would be false. It must be restated with the new admission. `preflight_ok`,
`submit_accepted` and `applyReply_accepted` (`:404`, `:421`, `:442`) take `Envelope` premises.

**F14. The session drops the admission's reason (reading).** `preflight` maps every admission
refusal to `refused envelope` (`Api/HostSession.lean:171-172`). The located reason exists on
`admit` and `replayChecked` only. Carrying it in the phase changes the derived `Runner` codec;
proposed below as its own step (it concerns every envelope refusal, not only fibers).

**F15. The case-site policy reaches the slice (reading).** `tools/Conform/Effect4/cases-policy.json`
refuses unlisted default arms for the families `Ty`, `Eff` and `NativeOp`. `fitsAt` (a default
arm on `Ty`), `envStep` (on `Eff`) and the new admission (on `NativeOp`, as `admit` is listed
today) each need an entry, or `make check-cases` refuses.

## 3. What I proved

All 50 theorems are at `[propext, Quot.sound]` or fewer axioms (§9 has the output).

`Research/Pass/FiberSlice/Proofs.lean` (31), the runtime check:
- Connector: `admitD_of_admit`, `admit_of_admitD`, `envelope_of_envelopeD`,
  `acceptReply_of_acceptReplyD`, `envelopeD_of_acceptReplyD`, `acceptReplyD_none_of_acceptReply`
  (at most once carries over from the old law).
- Receipt: `preflightD_envelope`, `submitD_receipt`, `submitD_machine` (receipt does not run).
- Application: `applyReplyD_applied` (the envelope holds at the application-time machine).
- The judgment: `fitsAt_hasTy`, `fits_hasTy`, `fitsAt_fiberOf` (the fiber clause, exactly),
  `fitsAt_none_of_hasTy`, `snapshot_nil_of_noFiber`, `firstRefusal_none`,
  `firstRefusal_of_all_none`, `noFiber_some`, `noFiber_of_mem_list`, `noFiber_of_mem_ctor`,
  `noFiber_fiber`.
- The admission: `admitD_of_admit_none`, `externalValue_result`, `noFiber_prepared`,
  `admitD_eq_of_fiberFree`, `envelopeD_fits` (receipt membership).
- Toward the typed guarantee: `declFits_narrower`, `fitsAt_narrower`, `fits_narrower` (the check
  transfers to every table at most as wide as the registry — the proof world's `Γ` has the
  registry's type, `FiberId → Option EffTy`), `envelopeD_fits_table` (receipt membership under
  such a table), `fiberDecl_congr` (declarations move only with origin records).

`Sites.lean` (17), the declaration is the checker's: `effTy_of_ok`, `inv_stmts_cons`,
`inv_stmt_bindYield`, `inv_stmt_yieldDiscard`, `inv_stmt_ifElse`, `inv_stmt_whileTrue`,
`inv_stmt_ret`, `inv_stmt_breakLoop`, `envStep_stmts_rest`, `envStep_stmts_head`, `envStep_checks`
(all 52 child positions of `Node.child`), `envAt_checks`, `root_checks`, `siteDecl_fork`,
`siteDecl_forkIn`, `siteDecl_forkScoped`, `siteDecl_race`.

`Typed.lean` (2), against the real typed world: `fiberDeclOf_native` (the machine-generic
declaration is the prototype's at the native machine) and `admitted_value_strong` (§5.2: given
the fiber part of `RegistryAgrees`, an admitted value is a strong value in the world, fiber
part). The file also declares one wanted obligation, `typedState_fiberRegistry`, in the
repository's `ProofGraph.Obligation … := ⟨⟩` style: that is its statement, not its proof.

## 4. Task 2: the production sites, in build-beside order

**Step 0 — path A, first and separate (recommended).** Refuse internal handle kinds in host
rows at table admission, as the path probe did (`host-answers-evidence/PathProbes.lean:24-38`),
with a located refusal. It closes F8, F9, F10 and the fiber hole at once and breaks no in-tree row
(path probe: 15 rows). If it adds a constructor to `TableRefusal` or `AdmitRefusal`, the derived
`Runner` group regenerates (`src/Effect4/Api/RunnerDerived.lean`; both types are in its manifest
type list) and `tools/Effect4Gen/guards/runner.lean`'s refusal samples grow.

**Step 1 — beside (library).**
- New `src/Effect4/Program/Sites.lean` (imports `Effect4.Program.Typing`): `envStep`, `envAt`,
  `siteDecl`.
- `src/Effect4/Program/Typed.lean`, after `Val.hasTy` (`:34-101`): `FitReason`, `FitRefusal`,
  `declFits`, `Val.fitsAt`, `Val.fits`. (Its exit arm names the failure constructor explicitly;
  every other type falls back to `Val.hasTy`.)
- `src/Effect4/Program/Admit.lean`: `Refusal` (`:46-55`) gains `handleDecl`; new `fiberDecl`
  (reads `m.fiber? id` and its origin), `declClause`, `admitDeclared` beside `admit`
  (`:77-92`), `EnvelopeDeclared` and `acceptReplyDeclared` beside `Envelope`/`acceptReply`
  (`:183-194`), with the five `acceptReply_*` laws restated beside `:196-243`.
- `tools/Conform/Effect4/cases-policy.json`: entries for `Effect4.Program.Val.fitsAt` (Ty,
  default, covering `never unit nat int string bool handle causeOf lit refOf deferredOf var
  unknown`), `Effect4.Program.envStep` (Eff, default) and `Effect4.Program.admitDeclared`
  (NativeOp, default, the cover `admit` has).
- `tools/Tools/ArchitectureRoles.lean`: role entries for the new modules (the map checks the
  register for totality).
- The traversal census will list `envStep`, `siteDecl` and `Val.fitsAt` as hand matches. Their
  connectors are step 2's theorems.

**Step 2 — connect (laws and tests).**
- New `src/Effect4/Laws/Program/Typing/Sites.lean`: this folder's `Sites.lean` (17 theorems).
- `src/Effect4/Laws/Program/Admit.lean`: this folder's `Research/Pass/FiberSlice/Proofs.lean`, renamed
  (`admit_of_admitDeclared`, `admitDeclared_eq_of_fiberFree`, `acceptReply_of_acceptReplyDeclared`,
  `envelopeDeclared_fits`, `fitsAt_hasTy`, `fitsAt_none_of_hasTy`, `fitsAt_narrower`, …).
- Tests: the forged reply as a registered counterexample (`E4-HOST-CE-007`, the id the
  host-answers note proposed) in `Test/Counterexamples/` with its `REGISTER.md` row; the
  `LivePath` scenarios as a battery; the declaration lane beside `ExitTypeLane`; `Test/All.lean`.
- Root import: `src/Effect4/Laws.lean` gains the new law module, at the coordinator's anchor.

**Step 3 — move the callers.**
- `src/Effect4/Api/HostSession.lean:171`: `acceptReply table s.machine` →
  `acceptReplyDeclared program table s.machine` (docstring `:160`).
- `src/Effect4/Program/Admit.lean:118`: `admit table m decision` → `admitDeclared program table
  m decision` inside `replayCheckedFrom`; this moves `Api.replayChecked` (`Api.lean:354-363`)
  with no change to its signature.
- Laws restated with the declared envelope or admission:
  `Laws/Api/HostSession.lean:12` (`preflight_envelope`), `:196`, `:219`, `:228`;
  `Laws/Run.lean:404`, `:421`, `:442`, `:625-650` (`Reactor.Envelops` gains the program;
  `drive_envelope`, F13), `:724`;
  `Laws/Program/Admit.lean:68`, `:109`, `:364`, `:438`, `:484`, `:497`, `:533` (each takes
  `admit … = none`; the declared versions get it from `admit_of_admitDeclared` in one line);
  `Laws/Program/Handles/Evaluation.lean:354-359`.
- Tests: `Test/Program/HostSpecContract.lean:217-256` (the envelope calls gain the program);
  names in `Test/Api/ExternalContract.lean:121` and `Test/Run/RunContract.lean:176`.
- The origin ledger: if it has landed, `fiberDecl` reads `m.originOf id`; if not, `fiberDecl`
  is one more reader on the ledger plan's step-3 checklist.

**Step 4 — delete.** `admit` (`:77-92`), `Envelope` (`:183-188`), `acceptReply` (`:192-194`),
their laws (`:196-272`) and `admit`'s case-site entry go. `admitAnswer` (`:59-75`) either stays
as the row-level shape and liveness part the new admission calls, or takes the `decl` argument
and becomes the one admission (preferred). An optional mechanical commit renames the declared
functions to the old names. `fiberOf` leaves path A's refused kinds.

**Generated groups.** Steps 1-4 regenerate nothing:
- `lcnf`: the admission is not reachable from the roots (F7), and `Val.hasTy`, `externalValue`
  and `prepareExternalAnswer` are unchanged.
- `derived`: `Program.Refusal` is in no manifest group; `HostSession.Refusal` is unchanged.
- `eff`, `wire`, `cas`, `ts`, `readme`, `truth`, `host-protocol`, `schema-ts`, `census`: none reads
  admission. The host-protocol projection has no refusal alphabet, and `check-keyed.ts:39` only
  tests that a status starts with `refused:`.
- `architecture`: an on-demand report; it needs the role entries above.
Two options would regenerate the derived `Runner` group: step 0 if it extends `TableRefusal` or
`AdmitRefusal`, and carrying the admission reason in the session phase (§7, P4).

## 5. Task 3: the slice's theorems, exactly

The runtime check and the typed guarantee are separate layers. Everything in §5.1 is proved on
the prototype and depends on neither M6 nor DI-57, so the runtime check can land first.

### 5.1 Runtime check — no M6, no DI-57 (proved, prototype names)

Receipt: an accepted submit establishes the envelope at the receipt state, and the prepared
value fits the row under the derived declarations.

```lean
theorem preflightD_envelope {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision)
    (h : preflightD s reply = .ok decision) :
    ∃ bound, s.active.find? (fun b => b.key == reply.key) = some bound ∧
      reply.callId = bound.call.callId ∧
      EnvelopeD program table s.machine (bound.record reply) ∧
      decision = .answerAsync bound.call.fiber bound.token reply.completion

theorem envelopeD_fits (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (v : Val) (henv : EnvelopeD program table m r)
    (hc : r.completion = .ofExit (.success v)) :
    ∃ i row allocated prepared, r.op = .external i ∧
      requestOf m r.fiber r.token = some (r.op, r.request) ∧
      externalRow table i = some row ∧
      externalValue row.answer m.state.externals.allocated v = some (allocated, prepared) ∧
      fits (fiberDecl (nativeSignature table) program m) allocated prepared row.answer = true
```

Application: an applied reply was admitted, with the declaration clause, at the machine it was
applied to.

```lean
theorem applyReplyD_applied {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat)
    (h : (applyReplyD s key fuel).phase = .applied) :
    ∃ reply bound, readReply s.pending key = some reply ∧
      s.active.find? (fun b => b.key == reply.key) = some bound ∧
      EnvelopeD program table s.machine (bound.record reply)
```

The fiber clause, the declaration, and the bridge to the proof world:

```lean
theorem fitsAt_fiberOf (decl : FiberId → Option EffTy) (allocated : List String) (p : List Nat)
    (v : Val) (a e : Ty) :
    fitsAt decl allocated p v (.fiberOf a e) = none ↔
      ∃ id, v = Value.fiber id ∧ declFits (decl ⟨id⟩) a e = true

theorem siteDecl_fork (sig : Signature NativeOp) (root : NativeEff) (t : EffTy)
    (ht : typeOfProgram sig root = some t) (site : List Nat) (body : NativeEff)
    (options : Supervision.ForkOptions)
    (hat : Node.at_ (.eff root.expandRefs) site = some (.action (.fork body options))) :
    ∃ env tAct d, envAt sig (.eff root.expandRefs) [] site = some env ∧
      checkAction sig env site (.fork body options) = .ok tAct ∧
      check sig env (site ++ [0]) body = .ok d ∧
      tAct.answer = .fiberOf d.answer d.error ∧
      siteDecl sig root site = some d

theorem envelopeD_fits_table (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (v : Val) (Γ : FiberId → Option EffTy)
    (hagree : Narrower Γ (fiberDecl (nativeSignature table) program m))
    (henv : EnvelopeD program table m r) (hc : r.completion = .ofExit (.success v)) :
    ∃ i row allocated prepared, r.op = .external i ∧
      requestOf m r.fiber r.token = some (r.op, r.request) ∧
      externalRow table i = some row ∧
      externalValue row.answer m.state.externals.allocated v = some (allocated, prepared) ∧
      fits Γ allocated prepared row.answer = true
```

with `Narrower Γ decl := ∀ id d, decl id = some d → ∃ g, Γ id = some g ∧ g.answer.sub d.answer ∧
g.error.sub d.error`. Also proved: `admitD_eq_of_fiberFree` (nothing else changes) and
`acceptReplyD_none_of_acceptReply` (at most once).

Contract §4's "receipt does not promise future applicability" holds by construction:
`applyReply` re-runs the preflight. For a fiber answer the verdict can change between receipt
and application only if the park goes, the allocation table grows (allocation rows only), or a
fiber's origin changes; `fiberDecl_congr` shows declarations move only with origins.

### 5.2 Typed guarantee — depends on M6; on the keyed route also DI-57

`Typed.lean` elaborates these against `Laws/Program/Typed` (the world, `RState`, `TypedState`),
so the statements are exact.

```lean
/-- `fiberDecl` over any instantiation of the machine; `fiberDeclOf_native` (proved) says it is
`fiberDecl` at the native machine. -/
def fiberDeclOf {κ φ η : Type} (sig : Signature NativeOp) (root : NativeEff)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores κ φ η) (id : FiberId) :
    Option EffTy

/-- The fiber part of `RegistryAgrees` (contract §3). -/
def FiberRegistryAgrees (root : ProgramSource) (w : Typed.World) (m : RState) : Prop :=
  Proofs.Narrower w.Γ (fiberDeclOf (nativeSignature root.table) root.program m)

/-- The fiber clause B3's constructor-complete `StrongValue` needs. -/
def StrongValueFibers (w : Typed.World) (ty : Ty) (v : Val) : Prop :=
  ValueOk w ty v ∧ fits w.Γ w.state.externals.allocated v ty = true ∧ HandlesLive w v

-- T1, wanted (M6):
theorem typedState_fiberRegistry (root : ProgramSource) (rootTy : EffTy) (w : Typed.World)
    (m : RState) :
    ProofGraph.Obligation (TypedState root rootTy w m → FiberRegistryAgrees root w m) := ⟨⟩

-- T2, proved from T1:
theorem admitted_value_strong (root : ProgramSource) (w : Typed.World) (m : RState) (ty : Ty)
    (v : Val) (hreg : FiberRegistryAgrees root w m)
    (hfits : fits (fiberDeclOf (nativeSignature root.table) root.program m)
      w.state.externals.allocated v ty = true)
    (hty : Val.hasTy v ty w.state.externals.allocated = true) (hlive : HandlesLive w v) :
    StrongValueFibers w ty v
```

So the boundary owes nothing more for fibers once M6 supplies T1: the runtime check's verdict
(`envelopeD_fits`, proved) becomes the world's fiber clause through `fits_narrower` (proved).

| Statement | Depends on |
| --- | --- |
| §5.1, all | nothing beyond the prototype (proved) |
| `admitted_value_strong` | T1 only, as a hypothesis (proved) |
| T1 `typedState_fiberRegistry` | M6's `TypedState` and its preservation; `PointTyped` strengthened to type a source point at `envAt`'s environment (today it quantifies over any environment, so the world's `Γ` at a fork could be wider than the declaration, and `Narrower` would fail); the origin ledger's lookup facts (origins never change, fibers are never removed) |
| `StrongValueFibers` as `StrongValue`'s fiber clause | B3, the membership amendment: today's `HandlesFit` skips products, Results and successful exits, so it neither needs nor uses this clause |
| `AnswerOk` for an admitted fiber answer | T1, B3, and the typed state declaring the external park's token (`Θ`) at the row's answer |
| typed execution on the keyed session | DI-57: the session steps the native machine and M6 is about the reference machine `RState` (or M6 restated natively); the session's answers reach M6 only through that relation |

## 6. Task 4: path A once fiber declarations land

| Kind | Live typing hole today? | Closed by fiber declarations? | What closes it | Path A needed after the slice? |
| --- | --- | --- | --- | --- |
| fiber (`fiberOf`) | yes (host-answers probe; F1) | yes | this slice | no |
| context (`Ty.context`) | yes (F8) | no | a static services clause in `fitsAt`: every service fits its key's type (`nativeServiceTy`); no registry | yes, until that clause lands |
| deferred (`Deferred<number, number>`, `deferredOf`) | yes: a layer's memo deferred read as a number (F9); `deferredOf a e` unchecked | no | deferred declarations from their creation sites: `deferredMake` gives `(nat, nat)`, `memoBuild` the layer's types — a creation record like the fork ledger | yes |
| cell (`refOf t`) | the certified type is wrong, no wrong read (F10) | no | a cell clause: every cell today is a number cell, so `refOf t` fits a cell iff `t` is `nat` both ways; generic cells (rows 42-44) then need creation-site declarations | yes, until that clause lands |
| cell (`Ref<number>` spelling) | no: aliasing only (F10) | — | authority rule (row 7, contract §3 correspondence) | not for typing |
| scope (`Ty.scope`) | no (F11) | — | authority rule | not for typing |
| memo map, handles under `unknown` | no (F12) | — | contract §3's `unknown` clause (authority) | no |

Recommendation: land path A for every internal kind now (it breaks nothing in the tree), then
lift it kind by kind as each kind's evidence lands — fibers with this slice, contexts with the
services clause (one arm of the same recursion, cheap), cells with the constant cell clause,
deferreds with a deferred creation record, scopes when the owner rules on authority. This is
stricter than row 7's open recommendation for scopes and number cells, which are type-safe; the
owner may prefer to allow those two now and keep path A for contexts, deferreds and `refOf`.

## 7. Proposals

P1. The slice as §4, with these library signatures (the prototype's, made `Op`-generic where
they can be):

```lean
-- src/Effect4/Program/Sites.lean
def envStep (sig : Signature Op) (env : TyEnv) : Node Op → Nat → Option TyEnv
def envAt (sig : Signature Op) : Node Op → TyEnv → List Nat → Option TyEnv
def siteDecl (sig : Signature Op) (root : Eff Op) (site : List Nat) : Option EffTy

-- src/Effect4/Program/Typed.lean
inductive FitReason
  | shape (expected : Ty)
  | fiberDecl (handle : FiberId) (expected : Ty)
deriving DecidableEq, Repr
structure FitRefusal where
  path : List Nat
  reason : FitReason
deriving DecidableEq, Repr
def declFits (d : Option EffTy) (a e : Ty) : Bool
def Val.fitsAt (decl : FiberId → Option EffTy) (allocated : List String) (p : List Nat)
    (v : Val) : Ty → Option FitRefusal
def Val.fits (decl : FiberId → Option EffTy) (allocated : List String) (v : Val) (ty : Ty) : Bool

-- src/Effect4/Program/Admit.lean
def fiberDecl (sig : Signature NativeOp) (root : NativeEff) (m : NativeMachine) (id : FiberId) :
    Option EffTy
--   Refusal gains: | handleDecl (fiber : FiberId) (token : Nat) (why : FitRefusal)
def admitDeclared (program : NativeEff) (table : RowTable) (m : NativeMachine) :
    NativeDecision → Option Refusal
def EnvelopeDeclared (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) : Prop
def acceptReplyDeclared (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) : Option NativeDecision
```

The production `FitReason.fiberDecl` drops the prototype's `declared : Option EffTy` field
(`EffTy` has no `Repr`, and `Refusal` derives one).

P2. Register the counterexamples: the forged fiber (`E4-HOST-CE-007`), and, if the coordinator
agrees, the forged context (F8), the layer deferred read as a number (F9) and the `refOf`
mislabel (F10) under the next free ids.

P3. A decisions row for the host boundary's handle rule, proposed for the coordinator: fibers
admitted by derived declaration; contexts by the static services clause; cells and deferreds
refused (path A) until their creation-site declarations; scopes and number-cell aliases left to
the authority rule (row 7).

P4. Separately: carry the admission's reason in the session phase,
`HostSession.Refusal.envelope (why : Program.Refusal)`. It makes every envelope refusal located
on the canonical route. It regenerates the derived `Runner` group (`Program.Refusal` and
`FitRefusal` join its manifest list) and restates `Laws/Run.lean:301` and `:639`.

P5. Strengthen `PointTyped` (`Laws/Program/Typed/Admission.lean:92-96`) to type a source point
at `envAt`'s environment, so M6 can prove `typedState_fiberRegistry`. `envAt_checks` already
shows that environment exists at every node of a checked program.

## 8. Open questions

1. P4 (reason in the phase): now, with this slice, or with the lane's X2?
2. Internal forks at the top only, or declared too? The registry seat declares every fiber of
   the lane; for a host, naming a finalizer or a layer build is odd, and the top rule is exact.
3. `siteDecl` reads the expanded program (as `typeOfProgram` does); `PointTyped` reads the
   unexpanded one. They agree on programs with no layer reference
   (`expandRefs_eq_self_of_refSites_nil`). Which should the typed state use?
4. The declaration is exactly as sound as the checker's rule at the site. The registry seat's
   layer findings (a layer body checked at `[]` but built with the enclosing environment; a
   layer leaf's value never compared with its key's type) would reach forks inside layer bodies.
5. Authority: may a host hand the program its own scope or number cell (F10, F11)? That is
   row 7 and contract §3's capability correspondence, not typing.
6. Deferred creation record: a separate list on the stores (like the fork ledger), or a tag on
   the memo entry? Needed before path A lifts for deferreds.

## 9. Commands and results

One script runs everything through the one-compiler lock (`serial.sh`):

```
bash docs/research/2026-09-30-pass/fiberslice/run.sh
```

It builds two modules' oleans inside this folder (`.build/`), then checks each probe against
them:

```
bash <scratchpad>/serial.sh lake env lean -M6144 -DwarningAsError=true \
  -R docs/research/2026-09-30-pass/fiberslice \
  -o docs/research/2026-09-30-pass/fiberslice/.build/Research/Pass/FiberSlice/Core.olean \
  docs/research/2026-09-30-pass/fiberslice/Research/Pass/FiberSlice/Core.lean
bash <scratchpad>/serial.sh env LEAN_PATH=<repo>/docs/research/2026-09-30-pass/fiberslice/.build \
  lake env lean -M6144 -DwarningAsError=true -R docs/research/2026-09-30-pass/fiberslice \
  -o docs/research/2026-09-30-pass/fiberslice/.build/Research/Pass/FiberSlice/Proofs.olean \
  docs/research/2026-09-30-pass/fiberslice/Research/Pass/FiberSlice/Proofs.lean
LEAN_PATH=<repo>/docs/research/2026-09-30-pass/fiberslice/.build \
  bash <scratchpad>/serial.sh lake env lean -M6144 -DwarningAsError=true \
  docs/research/2026-09-30-pass/fiberslice/<Probe>.lean
```

(`lake env` appends an existing `LEAN_PATH`, checked with `LEAN_PATH=/tmp/xyz lake env printenv
LEAN_PATH`.) Final run: every command exit 0, about 50 s. Logs in `logs/`:

| File | Content | Result |
| --- | --- | --- |
| `Research/Pass/FiberSlice/Core.lean` | prototype definitions (built as a module) | exit 0 |
| `Research/Pass/FiberSlice/Proofs.lean` | 31 theorems (built as a module) | exit 0 |
| `LivePath.lean` | task 1 live path, nestings, binders, red controls (45 guard lines, one pinned with `#guard_msgs`) | exit 0 |
| `Sites.lean` | 17 theorems | exit 0 |
| `Typed.lean` | the typed layer: 2 theorems, 1 wanted obligation | exit 0 |
| `Replays.lean` | the three batteries and the fiber row through the prototype (25 guards, 96,556 journals) | exit 0 |
| `Holes.lean` | task 4 (23 guards) | exit 0 |
| `DeclLane.lean` | the declaration lane and the arity check | exit 0; prints `declaration lane: 8584 programs, 34336 runs, 35744 forks: 28918 source forks with a declaration, 2626 layer builds, 4200 with no site; 28034 exited source forks checked, 0 violations` |

Axiom output (`logs/Proofs.log`, `logs/Sites.log`, `logs/Typed.log`): 44 theorems `depends on
axioms: [propext, Quot.sound]`; `firstRefusal_none`, `noFiber_some`, `noFiber_fiber`,
`externalValue_result` and `noFiber_prepared` depend on `[propext]`; `firstRefusal_of_all_none`
depends on no axioms. No `sorry`, `axiom`, `native_decide`, `partial`, `unsafe` or
`implemented_by` in any file (grep).

Red controls kept as fixtures: `LivePath.lean` §4 (the forged run finishing with `"wrong"`
through the prototype fails, pinned under `#guard_msgs`; a lying registry accepts every forged
nesting; the empty-environment registry refuses an honest reply under a binder), `Replays.lean`
(some forged journal differs), `DeclLane.lean` (declarations replaced by `never` are caught).

Other commands, all read-only: `git log`, `git diff --stat be15b062..HEAD`, `grep`/`sed` over
`src/`, `Test/`, `ocaml/`, `harness/`, `tools/`, and one dry run `make -n check-cases` (it
printed `python3 scripts/check-conform.py cases`; nothing ran).
