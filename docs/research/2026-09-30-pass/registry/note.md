M6's capstone is false even with no host answer, because of two layer typing gaps (kernel-checked in `LayerGap.lean`); separately, every fiber's declared type can be derived from its recorded site, the admitted program and the checker, with one three-valued field added to the fork record.

# Registry seat: fiber declarations from creation sites

Status: research probes and a proposal. Base `be15b062` on `refactor/phase1-phase3`. Nothing in
the tree was changed. Every probe exits 0; commands and axiom output are in §12.

Evidence words: **proved** means a kernel theorem at `[propext, Quot.sound]` or fewer axioms.
**Tested** means a finite check (`#guard`, or a counted run over a finite set). **Reading** means
I read the code and did not check it by machine. **Assumed** means I did not check it at all.

## 1. The answer

**Yes: a fiber's declared type (answer and error) can be derived at run time, and no type is
stored in any value.**

- **Root.** The declared type is the admitted program's type (`Api.typeOf`).
- **Source fork** (`fork`, `forkIn`, `forkScoped`). The site the machine records is the action's
  path. The declared type is the checker's type of the forked program at that path, checked in
  the path's static environment. `staticEnvAt` computes that environment; it is a new fold, and
  it is the only new function the rule needs.
- **Race entrant.** The site is the race's list cell. The declared type is the entrant's type
  there, found the same way.
- **Layer sibling build** (`merge`, `mergeAll`). The site is the sibling's layer node. The
  declared type is `unknown` for the answer and the layer's error type for the error.
- **Finalizer daemon** (a parallel scope close). It has no site. Its declared type is
  `unknown` for the answer and `never` for the error.

Data the machine already records is enough for native programs today. There is one inference:
an empty site means "finalizer". It holds only by a census of the code (§2). Recording which of
`spawn`'s three callers made the fiber removes that inference. The cost is one field, `kind`, in
the fork record the ledger plan already proposes (§6).

What stands behind this:

- **Proved** (`Proofs.lean`): in a well-typed program the fold is defined along every path, and
  the node it reaches checks in the fold's environment. So the registry has an answer at every
  fork site, race cell and layer node, and a fork's declared type is exactly the `fiberOf` the
  checker gives its handle.
- **Tested** against the real checker: 0 disagreements on 6662 program paths (2010 of them
  under a binder), and 0 failures on 10728 fork sites. Eleven deliberately wrong folds were all
  caught.
- **Tested** on 34,336 lane runs: all 70,080 fibers are declared, and every exited fiber fits
  its declaration. That includes 2,107 exits that hold fiber handles, each checked against the
  declaration of the fiber it names.

**The same test found a real soundness hole**, not in the registry but in layers (§5). A checked,
closed program with no host rows can exit with a value outside its checked type, on the native
machine and on the reference machine that M6 is stated on. This is **proved**, including the
refutation of `typedState_reachable` itself for these programs, on a tape that applies no host
answer. The M6 repair the host-answers note proposes (count only runs that apply no host answer,
its §4) does not reach these programs.

## 2. Every fiber creation site (task 1)

`spawn` (`Machine/Fibers.lean:924-939`) is the only function that creates a forked fiber. It
stamps `.forked parent.id options.daemon site` (`:935`), and `Fibers.lean:224-231` documents the
site. Three roots create fibers without `spawn`. Reading of the code; `Sites.lean` pins one run
of each native construct (tested).

| Creator | Where | Site recorded | Construct | Class |
| --- | --- | --- | --- | --- |
| `Api.load` | `Api.lean:255-260` | origin `.root` (id 0; `RunFiber.make`'s default, `Fibers.lean:272`) | the program. Used by `replay`, `run`, `replayChecked`, `HostSession.start` (`Api/HostSession.lean:138`) and `Run.lean:107` | root |
| `runFork` | `Fibers.lean:2183-2189` | `.root` | `runSyncExit` (`:2205-2212`): `Api.runSync` (`Api.lean:324-330`), `Provision.lean:397` | root |
| `runCallback` | `Fibers.lean:2193-2200` | `.root` | no caller outside the laws and one witness (`Laws/Machine/Witnesses.lean:1152`) | root |
| `fork` arm | `Fibers.lean:1212-1222` | the action path `q.path` (`Program/Compile.lean:987`) | `withFiber (fork …)` | source |
| `forkIn` arm | `Fibers.lean:1223-1230` | the action path (`Compile.lean:988-992`) | `withFiber (forkIn …)` | source |
| `forkIn` arm, reached from `forkScoped` | same | the `forkScoped` action path (`forkScopedAt`, `Compile.lean:1053-1057`) | `withFiber (forkScoped …)`. It compiles to the scope-service read (`:994`), then `forkIn`; the machine's own `forkScoped` arm (`Fibers.lean:1231-1242`) is never reached in native | source |
| `fork` arm, reached from `forkLayer` | same | the sibling's **layer** path (`Compile.lean:1453-1455`; `merge` child `:1164-1166`, `mergeAll` spine child `:1187-1189`) | a `merge`/`mergeAll` sibling build | located at a source node, but not a fork action |
| `launchEntrant` from `Cmd.launch` | `Fibers.lean:955-959`, `:1852-1869` | the race's list cell: `race.nextSite`, which starts at the `effs` path (`Compile.lean:1030`, `Fibers.lean:904`) and gains `[1]` per launch (`:1867`) | a `raceAll` entrant | source |
| `forkFinalizers` from `closePar` | `Fibers.lean:965-971`, `:1311-1316` | `[]` (`:969`) | a scope with the parallel strategy and at least two finalizers, closed. The route is `storesCloseScopeUnsafe` (`Machine/Stores.lean:1917-1923`) → `closeWalk parallel` (`:1872-1873`) → `ActionName.closePar` (`:2115`) → `embedAction` (`Compile.lean:387-410`) | internal |
| stores-alphabet `fork`/`forkIn`/`forkScoped` | `Stores.lean:2089-2093` | `[]` | `ProgName.forkThen`/`forkOnly`/`forkInScope`/`forkScopedOf`. Never reached from native code: the native compile embeds only completion, finalizer, cancel, race-settle, interrupt and close-walk programs, none of which fork (reading) | internal, not native |
| stores-alphabet `raceAll` | `Stores.lean:2104` | `none`, read as `[]` at launch | `ProgName.raceOf`. Never reached from native code (reading) | internal, not native |

The shared helpers `FiberAction.fork`/`forkIn`/`forkScoped`/`closePar` (`Fibers.lean:1424-1480`)
are the same three callers for the reference evaluator (`Laws/Program/EvaluateR.lean:237-292`).
It passes its denotation's sites, which I did not enumerate.

**Findings from the census** (tested in `Sites.lean`):

- **Layer builds record a site that is not a fork site.** `merge` and `mergeAll` fork one build
  per sibling, at the sibling's layer path. `Api.supervision` lists action and race-cell sites
  only, so it does not list these.
- **A merge of two or more siblings forks finalizer daemons at close.** When the provided scope
  closes, the merge's parallel parent scope closes through `closePar`: three empty-site daemons
  per merge in the probe. A `mergeAll` of one layer leaves one finalizer, which runs without a
  fork (`Stores.lean:1920-1923`).
- **A running layer build reads as an unpinned daemon.** While a sibling build is running,
  `Api.unpinnedDaemonsAlive` reports it (`slowMerge`), so `daemonsQuiet` is false while any layer
  builds.
- **The site omits the root index.** The recorded site drops `Point.root` (`Compile.lean:70-73`).
  This is harmless while a machine holds one root, and it becomes ambiguous if a machine ever
  holds several.

## 3. The static environment at a path (task 2)

`staticEnvAt sig root path` (`Core.lean:32-104`) is a fold along the path. Each step,
`stepEnv`, applies the checker's environment rule for the node it leaves and the child it takes:

- `bind` appends the first program's answer;
- a handler, and `matchCause`'s cause arm, append the cause type;
- `catchIf`'s handler appends the error type;
- `select` appends its arm's bindings;
- `onExit` appends the exit type;
- `iterate` appends the cursor type;
- a release appends the acquired value and `exitOf unknown unknown`;
- a statement list appends a statement's bindings;
- `whileTrue` sets the loop flag;
- every layer node, and a layer's effect body, starts from `[]`.

The fold computes a sibling's type by calling the checker itself. Programs are checked with their
layer references expanded, as `typeOfProgram` does. A reference is a leaf, so every other node
keeps its path (`Refs.lean:127-182`, reading).

**How I validated it** (`StaticEnv.lean`, tested):

1. **An oracle that uses nothing of the fold.** To read the environment the checker uses at path
   `p`, I replace the node at `p` with `withFiber (closeScope (var i) (var i))` and run
   `Checker.check` on the whole program. That node always refuses, and the refusal names level
   `i`'s type (`exitExpected` or `scopeExpected`) or says level `i` is unbound (`term`).
   - The replacement does not change the environment at `p`. Every rule computes a child's
     environment from the parent and the siblings checked before it, never from the child.
   - The checker stops at its first refusal. In a well-typed program, that is the probe's.
   - The probe also checks the refusal's path, `p ++ [0]`. So the checker's path numbering is
     the numbering `Node.at_` and the machine's sites use.
2. **Every program node of the typed corpus.** 1349 programs, 6662 program paths, 2010 of them
   under a binder: 0 disagreements.
3. **Every fork site and race cell of the corpus and its interleaving pairs.** 8457 programs and
   10728 sites (6200 race cells, 1300 sites under a binder).
   - The environment at the forked program agrees with the oracle.
   - A declaration exists.
   - Where the fork is the first child of a `bind`, the oracle reads the continuation's last
     level. That is the handle type the whole-program check itself assigns, and it equals
     `fiberOf` of the declared answer and error, at 3959 sites.
   - 0 failures.
4. **Fifteen binder forms** (`Core.lean:291-318`): `bind`, `gen`, `catchCause`, `catchIf`,
   `select`, both `matchCause` arms, `onExit`, `iterate`, `acquireRelease`, a layer body under an
   outer binder, `provideService`, `forkIn`, `forkScoped` and a nested fork. Each has a fork whose
   body reads the binder. All are typed, all are declared at the expected answer, and the oracle
   agrees at every node.
5. **Red controls.** Eleven wrong folds, each with one rule broken, are all caught. Disagreement
   counts:

   | Broken rule | Disagreements |
   | --- | --- |
   | `bindRest` | 1465 |
   | `gen` | 8 |
   | `catchHandler` | 197 |
   | `catchIfHandler` | 25 |
   | `selectArm` | 25 |
   | `matchValue` | 26 |
   | `onExitFinalizer` | 177 |
   | `iterateCursor` | 36 |
   | `releaseEnv` | 101 |
   | `layerInherits` | 18 |
   | `stmtBinds` | 2 |

   Two rules have thin coverage in the corpus: `stmtBinds` (2) and `gen` (8).
6. **Proved** (`Proofs.lean`):
   - `stepEnv_checks`: one case per clause of `Node.child`, 53 in all.
   - `envAlong_checks` and `staticEnv_checks`: if the root checks, the fold is defined along
     every path and the node reached checks in the fold's environment.
   - `fork_handle`: at a fork site, the declaration `d` exists and
     `checkAction env site (fork body o) = ok ⟨fiberOf d.answer d.error, never, d.requires⟩`.
   - `api_fork_handle`: the same, from `Api.typeOf program table = some T` (bridged by
     `check_of_typeOfProgram`).

   This proves the fold is sound: the child checks in the environment the fold gives. That it is
   *the* environment the checker's recursion passes is true by construction and tested by the
   oracle; it is not proved (§9, proposal 6).

## 4. Every fiber's declared type, derived and tested (task 3)

`Declared.lean` drives the exit-type lane's runs: `lanePrograms` × `tapes`, with the lane's host
replies (`Test/Program/ExitTypeLane.lean`). For every fiber of every final machine it classifies
the fiber by its origin, derives a declared type (`fiberDecl`, `Core.lean:224-230`), and checks
the exit two ways:

- **coarse**: the lane's own `fits`;
- **deep**: path C's `fitsB`, reading the registry itself for nested fiber handles.

Tested; 34,336 runs and 70,080 fibers:

| Class | Fibers | Declared | Exited | Coarse fit | Deep fit | Exits holding a fiber handle |
| --- | --- | --- | --- | --- | --- | --- |
| root | 34336 | 34336 | 31892 | 31892 | 31892 | 1263 |
| source fork | 16144 | 16144 | 15876 | 15876 | 15876 | 442 |
| race entrant | 12774 | 12774 | 12158 | 12158 | 12158 | 402 |
| layer build | 2626 | 2626 | 2626 | 2626 | 2626 | 0 |
| finalizer | 4200 | 4200 | 4200 | 4200 | 4200 | 0 |
| unrecognized site | 0 | | | | | |

**Red controls.** Each wrong registry must fail the same lane, and each does:

| Wrong registry | Violations |
| --- | --- |
| every fiber declared at the root's type | 13193 |
| forks typed at the empty environment (path B's first probe) | 348 |
| finalizers declared to answer `never` | 4200 |
| layer builds declared at `Ty.context` (the build answers an encoded service spine, which no `Ty` names) | 2626 |

**Deep-check controls.** Over the 2107 exits that hold fiber handles:

- with no registry, all 2107 fail;
- reading the registry at the wrong id, 2095 fail;
- with the registry itself, 0 fail.

**The boundary under a binder.** I reran path B+C of the host-answers probe with the forked
program reading a binder. The registry refuses the forged handle and admits the honest one. At the
empty environment the honest reply is refused too, which is why `staticEnvAt` is needed.

**The fixtures.** The binder forms and layer cases run under every tape. Exactly four runs fail,
all at the fork inside a layer body under an outer binder. That is layer gap 1 (§5): the registry
reports the checker's type, and the runtime breaks it.

## 5. Two layer typing gaps that break the typed guarantee with no host (found by task 3)

Everything in this section is proved in `LayerGap.lean` (`decide +kernel` evaluates the run),
except the printed-text check, which is tested. Neither gap is in
`Test/Counterexamples/REGISTER.md` or `docs/DESIGN-ISSUES.md` at `be15b062`. The exit-type lane
cannot reach them: its layer bodies bind nothing, and every layer value it provides is a number
at a number key.

### Gap 1: a layer body runs in the enclosing environment

The checker checks a layer's effect body in `[]` (`Checker.lean:227-236`). The runtime builds it
at the enclosing point, with that point's runtime environment:

- `provideLayerWithK` builds the layer at `p.child 0` (`Compile.lean:767-781`);
- `constructionAt` builds the body at `q.child 0` (`:741-749`);
- `Point.child` keeps `env` (`:79-80`).

Levels count from the outside. So a body's own binders sit at different levels in the checker
and in the runtime whenever the layer is under an outer binder. The example, `errLeak`:

```
bind (succeed 9) (scoped (provideLayer (effect key (bind (succeed "x") (fail (var 0)))) false (service key)))
```

- It is checked at `(nat, string)`.
- The run fails with the number 9 (`errLeak_native_exit`, `errLeak_violates`).
- The reference machine does the same (`errLeak_reference_exit`, through the proved
  `run_eq_ref_exit`).
- The control without the outer binder fails with `"x"` and fits its type.
- A fork inside the layer body shows it at a forked fiber: its handle is `fiberOf string never`,
  and it returns 9 (`forkLeak_*`).

**The printed TypeScript agrees with the checker** (tested). The printer names the body's binder
`a0`, shadowing the outer `a0`, so by JavaScript scoping `Effect.fail(a0)` fails with `"x"`. That
last step is a reading of the printed text; I did not run it under TypeScript. So the checker and
the TypeScript face agree, and the Lean runtime (and the OCaml engine compiled from it) disagree.

### Gap 2: a layer leaf's value is never compared with its service type

`checkLayer`'s `succeed` and `effect` rules never compare the provided value with
`sig.serviceTy key` (`Checker.lean:228-233`). `LayerTy.out` records keys only, and
`service key` answers the table's type (`:215-217`).

- `valueLeak` is checked at `nat` and answers `"x"`.
- `succeedLeak` is checked at `nat` and answers `true`.
- The control, a number at the number key, fits.

TypeScript's own checker would reject `Layer.effect(Service<number>, succeed("x"))`. That is
assumed: I did not run `tsc`.

### M6's capstone is refuted for each gap

`m6_capstone_false_without_hosts` and `m6_capstone_false_valueLeak` refute
`typedState_reachable` (`Laws/Program/Typed/Assembly.lean:224-227`), specialized to each program
and its reached machine. They use the plan review's technique (the `exit` field of `preds`,
`Assembly.lean:54`, and `WorldValid.root`, `Validity.lean:34`).

- The tape is `[evaluate, flush]`, and `tape_answers_nothing` is proved. So restricting
  `RReachable` to tapes that apply no host answer, as the host-answers note's §4 proposes, does
  not exclude these runs.
- They refute an open target. No accepted theorem is contradicted.

## 6. Internal forks and the ledger record (task 4)

**Which constructs fork with no source site, and their declared types by construction:**

- **Parallel-close finalizer daemons** (`forkFinalizers`, the only native one).
  - What makes them: scopes created with `scopeMake parallel`, and every `merge`/`mergeAll`
    parallel parent scope (`Compile.lean:725-732`), when closed with at least two finalizers.
  - Declared type: `⟨unknown, never⟩`. The answer is discarded (`Cmd.closeParAwait` feeds
    `exitAsVoidAll`), hence `unknown`. The error is `never` because a release cannot fail with a
    typed error (`releaseFails`, `Checker.lean:201-210`), and the other finalizer programs only
    interrupt, close, remove or complete (`finProgram`, `Stores.lean:1769-1795`); that last part
    is a reading.
  - Tested: all 4200 in the lane fit. The `never`-answer control fails 4200.
- **Layer sibling builds.** These do record a site, the layer node.
  - Declared type: `⟨unknown, the layer's error⟩`. The answer is an encoded service spine that
    no `Ty` names; `Val.hasTy _ Ty.context` refuses it (tested).
  - Tested: all 2626 fit. The `Ty.context` control fails 2626.
- **The stores alphabet's forks and races.** Not reachable in native code. No declaration is
  needed for the API.

**The proof side needs these declarations anyway.** `WorldValid.fibers` (`Validity.lean:21`)
requires a `Γ` entry for every fiber, and that includes finalizer daemons and layer builds.

**The ledger record, exact:**

```lean
namespace Effect4.Machine

/-- Which caller of `spawn` made a forked fiber. -/
inductive ForkKind
  /-- `WithFiberAction.fork`/`forkIn`/`forkScoped` (`Fibers.lean:1212-1238`, and the shared
  `FiberAction` helpers): the site is the action node, or a layer node for a layer sibling
  build. -/
  | action
  /-- `launchEntrant` (`:955-959`): the site is the race's `effs` cons cell. -/
  | raceEntrant
  /-- `forkFinalizers` (`:965-971`): a parallel scope close's daemon; the site is `[]`. -/
  | finalizer
deriving DecidableEq, Repr

/-- One record per forked fiber, appended by `spawn` beside the `forked` event
(the fork-ledger plan's record, §3, with `kind` added). Roots get no record. -/
structure ForkRecord where
  child : FiberId
  parent : FiberId
  daemon : Bool
  site : List Nat
  kind : ForkKind
deriving DecidableEq, Repr
```

**What changes in the machine:**

- `RunMachine` gains `forks : List ForkRecord`.
- `spawn` gains `(kind : ForkKind)` and appends
  `⟨⟨m.nextId⟩, parent.id, options.daemon, site, kind⟩` in the same step as the event.
- The three callers pass a constant each: the fork arms and the `FiberAction` twins pass
  `.action`, `launchEntrant` passes `.raceEntrant`, `forkFinalizers` passes `.finalizer`.
- Each caller's constant is a local fact, so no census is needed.

**Why the kind is not finer.** The site's node already says `fork`, `forkIn`, `forkScoped`, race
cell or layer. The kind records only what the site cannot: which `spawn` caller ran. A layer build
goes through the `fork` arm, so the machine could not record "layer" anyway.

## 7. Cells and deferreds (task 5)

Tested (`Cells.lean`):

- **The stores keep values, not creation sites.** The Ref heap is the values in allocation order
  (`RefHeap := List Val`, `Stores.lean:841`); a deferred cell is a completion plus waiters.
- **The compile drops the site.** A `perform` at point `p` becomes
  `Prim.sync (EffThunk.op operation)` (`Compile.lean:574-586`), and `SyncOp.refMake` carries only
  the initial value.
- **Memo deferreds already follow the pattern.** A `MemoEntry` is keyed by its layer's path
  (`SyncOp.memoBuild q.path`) and holds its deferred's key. The path names a layer node whose
  checked signature gives the error column.

**What the same pattern needs for the generic cells of decisions rows 42-44:**

1. **Record the creation site at the allocating step.** A cell ledger, `(key, site)` appended by
   `refMake`/`deferredMake` in the same step as the allocation, like the fork ledger. The site
   must reach the store step: today `EffThunk.op` carries no point, so the op or the thunk has to
   carry the perform's path.
2. **A `Ref` declaration from the request's type at the site.** With the template row
   `Ref.make : A → Ref<A>`, `rowTy` gives `refOf A` from the initial value's static type, which
   `staticEnvAt` and the request term supply (tested).
3. **A `Deferred` declaration written at the site.** `Deferred.make<A, E>()` takes `void`, so
   the template's parameters stay unbound and instantiate to `never`: `rowTy` gives
   `deferredOf never never` (tested). The creation site must carry `A` and `E`. The natural place
   is the operation itself, as `refUpdate` carries its `FnName` today, for example
   `NativeOp.deferredMake (answer error : Ty)`.
4. **Exact comparison at a boundary.** `refOf` and `deferredOf` are invariant (decisions row 55,
   `Ty.lean:453`), so a cell handle's declaration must equal the expected type; subtyping is not
   enough. Today's shape check accepts any cell handle at any `refOf` (tested).
5. **Invariance after creation.** The template rows already bind the handle's position first
   (`Ty.infer`), so writes are checked against the cell's type. The registry must also agree with
   `Ρ`/`Π` at creation, which is the contract's `RegistryAgrees`.

## 8. What is proved

`Proofs.lean`:

- `stepEnv_checks`, `envAlong_checks`, `staticEnv_checks`;
- `fork_handle`, `api_fork_handle`, `check_of_typeOfProgram`;
- `declared_fork`, `declared_forkIn`, `declared_forkScoped`, `declared_race`, `declared_layer`,
  `declared_finalizer`;
- helpers: `ok_of_bind`, `isSome_of_ok`, `expect_ok`, `term_ok`, `throw_not_some`,
  `stmts_after_ret`.

`LayerGap.lean`: 28 theorems in three groups.

- The checked types: `errLeak_checked`, `forkLeak_checked`, `valueLeak_checked`,
  `succeedLeak_checked`, `errLeak_typeOf`, `valueLeak_typeOf`, `forkLeak_handle`,
  `key_service_nat`.
- The exits, on both machines: `errLeak_native_exit`, `errLeak_violates`,
  `errLeak_reference_exit`, `errLeakControl_exit`, `errLeakControl_fits`,
  `forkLeak_child_exit`, `valueLeak_exit`, `valueLeak_violates`, `valueLeak_reference_exit`,
  `succeedLeak_exit`, `succeedLeak_violates`, `valueControl_fits`.
- The capstone refutations: `m6_capstone_false_without_hosts`, `m6_capstone_false_valueLeak`,
  and their parts (`errLeakTy_closed`, `tape_answers_nothing`, `bad_reachable`,
  `bad_has_bad_exit`, `bad_exit_not_typed`, `bad_not_typed`, `badValue_has_bad_exit`,
  `badValue_exit_not_typed`).

All are at `[propext, Quot.sound]` or fewer (§12). Everything else in this note is tested or a
reading, as marked.

## 9. Proposals, with exact signatures

1. **The ledger record** of §6, with `spawn`'s extra argument:

   ```lean
   def spawn (interp : RunInterp ν σ β ε δ ι α χ St κ) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
       (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
       (options : Supervision.ForkOptions) (site : List Nat) (kind : ForkKind) :
       RunMachine ν σ β ε δ ι α χ St κ φ η × RunFiber ν σ β ε δ ι α χ κ φ × FiberId
   ```

2. **The static environment**, in `Program/` beside the checker (it uses only `Checker` and
   `Node`):

   ```lean
   def stepEnv (sig : Signature Op) (st : TyEnv × Bool) (p : List Nat) :
       Node Op → Nat → Option (TyEnv × Bool)
   def envAlong (sig : Signature Op) : Node Op → List Nat → TyEnv × Bool → List Nat →
       Option (TyEnv × Bool)
   def staticEnvAt (sig : Signature Op) (root : Eff Op) (path : List Nat) : Option TyEnv
   ```

3. **The registry, derived, never stored.** The `root` argument has its layer references
   expanded, as `typeOfProgram` checks it.

   ```lean
   def checkedAt (sig : Signature Op) (root : Eff Op) (site : List Nat) (body : Eff Op) :
       Option EffTy
   def ForkRecord.declared (sig : Signature Op) (root : Eff Op) (r : ForkRecord) : Option EffTy
   /-- Declared type by id: the root's is the admitted type; a forked fiber's is its record's.
   `originOf` is the ledger plan's lookup (none / root / forked record). -/
   def fiberDecl (sig : Signature NativeOp) (root : NativeEff) (rootTy : EffTy)
       (m : NativeMachine) (id : FiberId) : Option EffTy
   ```

   The live session has everything these need: the admitted program, its type and the table
   (`HostSession`'s `admitted`). A per-site table computed once at admission is an optional
   derived view. Its connector would be "table = `checkedAt` at every site", and it saves
   recomputation, which costs at most one check of the program per lookup.

4. **The boundary check.** `fitsB (fiberDecl …) allocated v ty` replaces `Val.hasTy` for success
   values in `externalValue`/`admitAnswer`. This is path C with this registry; its signature is
   `Core.lean:238`. Fibers compare by subtyping (covariant); cells and deferreds compare exactly
   (§7).

5. **The typed-state connectors.** For the typed-state work, not the runtime.

   ```lean
   /-- A point's runtime environment fits the checker's environment at its path: the
   canonical form of `PointTyped`'s existential `env` (Laws/Program/Typed/Admission.lean:92-96). -/
   def PointEnvFits (w : Typed.World) (src : ProgramSource) (p : Point) : Prop :=
     ∃ env, staticEnvAt (nativeSignature src.table) src.program.expandRefs p.path = some env ∧
       EnvTyped w env p.env
   /-- The fiber part of the contract's `RegistryAgrees`. -/
   def FiberRegistryAgrees (src : ProgramSource) (rootTy : EffTy) (w : Typed.World)
       (m : NativeMachine) : Prop :=
     ∀ id, (m.fiber? id).isSome = true →
       w.Γ id = fiberDecl (nativeSignature src.table) src.program.expandRefs rootTy m id
   ```

   - `ForkSource.source_fork_extension` (`Laws/Program/Typed/ForkSource.lean:28`) takes `env` as
     a free parameter ("Env typing is deliberately not claimed here", `:15`). Instantiated at
     `staticEnvAt`, the new `Γ` entry is the registry's value by construction.
   - Gap 1 is exactly a violation of `PointEnvFits` inside layer bodies under binders.

6. **Make exactness definitional.** Rewrite the checker's child-environment computations to call
   `stepEnv`. Then `staticEnvAt` is the checker's environment by definition, not by test; this is
   the house rule that two traversals agree when they share one algebra.

7. **Repair gap 1 in the runtime.** Build a layer at a closed point, `{ p.child 0 with env := [] }`
   in `provideLayerWithK` (`Compile.lean:774`, `:777`). This matches the checker, the printed
   TypeScript and memo identity by path (DB-12). Making the checker read the enclosing
   environment instead would let one memo entry (one path) stand for builds under different
   environments.

8. **Repair gap 2 in the checker.** `succeed` and `effect` leaves must fit `sig.serviceTy key`,
   with a refusal like `provideService`'s `valueNotSubtype`. The alternative is typed rows in
   `LayerTy.out`, which is a larger change.

9. **Register the counterexamples** (proposed ids; the coordinator assigns them):
   - `E4-PROV-CE-005`: a layer body's environment;
   - `E4-PROV-CE-006`: a layer leaf's value against its service type;
   - the host-free capstone refutation, filed with them or as the next `E4-SCHED-CE` after the
     proposed `-015`.

## 10. Decisions for the owner

1. Add `kind` to the fork-ledger record, and have `spawn`'s three callers pass it. Recommended.
2. The fiber registry is derived from the ledger, the admitted program and the checker, and is
   never stored in values. Recommended as the fiber part of the contract's `RegistryAgrees`.
3. Whether a host may name fibers the program never held (finalizer daemons, layer builds, race
   entrants). Their declarations exist and are sound, but no program holds their handles.
   Recommended: refuse them at the boundary, and keep the declarations for `Γ`.
4. Gap 1 fixed in the runtime (closed layer point). Recommended.
5. Gap 2 fixed in the checker (compare leaves with `serviceTy`). Recommended.
6. **No M6 proof work on layers until 4 and 5 land.** The host-answer restriction does not make
   the capstone true for layer programs. Recommended.

## 11. Open questions

- **The OCaml engine.** Should it carry the checker and `staticEnvAt`, compiled through LCNF, to
  run the registry? Or should it receive a site table computed at admission? The generated OCaml
  already carries `origin` (`ocaml/gen/fibers_gen.ml`).
- **Several roots.** A machine holding more than one root needs `Point.root` in the site.
- **Capabilities, not types.** For source forks the registry admits any existing fiber of the
  right type, including one the host was never given. Types cannot settle whether that should be
  allowed (compare "echo-only" in the host-answers note).
- **Thin corpus coverage** of two environment rules (`stmtBinds`, `gen`): 2 and 8 red-control
  hits. A few more generator programs with forks would help.
- **Generic deferred types.** Should they live in the operation (`NativeOp.deferredMake a e`) or
  in a node annotation (like `iterate`'s `cursorTy`)?

## 12. Commands and results

All runs went through the one-compiler lock from the repository root. `S` is the session
scratchpad, `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad`,
and `D` is `docs/research/2026-09-30-pass/registry`. The shared module is compiled into the
scratchpad, not the tree. Final run, from a clean scratch olean directory:

```
bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true -R docs/research/2026-09-30-pass \
  -o $S/registry-olean/registry/Core.olean $D/Core.lean                  # exit 0, 1 s
LEAN_PATH=$S/registry-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/Sites.lean      # exit 0, 1 s
LEAN_PATH=$S/registry-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/StaticEnv.lean  # exit 0, 7 s
LEAN_PATH=$S/registry-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/Declared.lean   # exit 0, 117 s
LEAN_PATH=$S/registry-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/LayerGap.lean   # exit 0, 5 s
LEAN_PATH=$S/registry-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/Cells.lean      # exit 0, 1 s
LEAN_PATH=$S/registry-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/Proofs.lean     # exit 0, 8 s
```

`lake env` keeps an existing `LEAN_PATH` at the end of its own, which is how `import registry.Core`
resolves. `Sites.lean`, `LayerGap.lean` and `Cells.lean` do not import it. Logs sit beside each
file (`*.log`).

**Axioms.** Every theorem's `#print axioms`:

- `[propext, Quot.sound]`: all of them, except those listed below.
- fewer axioms: `ok_of_bind`, `isSome_of_ok`, `expect_ok`, `throw_not_some` and
  `errLeakTy_closed` use none; `term_ok` and `tape_answers_nothing` use `[propext]`.

No `sorry`, `axiom`, `native_decide`, `partial`, `unsafe` or `implemented_by`. The kernel
decisions use `decide +kernel`, which adds no axiom.

**Printed results:**

- `staticenv.log`: the three lines quoted in §3.
- `declared.log`: the table and controls quoted in §4.
- `sites.log`, `cells.log`: "all guards passed".
- `layergap.log`: 28 axiom lines and "all theorems checked, the print guard passed".
- `proofs.log`: 19 axiom lines.

**Files:** `Core.lean` (shared definitions), `Sites.lean`, `StaticEnv.lean`, `Declared.lean`,
`LayerGap.lean`, `Cells.lean`, `Proofs.lean`, this note and the logs. Nothing else was written,
except the scratch olean directory in the session scratchpad.

**Hashes** of the final probe files and logs (`shasum -a 256 *.lean *.log` in this folder):

```
d4e986bf71a087d02b99777813836db5fd8cfeff7af3a07e4f6ef3ce01d2841f  Cells.lean
8742b0ad298949b530ddc527d82642506459e27e6e8bbdeae8a3182af5a5a98e  Core.lean
3f1cb109744378f067cb2db35e0446a9ff0aab2f14d1f39de72e1a0df80870fc  Declared.lean
d73a5c67c3c055e927df27c34c6cf2ff8f94a84ea8d8f180773b74b74bfcf0da  LayerGap.lean
25e929b7770a9550cdbdedb02848f8070bacc782cafcdd270122b971481dde6b  Proofs.lean
ea6df6b98fe0f48a0d63806e5c06ffa2aa50c74505de9f5d44ae2b1dc5bd12a5  Sites.lean
6f1d950d2e8fe721ab04c9b019fdb6cc2c44873f96085a481d08896c37af2d8b  StaticEnv.lean
089c73e95e54e663415825e2194011d07244a88146359867b651e33a0d783c15  cells.log
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  core.log
0b6ac270b82108dbae70e3c422f19c9a8976961e723fc235844bab43f645be46  declared.log
9063c5d24d45e9041e8586124312aa780ce93a3f6f165173af291f656447dc20  layergap.log
6a03de2cf2d21dfb920d83c30c9ae01e3607e4cae7ff9fe06e9695f284f33938  proofs.log
97ead4853f33a9229ef030b80f4db6b2a16dcc424ce6cb7f5ed1f2614e7a9029  sites.log
13940554e6150f547f2573f75f687bb21b1965efeaeb3ac608fa44be691bccfa  staticenv.log
```
