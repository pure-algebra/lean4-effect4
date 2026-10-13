# 2026-10-13 seat BANK receipt: the banked Ref cache and the claim record's two labels

Status: receipt (history, not authority). Brief: `docs/research/2026-10-13-seat-bank-brief.md`.
Specification: decisions row 378.

**The one thing to know before merging:** the transfer law `cache_agrees` is proved and rests on
no planned goal, but only for the block's bodies with `get`'s loader read as a row, and for a
fresh cache read once on every recorded run (H8). A client that invokes the block by `Eff.invoke`
has no law yet, and the cache cannot be imposed on the to-do until three pieces exist. They are
a `DefSrc` with program parameters and an invocation with programs, an application entry that
invokes a definition, and HO-5's print of a method with a parameter.

## Base and head

Branch `seat/bank`, worktree `~/Dev/lean4-effect4-bank`, base `cfcb95e1b`. Head: the commit that
adds this receipt, on `f463ee53b` of `refactor/phase1-phase3`.

| Commit | What | On `refactor/phase1-phase3` as |
| --- | --- | --- |
| `13551903c` | the claim record's two labels (row 378 (7)) | `516f13bf8` |
| `63b513dce` | the block, its model, the parameter reading, the transfer law, the registry claim | `23f95aac2` |
| `5fc952510` | merge of `refactor/phase1-phase3` at `c4f56a879` (E1, E2, E3) | `23f95aac2` |
| fast-forward | to `d2d10b383`: the coordinator moved `mapOps` into `Block.lean` | — |
| `447484de9` | the bank entry of the Ref cache, its digest guard and its runs | `f463ee53b` |
| fast-forward | to `f463ee53b`, after `608448e5c` (STATE, row 378 (22)) | — |

## Changed files

- `Test/Dogfood/Application.lean`: `About` (an implementation or an application) and `Evidence`
  (theorem, finite check, outside oracle, monitored, validated, assumed). `Grade` became
  `Evidence`, and its `proved` became `«theorem»` (a keyword, so the constructor is escaped). A
  premise's grade and a claim's evidence are one type. `ClaimRecord` holds a claim's statement,
  its two labels and its premises. A note gains an `evidence` label, by default `«theorem»`.
  `Record.claimRecords` reads an application's notes as claim records about the application.
  `Kind` is unchanged, and no record holds a status.
- `Test/Dogfood/Scenario/Todo/Claims.lean`: the `open` line only (`Grade` to `Evidence`).
- `src/Effect4/Library/Ref/Cache.lean` (new): the block. `make` is the service's initial
  program, and `get` and `invalidate` are its methods (service `ListCache`). `get` takes the
  loader as a program parameter (row 340). The bodies hold no row position and no definition
  position.
- `src/Effect4/Library/Ref/CacheModel.lean` (new): the model over the cached value and a tape of
  storage's answers (`make`, `read`, `invalidate`). It imports nothing.
- `src/Effect4/Laws/Program/ParamRows.lean` (new): `paramAsRow` and `paramsAsRows`, a body's
  parameter runs read as rows. The coordinator moved my `mapOps` into `Block.lean`
  (`d2d10b383`), where `callsAsRows` reads it too.
- `src/Effect4/Laws/Library/Ref/Cache.lean` (new): the transfer law and its steps.
- `Test/Dogfood/Bank.lean` (new): `Entry` and the entry `refCache`, with its guards and runs.
- `tools/ProofGraph/Registry.lean`: the claim `ref-cache-agrees`, appended at the end of the
  claims.
- `src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`: one comment and the new modules'
  imports, appended at the end of each import list.

## Commands and results

Every command ran from the worktree through `~/Dev/lean4-effect4/scratch/lean-slot.sh`. The
`#axiom_audit`, `#plan_status` and `#auto_census` lines ran from scratch files under the worktree's
ignored `scratch/`, by `lake env lean`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Library.Ref.Operations Effect4.Laws.Api.SessionMeaning Effect4.Laws.Program.Validated Test.Dogfood.Scenario.Todo.Claims` (the cache, warmed) | `Build completed successfully (1204 jobs).` |
| `lake build Test.Dogfood.Application Test.Dogfood.Scenario.Todo.Claims` | `Build completed successfully (1173 jobs).` |
| `#axiom_audit Test.Dogfood.Application Test.Dogfood.Scenario.Todo.Claims` | `283 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 0 planned goals` (the two are `add_empty_calls_nothing` and `serves`, through `request_leads`, as before) |
| `lake build Effect4.Library.Ref.Cache Effect4.Library.Ref.CacheModel` | `Build completed successfully (66 jobs).` |
| `lake build Effect4.Laws.Library.Ref.Cache` | `Build completed successfully (519 jobs).` |
| `lake build Effect4 Effect4.Laws` (before the merge) | `Build completed successfully (1106 jobs).` |
| `#axiom_audit Effect4.Library.Ref.Cache Effect4.Library.Ref.CacheModel Effect4.Laws.Program.ParamRows Effect4.Laws.Library.Ref.Cache` | `51 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals` |
| `#auto_census Effect4.Laws.Library.Ref.Cache using aesop` | `0 of 15 theorems closed from their statements; 0 source lines they now take` |
| `lake build ProofGraph.Registry` | `Build completed successfully (2 jobs).` |
| `git merge refactor/phase1-phase3` (at `c4f56a879`) | conflicts at the end of the two root import lists only; kept the main line's lines, then mine |
| `lake build Effect4 Effect4.Laws` (after the merge) | `Build completed successfully (1109 jobs).` |
| `git merge --ff-only refactor/phase1-phase3` (at `d2d10b383`) | fast-forward |
| `lake build Effect4.Library.Ref.Cache Effect4.Laws.Library.Ref.Cache Test.Dogfood.Bank` | `Build completed successfully (1128 jobs).` |
| `#axiom_audit Effect4.Library.Ref.Cache Effect4.Library.Ref.CacheModel Effect4.Laws.Program.ParamRows Effect4.Laws.Library.Ref.Cache Test.Dogfood.Application Test.Dogfood.Bank` | `298 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals` |
| `#plan_status Effect4.Ref.Cache.cache_agrees Effect4.Ref.Cache.get_agrees Effect4.Ref.Cache.get_session` (after `d2d10b383`) | `cache_agrees: proved`; `get_agrees: proved`; `get_session: proved`; `next goals: 0` |

Not run, and why: `lake build Test` and the whole-tree axiom gate (the brief forbids them);
`make gen-semantics` (a whole-tree generated group, so `generated/semantics.md` does not show
`ref-cache-agrees` yet); the behaviour gates of `make check-full`. No change reaches a behaviour
gate. The printer, the codec, the machine, the OCaml route and the corpus are unchanged, and the
block prints nowhere yet.

## Axiom output

The last audit covers every module I added or changed, on the tree at `d2d10b383` plus the bank:
`298 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`.

## Evidence

| Claim | Evidence word | Bounds |
| --- | --- | --- |
| `cache_agrees`, its four laws and six helpers | proved (`#plan_status`, `#axiom_audit` above) | the reach in the placement below |
| the recorded digest is the block's, at the to-do's types | tested (`#guard`, `Test/Dogfood/Bank.lean`) | the one instance |
| the checker admits the block at the entry's own rows (none) | tested | the one instance |
| the ascription in `make` stands: without it the check refuses the block at `[0, 0]` | tested (control) | the one instance |
| a run of `get_session`'s client under the to-do's reference model meets the premises that a run decides (funded, at rest, driven by a host) and observes the model's read | tested | a finite probe on the Lean machine: one run. The run is reached by `runWith_session` (`src/Effect4/Laws/Api/HostDrive.lean`) under that theorem's reactor premises, which the guard does not decide |
| two reads ask the repository once; a `get` that holds nothing asks twice | tested (green and control) | a finite probe: one run each |
| a write between two reads leaves the second stale; an invalidation after the write makes it ask again | tested (control and green) | a finite probe: one run each |
| a loader that writes the cache's cell makes the next read answer a list the repository never gave | tested (control of the law's reach) | a finite probe: one run |
| `printServices` refuses a service method with a parameter (`serviceFaultOf`) | reading | not run on this block |
| an application entry cannot invoke a definition (`Application.openProgram` elaborates with no definitions in scope) | reading | — |

No evidence is host-only: every run is on the Lean machine under a Lean reactor. The runs are
finite probes, and the laws are proved for every cached value and every tape in their reach.

## Landed theorems and their placement

All in `src/Effect4/Laws/Library/Ref/Cache.lean`, each tagged
`@[semantics "translation-simulation" (requirement := R10)]`.

**`cache_agrees`** (and the laws it assembles: `make_agrees`, `get_agrees`, `invalidate_agrees`,
`get_session`):

- Concept: `translation-simulation`; property: a module's code is simulated by its model, the
  shape of R10's `Agrees` (decisions rows 79 and 378 (3)).
- Question: the registry claim `ref-cache-agrees` (role simulation), witness `cache_agrees`.
  Consumers: the bank entry `refCache` (`Test/Dogfood/Bank.lean`), and the to-do's claims once
  the cache is imposed on its `list` (row 378 (2)).
- Reach: the block's three methods, each law reading the block's own body
  (`bodyOf (block A E) k`), one fiber, the call tree's meaning (`meaningRows`). Every cached
  value, through any image of the element type. Every reply tape whose successes lie in the
  image. `get`'s loader is read as a row `n` of any table (`paramsAsRows`). The observation is
  the exit, the stores with the cell at the model's next value, and the unread tape; the cache
  has no waiter, so the wake order is empty. `get_session` adds H8's premises (a reached run,
  funded, at rest, driven by a host), a data row at `n`, and a fresh cache, and it reads the
  run's applied replies as the tape.
- Does not establish: any host's storage behaviour; a run that invokes the block by `Eff.invoke`
  (HO-2's `invoke-unfolds`, the inlining law PROC-6); several calls of the block in one run on the
  machine; a loader that writes the cache's cell; anything of a fiber-sharing schedule (Effect's
  `cachedInvalidateWithTTL` shares one run among callers, and this cache does not); progress, as
  an empty tape is the frontier; the block's typing, which is a finite check of the bank.
- Unlocks: R10 for the first banked module (row 378 (1) to (5)).

**The helpers** (`refPoke_peek`, `holding_self`, `hostRun_bind_straight`, `hostRun_bind_call`,
`get_hit`, `get_miss`): each is a step of `ref-cache-agrees`, and each docstring names its
consumer. `get_hit` and `get_miss` hold under any host, not only a reply tape: they are the form
that a claim of the imposed to-do under the reference model `repository` reads.

## What I reused

- Ref's operation laws through the claim's own theorem, `ref_steps_agree` (fields `get`, `set` and
  `make`; `src/Effect4/Laws/Library/Ref/Operations.lean`).
- The equal-observation side: H8, `Run.denoteRows_eq_session`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`).
- The call tree and its runs: `meaningRows`, `meaningUnder_straight`, `lt_of_dataRow`
  (`src/Effect4/Laws/Program/DenoteRows.lean`); `hostRun_bindExit`, `hostRun_straight`,
  `hostRun_call`, `meaningRows_eq_hostRun`, `tapeHost` (`src/Effect4/Laws/Program/HostRuns.lean`);
  `meaning_perform_sync`, `meaning_bind` (`src/Effect4/Laws/Program/Denote.lean`).
- `blockOf?` and, after the coordinator's fold, `mapOps` (`src/Effect4/Laws/Program/Block.lean`).
- `Image.option`, `Image.ident` (`src/Effect4/Store/Carrier/Image.lean`); `Authoring.ascribeFields`
  (`src/Effect4/Program/Authoring/Ascribe.lean`); `Store.Canonical.digest`; `Checker.checkModule`;
  `Author.Internal.finishBuild`, `Run.runWith`; core's `List.set_getElem_self`.
- The to-do's `application`, `repository`, `list`, `TodoRepo.insert`, `todo` and `noTodo`
  (`Test/Dogfood/Scenario/Todo.lean`): the runs use the to-do's own `list` as the loader.

New definitions where none existed: `paramAsRow` and `paramsAsRows`; `bodyOf` (no accessor of a
block's body existed); `exitOf`, `holding`, `observed`, `fresh`; `refPoke_peek` (no lemma for
writing a cell's own value back; the index lemma in `Stores.lean` is private); and
`hostRun_bind_straight` and `hostRun_bind_call` (only `hostRun_bindExit` existed). The last
three, and `bodyOf`, belong beside their peers: `StoresLaws.lean`, `HostRuns.lean` and
`Block.lean`. They stay in the cache's law file because the brief names no other file.

## How the to-do's `list` would impose the cache

1. The to-do's block gains the cache's three definitions at the to-do's types,
   `Ref.Cache.decls Todo.ty SqlError.ty` and its bodies. The bodies hold no row or definition
   position, so they keep their bytes wherever they stand. The built application pins
   `refCache.digest` by a guard that compares its definitions there with `refCache.block`'s
   (row 378 (4)).
2. One way to hold the cell (a proposal): the service's state holds it beside the context, and
   the initial program runs `Effect.context<R>()` and the cache's `make`.
3. `list` becomes `get` at the cell, with the to-do's old `list` body, `TodoRepo.all(unit)`, as its
   loader. `add`, `complete` and `remove` call `invalidate` at the cell after a successful write.
   The bank's stale control shows what a write without it does.
4. The pieces that do not exist yet:
   - `DefSrc` declares no program parameter, and `Def.invoke` writes `perform (call k)`, which the
     checker refuses for a definition with a parameter (`Test/Program/InvokeControls.lean`). An
     invocation with programs needs a surface form;
   - `Application.openProgram` elaborates an entry with no definition in scope, so an entry
     cannot invoke the cache;
   - `printServices` refuses a service method with a parameter until HO-5 (`serviceFaultOf`);
   - the to-do's claims read `denoteRows`, H8 and H9, which give `invoke` no meaning. With the
     inlining law, `get_agrees` at the to-do's table, `n` the position of `TodoRepo.all`, carries
     the cache's model to `list`'s run.
5. `list_after_add` would then hold of the imposed to-do only with step 3's obligation. Under
   the repository model its proof would read `get_miss`, `invalidate_agrees` and `add_on_model`.
   No statement of it exists yet.

## Open obligations

1. The machine law for a client that invokes the block: HO-2's `invoke-unfolds` (slice CX4) or
   PROC-6's inlining law. `cache_agrees` is its first consumer, and STATE says CX3 and CX4 wait
   for one.
2. Imposing the cache on the to-do (the coordinator's): the four pieces above.
3. The to-do's claims stated against the cache's model, with the invalidate-on-write obligation.
4. Moves: `refPoke_peek` to `StoresLaws.lean`; `hostRun_bind_straight` and `hostRun_bind_call` to
   `HostRuns.lean`; `bodyOf` beside `blockOf?`.
5. `make gen-semantics`, so that `generated/semantics.md` shows `ref-cache-agrees`.
6. Generic definitions (HO-4) would let one entry serve every element type. Today the entry pins
   the to-do's instance, so an edit of `Todo` or `SqlError` moves the digest, as an edit of the
   block does. The guard then fails until the digest is recorded again (row 378 (5)).
7. Models as data (row 378 (6)): one transfer law now stands, the condition for revisiting it.
8. Semaphore, the next banked module (row 378 (18)).

## Proposed decisions rows (proposals only)

1. **Where the bank lives** (representation). `ClaimRecord` and `Entry` live in `Test/Dogfood/`
   beside the application record. Recommended: they move to a core module when an application
   pins a block's digest (row 378 (4)), and the bank stays a battery until then.
2. **HO-5 and the invocation's laws join the slice's path** (domain). The banked cache takes its
   loader as a program parameter (row 340), as the brief preferred, so the block names no
   application. Imposing it then needs HO-5 (a method with a parameter, printed, and an authoring
   form for an invocation with programs) and HO-2's `invoke-unfolds`. Recommended: row 378 (12)
   counts both as on the slice's path. The other option is a loader as the cache's own storage
   row: it prints today, but its code names a row position, so an application that places the
   row elsewhere changes the block's bytes and its digest.
3. **The cache's write obligation** (meaning). An application that imposes the cache invalidates
   it after each write. Recommended: the imposed to-do's write entries call `invalidate`, and
   `list_after_add` is restated against the cache's model and the repository model.
