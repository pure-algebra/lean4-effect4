# The avatar re-diffed against the Lean model of 2026-09-04

Four places where `src/Effect4/Machine/{Fibers,Stores}.lean` moved and the avatar
(`ocaml/avatar/`) and its hand descriptions (`src/OCaml5/Render.lean`) had not.
Lean is the authority. Everything below was checked on this machine (Windows 11, WSL Ubuntu,
OCaml 5.1.1 / dune 3.24 / js_of_ocaml 5.7.1, Windows `node` v22.23.2, Lean v4.33.1).

## Summary

| drift | Lean today | avatar before | what changed |
|---|---|---|---|
| 1 `Cmd` | 8 arms: `evaluate`, `loop`, `deliver`, `finish`, `resume`, `launch (race)`, `link (mode scope key target interruptor extra)`, `drainDue` (`Fibers.lean:511-537`) | 5 OCaml arms (`Cevaluate`, `Cresume`, `Claunch`, `Clink`, `CdrainDue`); description listed the old five (`loop`, `launch` with `entrant`) | decision recorded arm by arm: no `Cloop`/`Cdeliver`/`Cfinish` (covered by control flow); description lists the eight Lean arms with the three absent ones commented |
| 2 `RunEvent` | `raceStarted (race host) (entrants : Nat)`; no `raceSkipped` (`:268-290`, 21 arms) | `deep_fibers.ml` already current (`RaceStarted of int * int * int`, no `RaceSkipped`); description still had `entrants : List FiberId` and `raceSkipped` | description fixed; avatar comments re-cited |
| 3 `WithFiberAction` | 20 arms incl. `awaitAllFailFast (targets)`, `dropObservers (token)`, `cancelRace (race)` (`:211-264`) | `awaitAllFailFast` missing from the avatar; `dropObservers`/`cancelRace` implemented but not described | `Op_await_fibers_fail_fast` + `arm_await_fibers_fail_fast` implemented on the existing `Pending.failFast` machinery; description lists all 20 |
| 4 `DeferredCell.completion` | `Option Program` (`Stores.lean:678-685`) | `completion option` over a separate `completion` inductive; description said `Option Completion` | the cell holds `program option` (the closure `completionPrim` builds); every use fixed; description says `Option Program` |

Every witness stays green and byte-identical to the baseline on all three hosts; the corpus is
unchanged on all three hosts and equal to rc.112 on every comparable program; the projection
guard prints OK on the four rows (`== 48 / 58 agree`, the ten remaining DIFFs being the
pair-alias / parameter / proof-field / abbrev rows that are not this re-diff's).

## Drift 1: `Cmd`

**Lean.** `inductive Cmd` (`Fibers.lean:511-537`): `evaluate (fiber)`, `loop (fiber, yielding)`,
`deliver (fiber, yielding)` — "the second half of `Sync[evaluate]` (`:933-934`, R2-1) ... the
continuation is popped now, by a `getCont` that sees what those nested runs recorded on this
fiber. No loop top, no op count" — `finish (fiber, exit)` — "the exit path of a fiber whose loop
returned `exit` (`:611-628`), run after what its last primitive owed synchronously (M1); the
fiber is re-read" — `resume (fiber token answer)`, `launch (race)` — one iteration of
`raceAll`'s register loop; the `entrant` argument is gone because an entrant has no id before
its launch (`57924eb`, R2-11) — `link (mode scope key target interruptor extra)` (R2-8) and
`drainDue`. `drive` (`:1160-1237`) runs `deliver` through `evaluatePrim` + `settle`, `finish`
through `exitFiber` (`:1112-1137`) followed by `drainDue` unless the fiber parked on its
children; `settle` (`:1142-1156`) queues `Cmd.deliver`/`Cmd.finish` *after* the iteration's
nested commands.

**Avatar before.** `type cmd = Cevaluate | Cresume | Claunch of int | Clink of ... | CdrainDue`
(five arms; `Claunch` already carried the race alone). The functions `deliver`
(`deep_fibers.ml:1035` before, now `:1063`) and `finish` (`:1289` before, now `:1317`) existed;
the DIVERGENCE 2 note only spoke about `Cmd.loop`, and the `cmd` comment cited
`Fibers.lean:499-521`.

**Decision, arm by arm** (written into the divergence table, `deep_fibers.ml:17-47`):

* `evaluate`, `resume`, `launch race`, `link ...`, `drainDue` — `Cevaluate`, `Cresume`,
  `Claunch`, `Clink`, `CdrainDue`, arity for arity. Nothing moved for `launch`: the OCaml arm
  never carried an entrant.
* `loop fiber yielding` — **no OCaml existence** (unchanged): `continue k` runs the fiber to its
  next `perform`; the `yielding` latch lives on `run_fiber.yielding`; the prelude is
  `guard`/`resume_iteration`.
* `deliver fiber yielding` — **covered by the function `deliver`**, not a command: the avatar's
  continuation is the OCaml `k` the store arm holds (DIVERGENCE 1), which no `cmd` of Lean's
  shape could carry. The store arm runs `drive [CdrainDue]` and then `deliver` — the same point
  in the order as Lean's `nested ++ [Cmd.deliver …]` (DIVERGENCE 4), with the same `getCont`-time
  deferred-interrupt check (`deep_fibers.ml:1055-1066`).
* `finish fiber exit` — **covered by the function `finish`**, not a command: it runs from
  `retc`/`exnc` once the fiber's own stack has returned, i.e. after the last primitive's nested
  commands ran inline (DIVERGENCE 4), so "what the last primitive owed, then the exit path"
  holds; it reads the live record (DIVERGENCE 3), so an interrupt a nested command recorded is
  seen, as Lean's re-read sees it. A `Cfinish` value would have no construction site.
* Therefore no `Cloop`, `Cdeliver` or `Cfinish` constructor is added.

**Changed.**
* `ocaml/avatar/deep_fibers.ml:17-47` — DIVERGENCE 2 rewritten as the arm-by-arm
  table above (it also drops the stale mention of `iteration_prelude`, which no longer exists);
  `:511-517` — the `cmd` comment cites `Fibers.lean:511-537` and the decision.
* `src/OCaml5/Render.lean:938-970` — `Avatar.cmd` lists the eight Lean arms in Lean order:
  `loop`, `deliver`, `finish` carry `comment := "DIVERGENCE 2: absent from deep_fibers.ml (…)"`
  (the existing `CtorDesc.comment` mechanism; no argument is erased, the arms are rendered arity
  for arity as the request asks), `launch` has the one argument `race : Nat`, `link` has
  `mode : Supervision.ScopeMode`, `scope key : Nat`, `target : FiberId`,
  `interruptor : Option FiberId`, `extra : ReasonAnnotations α`; site `Fibers.lean:511`.
* `Render.lean:1240` — `#guard Avatar.cmd.ctors.length == 8` (was 5), plus two new guards
  pinning which arms carry the absence comment and the rendered constructor names
  (`Cevaluate, Cloop, Cdeliver, Cfinish, Cresume, Claunch, Clink, CdrainDue`).

## Drift 2: `RunEvent`

**Lean.** `raceStarted (race : Nat) (host : FiberId) (entrants : Nat)` (`Fibers.lean:284`);
`raceSkipped` does not exist; 21 constructors (`:268-290`). `withFiber`'s `raceAll` arm emits
`raceStarted raceId f.id entrants.length` (`:967`).

**Avatar before.** `deep_fibers.ml` had already moved with `57924eb`: `RaceStarted of int * int
* int` "the entrant *count*; `raceSkipped` retired (R2-11)", emitted as
`RaceStarted (race_id, f.id, List.length programs)` (`:1786`), and `avatar_trace.ml:100` prints
the count. Only the hand description drifted: `entrants : List FiberId` and a `raceSkipped` arm.

**Changed.**
* `Render.lean:879-918` — `Avatar.runEvent`: `raceStarted`'s third argument is `.nat`,
  `raceSkipped` removed, docstring and site (`Fibers.lean:268`) updated; `Render.lean:1238` —
  `#guard Avatar.runEvent.ctors.length == 21` (was 22).
* `deep_fibers.ml:362-365` — the `run_event` comment cites `Fibers.lean:268-290` and states the
  21-arm shape (no code change: `grep raceSkipped` finds nothing in the avatar).

## Drift 3: `WithFiberAction.awaitAllFailFast` (+ `dropObservers`, `cancelRace` described)

**Lean.** `awaitAllFailFast (targets : List FiberId)` (`Fibers.lean:232-234`): "`Effect.all`/
`forEach` with concurrency (`Layer.ts:1597-1598`): await all, but the first failing exit
interrupts the outstanding targets with the awaiter's id." `withFiber` handles it as
`countdownPark interp m f targets Resume.exitsValue true` (`:948-950`) — the `failFast` flag of
`Pending` (`:83-85`) — and `fireObserver`'s `countdown` arm (`:1057-1089`) does the work: when
the *observed* target's exit fails and every exit collected so far succeeded (`:1067`),
`interruptEach waiter (stackAnnotations waiter) p.remaining` interrupts the targets not yet
visited, in list order, and the walk goes on; the countdown still waits for each and answers
the exits in input order (M6). A failure among the exits `countdownWalk` collected at park time
does not trigger it, nor does a second observed failure. The caller is `Layer.lean:348`'s
`ActionName.awaitAllFailFast` (`mergeForkAll`, `:839`, `:1211`); `Stores.lean`'s `ActionName`
has no such arm.

**Avatar before.** `countdown_park ?(fail_fast = false)` and the `Countdown` arm of
`fire_observer` already ported the fail-fast rule verbatim (`deep_fibers.ml:1077-1085` before;
`:1105-1114` now) — but nothing set the flag: no effect, no arm. `dropObservers` and
`cancelRace` were implemented (`Op_drop_observers`, `Op_cancel_race`, `drop_observers`,
`cancel_race`) but absent from the description. `deep_layer.ml:234` declares
`LaawaitAllFailFast`, and Layer's `action_of` refuses every action wholesale (`χ` is `unit`),
which is unchanged.

**Changed.**
* `deep_fibers.ml:591-594` — `Op_await_fibers_fail_fast : int list -> exitv list Effect.t`;
  `:1414-1415` — dispatched through `dispatch_exits` like `Op_await_fibers`; `:1991-2015` —
  `arm_await_fibers_fail_fast`: `countdown_park ~fail_fast:true m f targets RexitsValue`, the
  answer being the exits (or the cause on an interrupted park), with the semantics above spelled
  out in its comment and the site citations.
* `extra_fixture.ml:84-122` — an avatar-only program `awaitAllFailFast` (family `extra`, tape
  `0:0,1:0`) as executable evidence: a failing child (body 2) and a never-finishing one (body 4),
  both deferred-started; see "the fail-fast demonstration" below. `build-avatar.sh`'s
  `extra_programs` list does not name it, and `extra_rc112.mjs` cannot spell it (rc.112 reaches
  the arm only inside `Effect.all`/`forEach` with concurrency), so it is avatar-only like
  `refusesUnimplementedArm`.
* `Render.lean:977-1010` — `Avatar.withFiberAction`: `awaitAllFailFast (targets : List FiberId)`
  after `awaitAll`, `dropObservers (token : Nat)` and `cancelRace (race : Nat)` at the end, in
  Lean order; site `Fibers.lean:211`; `Render.lean:1241` — `#guard … == 20` (was 17);
  `Render.lean:2296-2312` — the `ActionName`-vs-`WithFiberAction` guards now state the true
  relation (every `Stores.lean` `ActionName` is a `WithFiberAction`; the one `WithFiberAction`
  that is no `ActionName` is `awaitAllFailFast`), and `Render.lean:2363-2367` drops the
  `|| n == "dropObservers" || n == "awaitAllFailFast"` escape from the Layer guard.

## Drift 4: `DeferredCell.completion`

**Lean.** `structure DeferredCell` (`Stores.lean:678-685`): `completion : Option Program` — "the
completion is a *primitive*, so `done exit = completeWith (Prim.ofExit exit)` is definitional" —
and `waiters : List (FiberId × Nat)`. `Completion` still exists (`:187-197`: `ofExit`,
`ofRefGet`) as the argument of `SyncOp.deferredCompleteWith` (`:237`); `syncOpStep` stores
`completionPrim completion` (`:1217-1219`), `deferredInterruptWith` stores
`Prim.ofExit (Exit.failure (Cause.interrupt (some interruptor)))` (`:1220-1224`);
`completionPrim` (`:1083-1085`) is `Prim.ofExit exit` / `Prim.sync (Thunk.op (refGet cell))`;
`register` answers the stored effect (`:721-728`) and `complete` owes every waiter a resume
carrying it (`due := … (w.1, w.2, effect)`, `:750-751`); `poll` answers the slot (`:715-717`).

**Avatar before.** `type deferred_cell = { mutable completion : completion option; … }` over
`type completion = CoofExit of exitv | CoofRefGet of ref_key`; `complete` took a `completion`;
the due resume carried `Aval Vunit` and the awaiting arm read the `Completion` back out of the
cell (report row W1-2); `poll` matched on `CoofExit`; the description said `Option Completion`
with a comment "Lean: `Option Program`; see the report".

**Changed** (the cell holds what Lean holds; a Lean `Program` is the avatar's
`program = unit -> value`, DIVERGENCE 1, per the substitution table `Render.lean:1332-1386`):
* `deep_stores.ml:255` — generated block: `type deferred_cell = { mutable completion : program
  option; mutable waiters : waiter_pair list }` (regenerated from the description, see
  "render diff"); `:26-36` — the header records the decision.
* `:531-533` `deferred_store_is_done` uses `Option.is_some` (a closure must not meet structural
  equality); `:537-540` `deferred_store_poll : … -> program option option`; `:544-556`
  `deferred_store_register : … -> program option`; `:572-585` `deferred_store_complete (effect
  : program)`, the due resume now carrying `Aprogram effect` — the stored program itself, as
  Lean's `(w.1, w.2, effect)`.
* `:800-815` — `prim_of_exit : exitv -> program` (`Prim.ofExit` on this stack) and
  `completion_prim` over it (`completionPrim_ofExit` is definitional here too); `ofRefGet` still
  refuses by name when *run* (see the residue below).
* `:1069-1076` — `sync_op_step`: `deferredCompleteWith` stores `completion_prim completion`,
  `deferredInterruptWith` stores `prim_of_exit (Efailure (cause_interrupt (Some interruptor)))`,
  arm for arm with `Stores.lean:1217-1224`.
* `:1174-1180` — the fixture's `succeed`/`fail` store `prim_of_exit exit_`; `:1197-1240` —
  `arm_def_await`: `answer_of (p : program)` projects `exit_of_run p`; a due resume's
  `Aprogram p` is used directly (the resume carries the effect, as Lean's does), a resume from
  outside the store (the tape's `answerAsync`) reads the slot back; `:1309-1322` — the fixture's
  `poll` answers the stored program's exit.
* `deep_layer.ml:633` — `LsmemoComplete` stores `prim_of_exit exit_`; `:282-286` shim comment.
* `deep_witnesses.ml:38` — the snapshot's `cells` carry `program option`; `:157-165` —
  `completion_exit_of` reads the stored program's exit; `:643` — W10's expectation compares that
  exit (`Efailure (cause_fail boom)`), not a `Completion`.
* `deep_clauses.ml:1728` — the one direct `deferred_store_complete` call passes
  `prim_of_exit (Esuccess (Vnat 9))`.
* `Render.lean:1690-1706` — `Deep.Stores.deferredCell`: `completion : Option Program`, site
  `Stores.lean:680`, and `waiters : List (FiberId × Nat)` spelled as Lean spells it
  (`.lst (.app "Prod" [fid, .nat])`) with the product mapped to the `waiter_pair` alias by a
  substitution local to this description (`("Prod", Ty.named "waiter_pair") :: subst`) — the
  rendered OCaml is unchanged (`waiter_pair list`), and the projection guard, which normalises
  under the hand description's own substitution, now sees the same shape on both sides. The
  other pair-alias rows (`deferredStore.due`, `scopeState.openMap`) are left as they were.

**Residue (recorded, not new).** Lean makes the stored effect the waiter's *current* primitive;
the avatar cannot, because the fixture's `awaitValue`/`awaitError`/`poll` rows need the exit on
the arm's stack, so the awaiting arms run the stored program there (`exit_of_run`). That is
exact for every program the store ever receives today (`Prim.ofExit`, a pure thunk: every
`deferredCompleteWith` site passes `Completion.ofExit`, and `deferredInterruptWith` an exit).
A `Completion.ofRefGet` program — a `sync` — cannot be performed from the arm, so
`completion_prim`'s `ofRefGet` arm still refuses by name when run, exactly as it did before
(`deferred.complete-with-stores-effect` remains a Lean-only clause; report row W1-2 shrinks to
this sentence).

## How it was checked

### (a) dune, witnesses, hosts

Baseline (before any edit; `tools/witnesses-before.txt`, native): 429 `HOLDS`, 0 `FAILS`;
`clauses 132 holds 127 fails 0 not-portable 5`; `witnesses 62 holds 61 fails 0 not-portable 1`;
`run-clauses holds 35 fails 0`; `park-guard violations 0`.

After (final binaries; `tools/witnesses-after.txt`, `-byte.txt`, `-jsoo.txt`):
* native (`avatar_witnesses.exe`): 429 `HOLDS`, 0 `FAILS`; `clauses 132 holds 127 fails 0
  not-portable 5`; `witnesses 62 holds 61 fails 0 not-portable 1`; `run-clauses holds 35
  fails 0`; `park-guard violations 0` — `diff witnesses-before.txt witnesses-after.txt` is
  empty (0 lines: not one row moved);
* bytecode (`ocamlrun avatar_witnesses.bc`): byte-identical to native;
* js_of_ocaml (`node avatar_witnesses.bc.js`, Windows node): byte-identical to native
  (`cmp` silent), i.e. **hosts witnesses AGREE (bytecode = native = js_of_ocaml)**;
* the native report is also byte-identical to the committed `out/witnesses.report.tsv`.

`dune build --root .` succeeds in all three modes (byte, exe, js). The `--root .` matters: see
"environment findings".

### (b) the corpus

`run-corpus.sh`/`run-witnesses.sh` hardcode a Mac scratch dir, a Mac opam prefix and the
pre-dune binary names, so the comparison was re-spelled in `tools/`: `run-corpus-wsl.sh`
(native + bytecode, WSL), `run-corpus-jsoo.ps1` (js_of_ocaml under the Windows `node`),
`run-corpus-rc112.ps1` (`corpus_rc112.mjs` over the vendored package at
`C:\Users\kokok\Dev\effect4-host\node_modules`, passed as a `file://` URL) and
`compare-faces.sh` (event rows only, program by program). `generated/traces/masks.tsv` is not in
this checkout, so `compare.py` ran under `tools/masks.tsv`, one mask keeping every row kind (the
strictest projection it can apply).

* 158 corpus programs. Before the edits: native = byte = jsoo, 158/158, and equal to the
  committed `out/corpus/*.ocaml.tsv` (the Mac run).
* After the edits (final binaries): native 158/158, byte 158/158, jsoo 158/158; native = byte
  = jsoo on all 158 (`compare-faces.sh`, event rows); every face identical to its own baseline
  run (158 agree / 0 differ on native, byte and jsoo) and to the committed Mac outputs
  (158 / 0). The re-diff changed no corpus row on any host.
* rc.112 reference: 149 traces (5 programs have no rc.112 surface for `childrenSnapshot`,
  4 budget programs did not terminate under the 8 s deadline — the same 149 the estate's last
  recorded run compared: "447 ok" = 149 × 3 masks). `compare.py` avatar (native, after) vs
  rc.112 under the full-row mask: **149 ok, 0 unclassified, 0 classified**
  (`tools/corpus-vs-rc112.txt`).

### (c) the projection guard

Recipe as given (Render.lean compiled into the scratch olean dir, then `DerivedCheck.lean`, one
`lean -M4096` at a time). Before (`tools/derivedcheck-before.txt`): `== 44 / 58 agree`, DIFF on
`Fibers.runEvent`, `Fibers.cmd`, `Fibers.withFiberAction`, `Stores.deferredCell` (both halves:
`completion` and the `WaiterPair` alias) and ten others. After (`tools/derivedcheck-after.txt`):

```
OK   Fibers.runEvent
OK   Fibers.cmd
OK   Fibers.withFiberAction
OK   Stores.deferredCell
== 48 / 58 agree
```

The ten remaining DIFFs are unchanged and not this re-diff's: `Stores.scopeState`,
`Stores.deferredStore`, `Context.service`, `Context.context`, `Context.reference`,
`Context.val`, `Layer.construction`, `Layer.name`, `Layer.scopeState`, `Layer.memoMap`.
`Render.lean` compiles with every `#guard` green; the pinned numbers that moved are
`runEvent` 22 → 21, `cmd` 5 → 8, `withFiberAction` 17 → 20, and the two `ActionName` guards
described under drift 3.

### (d) the render diff

`render-deep.lean` has modes `stores`, `layer`, `context`, `forkflow` — there is no `fibers`
mode (`deep_fibers.ml` carries no generated block; its descriptions are diffed by
`tools/fuzz.sh avatar`, outside this task). `render-deep.sh` cannot run here as written: its
`lake env lean --run` / `.lake/build` fallback cannot see the OCaml5 oleans, which live only in
the scratch olean dir, and it does not pass `-M4096`. The same steps were run from PowerShell —
`lean -M4096 --run src/OCaml5/Tools/RenderDeep.lean stores` against the freshly compiled
`Render.olean`, then `tools/render-diff.py` (the script's Python block as a file) —

```
ocaml\avatar\deep_stores.ml: carriers IDENTICAL to OCaml5.Ml.Deep
```

The block was hand-brought to the rendering (the `deferred_cell` line and its site comment) and
the renderer confirms it byte for byte; nothing was regenerated with `--write` (the one
difference the first diff showed was a comment I had edited inside the generated block, which I
reverted — the note now lives in the hand-written half at `deep_stores.ml:572-576`).

### The fail-fast demonstration

`EFFECT4_FAMILY=extra EFFECT4_PROGRAM=awaitAllFailFast EFFECT4_TAPE=0:0,1:0 EFFECT4_EVENTS=1
EFFECT4_STATUS=1` on the native, bytecode and js_of_ocaml hosts
(`tools/failfast-demo-{native,byte,jsoo}.txt`, byte-identical):

```
op      fork    2            # a = fork body 2 (fails with 1), deferred start
decide  0       false
answer  fork    0
op      fork    4            # b = fork body 4 (never), deferred start
decide  1       false
answer  fork    1
op      started []
answer  started [2, []]      # only body 2 ever ran: 4 was interrupted before its start
done    {"success":[[2, []], [[false, 1], ["interrupted", []]]]}   # exits in input order
#  started 0
#  forked 0 1 false / scheduledTask 0 0 start(1)
#  forked 0 2 false / scheduledTask 0 0 start(2)
#  parkedOn 0 0                    # the awaiter parks on the countdown, observing fiber 1
#  ranTask 0 start(1) / started 1
#  exited 1 {"failure":1}          # the first *observed* failing exit ...
#  observerFired 1 untrackChild(0)
#  observerFired 1 countdown(0,0)
#  interruptRecorded 0 2           # ... interrupts the remaining target with the awaiter's id
#  started 2
#  exited 2 {"interrupted":true}   # the countdown still waits for it
#  observerFired 2 untrackChild(0)
#  observerFired 2 countdown(0,0)
#  resumedWith 0 0 / started 0
#  exited 0 {"success":[[2, []], [[false, 1], ["interrupted", []]]]}
#  ranTask 0 start(2)              # b's deferred start finds it already exited
#  finished true  stuck -
```

`Fibers.lean:1064-1071` in one trace: the interruption is recorded at the countdown observer
of the first failing exit, in list order over the targets not yet visited, and the answer is
the exits in input order (M6). (A first version of this program passed wire handles where the
Lean-alphabet effect takes fiber ids — the countdown then observed the root itself, which the
trace showed as `waiting(0)` with no countdown firing; fixed with `handle_target "fiber"`.)

## Environment findings (worth knowing before the next run)

* **Another dune root appeared under `ocaml/` at 16:01** (`dune-project`,
  `dune-workspace`, `dune` — the `link`/`server` agents' work). From then on a bare `dune build`
  inside `avatar/` resolves its root to `ocaml` and never rebuilds `avatar/_build`,
  while reporting success. Build the avatar with `dune build --root .` from `avatar/`. (One
  `dune clean` of mine ran against that parent root before the cause was found and crashed
  midway with an internal `ENOENT`; the parent `_build` still exists but may need a rebuild by
  its owners.)
* WSL2's `/tmp` is a tmpfs that disappears when the VM idles out between `wsl -e` invocations;
  cross-invocation artifacts must live under `/mnt/c` (the scratchpad).
* `corpus/programs.txt` may carry CRLF; the `tools/` scripts strip `\r` from program names.
* PowerShell's `Select-String` is case-insensitive by default: a count of `FAILS` over a
  witness report also matches the header lines `fails 0` unless `-CaseSensitive` is passed.

## Files touched

`src/OCaml5/Render.lean` (the four descriptions and their guards only);
`ocaml/avatar/{deep_fibers,deep_stores,deep_layer,deep_witnesses,deep_clauses,extra_fixture}.ml`;
new under `ocaml/avatar/tools/`: `run-corpus-wsl.sh`, `run-corpus-jsoo.ps1`,
`run-corpus-rc112.ps1`, `compare-faces.sh`, `render-diff.py`, `masks.tsv`, the `witnesses-*.txt`,
`derivedcheck-*.txt`, `failfast-demo-*.txt`, `corpus-vs-rc112.txt` evidence files, and this
report. Nothing under `link/`, `server/`, `Derived/`, `DerivedCheck.lean`, `tools/Describe.lean`,
`lakefile.toml`, `Effect4.lean`, `Test/` or `src/` was edited; no git command that writes was run.
