# Seat "daemons" — receipt

Worktree `/Users/pooks/Dev/lean4-effect4-daemons`, branch `seat/daemons`, base `1a8587f2`.
Six commits: the five below, then this receipt as the head. Nothing pushed.

| commit | what |
| --- | --- |
| `84a0388e` | `Api/Supervision.lean`: the fork sites of a program as data |
| `483f3d96` | the same file: the fibers of a run with what holds each one |
| `6b6d4e71` | `Laws/Api/Supervision.lean` (a), (b), (c); root import in `Laws.lean` |
| `37d5c857` | `Test/Api/SupervisionContract.lean`; root import in `Test/All.lean` |
| `fb7b02bf` | `aesop` in place of four hand scripts, after the census |

Files: `/Users/pooks/Dev/lean4-effect4-daemons/src/Effect4/Api/Supervision.lean` (368 lines),
`/Users/pooks/Dev/lean4-effect4-daemons/src/Effect4/Laws/Api/Supervision.lean` (542),
`/Users/pooks/Dev/lean4-effect4-daemons/Test/Api/SupervisionContract.lean` (181).
Two one-line imports outside the three: `src/Effect4/Laws.lean:40` and `Test/All.lean:82`,
both of which the brief asked for (the second as "root it as `RunnerContract` is rooted").

---

## 1. Supervision as static data

`ForkKind` (`src/Effect4/Api/Supervision.lean:52`) has four alternatives — `child`, `daemon`,
`pinned (scope : Option Term)`, `raceEntrant` — and `ForkSite` (`:76`) is a path, a kind and
the `ForkOptions` **as the program wrote them**. `ForkSite.isDaemon` (`:86`) is a function of
the kind alone; the written options are kept beside it precisely so the rc.112 override at a
pin is visible rather than lost. `ForkSite.body` (`:91`) is `path ++ [0]`, which is the
forked program at every one of the four sites, because each of them takes its program as
child `0`.

`forkSitesOf` (`:105`) is the whole classification, four rows keyed by family and constructor
*name*, reading only leaf `ArgF` arguments — so it is generic in the carrier and a
constructor added to the alphabet arrives as a name the table does not carry and yields
nothing.

`supervision` (`:146`) is `cata_eff superAlg e []`: the fold of one generic layer function
(`superLayer`, `:135`) over the generated layer view, with the path-reader carrier
`SiteReader = fun _ => List Nat → List ForkSite`. A node's own sites come from `forkSitesOf`;
its children's come from `atChildPaths (childReaders args) p 0`, which numbers the *child*
arguments only — the same numbering `Node.child` and the path walk use, pinned by
`#guard`s that `Node.at_` at a site's path is the forking node and at its body the forked
program (`Api/Supervision.lean:332-337`, `Test/Api/SupervisionContract.lean:70-76`).

I first wrote this as `foldMapAt_eff` with `f_action` / `f_effs` yields, the shape `refSites`
uses. The coordinator's mid-task note redirected it to the `cata` + generated view shape of
`Laws/Codegen/PrintReadable.lean`, and that was the right call: it is what made the
whole-program law provable in one proof (§4a). Both versions produce the same paths — the
`#guard`s did not move.

The supervision **tree** is a projection of the list, not a second representation:
`ForkSite.parent` (`:155`) is the innermost earlier site whose body encloses this one
(`Api/Supervision.lean:339-346` pins nesting and siblings).

**`runIn` is deliberately not a fork site.** `ActionTerm.runIn` pins an existing fiber to a
scope through the same `linkScope` (`Machine/Fibers.lean:1229-1232`), so it changes a fiber's
status without forking. It is named in the module docstring and in `FiberStatus`'s.

## 2. The fibers of a run

`FiberStatus` (`:197`) and `statusOf` (`:235`) read **four observations, all machine state**:

| observation | where it lives |
| --- | --- |
| the fiber's own exit | `RunFiber.exit` |
| the fiber that tracks it | some `g.children` contains it (`parentOf`, `:221`) |
| the scope it is pinned to | `Observer.dropScopeFinalizer scope key` on its own observer list (`pinOf`, `:227`) |
| whether the run forked it | a `RunEvent.forked _ id _` in `m.trace` (`forkedIds`, `:179`) |

**The `forkIn` link is recoverable from machine state alone; nothing is missing.** The brief
allowed for it not being, and asked me to say exactly what would be. It is not needed:
`linkScope` (`Machine/Fibers.lean:988-989`) appends `Observer.dropScopeFinalizer scope key`
to the *linked fiber's* own observers at the same step it emits `RunEvent.scopeLinked`, and
nothing removes it while the fiber is live (`WithFiberAction.dropObservers` filters only
`resumeAwait` and `countdown`, `:1299-1306`). So the scope number **and** the registration
identity the store allocated are both on the fiber. The trace is read for one thing only —
telling the run's own root from a detached daemon — and that one thing genuinely has no other
source.

**Deviation from the brief, flagged.** `FiberStatus` has a fifth alternative, `root` (`:208`).
A freshly loaded root is untracked and unpinned exactly as a detached daemon is, so with four
alternatives every run reports its own root as a loose daemon and `daemonsQuiet` decides
nothing. The `forked` events separate them and only they can. If the owner prefers four, the
alternative is to drop `root` and special-case `Api.root` inside `unpinnedDaemonsAlive`; that
is exact for this face (`load` sets `nextId := 1`) but wrong for any machine whose root is not
fiber 0, and it hides the distinction inside a filter instead of showing it in the data.
I recommend keeping `root`.

`fiberStatuses` (`:248`) maps it over `m.fibers` in creation order (nothing ever removes a
fiber). `unpinnedDaemonsAlive` (`:252`), `daemonsQuiet` (`:257`), and `Supervised` (`:263`)
are the property it decides. `Run.fibers` / `Run.unpinnedDaemonsAlive` / `Run.daemonsQuiet` /
`Run.forked` (`:275-284`) are the run-level projections the run seat will want.

## 3. The laws

All of it at `[propext, Quot.sound]`: 219 declarations across the three modules, 0 outside the
ceiling (command in §6).

### (a) supervision is static

Static half, **whole-program, one proof, no case per constructor**:

* `forkSitesOf_child_flag` (`Laws/Api/Supervision.lean:107`) — the generic node step, the only
  place a `ForkSite` is made: a site the table calls a tracked child was written
  `daemon := false`.
* `supervision_child_flag` (`:165`) lifts it through the fold, via
  `supervision_child_flag_bounded` (`:144`): `cata_build` reduces a node's fold to the layer
  function on its folded arguments, `mem_atChildPaths` (`:120`) and `mem_childReaders`
  (`:129`) say a site that is not the node's own comes from a child the view lists, and
  `nodeSize_child_lt` (`:89`) says that child is smaller. `supervision_isDaemon_flag` (`:171`)
  is the same fact read off `isDaemon`.
* `nodeSizeLayer` / `nodeSizeAlg` / `nodeSizeLayer_eq` / `le_sum_of_mem` / `nodeSize_pos` /
  `nodeSize_child_lt` (`:62-101`) are a local copy of the measure. **The coordinator has since
  landed it once in main** as `src/Effect4/Laws/Program/Size.lean` (`c2688499`, namespace
  `Effect4.Program`, importing only `Effect4.Program.LayerView`) under the names `sizeLayer`,
  `sizeAlg`, `sizeLayer_eq`, `le_sum_of_mem`, `size_pos`, `size_child_lt`. This branch's base
  predates that commit, so **the copy stays as it is and is not grown**: at the merge the
  coordinator deletes lines `:62-101` and renames the uses. There are exactly four uses outside
  the copied section — `:146`, `:149`, `:158`, `:167` (`nodeSizeAlg` twice, `nodeSize_pos`,
  `nodeSize_child_lt`) — plus one mention in the module docstring at `:22`. This is the only
  duplication the seat introduces.

Machine half — every fork the machine can make, each appending exactly one `forked` event
carrying the flag the site carries:

| theorem | line | flag |
| --- | --- | --- |
| `spawn_forked` | `:197` | the options it was handed — every fork goes through here |
| `fork_forked` | `:235` | `options.daemon`, the program's own |
| `forkIn_forked` | `:245` | `true`, forced at the pin |
| `forkScoped_forked` | `:254` | `true`, forced at the pin |
| `forkScoped_none_forked` | `:265` | no event at all (no ambient scope) |
| `launchEntrant_forked` | `:275` | `true`, a race entrant |
| `forkFinalizers_forked` | `:284` | every event a parallel close adds is `true` |
| `action_fork_forked`, `action_forkIn_forked`, `action_forkScoped_forked` | `:300-317` | the same three on the shared arms the term evaluator takes |
| `supervision_static` | `:329` | the four bundled |

`start_forked` (`:228`) is why the equations read past the starting half: it emits a
`scheduledTask` and never a `forked`. The three `withFiber` equations rest on the existing
`rfl` clauses of `Laws/Machine/Clauses.lean:1357,1373,1387,1405`, so they are about the path
`Api.run` really takes, not a restatement beside it.

### (b) what a status can change by

* `status_persists` (`:372`) — the `guard_persists` shape: equal exits, equal tracking, equal
  pin and equal forked-ness give equal status, so the status survives every change to the
  machine except a change to one of the four.
* `publish_status` (`:382`), `status_exited_iff` (`:386`), `status_live_of_none` (`:392`) —
  the exit observation is written in exactly one place, `RunFiber.publish`.
* `spawn_status_fresh` (`:415`) — **DI-75 as a theorem**: a spawned fiber is a loose daemon
  the moment it exists. Tracking is `Cmd.trackChild` and the pin is `Cmd.link`, both of which
  run *after* the child's start, while the spawn's own `forked` event already names it. So a
  `daemonsQuiet` reading is a reading of a settled machine, and that is a real caveat for the
  run seat.
* `spawn_status_other` (`:450`) — a spawn changes no existing fiber's status.
  Both take `NextIdFresh` (`:356`), with the decidable twin `nextIdFresh` (`:360`) and
  `nextIdFresh_iff` (`:363`); the battery pins it on all three real runs.

### (c) the parked fibers

* `awaits_parked` (`:468`) — every entry of `Program.awaits` names a parked fiber of the
  machine, at its own token.
* `exited_notParked` (`:478`), `parked_status_live` (`:488`) — under `exitedUnparked` (the
  machine fact `RunFiber.publish` establishes, `Machine/Fibers.lean:1696-1704`), an exited
  fiber is off its guard and a parked one is live.
* `awaits_live` (`:502`) — the agreement: every outstanding host call names a fiber whose
  entry in `fiberStatuses` is live, never `.exited`.
* `daemonsQuiet_iff` (`:514`), `finished_daemonsQuiet` (`:526`), `terminated_daemonsQuiet`
  (`:538`) — the decidable check is exactly `Supervised`, and a terminated observation is
  quiet (through `observe_terminated_iff` of `Laws/Api/Frontier.lean:50`).

### aesop: what is closed, what needed hand steps, and why

`#auto_census Effect4.Laws.Api.Supervision using aesop` (§6) closes **8 of 44** theorems from
their statements alone. Of the 48 declarations, 4 are `def`s; of the 44 theorems, **31 call
`aesop`** (closed by it, or by it after one `unfold`/`rw` of the one definition the hypothesis
is about), 10 are `rfl` or a term with no tactic block, and **3 carry a tactic script with no
aesop in it**:

| hand step | why |
| --- | --- |
| `nodeSize_pos` (`:81`), `nodeSize_child_lt` (`:89`) | the generic step is `cata_build … (build_view fam e)`, a rewrite aesop has no way to guess, and the rest is `omega` — which this repo's rules forbid as an aesop rule |
| `supervision_child_flag_bounded` (`:144`) | the recursion itself, on the node count |

`le_sum_of_mem` (`:71`) counts among the 31: its base case is `aesop` and its step is `omega`,
for the same arithmetic reason.

The six `rfl`/term proofs the census also reports are definitional equations — `spawn_trace`,
`spawn_child`, `spawn_nextId`, `spawn_fibers`, `nodeSizeLayer_eq`, `publish_status` — stated
the way `Laws/Machine/Clauses.lean` states every machine clause. **I did not convert these to
`aesop`, against the letter of the instruction, and the census itself is the reason:** it
reports that aesop's proof of `nodeSizeLayer_eq` and `publish_status` reaches `[propext]`
where `rfl` reaches no axiom at all. Trading an axiom-free proof for one that touches
`propext`, on a repo whose gate is the axiom ceiling, is a regression. If the owner wants them
converted anyway the change is six lines.

The four the last commit converted were `parentOf_append_none`, `parentOf_append_same` (hand
`List.find?` rewrites → plain `aesop`), `status_persists` (→ `unfold statusOf; aesop`) and the
tail of `awaits_live`.

## 4. The battery

`Test/Api/SupervisionContract.lean`, three programs on the raw route
(`Api.run … 400 [] table`, `table = [Profile.Scalar.waitRow]`):

| program | line | shape | `daemonsQuiet` |
| --- | --- | --- | --- |
| `childFork` | `:44` | a tracked child, forked immediately and joined | `true` — nothing alive |
| `looseDaemon` | `:50` | **DI-75's `g78`**: a daemon whose root exits first, parked on a call nobody answers | **`false`** — the red control |
| `pinnedDaemon` | `:57` | `forkScoped` inside a scope that stays open, both halves parked | `true` — alive but held |

The three separate every case the data has to separate, and the middle one is the fixture that
fails if the check loses its teeth. `pinnedDaemon` also pins the rc.112 override: the program
writes `daemon := false`, the site's kind says daemon anyway, and `Run.forked` shows the
machine stamping `true` (`:68`, `:82-83`, `:94`).

Guards: `supervision` for each (`:66-88`), `Node.at_` at each site's path and body (`:71-76`),
`Run.forked` against `(supervision p).map ForkSite.isDaemon` (`:92-98` — `supervision_static`
on a real run), the status tags after the run (`:113-133`), `exitedUnparked` and `nextIdFresh`
(`:135-140`), `Program.awaits` and the `awaits_live` agreement (`:143-152`), and the
observation (`:154-161`). Eight `#print axioms` stamps at `[propext, Quot.sound]`
(`:164-180`); `status_persists` is `[propext]` alone.

## 5. What the observation should show — for the run and author seats

> **Ruled by the coordinator after this section was written.** Two edits land at the merge, both
> by the coordinator, neither by this seat: the old `Api.Run` (`src/Effect4/Api.lean:272`) is
> renamed `Api.Inspection`, so this seat's `Run.fibers` / `Run.unpinnedDaemonsAlive` /
> `Run.daemonsQuiet` / `Run.forked` (`src/Effect4/Api/Supervision.lean:275-284`) become
> `Inspection.*`; and the run seat's `Run.Observation` gains **`daemons : List FiberId`**, fed
> by `unpinnedDaemonsAlive`. So the answer below is right about `fibers` and overruled on the
> second field. The one caveat the ruling inherits is the one §5 gives for leaving it out: a
> field that is a function of another field can drift, and the guard against it is that
> `daemons` is computed by `Api.unpinnedDaemonsAlive` at the point `Observation` is built and
> never assigned from anywhere else. `daemonsQuiet` stays a function — `daemons.isEmpty`.

### The run seat: one field on `Observation`

Scout A's proposed record (`docs/research/2026-09-17-host-session-api-scout-A.md` §4.3) should
gain **one** field:

```lean
fibers : List (FiberId × FiberStatus)     -- Api.Supervision, = Api.fiberStatuses s.machine
```

and nothing else. The two derived readings, `unpinnedDaemonsAlive` and `daemonsQuiet`, are
already functions of it (`Api/Supervision.lean:252,257`) and should stay functions rather than
fields — a record with a field that is a function of another field is a drift point, and the
`Canonical` instance is cheaper without it. `FiberStatus` is first-order and derives
`DecidableEq`, so `Observation` stays codec-able and `"Observation"` can join the `schemas`
list as scout A proposes.

Three design reasons for the exact shape:

1. **A pair list, not a map.** `m.fibers` is a list in creation order and `fiberStatuses` is
   `map` over it, so the order carries information (who was forked when) that a map would
   throw away, and the projection stays one `List.map` with no lookup.
2. **The status, not a `Bool`.** `awaiting : List Await` already tells the holder *which*
   fibers are parked on a host call. What it cannot say is who is holding them. A holder that
   sees `(⟨3⟩, .daemon)` beside an empty `awaiting` knows it has a leak; `(⟨3⟩, .pinned 2 7)`
   beside the same `awaiting` knows it has a scope to close. That difference is the whole
   point of the field.
3. **Read it at a settled machine.** `spawn_status_fresh` proves that a child reads `.daemon`
   between its fork and the command that holds it. `Observation` is taken after `play`
   finishes a journal, which is settled; but if the run seat ever exposes a mid-command
   observation it must say so, and `nextIdFresh`/`exitedUnparked` are the decidable hypotheses
   the laws take.

For `Run` (the raw route) the same three projections already exist: `Run.fibers`,
`Run.unpinnedDaemonsAlive`, `Run.daemonsQuiet`, `Run.forked`
(`src/Effect4/Api/Supervision.lean:275-284`).

Two things the run seat should **not** do. It should not add a `supervision` field to
`Observation`: the supervision tree is a function of the program, which the session already
holds as `built.program`, and duplicating it into the observation would let the two drift. And
it should not report `daemonsQuiet` as a health verdict without the scope: it is exactly "no
live fiber is untracked and unpinned", and a *pinned* daemon on a scope nobody closes is
equally a leak — one the scope store, not this field, would have to show.

### The author seat: the sugar I would want

The author seat owns this; what the data above makes worth having:

1. **`daemon body` and `daemon in scope body` as the two spellings, and no third.** The
   authoring surface should offer `fork`, `daemon` (= `fork` with `daemon := true`) and
   `daemon in scope` (= `forkScoped`), and should *not* offer `forkIn` with a written
   `daemon := false`: the machine forces the flag there
   (`Machine/Fibers.lean:1205`, `:1213`) and a surface that lets an author write a flag the
   machine ignores is a surface that teaches the wrong model. The reader keeps reading
   rc.112's `Effect.forkIn` — that is a different obligation.
2. **`daemon` should require a scope, or say it does not have one.** The elaborated form of a
   bare `daemon body` is the thing `daemonsQuiet` flags. The cheapest honest design is that
   `daemon` elaborates to `forkScoped` when there is an enclosing `scoped` in the `Src` tree
   and to a detached fork otherwise, with the detached case named differently — `detach body`
   — so that "this fiber is held by nothing" is something an author wrote on purpose.
3. **The supervision tree as an authoring-time answer.** `Api.supervision` runs on the
   elaborated program, so `author`/`authorModule` can hand back the fork sites beside the
   certificate at no cost. An agent that writes a program and is told "this program has one
   detached daemon, at path `[0,0]`" before it runs anything is the whole "programs as data"
   claim in one interaction.
4. **Not a supervision *strategy* in the syntax.** No restart policy, no supervisor tree
   constructor. Those are programs over the fork sites, not a new alphabet — the estate's rule
   is one program representation, and a supervisor is an `Eff` that forks and awaits.

## 6. Verification

Run from `/Users/pooks/Dev/lean4-effect4-daemons`:

```
lake build Effect4.Api.Supervision
lake build Effect4.Laws.Api.Supervision
lake build Test.Api.SupervisionContract
```

All three green; every `#guard` and `#guard_msgs` in the three files is part of those builds.
The whole-root builds (`Effect4`, `Effect4.Laws`, `Test.All`) are the coordinator's: the brief
forbids them here. The two root imports are in place —
`src/Effect4/Laws.lean:40` reaches both new library modules and `Test/All.lean:82` the battery
— so the module-closure gate has what it needs.

The axiom sweep, in a scratch file importing the three built modules:

```lean
import Effect4.Api.Supervision
import Test.Api.SupervisionContract
import Effect4.Laws.Api.Supervision
open Lean Elab Command Meta
#eval show CommandElabM Unit from do
  let env ← getEnv
  let idxs := #[`Effect4.Api.Supervision, `Effect4.Laws.Api.Supervision,
    `Test.Api.SupervisionContract].filterMap (fun m => env.getModuleIdx? m)
  let mut bad : Array (Name × List Name) := #[]
  let mut total : Nat := 0
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if idxs.contains i then
        if !n.isInternal then
          total := total + 1
          let ax ← liftCoreM (collectAxioms n)
          let extra := ax.filter (fun a => a != ``propext && a != ``Quot.sound)
          if !extra.isEmpty then bad := bad.push (n, extra.toList)
  logInfo m!"declarations checked: {total}; outside the ceiling: {bad.size}"
  for (n, ax) in bad do logInfo m!"  {n}: {ax}"
```

→ `declarations checked: 219; outside the ceiling: 0`.

The census, in a scratch file importing `Effect4.Laws.Api.Supervision` and
`Effect4.Laws.Auto.Census`:

```lean
#auto_census Effect4.Laws.Api.Supervision using aesop
```

→ `8 of 44 theorems closed from their statements; 44 source lines they now take`, the eight
being `spawn_fibers`, `spawn_trace`, `parentOf_append_same`, `spawn_child`, `spawn_nextId`,
`parentOf_append_none`, `nodeSizeLayer_eq`, `publish_status`. The two `parentOf_*` are now
`aesop`; the six others are `rfl` (see §3).

No `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`, `extern` or `implemented_by`; no
`simp_all`, no hand-written `first | …` or `try` in the law module; every hand `simp` is
`simp only`.

## 7. Owed

1. **"at those paths".** `supervision_static` proves that the flag on a `forked` event is the
   fork site's. It does **not** prove that the event was emitted *at that site's path*, because
   `RunEvent.forked` carries no path: the compiled code carries provenance
   (`EffThunk.act p`, a `Point`, `Program/Compile.lean:619,988`) but the event drops it. To
   close this the machine would need a path on `RunEvent.forked`, or the law would have to run
   through the compile's `Point`-to-path relation. The battery pins the correspondence by
   count and by flag on three runs (`Test/Api/SupervisionContract.lean:92-98`) and nothing
   more. **I did not change the machine.** If the coordinator wants it, the diff is one field
   on one constructor plus every `spawn` call site, and it should be a machine-seat decision.
2. **No law that a `forked` event is the *only* way a fiber enters `m.fibers`.** `spawn` is
   the only caller of `RunFiber.make` inside the machine (`Api.load` makes the root), which is
   what makes `FiberStatus.root` exact; that is read off the source, not proved.
3. **No law about `runIn`.** A `fiberRunIn` pin reads as `.pinned` and is correct data, but no
   theorem says so; `linkScope` is shared, so the theorem would be `spawn_status_*`'s shape
   over `Cmd.link`.

Two items that were owed here are now **settled by the coordinator, at the merge, not by this
seat**: the `nodeSizeAlg` duplication against `src/Effect4/Laws/Program/Size.lean` (§3a), and
the `Api.Run` → `Api.Inspection` rename with `Observation.daemons` (§5). Neither is a change
to this branch.

## 8. Decisions for the owner

* **D1 — `FiberStatus.root`.** Keep the fifth alternative (recommended, §2) or drop it and
  filter `Api.root` out of `unpinnedDaemonsAlive`.
* **D2 — the six `rfl` proofs** the census reports (§3). Keep `rfl` (recommended: axiom-free)
  or convert to `aesop` for uniformity, at the cost of `propext` on two of them.
* **D3 — a path on `RunEvent.forked`** (§7.1). Closes "at those paths"; it is a machine change
  and I stopped at that boundary.
* **D4 — the authoring spellings** (§5): `fork` / `daemon in scope` / `detach`, with no
  author-written `daemon` flag at a pin. The author seat owns it; this is the recommendation
  the data supports.

Not open: the shape of the observation. The coordinator ruled it while this seat was
finishing — `Observation` gains `fibers` **and** `daemons : List FiberId` (§5) — and does both
merge edits itself.
