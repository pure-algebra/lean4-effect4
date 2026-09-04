# The `Eff` compile (lane A3 of the AST relation)

Date: 2026-09-04. Status: design, grilled below; nothing implemented yet. Plan:
`docs/research/2026-09-04-ast-relation-plan.md` §3. Inputs measured: `Effect4/Runtime/Runtime.lean`
(`Prim`, `PrimInterp`, `armA`, `step`), `Effect4/Deep/Stores.lean` (`progOf`, `contAOf`,
`actionOf`, `stores`), `Effect4/Deep/ForkFlow.lean` (`forkParkOf`, `forkActionOf`,
`forkInterp`), `Effect4/Semantics/RegionSimulation.lean` (`Config`, `RegionName`,
`compileRegion`, `regionInterp`).

## 0. The one finding that changes the machine

rc.112's `Iterator` frame holds a JavaScript generator object; `cont[contA](value)` calls
`iterator.next(value)`, which *advances the object*. The frame model abstracts the object
as a name: `Prim.iterator (generator : ν) (cursor : β)`, with

```
armA (iterator generator cursor) value = match (iterNext generator value).snd with
  | done result  => (success result, [])
  | halt cause   => (failure cause, [])
  | resume next  => (next, [iterator generator cursor])     -- Runtime.lean:848-852
```

The frame pushed under the yielded effect carries the *same* name, so the next resume
calls `iterNext generator value'` again: the generator's progress can only be a function
of the name and the last answer. A body with two `yield*`s is not expressible: after the
second answer the model resumes at the first. The census row `op.Iterator` is green because
its clauses are about the inline fold and the three outcomes, not about progress; the
witnesses (`Deep.Stores`) use `iterNext := fun _ v => ([], done v)`, a one-shot generator.

The fix is data, not a hook: the resume outcome names the advanced generator,

```
inductive IterStep … | done (value : β) | halt (cause : Cause …) | resume (next : Prim …) (continueAs : ν)
armA (iterator generator cursor) value = … | resume next continueAs => (next, [iterator continueAs cursor])
```

which is exactly "the object advanced": the frame is the same frame, its state moved. Cost:
`IterStep`, `armA`, `step`'s iterator arm (through `armA`), `iteratorFolded` (unchanged),
`armA_iterator_resume` and `iterator_folds_inline` (restated with `continueAs`), the
frames contract's statement snapshot (`Effect4Test/Runtime/FramesContract.lean`), the
`op.Iterator` coverage snapshot, and `Deep.Stores.stores.iterNext` (a one-shot generator
returns `done`; nothing there yields). Nothing else reads `IterStep`. This is the first
concrete correction the AST forces on the machine, and it is the kind the plan expected
(§2.1: `gen` as one `Iterator` primitive is the fidelity decision).

## 1. Alphabets

Names are addresses (plan §3). Everything is first-order and derives `DecidableEq`.

```lean
/-- Where a compiled program stands: the subterm, the values in scope, fuel, the tape. -/
structure Point where
  path : List Nat            -- the subterm of the root program (child index at each node)
  env  : List Val            -- positional values, D1
  fuel : Nat                 -- loops and the direct evaluator's exactness (S4's Config.fuel)
  tape : List Bool           -- decisions left, flows' `choose` sites only
deriving DecidableEq

inductive EffName
  | cont (p : Point)         -- `bind`'s continuation: rest at env ++ [v]
  | caught (p : Point)       -- `catchCause`'s handler at env ++ [cause]
  | onValue (p : Point) | onCause (p : Point)   -- `matchCause`'s two arms
  | fin (p : Point)          -- `onExit`'s finalizer name: its program at env ++ [exit]
  | restore (exit : ExitV) | merge (exit : ExitV)   -- the exit path's two names, as Stores spells them
  | gen (p : Point) (pc : List Nat)  -- a generator: its body's point and the statement path it stands at
  | loop (p : Point)         -- `whileLoop`: the loop's point; the cursor is the β
  | register (p : Point) | cancel (p : Point)     -- an async row's registration and cancel
  | release (p : Point)      -- `acquireRelease`'s release, a finalizer name
  | scopeCont (region : Nat) (p : Point) | scopeClose (region : Nat) (p : Point)  -- `scoped`'s frames, as RegionName spells them
  | reFail (cause : CauseV)  -- `cancelThenFail`'s tail, as Stores spells it
  | withWaiter (base : EffName) (waiter : FiberId) (token : Nat)  -- `cancelName`, as Stores spells it
  | constant (v : Val)

inductive EffThunk
  | pure (p : Point)         -- `sync`: the term at the point, evaluated in its env
  | body (p : Point)         -- `suspend`: the subterm at the point
  | op (operation : SyncOp)  -- a store operation, from a row and a request value
  | park (kind : ParkKind)   -- `awaitFiber`
  | act (p : Point)          -- `withFiber`: the action term at the point, expanded at run time
```

`Val`, `Err`, `Defect`, `FiberId`, `Ann`, `Ctx` and the store `Stores` are `Deep.Stores`'s;
the program carrier is `Prim EffName EffThunk Val Err Defect FiberId Ann` and the machine
`RunMachine … Ctx Stores`. The stores are reused unchanged: `Deep.Stores.stores` is
re-instantiated over `EffName`/`EffThunk` by one functor (its `Name`/`Thunk` arms that
matter are the ones `EffName`/`EffThunk` copy: `restore`, `merge`, `reFail`, `withWaiter`,
`op`, `park`), which is the "absorbed, not duplicated" of plan §1.1.

## 2. The compile

`compile (root : Eff Op) : Point → Prim …`, structural in the subterm at the point
(`subtermAt root p.path`), with `evalTerm : Term → List Val → Option Val` the pure term
evaluator (atoms through an `AtomInterp`, a name → function table the signature carries as
data plus one interpretation, the same discipline as `FnName`):

| constructor | compiles to |
| --- | --- |
| `succeed v` | `success (eval v)` |
| `fail e` / `failCause c` / `yieldError e` | `failure (Cause.fail (err e))` / `failure (causeOf c)` / `yieldableError (err e)` |
| `sync t` | `sync (pure p)`; `syncValue (pure p) = eval t` |
| `suspend b` | `suspend (body p/0)`; `suspendBody (body q) = compile q` |
| `perform op r` | by the row's kind: `sync (op (SyncOp.ofRow row (eval r)))`; `async (register p) withSignal cancel` per the store; a program row: `suspend (body …)` into the Layer/Context model's program |
| `bind a b` | `onSuccess (compile p/0) (cont p)`; `contA (cont p) v = compile (p/1 with env ++ [v])` |
| `gen body` | `iterator (gen p []) unit`; `iterNext (gen p pc) v` runs the body from `pc`, binding `v` when the statement at `pc` was a `bindYield`, through pure statements (`ret`, `ifElse` decided by the env, `whileTrue`/`break` with fuel) to the next yield: `resume (compile e) (gen p pc')`, or `done (eval v)`, or `halt` on a yielded failed exit |
| `catchCause b h` | `onFailure (compile p/0) (caught p)`; `contE (caught p) cause = compile (p/1 with env ++ [causeVal cause])` |
| `matchCause b v c` | `onSuccessAndFailure (compile p/0) (onValue p) (onCause p)` |
| `onExit b f` | `onExit (compile p/0) (fin p) false`; `finalizerProgram (fin p) exit = some (compile (p/1 with env ++ [exitVal exit]))`; `restoreName`/`mergeName` as Stores |
| `exit b` | `exitFrame (compile p/0)` |
| `uninterruptible b` / `interruptible b` | `withFiber (act p)` with `withFiberOf (act p) = setInterruptible (compile p/0) false/true` |
| `branch t a b` | `suspend (body p)` where `suspendBody (body p)` = `compile p/1` or `p/2` by `eval t` (one `suspend` frame, as the printed `Effect.suspend(() => t ? a : b)`) |
| `whileLoop i t s b` | `suspend (body p)` → `whileLoop (loop p) (eval i)`; `loopTest (loop p) c = eval t (env ++ [c])`, `loopBody (loop p) c = compile (p/3 with env ++ [c])`, `loopStep (loop p) c = eval s (env ++ [c, ?])` — see grill G3 |
| `yieldNow n` | `yieldNowWith n` |
| `callback op r` | `async (register p) withSignal cancel` where the row's store decides the cancel (`Deferred.await`: `registerAwait`/`cancelAwait` as Stores) |
| `awaitFiber f mode` | `suspend (park (join id mode))` with `id` read off `eval f` (a `Val.fiber`); a non-handle is the refused park (`Except.error (die badName)`) as ForkFlow does |
| `withFiber action` | `withFiber (act p)`; `withFiberOf (act p)` builds the `WithFiberAction` with programs `compile` of the subterms and handles/lists read off `eval` |
| `scoped b` | the region frames `compileRegion` emits: `onSuccessAndFailure (compile p/0 under a fresh scope) (scopeCont r p) (scopeClose r p)`, the scope made by a `sync (op (scopeMake sequential))` bound first — D3's shape |
| `acquireRelease a r` | `uninterruptible (onExit (compile p/0) (release p) …)` registered on the ambient scope: the same frames the region compile emits for `acquire` |
| `choose s l r` | by the tape: `compile p/1` or `p/2` with the tape's head consumed; tape exhausted → `suspend (body p)` (the live frontier, S4) |

The table is a function of the program: `interpOf root : RunInterp …` is defined by the
equations in the right column, so "the table is the AST" holds by definition. `ofFlow` and
`ofScript` (plan §4) are separate front-ends; R3 is stated once `compile` exists.

## 3. The direct evaluator and R2

`eval : Eff Op → Point → Stores → Outcome` is the single-fiber reference, structural in
the subterm and fuelled, over the same `Stores` (Ref/Deferred/Scope) and the same
`AtomInterp`. It does not evaluate forks, parks, races or the async registration: those
arms answer `Outcome.machine` ("what the machine does"), and R2 is stated for the
single-fiber fragment (every constructor except `withFiber`, `awaitFiber`, `callback`,
`yieldNow`), fuel-exact in S4's manner:

```
theorem compile_agrees (root) (p) (st) (h : singleFiber root) :
  run (interpOf root).toPrimInterp p.fuel (FrameFiber.mk (compile root p) [] true none false) = ⟨eval root p st …⟩
```

with the stores threaded through `RunInterp.syncState` on the machine side and through
`eval` on the other, so the statement is over `RunMachine`'s `drive` of one fiber, not over
the bare frame runner, exactly as `leaveConfig_agrees_runRegions` is. Progress (R2's second
half): `WellTyped sig root → compile root p` never has `notImplemented` in its image and
`interpOf root` never answers it on a name `compile` minted.

## 4. Grill

* **G1. Multi-yield generators.** §0. Without the `continueAs` name the compile of `gen`
  is unfaithful for every body with two `yield*`s; with it the statement path `pc` is the
  generator's program counter and `iterNext` is a pure function of `(name, value)` again.
  The change is small and it is the first correction the AST forces on the machine.
* **G2. `branch` through `suspend`.** rc.112 has no `if` primitive; the printed
  `Effect.suspend(() => t ? a : b)` is one `Suspend` frame followed by the branch's
  program. The compile emits the same. The flows' `branch` (E4-FLOW-CE-029) was "decided
  by value at compile time" with no frame; `ofFlow` maps it to `Eff.branch`, which now
  costs one `suspend` on both sides equally — R3 is stated against `compile ∘ ofFlow`, not
  against the old `compileRegion` (D3).
* **G3. `whileLoop`'s step reads the closure cursor.** rc.112's `While` (`internal/effect.ts:4624-4645`):
  `[contA](value) { step(value); if (while()) { push(this); return body() } return exitVoid }`
  — `step` mutates the closure's cursor from the body's answer *and* the cursor it can read;
  `while` and `body` read the cursor. The frame model's `armA (whileLoop loop _) value`
  drops the stored cursor and steps `loopStep loop value` from the answer alone, so a loop
  whose step counts (`i++`) is not expressible. Same kind of shortcut as §0, same kind of
  fix: `PrimInterp.loopStep : ν → β → β → β` (loop, current cursor, answer) and the arm
  steps the stored cursor. The AST's `step` over `env ++ [cursor, answer]` (A1 as written)
  is then exactly the model; no A1 change. The register rows are `E4-RUN-CE-027` (two-yield
  generator) and `E4-RUN-CE-028` (a counting loop); both corrections are one Opus piece.
* **G4. Positions vs. names.** A `Point.path` into the root program is what `RegionName.cont
  (point : Config)` does with a block id; the difference is that the subterm is recovered by
  `subtermAt`, a total function with a refusal (`none` → `suspend`, the frontier). The
  compile is structural in the subterm, the names are structural in the path: the pair is
  well-founded because every name minted by `compile` at `p` has a longer path.
* **G5. Stores reuse.** `Deep.Stores.stores` is over `Name`/`Thunk`; `EffName`/`EffThunk`
  copy the eight arms the stores read. Rather than a functor, the honest first cut is a
  second `RunInterp` in `Effect4/Syntax/Interp.lean` whose store-touching arms call the
  same `syncOpStep`, `DeferredStore.register`, `storesCloseScope`, `finProgram` — the
  functions, not the names. Duplication is then exactly the alphabet, and a later functor
  removes it once both are real (plan §1.1's "absorbed").
* **G6. Fuel.** `Point.fuel` decreases on every `bind`/`gen` step and every loop iteration,
  as `Config.fuel` does; exhaustion compiles to `suspend (body p)` at fuel 0 — a live
  frontier the machine reports as running, never an exit (DB-04).
* **G7. What is not compiled.** `raceAll` entrants, forks, parks, the async registration:
  the machine performs them; the compile's job is to hand the machine the right action
  with the right programs. R2 is silent on them by construction; R4 (host traces) is where
  they are checked. Same fence S4 drew.

## 5. Order

1. The machine correction (§0): `IterStep.resume … continueAs`, the four restatements, the
   two snapshots. Mechanical; an Opus piece.
2. A1 correction G3 (`whileLoop`'s `step` over the answer). Mine, small.
3. `Effect4/Syntax/Compile.lean`: `Point`, `EffName`, `EffThunk`, `subtermAt`, `evalTerm`,
   `compile`, `iterNext`, `interpOf`. Mine (design); the `#guard` battery over the
   witnesses' programs (Deep.Witnesses' W1–W13 respelled as `Eff`) is an Opus piece.
4. `eval` and R2, then R3 with `ofFlow`. Proofs after carriers.
