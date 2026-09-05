import OCaml5.Avatar
import OCaml5.Fuzz.Gen

/-!
# OCaml5.Fuzz.Corpus

**What it is.** Round four's random *program* generator over the avatar's alphabet: one
`Corpus.Prog` per seed, rendered **twice** from the one description — as the OCaml fixture the
avatar runs and as the TypeScript fixture rc.112 runs — with its tape and metadata, plus the two
aggregates a runner links. The oracle is rc.112 through the estate harness.

**Depends on.** `OCaml5.Fuzz.Gen`, `OCaml5.Avatar` (the alphabet, `OCaml5.Ml` for the OCaml side).

**Properties.**
* **Well-scoped by construction**: every operand is a handle the program already bound, on both
  sides — *by construction*; *tested* (the `#guard`s at the end).
* **One tape entry per fork**, and every program ends on a value — *tested*.
-/

namespace OCaml5.Fuzz

/-! ## Round four: a random *program* generator over the avatar's alphabet

`docs/research/2026-09-04-spike-a0-avatar.md` and the round-four brief: the corpus must be far
larger and nastier, and the oracle is rc.112 itself through the estate harness, not `replayEval`.
That unblocks the differential fuzzer of round three's request 4 by changing the reference — the
comparison is now `avatar` vs `rc.112`, on programs generated here and rendered **twice** from one
Lean description.

The alphabet is what the avatar answers (`deep_fibers.ml`'s `Effect.t` constructors) intersected
with what the estate's generated fixtures declare, so that both renderings land in a shape their
runner already consumes:

| family | operations | OCaml wrappers | TypeScript service |
| --- | --- | --- | --- |
| fiber | `fork`, `forkDetach`, `join`, `awaitValue`, `awaitError`, `interrupt`, `started`, `cleanups` | `Fibers_fixture` | `Fibers` (`fiber-fixture.ts`) |
| fiber, extra | `yieldNow`, `interruptAll`, `awaitAll` | `Extra_fixture` | declared on `Fibers` here |
| ref | `make`, `get`, `set`, `update`, `modify`, `getAndSet` | `Store_fixtures` | `Refs` (`ref-fixture.ts`) |
| deferred | `make`, `succeed`, `fail`, `isDone`, `poll`, `awaitValue`, `awaitError` | `Store_fixtures` | `Deferreds` |
| scope | `make`, `addFinalizer`, `remove`, `close` | `Store_fixtures` | `Scopes` |
| layer | `build`, `provideCount`, `scopeOf`, `close` | `Store_fixtures` | `Layers` |

`Op_ref_try_take` is in the avatar and not in `ref-fixture.ts`'s `Refs`, so it is out; the three
extra fiber rows are in the avatar and in rc.112 (`Fiber.interruptAll`, `Fiber.awaitAll`,
`Effect.yieldNowWith`) but not in the *generated* fiber fixture, so a program that uses one is
flagged `usesExtra` in its `meta.json` and the tail that runs it needs those three methods.

Every operand is a handle the program has already bound, so a generated program is well-scoped by
construction on both sides; the generator never has to be filtered for scope.
-/

namespace Corpus

/-- What an operation binds. `unitK` is a statement, not a binding. -/
inductive Kind where
  | fiberK | refK | defK | scopeK | layerK | valueK | unitK
deriving DecidableEq, Repr

/-- One operation. Every operand is a **variable number**: `join 3` is `join v3`, and `v3` is
whatever the third binding of the program was. -/
inductive Op where
  | fork (code : Nat) (daemon : Bool)
  | join (f : Nat)
  | awaitValue (f : Nat)
  | awaitError (f : Nat)
  | interrupt (f : Nat)
  | started
  | cleanups
  | yieldNow
  | interruptAll (fs : List Nat)
  | awaitAll (fs : List Nat)
  | refMake (n : Nat)
  | refGet (r : Nat)
  | refSet (r v : Nat)
  | refUpdate (r a : Nat)
  | refModify (r a : Nat)
  | refGetAndSet (r v : Nat)
  | defMake
  | defSucceed (d v : Nat)
  | defFail (d e : Nat)
  | defIsDone (d : Nat)
  | defPoll (d : Nat)
  | defAwaitValue (d : Nat)
  | defAwaitError (d : Nat)
  | scopeMake
  | scopeAdd (s k : Nat)
  | scopeRemove (s k : Nat)
  | scopeClose (s : Nat)
  | layerBuild (k : Nat)
  | layerProvideCount (k : Nat)
  | layerScopeOf (h : Nat)
  | layerClose
deriving Repr

/-- What the operation binds, which is what makes a later operand well-typed. -/
def Op.kind : Op → Kind
  | .fork _ _ => .fiberK
  | .refMake _ => .refK
  | .defMake => .defK
  | .scopeMake => .scopeK
  | .layerBuild _ => .layerK
  | .interrupt _ => .unitK
  | .refSet _ _ => .unitK
  | .refUpdate _ _ => .unitK
  | .scopeRemove _ _ => .unitK
  | .yieldNow => .unitK
  | _ => .valueK

/-- The families a program touches, for `meta.json` and for routing. -/
def Op.family : Op → String
  | .refMake _ | .refGet _ | .refSet _ _ | .refUpdate _ _ | .refModify _ _
  | .refGetAndSet _ _ => "ref"
  | .defMake | .defSucceed _ _ | .defFail _ _ | .defIsDone _ | .defPoll _
  | .defAwaitValue _ | .defAwaitError _ => "deferred"
  | .scopeMake | .scopeAdd _ _ | .scopeRemove _ _ | .scopeClose _ => "scope"
  | .layerBuild _ | .layerProvideCount _ | .layerScopeOf _ | .layerClose => "layer"
  | _ => "fiber"

/-- The three rows that are in the avatar and in rc.112 but not in the generated fiber
fixture's service. -/
def Op.isExtra : Op → Bool
  | .yieldNow => true
  | .interruptAll _ => true
  | .awaitAll _ => true
  | _ => false

/-- The variable numbers an operation reads. Used to name a binding `_v` when nothing later
refers to it, which is how `fibers_fixture.ml` spells its own unused results (`let _a = fork 0`)
and what keeps `ocamlc`'s warning 26 quiet on a generated fixture. -/
def Op.uses : Op → List Nat
  | .join f | .awaitValue f | .awaitError f | .interrupt f => [f]
  | .interruptAll fs | .awaitAll fs => fs
  | .refGet r | .refSet r _ | .refUpdate r _ | .refModify r _ | .refGetAndSet r _ => [r]
  | .defSucceed d _ | .defFail d _ | .defIsDone d | .defPoll d
  | .defAwaitValue d | .defAwaitError d => [d]
  | .scopeAdd s _ | .scopeRemove s _ | .scopeClose s => [s]
  | .layerScopeOf h => [h]
  | _ => []

/-- A fork is a decision site: one tape entry per fork, in fork order, exactly as
`fiber-tail.ts`'s `decide` and `deep_fibers.ml`'s `Tape.decide` read it. -/
def Op.isFork : Op → Bool
  | .fork _ _ => true
  | _ => false

/-- A generated program. `ops` is in evaluation order; `tape` has one branch per fork. -/
structure Prog where
  name : String
  seed : Nat
  ops : List Op
  tape : List Bool
deriving Repr

/-! ### The generator

Handles are tracked per kind so that every operand exists. The child-body codes are the shared
table both faces carry (`fibers_fixture.ml:12-40`, `fiber-fixture.ts`): 0 succeeds with 11, 1
with 22, 2 fails with 1, 3 fails with 2, 4 never settles. Codes 5 and 6 are the avatar's
round-three additions and are drawn less often, since 6 completes the deferred at handle 0 and
only makes sense when one exists. -/

structure Env where
  fibers : List Nat := []
  refs : List Nat := []
  defs : List Nat := []
  scopes : List Nat := []
  layers : List Nat := []
  next : Nat := 0
deriving Repr

private def pickFrom (xs : List Nat) : Gen Nat := do
  let i ← pick xs.length
  return xs.getD i 0

private def pickSome (xs : List Nat) : Gen (List Nat) := do
  if xs.length == 1 then return xs
  let k ← pick 2
  if k == 0 then return xs
  let i ← pick xs.length
  return [xs.getD i 0]

/-- One operation, drawn from whatever the environment makes legal. The weights are the shape of
the corpus: forks and their observations dominate, the stores are the interleaving, and the
extras are rare enough that most programs stay inside the generated fixtures' services. -/
def genOp (e : Env) : Gen Op := do
  let k ← pick 100
  -- makes first, so the environment fills up
  if k < 10 || e.fibers.isEmpty then
    let c ← pick 100
    -- body 6 completes the Deferred at handle 0 (`fibers_fixture.ml:36-40`), so it is only
    -- drawn once the program has made one; body 5 is the mask-across-a-yield child (M2).
    let code := if c < 25 then 0 else if c < 45 then 1 else if c < 60 then 2
                else if c < 72 then 3 else if c < 90 then 4 else if c < 95 then 5
                else if e.defs.isEmpty then 0 else 6
    let d ← pick 5
    return .fork code (d == 0)
  else if k < 16 && e.refs.length < 3 then
    let n ← pick 10
    return .refMake (n + 1)
  else if k < 21 && e.defs.length < 3 then
    return .defMake
  else if k < 25 && e.scopes.length < 2 then
    return .scopeMake
  else if k < 29 && e.layers.length < 2 then
    let b ← pick 4
    return .layerBuild b
  -- fiber observations
  else if k < 35 then return .join (← pickFrom e.fibers)
  else if k < 41 then return .awaitValue (← pickFrom e.fibers)
  else if k < 46 then return .awaitError (← pickFrom e.fibers)
  else if k < 52 then return .interrupt (← pickFrom e.fibers)
  else if k < 55 then return .started
  else if k < 58 then return .cleanups
  -- the extras
  else if k < 60 then return .yieldNow
  else if k < 62 then return .interruptAll (← pickSome e.fibers)
  else if k < 64 then return .awaitAll (← pickSome e.fibers)
  -- stores, when they exist
  else if k < 76 then
    if e.refs.isEmpty then return .started else
    let r ← pickFrom e.refs
    let a ← pick 10
    let j ← pick 5
    if j == 0 then return .refGet r
    else if j == 1 then return .refSet r a
    else if j == 2 then return .refUpdate r (a + 1)
    else if j == 3 then return .refModify r (a + 1)
    else return .refGetAndSet r a
  else if k < 87 then
    if e.defs.isEmpty then return .cleanups else
    let d ← pickFrom e.defs
    let v ← pick 10
    let j ← pick 6
    if j == 0 then return .defSucceed d v
    else if j == 1 then return .defFail d (v + 1)
    else if j == 2 then return .defIsDone d
    else if j == 3 then return .defPoll d
    else if j == 4 then return .defAwaitValue d
    else return .defAwaitError d
  else if k < 94 then
    if e.scopes.isEmpty then return .started else
    let s ← pickFrom e.scopes
    let key ← pick 4
    let j ← pick 4
    if j == 0 then return .scopeAdd s (key + 1)
    else if j == 1 then return .scopeRemove s (key + 1)
    else if j == 2 then return .scopeClose s
    else return .scopeAdd s (key + 1)
  else
    if e.layers.isEmpty then return .cleanups else
    let j ← pick 3
    if j == 0 then
      let b ← pick 4
      return .layerProvideCount b
    else if j == 1 then return .layerScopeOf (← pickFrom e.layers)
    else return .layerClose

private def bind (e : Env) (op : Op) : Env :=
  let v := e.next
  match op.kind with
  | .fiberK => { e with fibers := e.fibers ++ [v], next := v + 1 }
  | .refK => { e with refs := e.refs ++ [v], next := v + 1 }
  | .defK => { e with defs := e.defs ++ [v], next := v + 1 }
  | .scopeK => { e with scopes := e.scopes ++ [v], next := v + 1 }
  | .layerK => { e with layers := e.layers ++ [v], next := v + 1 }
  | .valueK => { e with next := v + 1 }
  | .unitK => e

/-- Every operand of every operation is a handle of the right kind that an earlier operation
bound. The generator maintains this by construction; the `#guard`s below check it, because a
badly scoped program would be a type error in *both* renderings and the corpus is meant to
compile unattended. -/
def Prog.wellScoped (p : Prog) : Bool :=
  let step : (Bool × Env) → Op → (Bool × Env) := fun (ok, e) op =>
    let live :=
      match op with
      | .join f | .awaitValue f | .awaitError f | .interrupt f => e.fibers.contains f
      | .interruptAll fs | .awaitAll fs => fs.all e.fibers.contains
      | .refGet r | .refSet r _ | .refUpdate r _ | .refModify r _
      | .refGetAndSet r _ => e.refs.contains r
      | .defSucceed d _ | .defFail d _ | .defIsDone d | .defPoll d
      | .defAwaitValue d | .defAwaitError d => e.defs.contains d
      | .scopeAdd s _ | .scopeRemove s _ | .scopeClose s => e.scopes.contains s
      | .layerScopeOf h => e.layers.contains h
      | _ => true
    (ok && live, bind e op)
  (p.ops.foldl step (true, {})).1

private def genOps (fuel : Nat) (e : Env) : Gen (List Op) :=
  match fuel with
  | 0 => return []
  | n + 1 => do
      let op ← genOp e
      let rest ← genOps n (bind e op)
      return op :: rest

/-- A value-returning operation to end on, so that both renderings have a result: OCaml's
`unit -> value` and TypeScript's `Effect.gen` return. -/
private def genLast (e : Env) : Gen Op := do
  let k ← pick 4
  if k == 0 || e.fibers.isEmpty then return .started
  else if k == 1 then return .cleanups
  else if k == 2 then return .awaitValue (← pickFrom e.fibers)
  else return .join (← pickFrom e.fibers)

private def envOf (ops : List Op) : Env := ops.foldl bind {}

/-- One program of `size` operations, plus a value-returning last one, plus its tape. -/
def genProg (seed size : Nat) : Prog :=
  let g : Gen Prog := do
    let ops ← genOps size {}
    let last ← genLast (envOf ops)
    let all := ops ++ [last]
    let forks := (all.filter (·.isFork)).length
    let tape ← (List.range forks).foldl (fun (acc : Gen (List Bool)) _ => do
      let xs ← acc
      let b ← pick 2
      return xs ++ [b == 0]) (pure [])
    return { name := "p" ++ toString seed, seed := seed, ops := all, tape := tape }
  (g (rngOf seed)).1

/-! ### Rendering, twice, from the one description -/

private def vn (n : Nat) : String := "v" ++ toString n
private def natsOf (xs : List Nat) (sep : String) (f : Nat → String) : String :=
  String.intercalate sep (xs.map f)

/-- The OCaml expression, in the avatar's fixture spelling: the wrappers of
`fibers_fixture.ml`, `store_fixtures.ml` and `extra_fixture.ml`, qualified, so that a generated
fixture is one more module in `build-avatar.sh`'s list and needs no edit to the others. -/
def Op.ocaml : Op → String
  | .fork c d => (if d then "Fibers_fixture.fork_detach " else "Fibers_fixture.fork ") ++ toString c
  | .join f => "Fibers_fixture.join " ++ vn f
  | .awaitValue f => "Fibers_fixture.await_value " ++ vn f
  | .awaitError f => "Fibers_fixture.await_error " ++ vn f
  | .interrupt f => "Fibers_fixture.interrupt " ++ vn f
  | .started => "Fibers_fixture.started ()"
  | .cleanups => "Fibers_fixture.cleanups ()"
  | .yieldNow => "Extra_fixture.yield ()"
  | .interruptAll fs => "Extra_fixture.interrupt_all [ " ++ natsOf fs "; " vn ++ " ]"
  | .awaitAll fs => "Extra_fixture.await_all [ " ++ natsOf fs "; " vn ++ " ]"
  | .refMake n => "Store_fixtures.ref_make " ++ toString n
  | .refGet r => "Store_fixtures.ref_get " ++ vn r
  | .refSet r v => "Store_fixtures.ref_set " ++ vn r ++ " " ++ toString v
  | .refUpdate r a => "Store_fixtures.ref_update " ++ vn r ++ " " ++ toString a
  | .refModify r a => "Store_fixtures.ref_modify " ++ vn r ++ " " ++ toString a
  | .refGetAndSet r v => "Store_fixtures.ref_get_and_set " ++ vn r ++ " " ++ toString v
  | .defMake => "Store_fixtures.def_make ()"
  | .defSucceed d v => "Store_fixtures.def_succeed " ++ vn d ++ " " ++ toString v
  | .defFail d e => "Store_fixtures.def_fail " ++ vn d ++ " " ++ toString e
  | .defIsDone d => "Store_fixtures.def_is_done " ++ vn d
  | .defPoll d => "Store_fixtures.def_poll " ++ vn d
  | .defAwaitValue d => "Store_fixtures.def_await_value " ++ vn d
  | .defAwaitError d => "Store_fixtures.def_await_error " ++ vn d
  | .scopeMake => "Store_fixtures.scope_make ()"
  | .scopeAdd s k => "Store_fixtures.scope_add " ++ vn s ++ " " ++ toString k
  | .scopeRemove s k => "Store_fixtures.scope_remove " ++ vn s ++ " " ++ toString k
  | .scopeClose s => "Store_fixtures.scope_close " ++ vn s
  | .layerBuild k => "Store_fixtures.layer_build " ++ toString k
  | .layerProvideCount k => "Store_fixtures.layer_provide_count " ++ toString k
  | .layerScopeOf h => "Store_fixtures.layer_scope_of " ++ vn h
  | .layerClose => "Store_fixtures.layer_close ()"

/-- The TypeScript expression, in the generated fixtures' spelling. A nullary row is a
*property* on the service (`fibers.started`, `deferreds.make`, `layers.close`), which is how
`fiber-fixture.ts` and its siblings declare them. -/
def Op.ts : Op → String
  | .fork c d => (if d then "fibers.forkDetach(" else "fibers.fork(") ++ toString c ++ ")"
  | .join f => "fibers.join(" ++ vn f ++ ")"
  | .awaitValue f => "fibers.awaitValue(" ++ vn f ++ ")"
  | .awaitError f => "fibers.awaitError(" ++ vn f ++ ")"
  | .interrupt f => "fibers.interrupt(" ++ vn f ++ ")"
  | .started => "fibers.started"
  | .cleanups => "fibers.cleanups"
  | .yieldNow => "fibers.yieldNow(0)"
  | .interruptAll fs => "fibers.interruptAll([" ++ natsOf fs ", " vn ++ "])"
  | .awaitAll fs => "fibers.awaitAll([" ++ natsOf fs ", " vn ++ "])"
  | .refMake n => "refs.make(" ++ toString n ++ ")"
  | .refGet r => "refs.get(" ++ vn r ++ ")"
  | .refSet r v => "refs.set(" ++ vn r ++ ", " ++ toString v ++ ")"
  | .refUpdate r a => "refs.update(" ++ vn r ++ ", " ++ toString a ++ ")"
  | .refModify r a => "refs.modify(" ++ vn r ++ ", " ++ toString a ++ ")"
  | .refGetAndSet r v => "refs.getAndSet(" ++ vn r ++ ", " ++ toString v ++ ")"
  | .defMake => "deferreds.make"
  | .defSucceed d v => "deferreds.succeed(" ++ vn d ++ ", " ++ toString v ++ ")"
  | .defFail d e => "deferreds.fail(" ++ vn d ++ ", " ++ toString e ++ ")"
  | .defIsDone d => "deferreds.isDone(" ++ vn d ++ ")"
  | .defPoll d => "deferreds.poll(" ++ vn d ++ ")"
  | .defAwaitValue d => "deferreds.awaitValue(" ++ vn d ++ ")"
  | .defAwaitError d => "deferreds.awaitError(" ++ vn d ++ ")"
  | .scopeMake => "scopes.make"
  | .scopeAdd s k => "scopes.addFinalizer(" ++ vn s ++ ", " ++ toString k ++ ")"
  | .scopeRemove s k => "scopes.remove(" ++ vn s ++ ", " ++ toString k ++ ")"
  | .scopeClose s => "scopes.close(" ++ vn s ++ ")"
  | .layerBuild k => "layers.build(" ++ toString k ++ ")"
  | .layerProvideCount k => "layers.provideCount(" ++ toString k ++ ")"
  | .layerScopeOf h => "layers.scopeOf(" ++ vn h ++ ")"
  | .layerClose => "layers.close"

/-- The services the program acquires, in the fixed order the renderings emit them. -/
def Prog.services (p : Prog) : List String :=
  let fams := p.ops.map (·.family)
  (["fiber", "ref", "deferred", "scope", "layer"].filter fun f => fams.contains f)

def Prog.usesExtra (p : Prog) : Bool := p.ops.any (·.isExtra)
def Prog.forks (p : Prog) : Nat := (p.ops.filter (·.isFork)).length

private def serviceLine : String → String
  | "fiber" => "  const fibers = yield* Fibers"
  | "ref" => "  const refs = yield* Refs"
  | "deferred" => "  const deferreds = yield* Deferreds"
  | "scope" => "  const scopes = yield* Scopes"
  | _ => "  const layers = yield* Layers"

/-- The OCaml fixture: one `unit -> value` per program, in `fibers_fixture.ml`'s shape, plus
the `programs` table `avatar_main.ml` looks the name up in. -/
def Prog.ocamlBody (p : Prog) : String :=
  -- the last binding is the result, so it is used whatever the operations say
  let lastIdx := (p.ops.filter (fun o => o.kind != Kind.unitK)).length - 1
  let used := lastIdx :: p.ops.flatMap (·.uses)
  let step : (String × Nat) → Op → (String × Nat) := fun (acc, n) op =>
    match op.kind with
    | .unitK => (acc ++ "  ignore (" ++ op.ocaml ++ ");\n", n)
    | _ =>
        let nm := if used.contains n then vn n else "_" ++ vn n
        (acc ++ "  let " ++ nm ++ " = " ++ op.ocaml ++ " in\n", n + 1)
  let (body, n) := p.ops.foldl step ("", 0)
  "let corpus_" ++ p.name ++ " () =\n" ++ body ++ "  " ++ vn (n - 1) ++ "\n"

/-- The TypeScript fixture body: `Effect.gen`, the services it acquires, one `yield*` per
operation, and the last binding returned. -/
def Prog.tsBody (p : Prog) : String :=
  let step : (String × Nat) → Op → (String × Nat) := fun (acc, n) op =>
    match op.kind with
    | .unitK => (acc ++ "    yield* " ++ op.ts ++ "\n", n)
    | _ => (acc ++ "    const " ++ vn n ++ " = yield* " ++ op.ts ++ "\n", n + 1)
  let (body, n) := p.ops.foldl step ("", 0)
  "export const corpus_" ++ p.name ++ " = (n: number) =>\n"
    ++ "  Effect.gen(function* () {\n"
    ++ String.join ((p.services.map serviceLine).map (fun l => "  " ++ l ++ "\n"))
    ++ "    void n\n"
    ++ body ++ "    return " ++ vn (n - 1) ++ "\n  })\n"

end Corpus


/-! ### The two files, and the corpus on disk -/

namespace Corpus

/-- The service declarations, copied from the estate's generated fixtures so that a generated
`fixture.ts` is the same shape their tails already import. `Fibers` carries three methods the
generated `fiber-fixture.ts` does not — `yieldNow`, `interruptAll`, `awaitAll` — because the
avatar and rc.112 both have them (`Effect.yieldNowWith`, `Fiber.interruptAll`, `Fiber.awaitAll`)
and a program that uses one is flagged `usesExtra`. -/
def tsService : String → String
  | "fiber" => String.intercalate "\n"
    ["/** Service `Fibers`: one method per operation of the Lean family, plus the three rows",
     " * `fiber-fixture.ts` does not declare and rc.112 does. */",
     "export class Fibers extends Context.Service<Fibers, {",
     "  readonly fork: (body: number) => Effect.Effect<Fiber.Fiber<number, number>>",
     "  readonly forkDetach: (body: number) => Effect.Effect<Fiber.Fiber<number, number>>",
     "  readonly join: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<number, number>",
     "  readonly awaitValue: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<Option.Option<number>>",
     "  readonly awaitError: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<Option.Option<number>>",
     "  readonly interrupt: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<void>",
     "  readonly started: Effect.Effect<ReadonlyArray<number>>",
     "  readonly cleanups: Effect.Effect<ReadonlyArray<number>>",
     "  readonly yieldNow: (priority: number) => Effect.Effect<void>",
     "  readonly interruptAll: (fibers: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>",
     "  readonly awaitAll: (fibers: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>",
     "}>()(\"Fibers\") {}", ""]
  | "ref" => String.intercalate "\n"
    ["/** Service `Refs` (`git:c407ab7:harness/trace/ref-fixture.ts`). */",
     "export class Refs extends Context.Service<Refs, {",
     "  readonly make: (initial: number) => Effect.Effect<Ref.Ref<number>>",
     "  readonly get: (ref: Ref.Ref<number>) => Effect.Effect<number>",
     "  readonly set: (ref: Ref.Ref<number>, value: number) => Effect.Effect<void>",
     "  readonly update: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<void>",
     "  readonly modify: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<number>",
     "  readonly getAndSet: (ref: Ref.Ref<number>, value: number) => Effect.Effect<number>",
     "}>()(\"Refs\") {}", ""]
  | "deferred" => String.intercalate "\n"
    ["/** Service `Deferreds` (`git:c407ab7:harness/trace/deferred-fixture.ts`). */",
     "export class Deferreds extends Context.Service<Deferreds, {",
     "  readonly make: Effect.Effect<Deferred.Deferred<number, number>>",
     "  readonly succeed: (cell: Deferred.Deferred<number, number>, value: number) => Effect.Effect<boolean>",
     "  readonly fail: (cell: Deferred.Deferred<number, number>, error: number) => Effect.Effect<boolean>",
     "  readonly isDone: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>",
     "  readonly poll: (cell: Deferred.Deferred<number, number>) => Effect.Effect<Option.Option<Result.Result<number, number>>>",
     "  readonly awaitValue: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>",
     "  readonly awaitError: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>",
     "}>()(\"Deferreds\") {}", ""]
  | "scope" => String.intercalate "\n"
    ["/** Service `Scopes` (`git:c407ab7:harness/trace/scope-fixture.ts`). */",
     "export class Scopes extends Context.Service<Scopes, {",
     "  readonly make: Effect.Effect<Scope.Closeable>",
     "  readonly addFinalizer: (scope: Scope.Closeable, key: number) => Effect.Effect<boolean>",
     "  readonly remove: (scope: Scope.Closeable, key: number) => Effect.Effect<void>",
     "  readonly close: (scope: Scope.Closeable) => Effect.Effect<ReadonlyArray<number>>",
     "}>()(\"Scopes\") {}", ""]
  | _ => String.intercalate "\n"
    ["/** Service `Layers` (`git:c407ab7:harness/trace/layer-fixture.ts`). */",
     "export class Layers extends Context.Service<Layers, {",
     "  readonly build: (layer: number) => Effect.Effect<Ref.Ref<number>>",
     "  readonly provideCount: (layer: number) => Effect.Effect<number>",
     "  readonly scopeOf: (service: Ref.Ref<number>) => Effect.Effect<Scope.Closeable>",
     "  readonly close: Effect.Effect<ReadonlyArray<Ref.Ref<number>>>",
     "}>()(\"Layers\") {}", ""]

/-- The `Rows` table of a service, which the tracer needs and the estate's fixtures export
next to the service. -/
def tsRows : String → String
  | "fiber" => "export const FibersRows = { \"fork\": { params: 1, answer: \"Fiber.Fiber<number, number>\" }, \"forkDetach\": { params: 1, answer: \"Fiber.Fiber<number, number>\" }, \"join\": { params: 1, answer: \"number\" }, \"awaitValue\": { params: 1, answer: \"Option.Option<number>\" }, \"awaitError\": { params: 1, answer: \"Option.Option<number>\" }, \"interrupt\": { params: 1, answer: \"void\" }, \"started\": { params: 0, answer: \"ReadonlyArray<number>\" }, \"cleanups\": { params: 0, answer: \"ReadonlyArray<number>\" }, \"yieldNow\": { params: 1, answer: \"void\" }, \"interruptAll\": { params: 1, answer: \"void\" }, \"awaitAll\": { params: 1, answer: \"void\" } }" ++ "\n"
  | "ref" => "export const RefsRows = { \"make\": { params: 1, answer: \"Ref.Ref<number>\" }, \"get\": { params: 1, answer: \"number\" }, \"set\": { params: 2, answer: \"void\" }, \"update\": { params: 2, answer: \"void\" }, \"modify\": { params: 2, answer: \"number\" }, \"getAndSet\": { params: 2, answer: \"number\" } }" ++ "\n"
  | "deferred" => "export const DeferredsRows = { \"make\": { params: 0, answer: \"Deferred.Deferred<number, number>\" }, \"succeed\": { params: 2, answer: \"boolean\" }, \"fail\": { params: 2, answer: \"boolean\" }, \"isDone\": { params: 1, answer: \"boolean\" }, \"poll\": { params: 1, answer: \"Option.Option<Result.Result<number, number>>\" }, \"awaitValue\": { params: 1, answer: \"number\" }, \"awaitError\": { params: 1, answer: \"number\" } }" ++ "\n"
  | "scope" => "export const ScopesRows = { \"make\": { params: 0, answer: \"Scope.Closeable\" }, \"addFinalizer\": { params: 2, answer: \"boolean\" }, \"remove\": { params: 2, answer: \"void\" }, \"close\": { params: 1, answer: \"ReadonlyArray<number>\" } }" ++ "\n"
  | _ => "export const LayersRows = { \"build\": { params: 1, answer: \"Ref.Ref<number>\" }, \"provideCount\": { params: 1, answer: \"number\" }, \"scopeOf\": { params: 1, answer: \"Scope.Closeable\" }, \"close\": { params: 0, answer: \"ReadonlyArray<Ref.Ref<number>>\" } }" ++ "\n"

/-- The `import type` line: only the type names the declared services mention, because
`verbatimModuleSyntax` is on and an unused *value* import would be an error. -/
def tsTypeImports (services : List String) : String :=
  let need : List (String × List String) :=
    [("fiber", ["Fiber", "Option"]), ("ref", ["Ref"]),
     ("deferred", ["Deferred", "Option", "Result"]), ("scope", ["Scope"]),
     ("layer", ["Ref", "Scope"])]
  let names := (need.filter fun p => services.contains p.1).flatMap (·.2)
  let uniq := (["Deferred", "Fiber", "Option", "Ref", "Result", "Scope"]).filter names.contains
  if uniq.isEmpty then "" else "import type { " ++ String.intercalate ", " uniq ++ " } from \"effect\"\n"

private def header (what : String) : String :=
  "/**\n * Generated by OCaml5.Fuzz (spike P5, round four). " ++ what ++ "\n *\n"
    ++ " * Do not edit; regenerate with `ocaml/tools/fuzz.sh corpus`.\n */\n"

/-- One program's `fixture.ts`. -/
def Prog.tsFile (p : Prog) : String :=
  header ("Program `" ++ p.name ++ "`, seed " ++ toString p.seed ++ ", "
    ++ toString p.ops.length ++ " operations.")
    ++ "import { Context, Effect } from \"effect\"\n"
    ++ tsTypeImports p.services ++ "\n"
    ++ String.join (p.services.map fun s => tsService s ++ "\n" ++ tsRows s ++ "\n")
    ++ "/** Lowered from `" ++ p.name ++ "` by OCaml5.Fuzz. */\n"
    ++ p.tsBody

/-- One program's `fixture.ml`. -/
def Prog.mlFile (p : Prog) : String :=
  "(* Generated by OCaml5.Fuzz (spike P5, round four). Program `" ++ p.name ++ "`, seed "
    ++ toString p.seed ++ ", " ++ toString p.ops.length ++ " operations.\n"
    ++ "   Do not edit; regenerate with `ocaml/tools/fuzz.sh corpus`. *)\n\n"
    ++ "open Deep_fibers\n\n"
    ++ p.ocamlBody ++ "\n"
    ++ "let programs : (string * (unit -> value)) list = [ (\"" ++ p.name ++ "\", corpus_"
    ++ p.name ++ ") ]\n"

def Prog.tapeText (p : Prog) : String :=
  String.intercalate ","
    ((p.tape.zipIdx).map fun (b, i) => toString i ++ ":" ++ (if b then "1" else "0"))

/-- The rules string the wire header carries. The generated programs are the fiber family's
lowering shape — a service acquire, a call and a bind per operation, discards for the unit rows,
a nullary value for `started`/`cleanups`/`make`/`close`, and a return — which is the rules string
every `generated/traces/fiber/*.tsv` golden carries. -/
def rulesText : String :=
  "service-acquire,perform-call,perform-bind,nullary-value,perform-discard,ret"

def Prog.metaJson (p : Prog) : String :=
  let fams := p.services
  let opNames := p.ops.map fun o => "\"" ++ o.family ++ "\""
  "{\n"
    ++ "  \"name\": \"" ++ p.name ++ "\",\n"
    ++ "  \"seed\": " ++ toString p.seed ++ ",\n"
    ++ "  \"operations\": " ++ toString p.ops.length ++ ",\n"
    ++ "  \"forks\": " ++ toString p.forks ++ ",\n"
    ++ "  \"families\": [" ++ String.intercalate ", " (fams.map fun f => "\"" ++ f ++ "\"") ++ "],\n"
    ++ "  \"usesExtra\": " ++ (if p.usesExtra then "true" else "false") ++ ",\n"
    ++ "  \"tape\": \"" ++ p.tapeText ++ "\",\n"
    ++ "  \"rules\": \"" ++ rulesText ++ "\",\n"
    ++ "  \"wireProgram\": \"corpus." ++ p.name ++ "\",\n"
    ++ "  \"ocamlEntry\": \"corpus_" ++ p.name ++ "\",\n"
    ++ "  \"tsEntry\": \"corpus_" ++ p.name ++ "\",\n"
    ++ "  \"opFamilies\": [" ++ String.intercalate ", " opNames ++ "]\n"
    ++ "}\n"

/-- The aggregate OCaml module: every program, and the `programs` table `avatar_main.ml` looks
a name up in. This is the file `build-avatar.sh` would add to its module list. -/
def aggregateMl (ps : List Prog) : String :=
  "(* Generated by OCaml5.Fuzz (spike P5, round four): " ++ toString ps.length
    ++ " programs over the avatar's alphabet.\n"
    ++ "   Add to `build-avatar.sh`'s module list after `extra_fixture.ml`, and select with\n"
    ++ "   EFFECT4_FAMILY=corpus. Do not edit. *)\n\n"
    ++ "open Deep_fibers\n\n"
    ++ String.join (ps.map fun p => p.ocamlBody ++ "\n")
    ++ "let programs : (string * (unit -> value)) list =\n  [ "
    ++ String.intercalate ";\n    "
         (ps.map fun p => "(\"" ++ p.name ++ "\", corpus_" ++ p.name ++ ")")
    ++ " ]\n"

/-- The aggregate TypeScript module: the five services once, then every program. -/
def aggregateTs (ps : List Prog) : String :=
  let all := ["fiber", "ref", "deferred", "scope", "layer"]
  header ("The whole corpus: " ++ toString ps.length ++ " programs.")
    ++ "import { Context, Effect } from \"effect\"\n"
    ++ tsTypeImports all ++ "\n"
    ++ String.join (all.map fun s => tsService s ++ "\n" ++ tsRows s ++ "\n")
    ++ String.join (ps.map fun p => p.tsBody ++ "\n")
    ++ "export const corpusPrograms = {\n"
    ++ String.intercalate ",\n"
         (ps.map fun p => "  \"" ++ p.name ++ "\": corpus_" ++ p.name)
    ++ "\n} as const\n"

end Corpus


/-! ### Checks

The corpus itself is checked by compiling it (`ocaml/tools/fuzz.sh corpus-smoke`, both sides). What is
pinned here is what has to hold for that to mean anything: the programs are well-scoped, the tape
has exactly one entry per fork, and every program ends on a value. -/

-- Thirty consecutive seeds of the committed schedule, at the sizes the schedule gives them.
#guard (List.range 30).all
  (fun i => (Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)).wellScoped)

-- One tape entry per fork, which is what `deep_fibers.ml`'s `Tape.decide` and
-- `fiber-tail.ts`'s `decide` both index by site.
#guard (List.range 30).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  p.tape.length == p.forks)

-- Every program ends on a value-returning operation, so both renderings have a result.
#guard (List.range 30).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  match p.ops.getLast? with
  | Option.some op => op.kind != Corpus.Kind.unitK
  | Option.none => false)

-- The schedule: seed 400000 at size 34, the first program of the committed corpus.
#guard (Corpus.genProg 400000 (5 + (400000 * 7 + 3) % 36)).ops.length == 37
#guard (Corpus.genProg 400000 (5 + (400000 * 7 + 3) % 36)).name == "p400000"

-- The two renderings come from the one description and have one line per operation each: the
-- OCaml body is a header, one line per operation and the result; the TypeScript body has one
-- `yield*` per operation plus one per service it acquires.
#guard (List.range 10).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  (p.ocamlBody.splitOn "\n").length == p.ops.length + 3)
#guard (List.range 10).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  (p.tsBody.splitOn "yield* ").length == p.ops.length + p.services.length + 1)

end OCaml5.Fuzz
