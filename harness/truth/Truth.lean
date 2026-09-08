import Effect4.Api
import TypeScript.Render
import Lean.Data.Json

/-!
# Truth — the Lean face of the rc.112 truth check

What it is: for every program of the `Eff` corpus (`Effect4.Program.Wire.Corpus.all` plus
`pTwo` of `src/OCaml5/Bridge.lean`), the Lean machine's verdict and its observable
schedule, written as one JSON manifest (`harness/truth/corpus.json`) that the rc.112 runner
(`harness/truth/run-truth.ts`) and, later, the OCaml host replay against.

    lake env lean -M4096 --run harness/truth/Truth.lean [harness/truth/corpus.json]

Without an argument the manifest goes to stdout. Depends on `Effect4.Api` (typing, printing,
running), `TypeScript.Render` (the pinned renderer: bytes of the printed program), and
`Lean.Data.Json` (escaping and layout of the manifest; nothing of the project's semantics).

Why one file: a `--run` tool can import only Lake modules, and `ocaml/tools` is not
a Lake library, so the library half (`OCaml5.Truth`, everything above `main`) and the thin
driver (`main`) share this file. The library half is pure; `main` only parses arguments and
writes.

Manifest (`format: effect4-truth-manifest-v1`), one entry per program:

* `name`, `wellTyped`, `type` (`{answer, error, requiresEmpty}` as `Ty.render` spells them,
  `null` when ill-typed);
* `expr`: the program as one TypeScript expression (`Api.print` rendered by
  `TypeScript.Render.expr house0 0`), or `null` with `exprRefusal` naming the refusal;
* `decl`: the exported constant `Api.printDecl "main"` rendered by
  `TypeScript.Render.constDecl house0`, or `null` (ill-typed, or refused);
* `run`: `Api.run p fuel` — `outcome` (`finished`, `frontier`, `stuck …`), `exit` (the root's
  exit in the wire below, `null` while the root is live), `fibers` (id, exited, parked token),
  `events` (the machine events with an rc.112 counterpart, in order), `schedule` (the same
  events reduced to the alphabet the runner can observe), `internal` (the other non-frame
  events, recorded, never compared), `frames` (how many frame rows were dropped);
* `runSync`: `Api.runSync p fuel` — `Effect.runSyncExit`'s exit, and `sync`, whether the
  program settled inside it (its exit is not the `AsyncFiberError` defect).

The value wire: `unit` ↦ `null`, `nat` ↦ number,
`bool` ↦ boolean, a tuple / exit list ↦ JSON array, `fiber k` ↦ `{"fiber":k}`,
`cell k` ↦ `{"ref":k}`, `promise k` ↦ `{"deferred":k}`, `scopeHandle k` ↦ `{"scope":k}`,
`context` ↦ `{"context":true}`, a reified exit ↦ `{"success":v}` / `{"failure":cause}`; a
cause is `{"reasons":[…]}` with `{"fail":n|"boom"}`, `{"die":d}`, `{"interrupt":who|null}`;
an exit is `{"success":v}` / `{"failure":cause}`. Annotations are dropped.

Behaviours held:

* deterministic — the manifest is a function of the corpus and the fuel (by construction:
  no IO above `main`);
* total under fuel — every run is `Api.run`/`Api.runSync` at the given fuel, a frontier when
  it runs out, never a hang (by construction);
* complete over the corpus — every program of `corpus` has one entry, names are unique
  (tested: the `#guard`s at the end);
* honest about refusals — a print refusal or an ill-typed program is recorded as such, the
  program is never patched (by construction: `expr`/`decl` are `Api.print`/`Api.printDecl`
  verbatim).
-/

open Lean (ToJson toJson)

/-- `Lean.Json`, named apart from `Effect4.Json` (the tree's own JSON carrier, which
`open Effect4` brings into scope). -/
abbrev J := Lean.Json

namespace OCaml5.Truth

open Effect4 Effect4.Api Effect4.Machine Effect4.Program
open TypeScript (house0)

/-! ## The corpus -/

/-- `Bridge.forkOptions`, verbatim. -/
def forkOptions : Supervision.ForkOptions :=
  { startImmediately := false, daemon := false, maskMode := .inherit }

/-- `Bridge.pTwo`, verbatim: two children forked, the second awaited twice (`.var 1` names the
second child before and after the first await). -/
def pTwo : Api.Program :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 1)))) forkOptions))
    (.bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 2)))) forkOptions))
      (.bind (.awaitFiber (.var 1) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))

/-- `acquireRelease` inside `scoped` (V1, 2026-09-07): the release, registered on the ambient
scope, runs when `scoped` closes it and writes the acquired value into a cell the root made
first; the root then reads the cell. The release is typed over `[ref, a, exit]`
(`Typing.lean`): `.var 0` is the cell, `.var 1` the acquired `7`. -/
def pAcquire : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.scoped (.acquireRelease (.succeed (.lit (.nat 7)))
        (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))))
      (.perform .refGet (.var 0)))

/-- `acquireRelease` after its scope closed (`scopeAddFinalizerExit`'s closed branch,
`internal/effect.ts:3851-3853`): a child forked inside `scoped` inherits the scoped context;
it runs after the root has left `scoped` — the root awaits it — so its `acquireRelease`
finds the ambient scope closed and runs the release at once, on the child. The root then
reads the cell the release wrote. In the child the release is typed over `[ref, a, exit]`. -/
def pAcquireClosed : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.scoped (.withFiber (.fork
        (.acquireRelease (.succeed (.lit (.nat 7)))
          (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))))
        forkOptions)))
      (.bind (.awaitFiber (.var 1) .awaitValue) (.perform .refGet (.var 0))))

/-! ### The join's fixtures (2026-09-07): `Effect.provide`, `Layer.effect`, the memo store

Keys are typed by their code on the native route (`nativeServiceTy`): `kA`, `kB` carry a
number (code `4`), `kRef` a `Ref.Ref<number>` (code `7`). A layer body is a closed program, so
a body reaches the root's cell through `Effect.service`, never through a binder. -/

def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def kB : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩

/-- `Effect.provide(Effect.service(kA), Layer.effect(kA, Effect.succeed(7)))`
(`internal/layer.ts:8-22`): the layer built into `provide`'s scope, the service read under the
built context. -/
def pProvide : Api.Program :=
  .provideLayer (.effect kA (.succeed (.lit (.nat 7)))) false (.service kA)

/-- A layer whose construction acquires a resource and whose release bumps the root's cell,
reached as the service `kRef`; the release is typed over `[ref, a, exit]`. -/
def layerBump (k : ServiceKey) : LayerTerm NativeOp :=
  .effect k (.bind (.service kRef)
    (.acquireRelease (.succeed (.lit (.nat 1))) (.perform (.refUpdate .incr) (.var 0))))

/-- Two layers merged (`Layer.ts:1587-1602`), each acquiring in its own layer scope; when
`Effect.provide` closes its scope on the way out (`internal/effect.ts:3967`) both memo entries
release their layer scopes (`Layer.ts:404-408`), both releases run, and the root reads `2`. -/
def pProvideMerge : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.scoped (.provideLayer (.merge (layerBump kA) (layerBump kB)) false (.service kB)))
        (.perform .refGet (.var 0))))

/-- A layer whose construction bumps the root's cell and provides `5`. -/
def layerCount (k : ServiceKey) : LayerTerm NativeOp :=
  .effect k (.bind (.service kRef)
    (.bind (.perform (.refUpdate .incr) (.var 0)) (.succeed (.lit (.nat 5)))))

/-- The same layer term at two sites under one memo map (`Layer.merge(L, L)`): printed inline
it is two layer objects (`Layer.ts:411`, identity by object) and here it is two paths
(`LayerId`), so each site builds once and the cell reads `2` on both faces. What this pins is
the memo store's protocol — one entry per site, built, completed, released and its layer scope
closed on exit — not a hit; a hit needs one object at two sites, which no inline-printed
program has (`docs/research/2026-09-07-join-delivery.md`). -/
def pProvideTwice : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer (.merge (layerCount kA) (layerCount kA)) false (.service kA))
        (.perform .refGet (.var 0))))

/-- The programs checked: the wire corpus, then `pTwo`, then the two `acquireRelease`
fixtures, then the join's three. -/
def corpus : List (String × Api.Program) :=
  Wire.Corpus.all ++ [("pTwo", pTwo), ("pAcquire", pAcquire), ("pAcquireClosed", pAcquireClosed),
    ("pProvide", pProvide), ("pProvideMerge", pProvideMerge), ("pProvideTwice", pProvideTwice)]

/-! ## The value wire -/

def defectJson : Defect → J
  | .notImplemented => Lean.Json.str "notImplemented"
  | .asyncFiber => Lean.Json.str "asyncFiber"
  | .badName => Lean.Json.str "badName"
  | .missingService => Lean.Json.str "missingService"
  | .user n => Lean.Json.mkObj [("user", toJson n)]

def errJson : Err → J
  | .boom => Lean.Json.str "boom"
  | .tag n => toJson n

def reasonJson : Reason Err Defect FiberId Ann → J
  | .fail e _ => Lean.Json.mkObj [("fail", errJson e)]
  | .die d _ => Lean.Json.mkObj [("die", defectJson d)]
  | .interrupt none _ => Lean.Json.mkObj [("interrupt", Lean.Json.null)]
  | .interrupt (some who) _ => Lean.Json.mkObj [("interrupt", toJson who.value)]

def causeJson (c : CauseV) : J :=
  Lean.Json.mkObj [("reasons", Lean.Json.arr (c.reasons.map reasonJson).toArray)]

/-- Values in the wire, on the shared carrier (`Machine/Value.lean`'s table): a handle by its
kind byte, a reified exit by its constructor index with the cause read back through
`causeImage`, the snapshot by its fibers, a `list` as one array. A shape the machine never
produces renders deterministically under `"raw"`, so the wire stays total. -/
partial def valJson : Val → J
  | .unit => Lean.Json.null
  | .nat n => toJson n
  | .bool b => Lean.Json.bool b
  | Value.fiber id => Lean.Json.mkObj [("fiber", toJson id)]
  | Value.fiberSnapshot handles =>
    Lean.Json.mkObj [("fibers", Lean.Json.arr
      ((((Effect4.Store.Image.list Value.fiberHandle).ofVal handles).getD []).map fun i =>
        toJson i.value).toArray)]
  | Value.cell k => Lean.Json.mkObj [("ref", toJson k)]
  | Value.promise k => Lean.Json.mkObj [("deferred", toJson k)]
  | Value.scope s => Lean.Json.mkObj [("scope", toJson s)]
  | Value.fiberContext _ _ _ => Lean.Json.mkObj [("context", Lean.Json.bool true)]
  -- a built service map (`Env.encode`, what a layer build answers and `Effect.provide` reads):
  -- the same `Context` object on the rc.112 face
  | Value.serviceContext _ => Lean.Json.mkObj [("context", Lean.Json.bool true)]
  | Val.exitOk v => Lean.Json.mkObj [("success", valJson v)]
  | Value.exitErr written =>
    Lean.Json.mkObj [("failure", ((causeImage.ofVal written).map causeJson).getD Lean.Json.null)]
  | .list values => Lean.Json.arr (values.map valJson).toArray
  | other => Lean.Json.mkObj [("raw", Lean.Json.str (toString (repr other)))]

def exitJson : ExitV → J
  | .success v => Lean.Json.mkObj [("success", valJson v)]
  | .failure c => Lean.Json.mkObj [("failure", causeJson c)]

/-- The kind of an exit, with the archived tracer's precedence (`outcomeWire`): a `Fail`
reason wins, then an `Interrupt`, then a `Die`; an empty cause is its own kind. -/
def exitKind : ExitV → String
  | .success _ => "success"
  | .failure c =>
    if c.reasons.any (fun | .fail _ _ => true | _ => false) then "fail"
    else if c.reasons.any (fun | .interrupt _ _ => true | _ => false) then "interrupt"
    else if c.reasons.any (fun | .die _ _ => true | _ => false) then "die"
    else "empty"

/-- Whether an exit is `runSyncExit`'s `AsyncFiberError` defect. -/
def isAsyncFiberDefect : ExitV → Bool
  | .failure c => c.reasons.any (fun | .die .asyncFiber _ => true | _ => false)
  | _ => false

/-! ## Events -/

abbrev Event := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- The events with an rc.112 counterpart, as the manifest spells them. `none` for the rest. -/
def observable : Event → Option String
  | .forked p c d => some s!"forked {p.value}->{c.value}{if d then " daemon" else ""}"
  | .started f => some s!"started {f.value}"
  | .scheduledTask o p _ => some s!"scheduledTask owner={o.value} prio={p}"
  | .ranTask o _ => some s!"ranTask owner={o.value}"
  | .yieldInjected f n => some s!"yieldInjected {f.value}@{n}"
  | .parkedOn f t => some s!"parkedOn {f.value} token={t}"
  | .resumedWith f t _ => some s!"resumedWith {f.value} token={t}"
  | .exited f e => some s!"exited {f.value} {(exitJson e).compress}"
  | _ => none

/-- The reduced schedule alphabet the runner can observe on rc.112: fiber starts, exits (by
kind), forks, parks and resumes, and the dispatcher's scheduling and runs. Tokens, priorities'
tasks and exit values are erased; fiber ids are the machine's (root `0`, children in fork
order), which the runner reproduces by first-seen order. -/
def reduced : Event → Option String
  -- a daemon fork is invisible to the runner: only a non-daemon child joins `fiber._children`
  -- (`internal/effect.ts:5279-5281`), which is where the runner sees forks; `events` keeps it
  | .forked _ _ true => none
  | .forked p c false => some s!"forked {p.value} {c.value}"
  | .started f => some s!"started {f.value}"
  | .scheduledTask o p _ => some s!"scheduled {o.value} {p}"
  | .ranTask o _ => some s!"ran {o.value}"
  | .parkedOn f _ => some s!"parked {f.value}"
  | .resumedWith f _ _ => some s!"resumed {f.value}"
  | .exited f e => some s!"exited {f.value} {exitKind e}"
  | _ => none

/-- The events that are neither observable nor frame rows: recorded, never compared. -/
def internal : Event → Option String
  | .interruptRecorded who t =>
    some s!"interruptRecorded by={(who.map (·.value)).getD 0} target={t.value}"
  | .interruptDeferred t => some s!"interruptDeferred {t.value}"
  | .childrenInterrupted p cs => some s!"childrenInterrupted {p.value} n={cs.length}"
  | .observerFired f _ => some s!"observerFired {f.value}"
  | .finalizerProgram f _ e => some s!"finalizerProgram {f.value} {exitKind e}"
  | .scopeLinked _ sc k f => some s!"scopeLinked scope={sc} key={k} fiber={f.value}"
  | .scopeClosedOnLink sc f => some s!"scopeClosedOnLink scope={sc} fiber={f.value}"
  | .raceStarted r h n => some s!"raceStarted {r} host={h.value} entrants={n}"
  | .raceLaunched r e => some s!"raceLaunched {r} entrant={e.value}"
  | .raceSettled r e => some s!"raceSettled {r} {exitKind e}"
  | .contextSet f _ => some s!"contextSet {f.value}"
  | .callback k e => some s!"callback key={k} {exitKind e}"
  | _ => none

def isFrame : Event → Bool
  | .frame _ _ => true
  | _ => false

/-! ## One program's entry -/

def outcomeText : Api.Outcome → String
  | .finished => "finished"
  | .frontier => "frontier"
  | .stuck why => s!"stuck {repr why}"

def typeJson (ty : EffTy) : J :=
  Lean.Json.mkObj
    [ ("answer", Lean.Json.str ty.answer.render)
    , ("error", Lean.Json.str ty.error.render)
    , ("requiresEmpty", Lean.Json.bool (decide (ty.requires = Machine.Env.Requirement.empty))) ]

def refusalText : PrintRefusal → String
  | .choose site => s!"choose site {site}"
  | .internalAction name => s!"internal action {name}"

def fiberJson (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) : J :=
  Lean.Json.mkObj
    [ ("id", toJson f.id.value)
    , ("exited", Lean.Json.bool f.exit.isSome)
    , ("exit", match f.exit with | some e => exitJson e | none => Lean.Json.null)
    , ("parkedToken", match f.parked with | .withGuard t => toJson t | .notParked => Lean.Json.null) ]

def strings (xs : List String) : J := Lean.Json.arr (xs.map Lean.Json.str).toArray

def runJson (p : Api.Program) (fuel : Nat) : J :=
  let r := Api.run p fuel
  let trace := r.trace
  Lean.Json.mkObj
    [ ("outcome", Lean.Json.str (outcomeText r.outcome))
    , ("exit", match r.exit with | some e => exitJson e | none => Lean.Json.null)
    , ("exitKind", match r.exit with | some e => Lean.Json.str (exitKind e) | none => Lean.Json.null)
    , ("fiberCount", toJson r.fiberCount)
    , ("fibers", Lean.Json.arr (r.machine.fibers.map fiberJson).toArray)
    , ("events", strings (trace.filterMap observable))
    , ("schedule", strings (trace.filterMap reduced))
    , ("internal", strings (trace.filterMap internal))
    , ("frames", toJson (trace.filter isFrame).length) ]

def runSyncJson (p : Api.Program) (fuel : Nat) : J :=
  let (_, exit) := Api.runSync p fuel
  Lean.Json.mkObj
    [ ("exit", exitJson exit)
    , ("exitKind", Lean.Json.str (exitKind exit))
    , ("sync", Lean.Json.bool (!isAsyncFiberDefect exit)) ]

def entry (fuel : Nat) (name : String) (p : Api.Program) : J :=
  let ty := Api.typeOf p
  let printed := Api.print p
  let decl := Api.printDecl "main" p
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name)
    , ("wellTyped", Lean.Json.bool ty.isSome)
    , ("type", match ty with | some t => typeJson t | none => Lean.Json.null)
    , ("expr", match printed with
        | .ok e => Lean.Json.str (TypeScript.Render.expr house0 0 e)
        | .error _ => Lean.Json.null)
    , ("exprRefusal", match printed with
        | .ok _ => Lean.Json.null
        | .error why => Lean.Json.str (refusalText why))
    , ("decl", match decl with
        | some d => Lean.Json.str (TypeScript.Render.constDecl house0 d)
        | none => Lean.Json.null)
    , ("run", runJson p fuel)
    , ("runSync", runSyncJson p fuel) ]

/-- The whole manifest. -/
def manifest (fuel : Nat) : J :=
  Lean.Json.mkObj
    [ ("format", Lean.Json.str "effect4-truth-manifest-v1")
    , ("generated", Lean.Json.str "GENERATED by harness/truth/Truth.lean — do not edit")
    , ("regenerate", Lean.Json.str "lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json")
    , ("fuel", toJson fuel)
    , ("programs", Lean.Json.arr (corpus.map fun (name, p) => entry fuel name p).toArray) ]

/-! ## Receipts -/

#guard corpus.length = 14
#guard (corpus.map (·.1)).eraseDups.length = corpus.length
#guard (corpus.map (·.1)) =
  ["p42", "pBind", "pFork", "pAwait", "pGen", "pLoop", "pCatch", "pScope", "pTwo", "pAcquire",
   "pAcquireClosed", "pProvide", "pProvideMerge", "pProvideTwice"]
-- the join's fixtures are well-typed, so they cross as declarations
#guard Api.wellTyped pProvide
#guard Api.wellTyped pProvideMerge
#guard Api.wellTyped pProvideTwice

end OCaml5.Truth

/-- The driver: `[out]` writes the manifest there, else prints it. The fuel is fixed at
`1000`, enough for every corpus program to settle or park. -/
def main (args : List String) : IO Unit := do
  let fuel := 1000
  let text := (OCaml5.Truth.manifest fuel).pretty 100 ++ "\n"
  match args with
  | [out] =>
    IO.FS.writeFile out text
    IO.println s!"wrote {OCaml5.Truth.corpus.length} programs to {out}"
  | _ => IO.println text
