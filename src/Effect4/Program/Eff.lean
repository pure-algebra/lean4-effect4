import Effect4.Machine.Key
import Effect4.Machine.Supervision
import Effect4.Program.Ty

/-!
# Syntax.Eff — the Effect TS program AST (lane A1 of the AST relation)

Plan: `docs/research/2026-09-04-ast-relation-plan.md` §2. `Eff` is the syntax of the
Effect TS programs this tree prints and reads, sitting between the portable layer and the
frame machine:

```
 Effect TS text  ⇄  Eff  →  Prim + PrimInterp  →  Deep machine
   print/parse        compile                     drive / run
```

Every constructor names the rc.112 primitive it compiles to and the public combinator it
prints as (`arms` below, one row per constructor, with the `internal/effect.ts` line). The
AST is first-order throughout: values are `Term`s over positional variables (decision D1:
the flows' convention, every node passes its whole scope forward and an answer is appended),
programs carried by fiber actions are `Eff` subterms, and there is no Lean function anywhere
inside it. `DecidableEq` is derived for every type here; the separation-4 gate
(`docs/research/FRAMES-DAG.md`) is the `example`s at the end.

Two sequencing forms on purpose (§2.1): `bind` is `Effect.flatMap`, an `OnSuccess` frame;
`gen` is `Effect.gen(function* () { … })`, one `Iterator` primitive. They print differently
and compile differently, and that difference is what the host relation (R4) is stated over.

`Option (Eff Op)` and `List (Eff Op)` fields would make the block a nested inductive, whose
`DecidableEq` handler this tree refuses (`src/Effect4/Machine/Stores.lean`, state note §3.5); the
list-shaped fields are the mutual cons-types `Terms`, `Stmts` and `Effs`, and the optional
cancel of a callback is a second constructor.
-/

namespace Effect4.Program

open Effect4 (ServiceKey)



/-- The closed error language represented without payload loss by `Err` (DI-62).
`never` admits no values; unions admit only represented columns. Defects and interruptions
remain outside this error language. -/
def supportedErrTy : Ty → Bool
  | .never | .nat | .string => true
  | .prod a b => decide (a = .string ∧ b = .string)
  | .union l r => supportedErrTy l && supportedErrTy r
  | _ => false

/-- Failure introduction compares the closed error profile after deep normalization.
The raw support predicate remains available for exact image proofs. -/
def admittedErrTy (t : Ty) : Bool := supportedErrTy t.normalize

/-! ## Rows: the perform alphabet's declarations

`Eff` is parameterised by `Op`, the positions of a table of rows. The service route's
table is a family's rows; the native route's is the standard-library links
(`git:62c04d9:src/Effect4/StdLib/Links.lean`) whose model reference is a store operation, an async
registration, or a Layer/Context program. `Row` is what typing and the compile read off a
position. -/

inductive RowKind
  /-- A `sync` thunk that reads or writes a store (`src/Effect4/Machine/Stores.lean` `SyncOp`). -/
  | sync
  /-- An `Async` whose registration is a store operation (`Deferred.await`). -/
  | async
  /-- A program of the Layer or Context model, run as a nested body. -/
  | program
deriving DecidableEq, Repr

/-- How a row prints: a call `spelling(request)` (`spelling()` on a unit request), or a
value `spelling` on a unit request (the service route's nullary rows, `cell.get`). -/
inductive RowShape
  | call
  | value
  /-- Apply the request tuple as separate arguments, followed by trailing names. -/
  | tupleCall
  /-- The first request component is the receiver; its second component supplies the arguments. -/
  | method
deriving DecidableEq, Repr

/-- Who answers an asynchronous row: the deferred store or the external oracle. -/
inductive Registration
  | deferred
  | external
deriving DecidableEq, Repr

structure Row where
  name : String
  /-- What the printer prints the operation as: the qualified export on the native route
  (`Ref.get`), the receiver's method on the service route (`refs.get`). -/
  spelling : String
  shape : RowShape := .call
  /-- Literal arguments printed after the request: the pure function of a read-modify-write
  row (`Ref.update(ref, incr)`), a scope's strategy. Names, never values. -/
  trailing : List String := []
  kind : RowKind
  request : Ty
  answer : Ty
  error : Ty := .never
  requires : List ServiceKey := []
  /-- The rc.112 file and lines the row transcribes. -/
  cite : String
  /-- Explicit type arguments the export must be called with, target type spellings, in
  order: `Deferred.make<number, number>()`. A row whose answer handle is generic and whose
  arguments do not determine it needs them, or the host infers the parameter's default and
  every later use of the handle is typed at that default instead
  (`E4-CHECK-CE-013`). Empty means the call is printed and read without type arguments. -/
  typeArgs : List String := []
  registration : Registration := .deferred
deriving DecidableEq, Repr

namespace Row

/-- The transient linked view of a raw row. Identity, spelling, call shape, registration,
requirements and provenance stay unchanged; only the three type columns are canonicalized. -/
def normalizeTypes (row : Row) : Row :=
  { row with
    request := row.request.normalize
    answer := row.answer.normalize
    error := row.error.normalize }

@[simp] theorem normalizeTypes_idem (row : Row) :
    row.normalizeTypes.normalizeTypes = row.normalizeTypes := by
  cases row
  simp only [normalizeTypes, Ty.normalize_idem]

end Row

/-! ## Values -/

/-- The literals a program may write. -/
inductive Lit
  | unit
  | nat (value : Nat)
  | bool (value : Bool)
  | str (value : String)
deriving DecidableEq, Repr

def Lit.ty : Lit → Ty
  | .unit => .unit
  | .nat _ => .nat
  | .bool _ => .bool
  | .str _ => .string

/-- A variable is a position in the current environment (D1). -/
abbrev Var := Nat

mutual
  /-- A pure value: a variable, a literal, or an atom applied to values. Atoms are the
  pure functions a family declares (`AtomRow`), named, never stored. -/
  inductive Term
    | var (index : Var)
    | lit (value : Lit)
    | app (atom : String) (args : Terms)
  inductive Terms
    | nil
    | cons (head : Term) (tail : Terms)
end

deriving instance DecidableEq for Term, Terms

def Terms.toList : Terms → List Term
  | .nil => []
  | .cons head tail => head :: Terms.toList tail

/-- The first-order spelling of a `Cause`: `Cause.fail`, `Cause.die`, `Cause.interrupt`,
and the merge of two (`Cause.combine`, a list append in the model). -/
inductive CauseTerm
  | fail (error : Term)
  | die (defect : Term)
  /-- `none` is an interrupt with no interruptor; `some who` names the interrupting fiber. -/
  | interrupt (interruptor : Option Term)
  | both (left right : CauseTerm)
deriving DecidableEq

/-! ## Programs -/

mutual
  /-- The program syntax. Each constructor's rc.112 primitive and public combinator are the
  row of `arms` with its name. -/
  inductive Eff (Op : Type)
    -- exits
    | succeed (value : Term)
    | fail (error : Term)
    | failCause (cause : CauseTerm)
    | yieldError (error : Term)
    -- thunks
    | sync (thunk : Term)
    | suspend (body : Eff Op)
    | perform (op : Op) (request : Term)
    -- sequencing, two frame shapes on purpose
    | bind (first rest : Eff Op)
    | gen (body : Stmts Op)
    -- failure
    | catchCause (body handler : Eff Op)
    | matchCause (body onValue onCause : Eff Op)
    | onExit (body finalizer : Eff Op)
    | exit (body : Eff Op)
    -- masks
    | uninterruptible (body : Eff Op)
    | interruptible (body : Eff Op)
    -- control by value
    | branch (test : Term) (thenB elseB : Eff Op)
    /-- `Effect.whileLoop({ while, body, step })` (`Effect.ts:1282-1286`): rc.112 keeps the
    cursor in a closure variable; here it is the next variable, initialised by `initial`.
    `test` is a term over the environment extended by the cursor, `body` a program over it,
    and `step` a term over the cursor and the body's answer, giving the next cursor. -/
    | whileLoop (initial test step : Term) (body : Eff Op)
    -- scheduling and parking
    | yieldNow (priority : Nat)
    /-- An `Async` whose registration is the row's (`Deferred.await`): the store decides
    whether the registration returns a cancel, so the cancel is not syntax. -/
    | callback (register : Op) (request : Term)
    | awaitFiber (fiber : Term) (mode : Effect4.Supervision.ObserverMode)
    -- fibers and scopes
    | withFiber (action : ActionTerm Op)
    | scoped (body : Eff Op)
    /-- `release` is a program over the environment extended by the resource and the exit. -/
    | acquireRelease (acquire release : Eff Op)
    -- flows only: refused by the native printer, tape-answered by the compile (D2)
    | choose (site : Nat) (left right : Eff Op)
    -- provision (the join, 2026-09-07): a layer is a subterm, and its build runs at its point.
    -- Appended, so no stored program's bytes move (`Wire.lean`).
    /-- `Effect.provide(self, layer, { local })` (`internal/layer.ts:8-22`): `scopedWith` a
    fresh scope, the layer built into it — `Layer.buildWithScope` off the fiber context's memo
    map, or `buildWithMemoMap` over a private one when `isLocal` — and the body under
    `provideContext(self, built)`. -/
    | provideLayer (layer : LayerTerm Op) (isLocal : Bool) (body : Eff Op)
    /-- `Effect.service(key)` (`internal/effect.ts:2059`): the key is the effect that reads it;
    a key the context lacks is the host throw (`Context.getUnsafe`), a defect. -/
    | service (key : ServiceKey)
    /-- `Effect.provideService(self, key, value)` (`internal/effect.ts:2202-2232`):
    `updateContext(self, Context.add(key, value))`, a region over the body. -/
    | provideService (key : ServiceKey) (value : Term) (body : Eff Op)
    /-- `Effect.catchIf` (`internal/effect.ts:2798-2810`): test and handler bind the
    first Fail's represented error value. A miss or unrepresented first Fail retains
    the whole cause; a hit replaces it. DI-09's boom policy is `CATCH-FB-BOOM`.
    Body is child 0 and handler child 1; this form remains outside Straight/Plain. -/
    | catchIf (test : Term) (body handler : Eff Op)
  /-- A statement of a generator body. -/
  inductive Stmt (Op : Type)
    /-- `const aN = yield* e`: binds the answer as the next variable. -/
    | bindYield (effect : Eff Op)
    /-- `yield* e`. -/
    | yieldDiscard (effect : Eff Op)
    | ret (value : Term)
    /-- Block-scoped: the bindings of a branch do not survive it. -/
    | ifElse (test : Term) (thenB elseB : Stmts Op)
    | whileTrue (body : Stmts Op)
    | breakLoop
  inductive Stmts (Op : Type)
    | nil
    | cons (head : Stmt Op) (tail : Stmts Op)
  /-- Race entrants. -/
  inductive Effs (Op : Type)
    | nil
    | cons (head : Eff Op) (tail : Effs Op)
  /-- What a `withFiber` thunk does: `Effect4.Machine.WithFiberAction` with programs as `Eff`
  subterms and handles as terms. Finalizer keys are not syntax: the compile mints them. -/
  inductive ActionTerm (Op : Type)
    | fork (program : Eff Op) (options : Effect4.Supervision.ForkOptions)
    | forkIn (program : Eff Op) (options : Effect4.Supervision.ForkOptions) (scope : Term)
    | forkScoped (program : Eff Op) (options : Effect4.Supervision.ForkOptions)
    | runIn (target scope : Term)
    | interrupt (target : Term)
    | interruptScoped (target : Term)
    | interruptAll (targets : Term) (interruptor : Option Term)
    | awaitAll (targets : Term)
    | awaitAllFailFast (targets : Term)
    | snapshotChildren
    | awaitNewChildren (snapshot : Term)
    | raceAll (entrants : Effs Op)
    | setContext (context : Term)
    | getContext
    | getId
    | closeScope (scope exit : Term)
  /-- The first-order layer term (the join, 2026-09-07; before it `Program/Provision.lean`):
  one constructor per rc.112 export, each naming the line it transcribes. A body is an `Eff`
  program — the same syntax the printer prints and the compile compiles — closed: a layer's
  own scope is its ambient one (`Layer.ts:1438`), so a body is typed and printed at the empty
  environment. A layer's identity is its path in the program (`LayerId`, `Machine/Stores.lean`),
  never a name: rc.112 keys its memo map on the layer object (`Layer.ts:411`, `:438`), and an
  inline-printed term is one object per site; a second site of one object is `ref`, the
  path of the defining occurrence (the host rows slice, 2026-09-08, DB-12 amended). The two
  constructors after `orDie` are appended, so no stored program's bytes move (`Wire.lean`). -/
  inductive LayerTerm (Op : Type)
    /-- `Layer.succeed(key, value)` (`Layer.ts:1074`): a service from a value already in hand. -/
    | succeed (key : ServiceKey) (value : Lit)
    /-- `Layer.effect(key, body)` (`Layer.ts:1427`): a service built by a program, in the
    layer's own scope — `Exclude<R, Scope.Scope>` (`:1438`). -/
    | effect (key : ServiceKey) (body : Eff Op)
    /-- `Layer.effectDiscard(body)` (`Layer.ts:1512`): construction work that provides nothing. -/
    | effectDiscard (body : Eff Op)
    /-- `self.pipe(Layer.provide(that))` (`Layer.ts:2258`). -/
    | provide (self that : LayerTerm Op)
    /-- `self.pipe(Layer.provideMerge(that))` (`Layer.ts:2704`). -/
    | provideMerge (self that : LayerTerm Op)
    /-- `Layer.merge(left, right)` (`Layer.ts:1850`). -/
    | merge (left right : LayerTerm Op)
    /-- `Layer.fresh(inner)` (`Layer.ts:3850`): the same signature, a private memo map. -/
    | fresh (inner : LayerTerm Op)
    /-- `Layer.orDie(inner)` (`Layer.ts:3327`). -/
    | orDie (inner : LayerTerm Op)
    /-- `const L = …` used at a second site (`Layer.ts:411`, `:438`: rc.112 keys the memo map
    on the layer object): a reference to the defining occurrence of another layer term of
    the same program, by its path (`LayerId`). The target precedes the reference in program
    order and is not itself a reference (`Program/Refs.lean` `layerRefsWF`); the compile
    redirects to the target's path, so both sites share one memo key (DB-12). -/
    | ref (target : List Nat)
    /-- `Layer.mergeAll(a, b, …)` (`Layer.ts:1652`, `mergeAllEffect` `:1587-1602`): one
    parallel parent scope forked from the caller's, one sequential child of it per layer,
    every layer built with concurrency equal to their number over one memo map, the contexts
    merged last-wins (`Context.mergeAll`, `:1600`). `merge` is its binary case (`:1905`);
    the two build different scope trees, so neither is a spelling of the other. -/
    | mergeAll (layers : LayerTerms Op)
  /-- The layers of a `mergeAll`, a spine like `Effs`. -/
  inductive LayerTerms (Op : Type)
    | nil
    | cons (head : LayerTerm Op) (tail : LayerTerms Op)
end

deriving instance DecidableEq for Eff, Stmt, Stmts, Effs, ActionTerm, LayerTerm, LayerTerms

def LayerTerms.toList {Op : Type} : LayerTerms Op → List (LayerTerm Op)
  | .nil => []
  | .cons head tail => head :: LayerTerms.toList tail

def LayerTerms.length {Op : Type} : LayerTerms Op → Nat
  | .nil => 0
  | .cons _ tail => LayerTerms.length tail + 1

def LayerTerms.ofList {Op : Type} : List (LayerTerm Op) → LayerTerms Op
  | [] => .nil
  | head :: tail => .cons head (LayerTerms.ofList tail)

def Stmts.toList {Op : Type} : Stmts Op → List (Stmt Op)
  | .nil => []
  | .cons head tail => head :: Stmts.toList tail

def Effs.toList {Op : Type} : Effs Op → List (Eff Op)
  | .nil => []
  | .cons head tail => head :: Effs.toList tail

/-! ## Inserting an environment slot

Variables are positions from the start of the environment. Inserting one slot at
`cut` moves every old position at or above it, including local binders introduced
inside the program. The cut stays fixed under those binders. Layer bodies use an
independent empty environment, so a layer subterm is left unchanged.
-/

/-- The old position after inserting one slot at `cut`. -/
def Var.weaken (cut index : Nat) : Nat := if index < cut then index else index + 1

mutual
  def Term.weaken (cut : Nat) : Term → Term
    | .var index => .var (Var.weaken cut index)
    | .lit value => .lit value
    | .app atom args => .app atom (Terms.weaken cut args)

  def Terms.weaken (cut : Nat) : Terms → Terms
    | .nil => .nil
    | .cons head tail => .cons (Term.weaken cut head) (Terms.weaken cut tail)
end

@[simp] theorem Term.weaken_eq_lit (cut : Nat) (term : Term) (value : Lit) :
    Term.weaken cut term = .lit value ↔ term = .lit value := by
  cases term <;> simp [Term.weaken]

def CauseTerm.weaken (cut : Nat) : CauseTerm → CauseTerm
  | .fail error => .fail (Term.weaken cut error)
  | .die defect => .die (Term.weaken cut defect)
  | .interrupt who => .interrupt (who.map (Term.weaken cut))
  | .both left right => .both (CauseTerm.weaken cut left) (CauseTerm.weaken cut right)

mutual
  /-- Insert a slot into the program's surrounding positional environment. This
  changes variable positions only; operations, service keys and closed layers stay
  unchanged. Typing under the inserted environment is `effTy_weaken`. -/
  def Eff.weaken {Op : Type} (cut : Nat) : Eff Op → Eff Op
    | .succeed value => .succeed (Term.weaken cut value)
    | .fail error => .fail (Term.weaken cut error)
    | .failCause cause => .failCause (CauseTerm.weaken cut cause)
    | .yieldError error => .yieldError (Term.weaken cut error)
    | .sync thunk => .sync (Term.weaken cut thunk)
    | .suspend body => .suspend (Eff.weaken cut body)
    | .perform op request => .perform op (Term.weaken cut request)
    | .bind first rest => .bind (Eff.weaken cut first) (Eff.weaken cut rest)
    | .gen body => .gen (Stmts.weaken cut body)
    | .catchCause body handler => .catchCause (Eff.weaken cut body) (Eff.weaken cut handler)
    | .catchIf test body handler =>
      .catchIf (Term.weaken cut test) (Eff.weaken cut body) (Eff.weaken cut handler)
    | .matchCause body onValue onCause =>
      .matchCause (Eff.weaken cut body) (Eff.weaken cut onValue) (Eff.weaken cut onCause)
    | .onExit body finalizer => .onExit (Eff.weaken cut body) (Eff.weaken cut finalizer)
    | .exit body => .exit (Eff.weaken cut body)
    | .uninterruptible body => .uninterruptible (Eff.weaken cut body)
    | .interruptible body => .interruptible (Eff.weaken cut body)
    | .branch test thenB elseB =>
      .branch (Term.weaken cut test) (Eff.weaken cut thenB) (Eff.weaken cut elseB)
    | .whileLoop initial test step body =>
      .whileLoop (Term.weaken cut initial) (Term.weaken cut test)
        (Term.weaken cut step) (Eff.weaken cut body)
    | .yieldNow priority => .yieldNow priority
    | .callback register request => .callback register (Term.weaken cut request)
    | .awaitFiber fiber mode => .awaitFiber (Term.weaken cut fiber) mode
    | .withFiber action => .withFiber (ActionTerm.weaken cut action)
    | .scoped body => .scoped (Eff.weaken cut body)
    | .acquireRelease acquire release =>
      .acquireRelease (Eff.weaken cut acquire) (Eff.weaken cut release)
    | .choose site left right => .choose site (Eff.weaken cut left) (Eff.weaken cut right)
    | .provideLayer layer isLocal body => .provideLayer layer isLocal (Eff.weaken cut body)
    | .service key => .service key
    | .provideService key value body =>
      .provideService key (Term.weaken cut value) (Eff.weaken cut body)

  def Stmt.weaken {Op : Type} (cut : Nat) : Stmt Op → Stmt Op
    | .bindYield effect => .bindYield (Eff.weaken cut effect)
    | .yieldDiscard effect => .yieldDiscard (Eff.weaken cut effect)
    | .ret value => .ret (Term.weaken cut value)
    | .ifElse test thenB elseB =>
      .ifElse (Term.weaken cut test) (Stmts.weaken cut thenB) (Stmts.weaken cut elseB)
    | .whileTrue body => .whileTrue (Stmts.weaken cut body)
    | .breakLoop => .breakLoop

  def Stmts.weaken {Op : Type} (cut : Nat) : Stmts Op → Stmts Op
    | .nil => .nil
    | .cons head tail => .cons (Stmt.weaken cut head) (Stmts.weaken cut tail)

  def Effs.weaken {Op : Type} (cut : Nat) : Effs Op → Effs Op
    | .nil => .nil
    | .cons head tail => .cons (Eff.weaken cut head) (Effs.weaken cut tail)

  def ActionTerm.weaken {Op : Type} (cut : Nat) : ActionTerm Op → ActionTerm Op
    | .fork program options => .fork (Eff.weaken cut program) options
    | .forkIn program options scope =>
      .forkIn (Eff.weaken cut program) options (Term.weaken cut scope)
    | .forkScoped program options => .forkScoped (Eff.weaken cut program) options
    | .runIn target scope => .runIn (Term.weaken cut target) (Term.weaken cut scope)
    | .interrupt target => .interrupt (Term.weaken cut target)
    | .interruptScoped target => .interruptScoped (Term.weaken cut target)
    | .interruptAll targets who =>
      .interruptAll (Term.weaken cut targets) (who.map (Term.weaken cut))
    | .awaitAll targets => .awaitAll (Term.weaken cut targets)
    | .awaitAllFailFast targets => .awaitAllFailFast (Term.weaken cut targets)
    | .snapshotChildren => .snapshotChildren
    | .awaitNewChildren snapshot => .awaitNewChildren (Term.weaken cut snapshot)
    | .raceAll entrants => .raceAll (Effs.weaken cut entrants)
    | .setContext context => .setContext (Term.weaken cut context)
    | .getContext => .getContext
    | .getId => .getId
    | .closeScope scope exit => .closeScope (Term.weaken cut scope) (Term.weaken cut exit)
end

/-! ## The arms: constructor ↔ combinator ↔ primitive, with rc.112 lines -/

/-- One row of the table. `primitive` names the `Effect4.Prim` constructor, the
`WithFiberAction`, or the compile's region shape the constructor becomes. -/
structure Arm where
  constructor : String
  combinator : String
  primitive : String
  /-- `vendor/effect-4.0.0-rc.112/src/internal/effect.ts` unless another file is named. -/
  cite : String
deriving DecidableEq, Repr

def arms : List Arm :=
  [ ⟨"succeed", "Effect.succeed", "Prim.success", "internal/effect.ts:1275"⟩
  , ⟨"fail", "Effect.fail", "Prim.failure (Cause.fail e)", "internal/effect.ts:1322"⟩
  , ⟨"failCause", "Effect.failCause", "Prim.failure", "internal/effect.ts:1330"⟩
  , ⟨"yieldError", "yield* new E()", "Prim.yieldableError", "internal/effect.ts:1226"⟩
  , ⟨"sync", "Effect.sync", "Prim.sync", "internal/effect.ts:929"⟩
  , ⟨"suspend", "Effect.suspend", "Prim.suspend", "internal/effect.ts:1093"⟩
  , ⟨"perform", "yield* op(x) (by the row's kind)", "Prim.sync | Prim.async | a nested body", "git:62c04d9:src/Effect4/StdLib/Links.lean"⟩
  , ⟨"bind", "Effect.flatMap", "Prim.onSuccess", "internal/effect.ts:1590"⟩
  , ⟨"gen", "Effect.gen(function* () { … })", "Prim.iterator", "internal/effect.ts:1184"⟩
  , ⟨"catchCause", "Effect.catchCause", "Prim.onFailure", "internal/effect.ts:2417"⟩
  , ⟨"matchCause", "Effect.matchCauseEffect", "Prim.onSuccessAndFailure", "internal/effect.ts:2645"⟩
  , ⟨"onExit", "Effect.onExit", "Prim.onExit", "internal/effect.ts:4006"⟩
  , ⟨"exit", "Effect.exit", "Prim.exitFrame", "internal/effect.ts:2320"⟩
  , ⟨"uninterruptible", "Effect.uninterruptible", "WithFiberAction.setInterruptible false", "internal/effect.ts:4302-4310"⟩
  , ⟨"interruptible", "Effect.interruptible", "WithFiberAction.setInterruptible true", "internal/effect.ts:4331-4352"⟩
  , ⟨"branch", "if in a generator body", "decided by the environment at compile", "E4-FLOW-CE-029"⟩
  , ⟨"whileLoop", "Effect.whileLoop", "Prim.whileLoop", "internal/effect.ts:4628"⟩
  , ⟨"yieldNow", "Effect.yieldNowWith", "Prim.yieldNowWith", "internal/effect.ts:982-990"⟩
  , ⟨"callback", "the row's export (Deferred.await)", "Prim.async (+ Prim.asyncFinalizer when the store returns a cancel)", "internal/effect.ts:1109-1143"⟩
  , ⟨"awaitFiber", "Fiber.join | Fiber.await", "Prim.sync (ParkKind.join)", "internal/effect.ts:5291, :5304"⟩
  , ⟨"withFiber", "Effect.withFiber", "Prim.withFiber", "internal/effect.ts:1147"⟩
  , ⟨"scoped", "Effect.scoped", "the region frames of compileRegion", "internal/effect.ts:3960"⟩
  , ⟨"acquireRelease", "Effect.acquireRelease", "uninterruptible + onExit over the scope", "internal/effect.ts:3978"⟩
  , ⟨"choose", "(flows only; refused by the native printer)", "tape-answered at compile", "Effects.Flow.RawTerm.choose"⟩
  , ⟨"provideLayer", "Effect.provide", "scoped layer build + provideContext region", "internal/layer.ts:8-22"⟩
  , ⟨"service", "Effect.service", "Prim.onSuccess (Prim.withFiber getCtx) serviceLookup", "internal/effect.ts:2059"⟩
  , ⟨"provideService", "Effect.provideService", "updateContext region", "internal/effect.ts:2202-2232"⟩
  , ⟨"catchIf", "Effect.catchIf", "Prim.onFailure", "internal/effect.ts:2798-2810"⟩ ]

/-- Every constructor has one arm and every arm one constructor. -/
def constructorNames : List String :=
  ["succeed", "fail", "failCause", "yieldError", "sync", "suspend", "perform", "bind", "gen",
   "catchCause", "matchCause", "onExit", "exit", "uninterruptible", "interruptible", "branch",
   "whileLoop", "yieldNow", "callback", "awaitFiber", "withFiber", "scoped", "acquireRelease",
   "choose", "provideLayer", "service", "provideService", "catchIf"]

#guard arms.map Arm.constructor = constructorNames
#guard constructorNames.length = 28

/-! ## The separation-4 receipts: first-order, decidable throughout -/

example : DecidableEq Ty := inferInstance
example : DecidableEq Row := inferInstance
example : DecidableEq Term := inferInstance
example : DecidableEq CauseTerm := inferInstance
example {Op : Type} [DecidableEq Op] : DecidableEq (Eff Op) := inferInstance
example {Op : Type} [DecidableEq Op] : DecidableEq (Stmts Op) := inferInstance
example {Op : Type} [DecidableEq Op] : DecidableEq (ActionTerm Op) := inferInstance

end Effect4.Program
