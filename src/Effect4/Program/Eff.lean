import Effect4.Machine.Key
import Effect4.Machine.Supervision
import Effect4.Codegen.Profile

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
(`docs/FRAMES-DAG.md`) is the `example`s at the end.

Two sequencing forms on purpose (§2.1): `bind` is `Effect.flatMap`, an `OnSuccess` frame;
`gen` is `Effect.gen(function* () { … })`, one `Iterator` primitive. They print differently
and compile differently, and that difference is what the host relation (R4) is stated over.

`Option (Eff Op)` and `List (Eff Op)` fields would make the block a nested inductive, whose
`DecidableEq` handler this tree refuses (`Effect4/Deep/Stores.lean`, state note §3.5); the
list-shaped fields are the mutual cons-types `Terms`, `Stmts` and `Effs`, and the optional
cancel of a callback is a second constructor.
-/

namespace Effect4.Program

open Effect4 (ServiceKey)

/-! ## The type language

`Ty` is the profile's `Spelling` (`Effect4/Target/TypeScript/EffectV4.lean`) plus what an
`Effect<A, E, R>` needs and a service row never spells: `never`, the `Exit`, `Cause` and
`Fiber` handles, and unions of error types. Unions are canonical through `join`: members
sorted by their rendering, no duplicates, right-nested, `never` the empty union. -/

inductive Ty
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | except (error value : Ty)
  /-- `Exit.Exit<A, E>`: what `Effect.exit` and `Fiber.await` answer. -/
  | exitOf (value error : Ty)
  /-- `Cause.Cause<E>`: what a `catchCause` handler receives. -/
  | causeOf (error : Ty)
  /-- `Fiber.Fiber<A, E>`: what a fork answers. -/
  | fiberOf (value error : Ty)
  | union (left right : Ty)
deriving DecidableEq, Repr

namespace Ty

/-- The profile's spellings embed. -/
def ofSpelling : Effect4.Target.EffectV4.Spelling → Ty
  | .nat => .nat
  | .int => .int
  | .string => .string
  | .bool => .bool
  | .unit => .unit
  | .handle target => .handle target
  | .option inner => .option (ofSpelling inner)
  | .list inner => .list (ofSpelling inner)
  | .except error value => .except (ofSpelling error) (ofSpelling value)
  | .prod left right => .prod (ofSpelling left) (ofSpelling right)

/-- The TypeScript spelling; on the profile's fragment it is `Spelling.render`. -/
def render : Ty → String
  | .never => "never"
  | .unit => "void"
  | .nat | .int => "number"
  | .string => "string"
  | .bool => "boolean"
  | .handle target => target
  | .option inner => "Option.Option<" ++ render inner ++ ">"
  | .list inner => "ReadonlyArray<" ++ render inner ++ ">"
  | .prod left right => "readonly [" ++ render left ++ ", " ++ render right ++ "]"
  | .except error value => "Result.Result<" ++ render value ++ ", " ++ render error ++ ">"
  | .exitOf value error => "Exit.Exit<" ++ render value ++ ", " ++ render error ++ ">"
  | .causeOf error => "Cause.Cause<" ++ render error ++ ">"
  | .fiberOf value error => "Fiber.Fiber<" ++ render value ++ ", " ++ render error ++ ">"
  | .union left right => render left ++ " | " ++ render right

theorem render_ofSpelling (s : Effect4.Target.EffectV4.Spelling) :
    (ofSpelling s).render = s.render := by
  induction s with
  | nat | int | string | bool | unit | handle _ => rfl
  | option _ ih => simp [ofSpelling, render, Effect4.Target.EffectV4.Spelling.render, ih]
  | list _ ih => simp [ofSpelling, render, Effect4.Target.EffectV4.Spelling.render, ih]
  | except _ _ ihe ihv => simp [ofSpelling, render, Effect4.Target.EffectV4.Spelling.render, ihe, ihv]
  | prod _ _ ihl ihr => simp [ofSpelling, render, Effect4.Target.EffectV4.Spelling.render, ihl, ihr]

/-- The members of a union, flattened at the top; `never` contributes none. -/
def members : Ty → List Ty
  | .never => []
  | .union left right => members left ++ members right
  | t => [t]

/-- An injective structural key, for ordering union members: a constructor code, then the
length-prefixed keys of the components; a handle's target by its UTF-8 bytes
(`String.toUTF8` is the representation; `String.toList` and the string order reach
`Classical.choice` on this toolchain, so no member is ordered by its rendering). -/
def key : Ty → List Nat
  | .never => [0]
  | .unit => [1]
  | .nat => [2]
  | .int => [3]
  | .string => [4]
  | .bool => [5]
  | .handle target => 6 :: target.toUTF8.data.toList.map UInt8.toNat
  | .option inner => 7 :: key inner
  | .list inner => 8 :: key inner
  | .prod left right => 9 :: (key left).length :: key left ++ key right
  | .except error value => 10 :: (key error).length :: key error ++ key value
  | .exitOf value error => 11 :: (key value).length :: key value ++ key error
  | .causeOf error => 12 :: key error
  | .fiberOf value error => 13 :: (key value).length :: key value ++ key error
  | .union left right => 14 :: (key left).length :: key left ++ key right

/-- Lexicographic order on keys, as a Boolean. -/
def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

/-- Insert into a list sorted by key, without duplicates. -/
def insertMember (t : Ty) : List Ty → List Ty
  | [] => [t]
  | u :: rest =>
    if t = u then u :: rest
    else if ltKey t.key u.key then t :: u :: rest
    else u :: insertMember t rest

/-- A right-nested union of the given members; none is `never`. -/
def ofMembers : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: rest => .union t (ofMembers rest)

/-- The canonical union of two types. -/
def join (a b : Ty) : Ty :=
  ofMembers ((members a ++ members b).foldl (fun acc t => insertMember t acc) [])

def isNever : Ty → Bool
  | .never => true
  | _ => false

/-- The `Scope` service handle. -/
def scope : Ty := .handle "Scope.Scope"

/-- A context handle. -/
def context : Ty := .handle "Context.Context<unknown>"

end Ty

/-! ## Rows: the perform alphabet's declarations

`Eff` is parameterised by `Op`, the positions of a table of rows. The service route's
table is a family's rows; the native route's is the standard-library links
(`Effect4/StdLib/Links.lean`) whose model reference is a store operation, an async
registration, or a Layer/Context program. `Row` is what typing and the compile read off a
position. -/

inductive RowKind
  /-- A `sync` thunk that reads or writes a store (`Effect4/Deep/Stores.lean` `SyncOp`). -/
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
deriving DecidableEq, Repr

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
end

deriving instance DecidableEq for Eff, Stmt, Stmts, Effs, ActionTerm

def Stmts.toList {Op : Type} : Stmts Op → List (Stmt Op)
  | .nil => []
  | .cons head tail => head :: Stmts.toList tail

def Effs.toList {Op : Type} : Effs Op → List (Eff Op)
  | .nil => []
  | .cons head tail => head :: Effs.toList tail

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
  , ⟨"perform", "yield* op(x) (by the row's kind)", "Prim.sync | Prim.async | a nested body", "Effect4/StdLib/Links.lean"⟩
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
  , ⟨"choose", "(flows only; refused by the native printer)", "tape-answered at compile", "Effects.Flow.RawTerm.choose"⟩ ]

/-- Every constructor has one arm and every arm one constructor. -/
def constructorNames : List String :=
  ["succeed", "fail", "failCause", "yieldError", "sync", "suspend", "perform", "bind", "gen",
   "catchCause", "matchCause", "onExit", "exit", "uninterruptible", "interruptible", "branch",
   "whileLoop", "yieldNow", "callback", "awaitFiber", "withFiber", "scoped", "acquireRelease",
   "choose"]

#guard arms.map Arm.constructor = constructorNames
#guard constructorNames.length = 24

/-! ## The separation-4 receipts: first-order, decidable throughout -/

example : DecidableEq Ty := inferInstance
example : DecidableEq Row := inferInstance
example : DecidableEq Term := inferInstance
example : DecidableEq CauseTerm := inferInstance
example {Op : Type} [DecidableEq Op] : DecidableEq (Eff Op) := inferInstance
example {Op : Type} [DecidableEq Op] : DecidableEq (Stmts Op) := inferInstance
example {Op : Type} [DecidableEq Op] : DecidableEq (ActionTerm Op) := inferInstance

end Effect4.Program
