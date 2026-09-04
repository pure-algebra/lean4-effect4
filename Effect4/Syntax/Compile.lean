import Effect4.Syntax.Native
import Effect4.Deep.Fibers

/-!
# Syntax.Compile — `Eff` to the frames, names as addresses (lane A3)

Plan: `docs/research/2026-09-04-eff-compile.md` §1-§2. `compileEff` takes a program and a
`Point` (the subterm's path in the root program, the values in scope, the fuel, the tape)
to a primitive of the frame machine over the name alphabet `EffName` and the thunk alphabet
`EffThunk`. Every name a continuation carries is a *point*, and `interpOf root` gives the
names their meaning by compiling the subterm the point addresses: the table is a function
of the program, so "the table is the AST" is a definition.

What this cut compiles: every constructor of `Eff` except `acquireRelease` (the scope store
holds `FinName`s, a closed alphabet with no place for a compiled release yet) and the rows
of kind `program` (the Layer and Context models); those compile to the frontier. `choose` is
answered by the point's tape. The stores are `Effect4/Deep/Stores.lean`'s, unchanged: the
store-touching arms of `interpOf` call the same `syncOpStep`, `DeferredStore.register`,
`storesCloseScope` and `cancelProgram`-shaped functions (`docs/research/2026-09-04-eff-compile.md`
G5); only the alphabet is new.

Generators (`gen`) compile to one `Iterator` primitive whose name carries the generator's
program counter — a path from the body's statement list to the list to run next — and the
values in scope; `iterNext` walks pure statements (`return`, `if` decided by the environment,
`while`/`break`) with the point's fuel, folds a yielded pure success inline
(`Prim.iteratorFolded`), and resumes with the *advanced* name (`IterStep.resume next
continueAs`, the correction of 2026-09-04). A block's bindings are dropped at its end, as a
`const` inside a brace is.
-/

namespace Effect4.Syntax

open Effect4 Effect4.Deep

/-! ## Nodes and paths -/

/-- A node of the mutual program family, addressed by a path of child indices. -/
inductive Node
  | eff (e : NativeEff)
  | stmts (s : Stmts NativeOp)
  | stmt (s : Stmt NativeOp)
  | action (a : ActionTerm NativeOp)
  | effs (es : Effs NativeOp)
deriving DecidableEq

namespace Node

/-- The child at an index. Terms are not nodes: only programs, statements and actions are
addressed. -/
def child : Node → Nat → Option Node
  | eff (.suspend b), 0 => some (eff b)
  | eff (.bind a _), 0 => some (eff a)
  | eff (.bind _ b), 1 => some (eff b)
  | eff (.gen ss), 0 => some (stmts ss)
  | eff (.catchCause b _), 0 => some (eff b)
  | eff (.catchCause _ h), 1 => some (eff h)
  | eff (.matchCause b _ _), 0 => some (eff b)
  | eff (.matchCause _ v _), 1 => some (eff v)
  | eff (.matchCause _ _ c), 2 => some (eff c)
  | eff (.onExit b _), 0 => some (eff b)
  | eff (.onExit _ f), 1 => some (eff f)
  | eff (.exit b), 0 => some (eff b)
  | eff (.uninterruptible b), 0 => some (eff b)
  | eff (.interruptible b), 0 => some (eff b)
  | eff (.branch _ a _), 0 => some (eff a)
  | eff (.branch _ _ b), 1 => some (eff b)
  | eff (.whileLoop _ _ _ b), 0 => some (eff b)
  | eff (.withFiber a), 0 => some (action a)
  | eff (.scoped b), 0 => some (eff b)
  | eff (.acquireRelease a _), 0 => some (eff a)
  | eff (.acquireRelease _ r), 1 => some (eff r)
  | eff (.choose _ l _), 0 => some (eff l)
  | eff (.choose _ _ r), 1 => some (eff r)
  | stmts (.cons h _), 0 => some (stmt h)
  | stmts (.cons _ t), 1 => some (stmts t)
  | stmt (.bindYield e), 0 => some (eff e)
  | stmt (.yieldDiscard e), 0 => some (eff e)
  | stmt (.ifElse _ a _), 0 => some (stmts a)
  | stmt (.ifElse _ _ b), 1 => some (stmts b)
  | stmt (.whileTrue b), 0 => some (stmts b)
  | action (.fork p _), 0 => some (eff p)
  | action (.forkIn p _ _), 0 => some (eff p)
  | action (.forkScoped p _), 0 => some (eff p)
  | action (.raceAll es), 0 => some (effs es)
  | effs (.cons h _), 0 => some (eff h)
  | effs (.cons _ t), 1 => some (effs t)
  | _, _ => none

/-- The node at a path. -/
def at_ : Node → List Nat → Option Node
  | n, [] => some n
  | n, i :: rest => (n.child i).bind (at_ · rest)

end Node

/-! ## Points, names, thunks -/

/-- Where a compiled program stands. -/
structure Point where
  /-- The subterm of the root program: child indices from the root. -/
  path : List Nat
  /-- The positional values in scope (D1). -/
  env : List Val
  /-- What is left: every continuation name costs one, every loop iteration one. -/
  fuel : Nat
  /-- The decisions left, for `choose` sites. -/
  tape : List Bool
deriving DecidableEq

namespace Point

/-- The point of the child at index `i`, same environment, one fuel down. -/
def child (p : Point) (i : Nat) : Point :=
  { p with path := p.path ++ [i], fuel := p.fuel - 1 }

/-- The point of the child at index `i` with a value appended to the scope. -/
def childWith (p : Point) (i : Nat) (v : Val) : Point :=
  { p with path := p.path ++ [i], env := p.env ++ [v], fuel := p.fuel - 1 }

def childWith2 (p : Point) (i : Nat) (v w : Val) : Point :=
  { p with path := p.path ++ [i], env := p.env ++ [v, w], fuel := p.fuel - 1 }

end Point

/-- The continuation, finalizer, generator, loop, registration and cancel names. First-order
data; `contAOf`/`contEOf` and the other hooks of `interpOf` give them meaning. -/
inductive EffName
  /-- `bind`'s continuation: the rest at the point's child 1, the answer appended. -/
  | cont (p : Point)
  /-- `catchCause`'s handler: child 1, the cause appended as a reified exit. -/
  | caught (p : Point)
  /-- `matchCause`'s two arms: children 1 and 2. -/
  | onValue (p : Point)
  | onCause (p : Point)
  /-- `onExit`'s finalizer: child 1, the exit appended as a value. -/
  | fin (p : Point)
  /-- The exit path's two names, as the stores spell them. -/
  | restore (exit : ExitV)
  | merge (exit : ExitV)
  /-- A generator: the `gen` node's point (its `env` the values in scope at the program
  counter), the program counter `pc` (a path from the body's statement list to the list to
  run next), and whether the next answer is bound as the next variable. -/
  | gen (p : Point) (pc : List Nat) (bind : Bool)
  /-- `whileLoop` at its point; the cursor is the frame's `β`. -/
  | loop (p : Point)
  /-- `Deferred.await`'s registration and cancel, as the stores spell them. -/
  | registerAwait (cell : DeferredKey)
  | cancelAwait (cell : DeferredKey)
  | withWaiter (base : EffName) (waiter : FiberId) (token : Nat)
  | abort
  | reFail (cause : CauseV)
  /-- `scoped`: the scope was made (the value is its handle). -/
  | scopeOpen (p : Point)
  /-- `scoped`: the context was read (the value is it); provide the scope and run the body. -/
  | scopeProvide (p : Point) (scope : Nat)
  /-- `scoped`: the context was set; run the body under the restoring finalizer. -/
  | scopeBody (p : Point) (previous : Ctx)
  /-- The finalizer that closes a scope with the body's exit. -/
  | scopeClose (scope : Nat)
  /-- The finalizer that restores a context. -/
  | restoreCtx (previous : Ctx)
  | constant (v : Val)
  /-- A name of the stores' own alphabet: the programs the stores build (a scope's close
  chain, a completion, a finalizer name) embed as they are. -/
  | store (name : Name)
deriving DecidableEq

/-- The thunk alphabet: a pure term at a point, a body to compile at a point, a store
operation, a park, a fiber action at a point, and the context and scope actions the
`scoped` frames need. -/
inductive EffThunk
  | pure (p : Point)
  | body (p : Point)
  | op (operation : SyncOp)
  | park (kind : ParkKind)
  | act (p : Point)
  | getCtx
  | setCtx (context : Ctx)
  | closeScope (scope : Nat) (exit : ExitV)
  /-- A thunk of the stores' own alphabet, embedded. -/
  | store (thunk : Thunk)
deriving DecidableEq

/-- The compiled program carrier. -/
abbrev NCode := Prim EffName EffThunk Val Err Defect FiberId Ann

/-- The machine's action alphabet at this instantiation. -/
abbrev NAction := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx

/-! ## The stores' programs embed

The deferred store holds programs of the stores' alphabet (a completion, the resumes it
owes), and the scope store's close is a program of that alphabet. They embed name by name
and thunk by thunk; the hooks of `interpOf` delegate to `Deep.Stores.stores` on an embedded
name, so the stores are reused unchanged (plan G5). -/

/-- The embedding of a stores program. -/
def embed : Program → NCode
  | .success v => .success v
  | .failure c => .failure c
  | .sync t => .sync (.store t)
  | .suspend t => .suspend (.store t)
  | .withFiber t => .withFiber (.store t)
  | .yieldableError e => .yieldableError e
  | .iterator g c => .iterator (.store g) c
  | .onSuccess body n => .onSuccess (embed body) (.store n)
  | .onFailure body n => .onFailure (embed body) (.store n)
  | .onSuccessAndFailure body a e => .onSuccessAndFailure (embed body) (.store a) (.store e)
  | .exitFrame body => .exitFrame (embed body)
  | .onExit body f flag => .onExit (embed body) (.store f) flag
  | .setInterruptible flag => .setInterruptible flag
  | .whileLoop l c => .whileLoop (.store l) c
  | .yieldNowWith n => .yieldNowWith n
  | .async r s c => .async (.store r) s (c.map EffName.store)
  | .asyncFinalizer n => .asyncFinalizer (.store n)

/-- The embedding of a stores action. -/
def embedAction : WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx → NAction
  | .fork p o => .fork (embed p) o
  | .forkIn p o s k => .forkIn (embed p) o s k
  | .forkScoped p o k => .forkScoped (embed p) o k
  | .runIn t s k => .runIn t s k
  | .interrupt t => .interrupt t
  | .interruptScoped t => .interruptScoped t
  | .interruptAll ts who => .interruptAll ts who
  | .awaitAll ts => .awaitAll ts
  | .awaitAllFailFast ts => .awaitAllFailFast ts
  | .snapshotChildren => .snapshotChildren
  | .awaitNewChildren s => .awaitNewChildren s
  | .raceAll es => .raceAll (es.map embed)
  | .setInterruptible body flag => .setInterruptible (embed body) flag
  | .setContext c => .setContext c
  | .getContext => .getContext
  | .getId => .getId
  | .closeScope s e => .closeScope s e
  | .refuse c => .refuse c

/-! ## The compile -/

/-- The error alphabet's image of a value: numbers are tags; anything else is `boom`
(`typeOf` admits only numbers). -/
def errOf : Val → Err
  | Val.nat n => Err.tag n
  | _ => Err.boom

/-- A value of the wrong shape where the program's typing promised another: the same
defect the stores answer for a continuation applied to the wrong value. -/
def badShape : NCode := Prim.failure (Cause.die Defect.badName)

/-- A live frontier: what the compile answers at fuel zero. -/
def frontier (p : Point) : NCode := Prim.suspend (EffThunk.body p)

/-- The cause a cause term spells. -/
def causeOf (env : List Val) : CauseTerm → Option CauseV
  | .fail error => (evalTerm env error).map fun v => Cause.fail (errOf v)
  | .die defect =>
    (evalTerm env defect).map fun
      | Val.nat n => Cause.die (Defect.user n)
      | _ => Cause.die Defect.badName
  | .interrupt none => some (Cause.interrupt none)
  | .interrupt (some who) =>
    match evalTerm env who with
    | some (Val.fiber id) => some (Cause.interrupt (some id))
    | _ => none
  | .both left right => do
    let l ← causeOf env left
    let r ← causeOf env right
    some (Cause.combine l r)

/-- The exit a reified exit value spells. -/
def exitOfVal : Val → Option ExitV
  | Val.exitOk v => some (Exit.success v)
  | Val.exitErr c => some (Exit.failure c)
  | _ => none

/-- `compile` of plan §3, structural in the program; the point is data. Names are minted at
the point; `interpOf` resolves them by compiling the subterm they address. -/
def compileEff : NativeEff → Point → NCode
  | e, p =>
    match p.fuel with
    | 0 => frontier p
    | _ + 1 =>
      match e with
      | .succeed v =>
        match evalTerm p.env v with
        | some val => Prim.success val
        | none => badShape
      | .fail e =>
        match evalTerm p.env e with
        | some val => Prim.failure (Cause.fail (errOf val))
        | none => badShape
      | .failCause c =>
        match causeOf p.env c with
        | some cause => Prim.failure cause
        | none => badShape
      | .yieldError e =>
        match evalTerm p.env e with
        | some val => Prim.yieldableError (errOf val)
        | none => badShape
      | .sync _ => Prim.sync (EffThunk.pure p)
      | .suspend _ => Prim.suspend (EffThunk.body (p.child 0))
      | .perform op request =>
        match (NativeOp.row op).kind with
        | .sync =>
          match evalTerm p.env request with
          | some val =>
            match NativeOp.syncOpOf op val with
            | some operation => Prim.sync (EffThunk.op operation)
            | none => badShape
          | none => badShape
        | .async =>
          match (evalTerm p.env request).bind NativeOp.awaitCellOf with
          | some cell =>
            Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
          | none => badShape
        | .program => frontier p
      | .bind first _ => Prim.onSuccess (compileEff first (p.child 0)) (EffName.cont p)
      | .gen _ => Prim.iterator (EffName.gen p [] false) Val.unit
      | .catchCause body _ => Prim.onFailure (compileEff body (p.child 0)) (EffName.caught p)
      | .matchCause body _ _ =>
        Prim.onSuccessAndFailure (compileEff body (p.child 0)) (EffName.onValue p)
          (EffName.onCause p)
      | .onExit body _ => Prim.onExit (compileEff body (p.child 0)) (EffName.fin p) false
      | .exit body => Prim.exitFrame (compileEff body (p.child 0))
      | .uninterruptible _ => Prim.withFiber (EffThunk.act p)
      | .interruptible _ => Prim.withFiber (EffThunk.act p)
      | .branch _ _ _ => Prim.suspend (EffThunk.body p)
      | .whileLoop initial _ _ _ =>
        match evalTerm p.env initial with
        | some cursor => Prim.whileLoop (EffName.loop p) cursor
        | none => badShape
      | .yieldNow priority => Prim.yieldNowWith priority
      | .callback register request =>
        match (NativeOp.row register).kind with
        | .async =>
          match (evalTerm p.env request).bind NativeOp.awaitCellOf with
          | some cell =>
            Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
          | none => badShape
        | _ => badShape
      | .awaitFiber fiber mode =>
        match evalTerm p.env fiber with
        | some (Val.fiber id) => Prim.suspend (EffThunk.park (ParkKind.join id mode))
        | _ => badShape
      | .withFiber _ => Prim.withFiber (EffThunk.act p)
      | .scoped _ =>
        Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeMake FinalizerStrategy.sequential)))
          (EffName.scopeOpen p)
      | .acquireRelease _ _ => frontier p
      | .choose _ left right =>
        match p.tape with
        | true :: rest => compileEff left { p with path := p.path ++ [0], tape := rest }
        | false :: rest => compileEff right { p with path := p.path ++ [1], tape := rest }
        | [] => frontier p

/-- The program at a point of the root: the subterm compiled there, or the frontier. -/
def resolve (root : NativeEff) (p : Point) : NCode :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff e) => compileEff e p
  | _ => badShape

/-! ## Generators: the statement walker behind `iterNext` -/

/-- The number of `bindYield` statements among the first `k` of a list: the bindings a block
has made at position `k`, dropped when the block ends. -/
def localBinds : Stmts NativeOp → Nat → Nat
  | .cons (.bindYield _) t, k + 1 => 1 + localBinds t k
  | .cons _ t, k + 1 => localBinds t k
  | _, _ => 0

/-- Split a program counter into the block it stands in and the position within it. A
program counter is `1^k₀ ++ [0, s₁] ++ 1^k₁ ++ … ++ [0, sₙ] ++ 1^kₙ`: a run of `1`s is the
position in a list, `0` descends into the head statement and the next index selects its
block. Read from the front, so an else block's selector `[0, 1]` is never mistaken for a
position (finding A3-2, 2026-09-04). -/
def walkPc : List Nat → List Nat → Nat → List Nat × Nat
  | [], block, k => (block, k)
  | 1 :: rest, block, k => walkPc rest block (k + 1)
  | 0 :: sel :: rest, block, k => walkPc rest (block ++ List.replicate k 1 ++ [0, sel]) 0
  | _ :: rest, block, k => walkPc rest block k

def splitPc (pc : List Nat) : List Nat × Nat := walkPc pc [] 0

/-- The statements of the block at `block` (a path to a `stmts` node under the generator's
body). -/
def blockAt (root : NativeEff) (p : Point) (block : List Nat) : Option (Stmts NativeOp) :=
  match Node.at_ (Node.eff root) (p.path ++ [0] ++ block) with
  | some (Node.stmts ss) => some ss
  | _ => none

/-- Leave the block at `pc` (its statements exhausted): the environment loses the block's
bindings, and control continues after the enclosing statement — or at the head of the
enclosing `while` again. `none` is the end of the generator's body. -/
def blockExit (root : NativeEff) (p : Point) (pc : List Nat) (env : List Val) :
    Option (List Nat × List Val) :=
  let (block, k) := splitPc pc
  let env := match blockAt root p block with
    | some ss => env.take (env.length - localBinds ss k)
    | none => env
  match block.reverse with
  | _ :: 0 :: outer =>
    let base := outer.reverse
    match Node.at_ (Node.eff root) (p.path ++ [0] ++ base) with
    | some (Node.stmts (.cons (.whileTrue _) _)) => some (base ++ [0, 0], env)
    | _ => some (base ++ [1], env)
  | _ => none

/-- Leave the innermost enclosing `while` (`break`): pop blocks until one is a loop body,
dropping their bindings. -/
def loopExit (root : NativeEff) : Nat → Point → List Nat → List Val →
    Option (List Nat × List Val)
  | 0, _, _, _ => none
  | depth + 1, p, pc, env =>
    let (block, k) := splitPc pc
    let env := match blockAt root p block with
      | some ss => env.take (env.length - localBinds ss k)
      | none => env
    match block.reverse with
    | _ :: 0 :: outer =>
      let base := outer.reverse
      match Node.at_ (Node.eff root) (p.path ++ [0] ++ base) with
      | some (Node.stmts (.cons (.whileTrue _) _)) => some (base ++ [1], env)
      | _ => loopExit root depth p base env
    | _ => none

/-- The generator's step: from the list at `pc` with `env` in scope, through pure statements
to the next yield, the return, or the body's end. Pure successes are folded inline
(`folded`); a yielded failure halts; anything else resumes with the advanced name. -/
def runStmts (root : NativeEff) (p : Point) :
    Nat → List Nat → List Val → List Val → List Val × IterStep EffName EffThunk Val Err Defect FiberId Ann
  | 0, pc, env, folded =>
    (folded, IterStep.resume (frontier { p with path := p.path ++ [0] ++ pc, env := env, fuel := 0 })
      (EffName.gen { p with env := env } pc false))
  | fuel + 1, pc, env, folded =>
    match blockAt root p pc with
    | some .nil =>
      match blockExit root p pc env with
      | none => (folded, IterStep.done Val.unit)
      | some (pc', env') => runStmts root p fuel pc' env' folded
    | some (.cons s _) =>
      match s with
      | .bindYield e => yieldOf e true fuel pc env folded
      | .yieldDiscard e => yieldOf e false fuel pc env folded
      | .ret v =>
        match evalTerm env v with
        | some value => (folded, IterStep.done value)
        | none => (folded, IterStep.halt (Cause.die Defect.badName))
      | .ifElse test _ _ =>
        match evalTerm env test with
        | some (Val.bool true) => runStmts root p fuel (pc ++ [0, 0]) env folded
        | some (Val.bool false) => runStmts root p fuel (pc ++ [0, 1]) env folded
        | _ => (folded, IterStep.halt (Cause.die Defect.badName))
      | .whileTrue _ => runStmts root p fuel (pc ++ [0, 0]) env folded
      | .breakLoop =>
        match loopExit root (pc.length + 1) p pc env with
        | some (pc', env') => runStmts root p fuel pc' env' folded
        | none => (folded, IterStep.halt (Cause.die Defect.badName))
    | none => (folded, IterStep.halt (Cause.die Defect.badName))
  where
    /-- The effect of a yield statement at `pc`, compiled at its own point. -/
    yieldOf (e : NativeEff) (bind : Bool) (fuel : Nat) (pc : List Nat) (env : List Val)
        (folded : List Val) : List Val × IterStep EffName EffThunk Val Err Defect FiberId Ann :=
      let q : Point := { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 }
      match compileEff e q with
      | Prim.success value =>
        runStmts root p fuel (pc ++ [1]) (if bind then env ++ [value] else env) (folded ++ [value])
      | Prim.failure cause => (folded, IterStep.halt cause)
      | prim => (folded, IterStep.resume prim (EffName.gen { p with env := env } (pc ++ [1]) bind))

/-! ## The names' meaning -/

/-- The fiber action a point names: the action node, or a mask over a body. -/
def actionAt (root : NativeEff) (p : Point) : Option NAction :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff (.uninterruptible _)) =>
    some (WithFiberAction.setInterruptible (resolve root (p.child 0)) false)
  | some (Node.eff (.interruptible _)) =>
    some (WithFiberAction.setInterruptible (resolve root (p.child 0)) true)
  | some (Node.eff (.withFiber a)) =>
    let q := p.child 0
    let refuse : NAction := WithFiberAction.refuse (Cause.die Defect.badName)
    let handles : Val → Option (List FiberId) := fun
      | Val.fibers ids => some ids
      | v => (Val.tuple? v).bind fun vs => vs.mapM fun
        | Val.fiber id => some id
        | _ => none
    some (match a with
      | .fork _ options => WithFiberAction.fork (resolve root (q.child 0)) options
      | .forkIn _ options scope =>
        match evalTerm p.env scope with
        | some (Val.scopeHandle s) =>
          WithFiberAction.forkIn (resolve root (q.child 0)) options s p.fuel
        | _ => refuse
      | .forkScoped _ options =>
        WithFiberAction.forkScoped (resolve root (q.child 0)) options p.fuel
      | .runIn target scope =>
        match evalTerm p.env target, evalTerm p.env scope with
        | some (Val.fiber id), some (Val.scopeHandle s) => WithFiberAction.runIn id s p.fuel
        | _, _ => refuse
      | .interrupt target =>
        match evalTerm p.env target with
        | some (Val.fiber id) => WithFiberAction.interrupt id
        | _ => refuse
      | .interruptScoped target =>
        match evalTerm p.env target with
        | some (Val.fiber id) => WithFiberAction.interruptScoped id
        | _ => refuse
      | .interruptAll targets interruptor =>
        match (evalTerm p.env targets).bind handles with
        | some ids =>
          match interruptor with
          | none => WithFiberAction.interruptAll ids none
          | some who =>
            match evalTerm p.env who with
            | some (Val.fiber id) => WithFiberAction.interruptAll ids (some id)
            | _ => refuse
        | none => refuse
      | .awaitAll targets =>
        match (evalTerm p.env targets).bind handles with
        | some ids => WithFiberAction.awaitAll ids
        | none => refuse
      | .awaitAllFailFast targets =>
        match (evalTerm p.env targets).bind handles with
        | some ids => WithFiberAction.awaitAllFailFast ids
        | none => refuse
      | .snapshotChildren => WithFiberAction.snapshotChildren
      | .awaitNewChildren snapshot =>
        match (evalTerm p.env snapshot).bind handles with
        | some ids => WithFiberAction.awaitNewChildren ids
        | none => refuse
      | .raceAll es => WithFiberAction.raceAll (entrants es (q.child 0))
      | .setContext context =>
        match evalTerm p.env context with
        | some (Val.context ctx) => WithFiberAction.setContext ctx
        | _ => refuse
      | .getContext => WithFiberAction.getContext
      | .getId => WithFiberAction.getId
      | .closeScope scope exit =>
        match evalTerm p.env scope, (evalTerm p.env exit).bind exitOfVal with
        | some (Val.scopeHandle s), some e => WithFiberAction.closeScope s e
        | _, _ => refuse)
  | _ => none
where
  /-- The entrants of a race, each compiled at its own point (`effs` node children). -/
  entrants : Effs NativeOp → Point → List NCode
    | .nil, _ => []
    | .cons h t, q => compileEff h (q.child 0) :: entrants t (q.child 1)

/-- `cont[contA](value, fiber)`. -/
def contAOf (root : NativeEff) : EffName → Val → NCode
  | .cont p, v => resolve root (p.childWith 1 v)
  | .onValue p, v => resolve root (p.childWith 1 v)
  | .restore exit, _ => Prim.ofExit exit
  | .merge exit, _ => Prim.ofExit exit
  | .reFail cause, _ => Prim.failure cause
  | .scopeOpen p, Val.scopeHandle s =>
    Prim.onExit (Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.scopeProvide p s))
      (EffName.scopeClose s) false
  | .scopeOpen _, _ => badShape
  | .scopeProvide p s, Val.context previous =>
    Prim.onSuccess (Prim.withFiber (EffThunk.setCtx { previous with ambientScope := some s }))
      (EffName.scopeBody p previous)
  | .scopeProvide _ _, _ => badShape
  | .scopeBody p previous, _ =>
    Prim.onExit (resolve root (p.child 0)) (EffName.restoreCtx previous) false
  | .constant v, _ => Prim.success v
  | .abort, _ => Prim.success Val.unit
  | .store name, v => embed (Effect4.Deep.contAOf name v)
  | _, v => Prim.success v

/-- `cont[contE](cause, fiber)`. -/
def contEOf (root : NativeEff) : EffName → CauseV → NCode
  | .caught p, cause => resolve root (p.childWith 1 (Val.exitErr cause))
  | .onCause p, cause => resolve root (p.childWith 2 (Val.exitErr cause))
  | .restore exit, cause => Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | .merge exit, cause => Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | .constant v, _ => Prim.success v
  | .store name, cause => embed (Effect4.Deep.contEOf name cause)
  | _, cause => Prim.failure cause

/-- The cancel effect a cancel name runs (`Deferred.await`'s cleanup splices the waiter out,
as the stores spell it); an embedded cancel name runs the stores' cancel program. -/
def cancelProgramOf : EffName → NCode
  | .withWaiter (.cancelAwait cell) waiter token =>
    Prim.sync (EffThunk.op (SyncOp.deferredAwaitCleanup cell waiter token))
  | .withWaiter (.store base) waiter token => embed (cancelProgram (Name.withWaiter base waiter token))
  | .store name => embed (cancelProgram name)
  | _ => Prim.success Val.unit

/-- The value of a `sync` thunk that touches no store: the term at its point. -/
def syncValueAt (root : NativeEff) : EffThunk → Val
  | .pure p =>
    match Node.at_ (Node.eff root) p.path with
    | some (Node.eff (.sync t)) => (evalTerm p.env t).getD Val.unit
    | _ => Val.unit
  | _ => Val.unit

/-- What a `suspend` thunk returns: a body compiled at its point, or a branch decided by
its point's environment. -/
def suspendBodyAt (root : NativeEff) : EffThunk → NCode
  | .body p =>
    match p.fuel with
    | 0 => frontier p
    | _ + 1 =>
      match Node.at_ (Node.eff root) p.path with
      | some (Node.eff (.branch test _ _)) =>
        match evalTerm p.env test with
        | some (Val.bool true) => resolve root (p.child 0)
        | some (Val.bool false) => resolve root (p.child 1)
        | _ => badShape
      | some (Node.eff e) => compileEff e p
      | _ => badShape
  | .store (Thunk.body program) => embed (progOf program)
  | _ => Prim.failure (Cause.die Defect.notImplemented)

/-- The loop at a point: its test, step and body terms. -/
def loopAt (root : NativeEff) (p : Point) : Option (Term × Term × NativeEff) :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff (.whileLoop _ test step body)) => some (test, step, body)
  | _ => none

/-- The interp of a root program: names mean the subterms they address. -/
def interpOf (root : NativeEff) :
    RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores where
  contA := contAOf root
  contE := contEOf root
  syncValue := syncValueAt root
  suspendBody := suspendBodyAt root
  finalizerExit := fun
    | .store (Name.finalizerName fin), exit => finExit fin exit
    | _, _ => Exit.void
  reifyExit := reifyExitVal
  iterNext := fun name value =>
    match name with
    | .gen p pc bind => runStmts root p p.fuel pc (if bind then p.env ++ [value] else p.env) []
    | _ => ([], IterStep.done value)
  loopTest := fun name cursor =>
    match name with
    | .loop p =>
      match loopAt root p with
      | some (test, _, _) => evalTerm (p.env ++ [cursor]) test = some (Val.bool true)
      | none => false
    | _ => false
  loopBody := fun name cursor =>
    match name with
    | .loop p => resolve root (p.childWith 0 cursor)
    | _ => Prim.success cursor
  loopStep := fun name cursor answer =>
    match name with
    | .loop p =>
      match loopAt root p with
      | some (_, step, _) => (evalTerm (p.env ++ [cursor, answer]) step).getD cursor
      | none => cursor
    | _ => cursor
  loopDone := fun _ => Val.unit
  notImplemented := Defect.notImplemented
  cancelThenFail := fun name cause => Prim.onSuccess (cancelProgramOf name) (EffName.reFail cause)
  parkOf := fun
    | Prim.suspend (EffThunk.park kind) => some (Except.ok kind)
    | Prim.suspend (EffThunk.store (Thunk.park kind)) => some (Except.ok kind)
    | _ => none
  withFiberOf := fun
    | EffThunk.act p => actionAt root p
    | EffThunk.getCtx => some WithFiberAction.getContext
    | EffThunk.setCtx context => some (WithFiberAction.setContext context)
    | EffThunk.closeScope scope exit => some (WithFiberAction.closeScope scope exit)
    | EffThunk.store (Thunk.act action) => some (embedAction (actionOf action))
    | _ => none
  syncState := fun
    | EffThunk.op operation, state => syncOpStep operation state
    | EffThunk.store (Thunk.op operation), state => syncOpStep operation state
    | _, _ => none
  registerAsync := fun name fiber token state =>
    match name with
    | .registerAwait cell =>
      let (deferreds, immediate) := state.deferreds.register cell fiber token
      ({ state with deferreds := deferreds }, immediate.map embed)
    | .store (Name.registerAwait cell) =>
      let (deferreds, immediate) := state.deferreds.register cell fiber token
      ({ state with deferreds := deferreds }, immediate.map embed)
    | _ => (state, none)
  dueResumes := fun state =>
    let (due, deferreds) := state.deferreds.drainDue
    (due.map fun d => (d.1, d.2.1, embed d.2.2), { state with deferreds := deferreds })
  cancelName := fun base fiber token => EffName.withWaiter base fiber token
  abortName := EffName.abort
  finalizerProgram := fun name exit =>
    match name with
    | .fin p => some (resolve root (p.childWith 1 (reifyExitVal exit)))
    | .scopeClose scope => some (Prim.withFiber (EffThunk.closeScope scope exit))
    | .restoreCtx previous => some (Prim.withFiber (EffThunk.setCtx previous))
    | .store (Name.finalizerName fin) => some (embed (finProgram fin exit))
    | _ => none
  restoreName := EffName.restore
  mergeName := EffName.merge
  scopeStatus := fun scope state => state.scopes.status scope
  scopeLinkFiber := fun mode scope key fiber state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ =>
      let skipSelf :=
        match mode with
        | Supervision.ScopeMode.forkIn => true
        | Supervision.ScopeMode.fiberRunIn => false
      some { state with
        scopes := (state.scopes.addFinalizer scope key (FinName.interruptFiber fiber skipSelf)).1 }
  dropFinalizer := fun scope key state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ => some { state with scopes := state.scopes.removeFinalizer scope key }
  closeScope := fun scope exit closerInterruptible _closer state =>
    (storesCloseScope scope exit closerInterruptible state).map fun r => (r.1, embed r.2)
  ambientScope := Ctx.ambientScope
  budgetOf := fun ctx => (ctx.maxOpsBeforeYield, ctx.preventYield)
  emptyContext := emptyCtx
  contextValue := Val.context
  exitValue := fun exit mode =>
    match mode with
    | Supervision.ObserverMode.awaitValue => Prim.success (reifyExitVal exit)
    | Supervision.ObserverMode.joinEffect => Prim.ofExit exit
  fiberValue := Val.fiber
  fibersValue := Val.fibers
  exitsValue := exitsVal
  voidValue := Val.unit
  encodeFiber := id
  stackAnnotations := stackAnnotationsOf
  asyncFiberError := Defect.asyncFiber
  missingScope := Defect.missingService

/-- The root point of a program: the empty path, no values, the fuel and the tape. -/
def rootPoint (fuel : Nat) (tape : List Bool := []) : Point := ⟨[], [], fuel, tape⟩

/-- The compiled root. -/
def compile (root : NativeEff) (fuel : Nat) (tape : List Bool := []) : NCode :=
  compileEff root (rootPoint fuel tape)

/-! ## Separation-4 gates: names and thunks stay data -/

example : DecidableEq EffName := inferInstance
example : DecidableEq EffThunk := inferInstance
example : DecidableEq NCode := inferInstance

end Effect4.Syntax
