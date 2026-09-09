import Effect4.Program.Typing
import TypeScript

/-!
# Syntax.Print — `Eff` into TypeScript (lane A2 of the AST relation)

Plan: `docs/research/2026-09-04-ast-relation-plan.md` §5, and the spelling table of §5.1,
which this module implements one row at a time. `print` takes a program of `Eff.lean` into
the pinned lean4-typescript fragment (`TypeScript.Expr`, `TypeScript.Stmt`), which
`TypeScript.Render.expr house0 0` renders at a fixed layout: equal syntax is equal bytes,
so the printer is byte-deterministic without a width heuristic anywhere in it.

Three formers of lean4-typescript v0.5.0 carry the shapes the fragment lacked before, and
each has exactly one consumer here: `Expr.generator` (`function* () { … }`) is what
`Effect.gen` takes, `Expr.cond` (`t ? a : b`) is the value-decided `branch`, and
`Expr.arrowBlock` (`(a) => { … }`) is the suspended block and the `step` of a
`whileLoop`.

The `Nat` every printing function carries is the environment's length (decision D1: a
positional environment, the flows' convention), so the next binder minted is
`Var.name n = a{n}`. Nothing else decides a name: the printer never reads a source
identifier and never invents one twice.

What the table refuses, the printer refuses by name rather than by a fallback spelling:
`choose` is a flows-only constructor with no Effect combinator (D2), and the five internal
fiber actions (`interruptScoped`, `awaitAllFailFast`, `snapshotChildren`,
`awaitNewChildren`, `setContext`) have no public rc.112 export with the same frame shape.
`PrintRefusal` is the closed refusal alphabet; a refusal is data, never a printed guess.
-/

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

/-- Why the printer declined a program. The first two arms are the §5.1 table's "refused"
row: `choose` names the decision site the flows front-end would have answered from a tape,
and `internalAction` names the `ActionTerm` constructor whose rc.112 counterpart has no
public export with the same frame shape. `layerRef` is the declaration block's (the host
rows slice): a layer reference whose target path names no layer, so no `const` can be
hoisted for it. -/
inductive PrintRefusal
  | choose (site : Nat)
  | internalAction (name : String)
  | layerRef (target : List Nat)
deriving DecidableEq, Repr

/-- The binder minted for environment position `index`: `a0`, `a1`, … The environment is
positional, so a position is a name and the printer needs no source identifiers. -/
def Var.name (index : Nat) : String := "a" ++ toString index

/-- A literal as target syntax: `undefined` for unit, the number, `true`/`false`, and the
quoted string (the renderer owns the quoting and the escapes). -/
def printLit : Lit → TypeScript.Expr
  | .unit => .ident "undefined"
  | .nat value => .int (Int.ofNat value)
  | .bool value => .bool value
  | .str value => .str value

mutual
  /-- A pure term: a variable as its binder name, a literal as itself, and an atom applied
  to its arguments as the call `atom(args)`. -/
  def printTerm : Term → TypeScript.Expr
    | .var index => .ident (Var.name index)
    | .lit value => printLit value
    | .app atom args => .call (.ident atom) (printTerms args)

  /-- The argument list of an atom application, in order. -/
  def printTerms : Terms → List TypeScript.Expr
    | .nil => []
    | .cons head tail => printTerm head :: printTerms tail
end

/-- A cause as the public `Cause` constructors of rc.112. `Cause.merge` is not an export at
the pin, so the merge of two causes is spelled `Cause.combine` (§5.1). -/
def printCause : CauseTerm → TypeScript.Expr
  | .fail error => .call (.ident "Cause.fail") [printTerm error]
  | .die defect => .call (.ident "Cause.die") [printTerm defect]
  | .interrupt none => .call (.ident "Cause.interrupt") []
  | .interrupt (some who) => .call (.ident "Cause.interrupt") [printTerm who]
  | .both left right => .call (.ident "Cause.combine") [printCause left, printCause right]

/-- The two components of a `pair` application, the request shape a tuple-call row
receives from an admitted program. -/
def pairArgs? : Term → Option (Term × Term)
  | .app atom (.cons x (.cons y .nil)) => if atom = "pair" then some (x, y) else none
  | _ => none

theorem pairArgs?_some {r x y : Term} (h : pairArgs? r = some (x, y)) :
    r = .app "pair" (.cons x (.cons y .nil)) := by
  unfold pairArgs? at h
  split at h
  · split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hp
      rfl
    · cases h
  · cases h

/-- The argument list of a tuple-call row (source-repairs §18): the components of a
`pair` application print as the two arguments the pinned two-argument export declares,
so the host infers the export's type parameters from them; any other request, a saved
variable in the admitted image, prints as `fst(request)` and `snd(request)`, one read
of the value per component. -/
def printTupleArgs (request : Term) : List TypeScript.Expr :=
  match pairArgs? request with
  | some (x, y) => [printTerm x, printTerm y]
  | none => [.call (.ident "fst") [printTerm request], .call (.ident "snd") [printTerm request]]

/-- A row's called head: its `spelling`, applied to the declared type arguments when it has
any. rc.112's `Deferred.make` has defaulted type parameters, so the arguments alone do not
determine the handle's types and the call must carry them (`E4-CHECK-CE-013`). -/
def printRowHead (row : Row) : TypeScript.Expr :=
  match row.typeArgs with
  | [] => .ident row.spelling
  | args => .generic (.ident row.spelling) args

/-- A row's operation, by the row's declared shape and request type: a value row is the
bare `spelling` (the service route's nullary rows), a call row on a `unit` request is
`spelling()`, and every other call row is `spelling(request)`. A tuple-call row receives
`printTupleArgs` of its request as two ordinary arguments, then the declared trailing
names. A row that declares type arguments carries them on the head. -/
def printRow (row : Row) (request : Term) : TypeScript.Expr :=
  let trailing := row.trailing.map TypeScript.Expr.ident
  match row.shape with
  | .value => .ident row.spelling
  | .call =>
    if row.request = Ty.unit then .call (printRowHead row) trailing
    else .call (printRowHead row) (printTerm request :: trailing)
  | .tupleCall => .call (printRowHead row) (printTupleArgs request ++ trailing)

/-- The fork options object rc.112's fork family takes:
`{ startImmediately: b, uninterruptible: true | false | "inherit" }`. `daemon` is not a
field — it selects `Effect.forkChild` against `Effect.forkDetach` instead. -/
def printForkOptions (options : Effect4.Supervision.ForkOptions) : TypeScript.Expr :=
  .object
    [ ("startImmediately", .bool options.startImmediately)
    , ("uninterruptible",
        match options.maskMode with
        | .uninterruptible => .bool true
        | .interruptible => .bool false
        | .inherit => .str "inherit") ]

variable {Op : Type}

/-- A service key as rc.112 spells one — `Context.Service<Shape>("key")`
(`Context.ts:201-215`): the key's two numbers as the string that is its runtime identity
(`:219`, so two spellings of one key are one service), with its carrier from the signature's
service table as the type argument when the table has one. Minted from the key's own data,
as `Var.name` mints a binder from its position: the printer invents no name. -/
def printKey (sig : Signature Op) (key : ServiceKey) : TypeScript.Expr :=
  let head : TypeScript.Expr :=
    match sig.serviceTy key with
    | some ty => .generic (.ident "Context.Service") [ty.render]
    | none => .ident "Context.Service"
  .call head [.str ("k" ++ toString key.name.value ++ "_" ++ toString key.service.value)]

mutual
  /-- `print sig n e` is `e` as one TypeScript expression, with `n` the environment's
  length. Every binder the shape introduces is `Var.name` of the position it occupies:
  `bind`'s answer at `n`, `catchCause`'s cause at `n`, `matchCause`'s two arms each at `n`,
  `onExit`'s exit at `n`, `acquireRelease`'s resource and exit at `n` and `n + 1`, and
  `whileLoop`'s cursor at `n` with the body's answer at `n + 1`. The refusals are §5.1's
  refused row. -/
  def print (sig : Signature Op) (n : Nat) : Eff Op → Except PrintRefusal TypeScript.Expr
    | .succeed value => .ok (.call (.ident "Effect.succeed") [printTerm value])
    | .fail error => .ok (.call (.ident "Effect.fail") [printTerm error])
    | .failCause cause => .ok (.call (.ident "Effect.failCause") [printCause cause])
    | .yieldError error => .ok (printTerm error)
    | .sync thunk => .ok (.call (.ident "Effect.sync") [.arrow none (printTerm thunk)])
    | .suspend body => do
      let b ← print sig n body
      .ok (.call (.ident "Effect.suspend") [.arrow none b])
    | .perform op request => .ok (printRow (sig.rowOf op) request)
    | .bind first rest => do
      let f ← print sig n first
      let r ← print sig (n + 1) rest
      .ok (.call (.ident "Effect.flatMap") [f, .lambda [Var.name n] r])
    | .gen body => do
      let statements ← printStmts sig n body
      .ok (.call (.ident "Effect.gen") [.generator statements])
    | .catchCause body handler => do
      let b ← print sig n body
      let h ← print sig (n + 1) handler
      .ok (.call (.ident "Effect.catchCause") [b, .lambda [Var.name n] h])
    | .matchCause body onValue onCause => do
      let b ← print sig n body
      let v ← print sig (n + 1) onValue
      let c ← print sig (n + 1) onCause
      .ok (.call (.ident "Effect.matchCauseEffect")
        [ b
        , .object
            [ ("onFailure", .lambda [Var.name n] c)
            , ("onSuccess", .lambda [Var.name n] v) ] ])
    | .onExit body finalizer => do
      let b ← print sig n body
      let f ← print sig (n + 1) finalizer
      .ok (.call (.ident "Effect.onExit") [b, .lambda [Var.name n] f])
    | .exit body => do
      let b ← print sig n body
      .ok (.call (.ident "Effect.exit") [b])
    | .uninterruptible body => do
      let b ← print sig n body
      .ok (.call (.ident "Effect.uninterruptible") [b])
    | .interruptible body => do
      let b ← print sig n body
      .ok (.call (.ident "Effect.interruptible") [b])
    | .branch test thenB elseB => do
      let a ← print sig n thenB
      let b ← print sig n elseB
      .ok (.call (.ident "Effect.suspend") [.arrow none (.cond (printTerm test) a b)])
    | .whileLoop initial test step body => do
      let b ← print sig (n + 1) body
      .ok (.call (.ident "Effect.suspend")
        [ .arrowBlock []
            [ .letInit (Var.name n) (printTerm initial)
            , .ret (.call (.ident "Effect.whileLoop")
                [ .object
                    [ ("while", .arrow none (printTerm test))
                    , ("body", .arrow none b)
                    , ("step", .arrowBlock [Var.name (n + 1)]
                        [.assign (Var.name n) (printTerm step)]) ] ]) ] ])
    | .yieldNow priority =>
      .ok (.call (.ident "Effect.yieldNowWith") [.int (Int.ofNat priority)])
    | .callback register request => .ok (printRow (sig.rowOf register) request)
    | .awaitFiber fiber mode =>
      match mode with
      | .joinEffect => .ok (.call (.ident "Fiber.join") [printTerm fiber])
      | .awaitValue => .ok (.call (.ident "Fiber.await") [printTerm fiber])
    | .withFiber action => printAction sig n action
    | .scoped body => do
      let b ← print sig n body
      .ok (.call (.ident "Effect.scoped") [b])
    | .acquireRelease acquire release => do
      let a ← print sig n acquire
      let r ← print sig (n + 2) release
      .ok (.call (.ident "Effect.acquireRelease")
        [a, .lambda [Var.name n, Var.name (n + 1)] r])
    | .choose site _ _ => .error (.choose site)
    -- `Effect.provide(self, layer, { local })` (`internal/layer.ts:8-22`, `Effect.ts:11383`):
    -- the option object only when set, as the corpus writes it
    | .provideLayer layer isLocal body => do
      let b ← print sig n body
      let l ← printLayer sig layer
      .ok (.call (.ident "Effect.provide")
        (if isLocal then [b, l, .object [("local", .bool true)]] else [b, l]))
    -- `Effect.service(key)` (`internal/effect.ts:2059`)
    | .service key => .ok (.call (.ident "Effect.service") [printKey sig key])
    -- `Effect.provideService(self, key, value)` (`internal/effect.ts:2202`)
    | .provideService key value body => do
      let b ← print sig n body
      .ok (.call (.ident "Effect.provideService") [b, printKey sig key, printTerm value])

  /-- A layer term as the rc.112 combinators it transcribes, one arm per `Layer.ts` export
  (the join, 2026-09-07). A body is closed — the layer's own scope is its ambient one
  (`Layer.ts:1438`) — so it prints at environment length `0` and its first binder is `a0`.
  `merge` prints as the two-argument `Layer.merge(a, b)` (`Layer.ts:1850`) and `mergeAll` as
  the n-ary `Layer.mergeAll(a, b, …)` (`:1652`), never one as the other: the two build
  different scope trees, and the compile follows the term's. A reference prints as the
  identifier that carries its target's path (`LayerTerm.refName`, `Refs.lean`); the `const`
  that binds it is `printModule`'s, and an expression printed on its own leaves the
  identifier free. The named spelling of a layer, keys as class identifiers, is
  `Codegen/Layer.lean`'s. -/
  def printLayer (sig : Signature Op) : LayerTerm Op → Except PrintRefusal TypeScript.Expr
    | .succeed key value =>
      .ok (.call (.ident "Layer.succeed") [printKey sig key, printLit value])
    | .effect key body => do
      let b ← print sig 0 body
      .ok (.call (.ident "Layer.effect") [printKey sig key, b])
    | .effectDiscard body => do
      let b ← print sig 0 body
      .ok (.call (.ident "Layer.effectDiscard") [b])
    | .provide self that => do
      let s ← printLayer sig self
      let t ← printLayer sig that
      .ok (.method s "pipe"
        [.call (.ident "Layer.provide") [t]])
    | .provideMerge self that => do
      let s ← printLayer sig self
      let t ← printLayer sig that
      .ok (.method s "pipe"
        [.call (.ident "Layer.provideMerge") [t]])
    | .merge left right => do
      let l ← printLayer sig left
      let r ← printLayer sig right
      .ok (.call (.ident "Layer.merge") [l, r])
    | .fresh inner => do
      let i ← printLayer sig inner
      .ok (.call (.ident "Layer.fresh") [i])
    | .orDie inner => do
      let i ← printLayer sig inner
      .ok (.call (.ident "Layer.orDie") [i])
    | .ref target => .ok (.ident (LayerTerm.refName target))
    | .mergeAll layers => do
      let items ← printLayers sig layers
      .ok (.call (.ident "Layer.mergeAll") items)

  /-- The layers of a `mergeAll`, each closed. -/
  def printLayers (sig : Signature Op) :
      LayerTerms Op → Except PrintRefusal (List TypeScript.Expr) := fun layers =>
    match layers with
    | .nil => .ok []
    | .cons head tail => do
      let h ← printLayer sig head
      let t ← printLayers sig tail
      .ok (h :: t)

  /-- A generator body, statement by statement. `bindYield` binds the answer as the next
  variable and the rest continues one longer; `ifElse` and `whileTrue` are block-scoped, so
  their branches and the rest all continue at `n`. -/
  def printStmts (sig : Signature Op) (n : Nat) :
      Stmts Op → Except PrintRefusal (List TypeScript.Stmt)
    | .nil => .ok []
    | .cons (.bindYield effect) rest => do
      let value ← print sig n effect
      let tail ← printStmts sig (n + 1) rest
      .ok (TypeScript.Stmt.constYield (Var.name n) value :: tail)
    | .cons (.yieldDiscard effect) rest => do
      let value ← print sig n effect
      let tail ← printStmts sig n rest
      .ok (TypeScript.Stmt.yieldDiscard value :: tail)
    | .cons (.ret value) rest => do
      let tail ← printStmts sig n rest
      .ok (TypeScript.Stmt.ret (printTerm value) :: tail)
    | .cons (.ifElse test thenB elseB) rest => do
      let a ← printStmts sig n thenB
      let b ← printStmts sig n elseB
      let tail ← printStmts sig n rest
      .ok (TypeScript.Stmt.ifElse (printTerm test) a b :: tail)
    | .cons (.whileTrue body) rest => do
      let b ← printStmts sig n body
      let tail ← printStmts sig n rest
      .ok (TypeScript.Stmt.whileTrue none b :: tail)
    | .cons .breakLoop rest => do
      let tail ← printStmts sig n rest
      .ok (TypeScript.Stmt.breakTo none :: tail)

  /-- The race entrants, each printed at the same environment length. -/
  def printEffs (sig : Signature Op) (n : Nat) :
      Effs Op → Except PrintRefusal (List TypeScript.Expr) := fun entrants =>
    match entrants with
    | .nil => .ok []
    | .cons head tail => do
      let h ← print sig n head
      let t ← printEffs sig n tail
      .ok (h :: t)

  /-- The fiber actions. The five with no public rc.112 export of the same frame shape are
  refused by constructor name; everything else is `Effect.fork*`, `Fiber.*`, `Scope.close`,
  `Effect.context()` or `Effect.fiberId`, with synchronous `Fiber.runIn` wrapped by
  `Effect.withFiber` to return its declared unit effect. -/
  def printAction (sig : Signature Op) (n : Nat) :
      ActionTerm Op → Except PrintRefusal TypeScript.Expr
    | .fork program options => do
      let p ← print sig n program
      .ok (.call (.ident (if options.daemon then "Effect.forkDetach" else "Effect.forkChild"))
        [p, printForkOptions options])
    | .forkIn program options scope => do
      let p ← print sig n program
      .ok (.call (.ident "Effect.forkIn") [p, printTerm scope, printForkOptions options])
    | .forkScoped program options => do
      let p ← print sig n program
      .ok (.call (.ident "Effect.forkScoped") [p, printForkOptions options])
    | .runIn target scope =>
      -- `Fiber.runIn` is synchronous and returns its fiber (rc.112 :5440-5462).
      -- The IR action returns unit after this WithFiber callback has linked it.
      .ok (.call (.ident "Effect.withFiber")
        [.arrowBlock []
          [.exprStmt (.call (.ident "Fiber.runIn") [printTerm target, printTerm scope]),
            .ret (.ident "Effect.void")]])
    | .interrupt target => .ok (.call (.ident "Fiber.interrupt") [printTerm target])
    | .interruptScoped _ => .error (.internalAction "interruptScoped")
    | .interruptAll targets none =>
      .ok (.call (.ident "Fiber.interruptAll") [printTerm targets])
    | .interruptAll targets (some who) =>
      .ok (.call (.ident "Fiber.interruptAllAs") [printTerm targets, printTerm who])
    | .awaitAll targets => .ok (.call (.ident "Fiber.awaitAll") [printTerm targets])
    | .awaitAllFailFast _ => .error (.internalAction "awaitAllFailFast")
    | .snapshotChildren => .error (.internalAction "snapshotChildren")
    | .awaitNewChildren _ => .error (.internalAction "awaitNewChildren")
    | .raceAll entrants => do
      let items ← printEffs sig n entrants
      .ok (.call (.ident "Effect.raceAll") [.arr items])
    | .setContext _ => .error (.internalAction "setContext")
    | .getContext => .ok (.call (.ident "Effect.context") [])
    | .getId => .ok (.ident "Effect.fiberId")
    | .closeScope scope exit =>
      .ok (.call (.ident "Scope.close") [printTerm scope, printTerm exit])
end

/-- The printed program as an exported constant. The declared type is
`Effect.Effect<A, E>` — the two parameters `EffTy` spells — exactly when the requirement
row is empty; a program with a requirement has no two-parameter spelling here, so its type
is left to inference (§2.2 owns the third parameter, and the requirement's service names
are not this lane's). -/
def printDecl (name : String) (ty : EffTy) (body : TypeScript.Expr) : TypeScript.ConstDecl :=
  { doc := []
  , name := name
  , value := body
  , type :=
      if ty.requires = Requirement.empty then
        some ("Effect.Effect<" ++ ty.answer.render ++ ", " ++ ty.error.render ++ ">")
      else
        none }

/-- The printed program as a declaration block (the host rows slice): one
`const L_<path> = …` per referenced layer target, in declaration order (`Path.declBefore`: a
target inside another first, then program order), each hoisted out of the program so that
its defining site and every reference print as the one identifier (`Refs.lean` `hoistAll`),
which is one rc.112 layer object and one memo entry; the main declaration last. A program
with no references is `[printDecl name ty (print …)]`. `readModule` (`Codegen/Read.lean`)
is the inverse on what this prints. -/
def printModule (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  match e.hoistAll with
  | .error target => .error (.layerRef target)
  | .ok (main, decls) => do
    let ordered := Path.sortBy Path.declBefore (decls.map (·.1))
    let ds ← ordered.mapM fun t =>
      match decls.find? (·.1 == t) with
      | some (_, l) => do
        let x ← printLayer sig l
        .ok ({ doc := [], name := LayerTerm.refName t, value := x } : TypeScript.ConstDecl)
      | none => .error (.layerRef t)
    let m ← print sig 0 main
    .ok (ds ++ [printDecl name ty m])

end Effect4.Program
