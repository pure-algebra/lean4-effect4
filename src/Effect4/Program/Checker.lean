import Effect4.Program.Typing

/-!
# Program.Checker — the typing rules as a fold of the program

The checker of `Program/Typing.lean` rule for rule, re-cut so that every member of the block
is a fold of its sort (`docs/core/traversal-census.md` §7.4): the second file beside the hand
checker, connected by `Laws/Program/Typing/Checker.lean` (`Checker.effTy sig env e = effTy sig
env e`, one theorem per sort), from which `fold_of` derives the algebra
(`Program/Folds/Checker.lean`). Two rules change shape, neither changes what is accepted:

- **A statement has a type** (`StmtTy`). `stmtsTy` split on the statement child and typed its
  grandchild, so statements had no carrier. `stmtTy` types one statement — a *step* with the
  state it contributes and the variables it binds, a *return* with its answer, or *nothing*
  (`break`) — and `stmtsTy` sequences by the statement's type alone. "No statement after a
  return" was a case split on the tail; it is now the mode flag `afterRet`, set by a return
  for its tail, as `inLoop` is set by a loop for its body.
- **The layers of a `mergeAll` are a list of signatures.** `layersTy` refused the empty list
  and merged from the singleton, a case split on the tail. Its result is now the list of the
  members' signatures and `mergeAll`'s own rule takes the nonempty merge
  (`LayerTy.mergeNonempty`).

Nothing here is the authority: the rules are `Typing.lean`'s and the agreement theorem is what
admits this file. Callers move across it before the hand checker is deleted.
-/

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)

/-- The type of one statement of a generator body. -/
inductive StmtTy where
  /-- A statement that contributes a state (its error and requirements, and for a branch or a
  loop its body's answer) and binds `binds` for the statements after it. -/
  | step (state : GenTy) (binds : List Ty)
  /-- `return`: the body's answer; terminal. -/
  | ret (answer : Ty)
  /-- `break`: nothing. -/
  | pass

namespace LayerTy

/-- `Layer.mergeAll` over at least one signature (`Layer.ts:1652`): `merge` folded to the
right from the last; `none` on the empty list. -/
def mergeNonempty : List LayerTy → Option LayerTy
  | [] => none
  | [l] => some l
  | l :: m :: rest => (mergeNonempty (m :: rest)).map l.merge

end LayerTy

namespace Checker

variable {Op : Type}

mutual
  /-- `typeOf` over the environment, structural in the program: `Effect4.Program.effTy`
  rule for rule (`Typing.lean`), with `stmtsTy` under its mode flags. -/
  def effTy (sig : Signature Op) (env : TyEnv) : Eff Op → Option EffTy
    | .succeed value => (termTy sig env value).map EffTy.pure
    | .fail error => do
      let e ← termTy sig env error
      if admittedErrTy e then some ⟨.never, e, Requirement.empty⟩ else none
    | .failCause cause => (causeTy sig env cause).map fun e => ⟨.never, e, Requirement.empty⟩
    | .sync thunk => (termTy sig env thunk).map EffTy.pure
    | .suspend body => effTy sig env body
    -- The operation must be in the signature's domain (`Signature.dom`, DI-54): an external
    -- index outside the supplied table is refused here rather than typed through the
    -- placeholder row, whose `request := .never` otherwise admits any request term typed
    -- `never` (`Native.lean:189-191`). The OCaml checker already refuses it categorically.
    -- The request is admitted at a subtype of the row's request (DI-15, subsumption at the
    -- row request; TypeScript assignability at the call site); the answer is the row's.
    | .perform op request => do
      let row := sig.rowOf op
      let r ← termTy sig env request
      if sig.dom op = true ∧ Ty.sub r.normalize row.request.normalize = true then
        some ⟨row.answer, row.error, Requirement.ofList row.requires⟩
      else none
    | .bind first rest => do
      let f ← effTy sig env first
      let r ← effTy sig (env ++ [f.answer]) rest
      some ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩
    | .gen body => do
      let g ← stmtsTy sig env false false body
      some ⟨g.answer.getD .unit, g.error, g.requires⟩
    | .catchCause body handler => do
      let b ← effTy sig env body
      let h ← effTy sig (env ++ [.causeOf b.error]) handler
      let answer ← EffTy.joinAnswer b.answer h.answer
      some ⟨answer, h.error, b.requires.union h.requires⟩
    -- `catchIfError` keeps every retained failure; only a proved all-caught column leaves E.
    -- The handler is checked under the original first-failure value type.
    | .catchIf test body handler => do
      let b ← effTy sig env body
      let predicate ← termTy sig (env ++ [b.error]) test
      if predicate = .bool then
        let h ← effTy sig (env ++ [b.error]) handler
        let answer ← EffTy.joinAnswer b.answer h.answer
        some ⟨answer, catchIfError test env.length b.error h.error, b.requires.union h.requires⟩
      else none
    -- `select`: the arms are typed at the environments the decision gives from the
    -- scrutinee's type; their answers join, both errors and requirements are kept.
    | .select s d a0 a1 => do
      let t ← termTy sig env s
      let (e0, e1) ← d.arms t
      let t0 ← effTy sig (env ++ e0) a0
      let t1 ← effTy sig (env ++ e1) a1
      let answer ← EffTy.joinAnswer t0.answer t1.answer
      some ⟨answer, t0.error.join t1.error, t0.requires.union t1.requires⟩
    | .matchCause body onValue onCause => do
      let b ← effTy sig env body
      let v ← effTy sig (env ++ [b.answer]) onValue
      let c ← effTy sig (env ++ [.causeOf b.error]) onCause
      let answer ← EffTy.joinAnswer v.answer c.answer
      some ⟨answer, v.error.join c.error, (b.requires.union v.requires).union c.requires⟩
    | .onExit body finalizer => do
      let b ← effTy sig env body
      let f ← effTy sig (env ++ [.exitOf b.answer b.error]) finalizer
      some ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩
    | .exit body => do
      let b ← effTy sig env body
      some ⟨.exitOf b.answer b.error, .never, b.requires⟩
    | .uninterruptible body => effTy sig env body
    | .interruptible body => effTy sig env body
    -- `iterate`: the cursor is typed at its annotation, or at `initial`'s type when there is
    -- none (DI-91); `initial` and `step` are under it by subsumption (both sides normalized, as
    -- the annotation is stored raw), so the body, the test and the result see one cursor type
    -- across every round. The answer is `result`'s.
    | .iterate cursorTy initial test step result body => do
      let c0 ← termTy sig env initial
      let cursor := cursorTy.getD c0
      let t ← termTy sig (env ++ [cursor]) test
      let b ← effTy sig (env ++ [cursor]) body
      let c1 ← termTy sig (env ++ [cursor, b.answer]) step
      let d ← termTy sig (env ++ [cursor]) result
      if t = .bool ∧ Ty.sub c0.normalize cursor.normalize = true
          ∧ Ty.sub c1.normalize cursor.normalize = true
        then some ⟨d, b.error, b.requires⟩ else none
    | .yieldNow _ => some (EffTy.pure .unit)
    -- Same domain check as `perform` (DI-54). The kind check is not a domain check: an
    -- out-of-range external index has the placeholder's `kind = .program`, but a *supplied*
    -- table can make an in-range row async while the index is still outside the domain of a
    -- different signature.
    | .awaitFiber fiber mode => do
      let t ← termTy sig env fiber
      let (value, error) ← fiberTy t
      match mode with
      | .joinEffect => some ⟨value, error, Requirement.empty⟩
      | .awaitValue => some (EffTy.pure (.exitOf value error))
    | .withFiber action => actionTy sig env action
    -- DI-63: Effect.scoped excludes only Scope (vendor/effect-4.0.0-rc.112/src/Effect.ts:12815-12817).
    | .scoped body => (effTy sig env body).map fun t =>
        { t with requires := bodyRequires sig t }
    | .acquireRelease acquire release => do
      let a ← effTy sig env acquire
      let r ← effTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release
      some ⟨a.answer, a.error, (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩
    -- `Effect.provide(self, layer)`: `Effect<A, E | E2, RIn | Exclude<R, ROut>>`
    -- (`internal/layer.ts:8-14`) — the layer's requirements join, what it provides is
    -- discharged from the body's
    | .provideLayer layer _ body => do
      let l ← layerTy sig layer
      let b ← effTy sig env body
      some ⟨b.answer, b.error.join l.error, Row.union l.requires (Row.diff b.requires l.out)⟩
    -- `Effect.service(key)`: `Effect<S, never, I>` (`internal/effect.ts:2059`), the carrier
    -- from the service table
    | .service key => (sig.serviceTy key).map fun ty => ⟨ty, .never, Requirement.single key⟩
    -- `Effect.provideService(self, key, value)`: `Effect<A, E, Exclude<R, I>>` (`:2202`), the
    -- value admitted at a subtype of the key's carrier (DI-15, subsumption at service
    -- provision)
    | .provideService key value body => do
      let ty ← sig.serviceTy key
      let v ← termTy sig env value
      let b ← effTy sig env body
      if Ty.sub v.normalize ty.normalize = true then
        some ⟨b.answer, b.error, Row.diff b.requires (Requirement.single key)⟩
      else none

  /-- The signature of a layer term, structural; `none` refuses an ill-typed body or a literal
  outside the value alphabet. The rules are the four `LayerTy` operations and the leaf rules:
  `Layer.succeed` provides its key and requires nothing (`Layer.ts:1074`); `Layer.effect`
  provides its key with the body's error and the body's scope-free requirements
  (`:1427`, `:1438`); `Layer.effectDiscard` provides nothing (`:1512`); `fresh` keeps the
  signature (`:3850`); `orDie` clears the error (`:3327`). A body is closed: it is typed at
  the empty environment. -/
  def layerTy (sig : Signature Op) : LayerTerm Op → Option LayerTy
    | .succeed key value =>
      (litVal value).map fun _ => ⟨Requirement.single key, .never, Requirement.empty⟩
    | .effect key body =>
      (effTy sig [] body).map fun t => ⟨Requirement.single key, t.error, bodyRequires sig t⟩
    | .effectDiscard body =>
      (effTy sig [] body).map fun t => ⟨Requirement.empty, t.error, bodyRequires sig t⟩
    | .provide self that => do
      let s ← layerTy sig self
      let t ← layerTy sig that
      some (s.provide t)
    | .provideMerge self that => do
      let s ← layerTy sig self
      let t ← layerTy sig that
      some (s.provideMerge t)
    | .merge left right => do
      let a ← layerTy sig left
      let b ← layerTy sig right
      some (a.merge b)
    | .fresh inner => layerTy sig inner
    | .orDie inner => (layerTy sig inner).map LayerTy.orDie
    -- a reference is typed by the whole program (`typeOfProgram` expands it to its target);
    -- structurally it is nothing
    | .ref _ => none
    -- the layers' signatures, then the nonempty merge (`Layer.ts:1652`, at least one): the
    -- list sort's result is the list of its members' results, the combining is this rule's
    | .mergeAll layers => (layersTy sig layers).bind LayerTy.mergeNonempty

  /-- The signatures of a list of layer terms, in order; `none` when any is refused. -/
  def layersTy (sig : Signature Op) : LayerTerms Op → Option (List LayerTy)
    | .nil => some []
    | .cons head tail => do
      let h ← layerTy sig head
      let t ← layersTy sig tail
      some (h :: t)

  /-- The type of one statement (`StmtTy`): `const aN = yield* e` and `yield* e` contribute
  the effect's error and requirements and bind its answer or nothing; a branch or a loop
  contributes its body's generator state (a loop's body under `inLoop`); `return` is the
  answer, terminal; `break` is nothing, admitted under `inLoop`. -/
  def stmtTy (sig : Signature Op) (env : TyEnv) (inLoop : Bool) : Stmt Op → Option StmtTy
    | .bindYield effect => do
      let t ← effTy sig env effect
      some (.step ⟨none, t.error, t.requires⟩ [t.answer])
    | .yieldDiscard effect => do
      let t ← effTy sig env effect
      some (.step ⟨none, t.error, t.requires⟩ [])
    | .ret value => (termTy sig env value).map StmtTy.ret
    | .ifElse test thenB elseB => do
      let t ← termTy sig env test
      if t = .bool then
        let a ← stmtsTy sig env inLoop false thenB
        let b ← stmtsTy sig env inLoop false elseB
        let ab ← a.merge b
        some (.step ab [])
      else none
    | .whileTrue body => do
      let b ← stmtsTy sig env true false body
      some (.step b [])
    | .breakLoop => if inLoop then some .pass else none

  /-- A generator body, statement by statement; `inLoop` admits `break`, `afterRet` refuses
  every statement (a `return` ends the body, and sets it for its tail). A step's state merges
  with the tail's, typed under the step's bindings; a `return` is the answer once the tail is
  empty; `break` contributes nothing. -/
  def stmtsTy (sig : Signature Op) (env : TyEnv) (inLoop afterRet : Bool) :
      Stmts Op → Option GenTy
    | .nil => some ⟨none, .never, Requirement.empty⟩
    | .cons head rest =>
      if afterRet then none else do
        let s ← stmtTy sig env inLoop head
        match s with
        | .step g binds => do
          let r ← stmtsTy sig (env ++ binds) inLoop false rest
          g.merge r
        | .ret t => do
          let _ ← stmtsTy sig env inLoop true rest
          some ⟨some t, .never, Requirement.empty⟩
        | .pass => stmtsTy sig env inLoop false rest

  /-- Race entrants: every entrant's answer joins, the errors union. -/
  def effsTy (sig : Signature Op) (env : TyEnv) : Effs Op → Option EffTy
    | .nil => some ⟨.never, .never, Requirement.empty⟩
    | .cons head tail => do
      let h ← effTy sig env head
      let t ← effsTy sig env tail
      let answer ← EffTy.joinAnswer h.answer t.answer
      some ⟨answer, h.error.join t.error, h.requires.union t.requires⟩

  /-- The fiber actions. -/
  def actionTy (sig : Signature Op) (env : TyEnv) : ActionTerm Op → Option EffTy
    | .fork program _ => do
      let p ← effTy sig env program
      some ⟨.fiberOf p.answer p.error, .never, p.requires⟩
    | .forkIn program _ scope => do
      let p ← effTy sig env program
      let s ← termTy sig env scope
      if s = Ty.scope then some ⟨.fiberOf p.answer p.error, .never, p.requires⟩ else none
    | .forkScoped program _ => do
      let p ← effTy sig env program
      some ⟨.fiberOf p.answer p.error, .never, p.requires.union (Requirement.single sig.scopeKey)⟩
    | .runIn target scope => do
      let t ← termTy sig env target
      let _ ← fiberTy t
      let s ← termTy sig env scope
      if s = Ty.scope then some (EffTy.pure .unit) else none
    | .interrupt target => do
      let t ← termTy sig env target
      let _ ← fiberTy t
      some (EffTy.pure .unit)
    | .interruptScoped target => do
      let t ← termTy sig env target
      let _ ← fiberTy t
      some (EffTy.pure .unit)
    | .interruptAll targets interruptor => do
      let ts ← termTy sig env targets
      match ts with
      | .list inner =>
        let _ ← fiberTy inner
        match interruptor with
        | none => some (EffTy.pure .unit)
        | some who => do
          let w ← termTy sig env who
          if w = .nat then some (EffTy.pure .unit) else none
      | _ => none
    | .awaitAll targets => do
      let ts ← termTy sig env targets
      match ts with
      | .list inner =>
        let (value, error) ← fiberTy inner
        some (EffTy.pure (.list (.exitOf value error)))
      | _ => none
    | .awaitAllFailFast targets => do
      let ts ← termTy sig env targets
      match ts with
      | .list inner =>
        let (value, error) ← fiberTy inner
        some (EffTy.pure (.list (.exitOf value error)))
      | _ => none
    | .snapshotChildren =>
      some (EffTy.pure (.list (.fiberOf (.handle "unknown") (.handle "unknown"))))
    | .awaitNewChildren snapshot => do
      let s ← termTy sig env snapshot
      if s = .list (.fiberOf (.handle "unknown") (.handle "unknown")) then some (EffTy.pure .unit)
      else none
    | .raceAll entrants => effsTy sig env entrants
    | .setContext context => do
      let c ← termTy sig env context
      if c = Ty.context then some (EffTy.pure .unit) else none
    | .getContext => some (EffTy.pure Ty.context)
    | .getId => some (EffTy.pure .nat)
    | .closeScope scope exit => do
      let s ← termTy sig env scope
      let e ← termTy sig env exit
      match e with
      | .exitOf _ _ => if s = Ty.scope then some (EffTy.pure .unit) else none
      | _ => none
end

end Checker

end Effect4.Program
