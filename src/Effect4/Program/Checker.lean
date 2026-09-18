import Effect4.Program.Typing.Blame

/-!
# Program.Checker — typing with located refusal, as one fold of the program

The located-refusal arrow of the ontology (`docs/core/ontology.md` §5, K4) as one function:
`check sig env p e : Except TypeRefusal EffTy` is the program's type, or the refusal at the path
that earns it. `Program/Typing.lean`'s `effTy` is its success projection and
`Typing/Blame.lean`'s `explainEff` its refusal, rule for rule — the agreement theorems in
`Typing/Agreement.lean` say so (`check_eq`, both projections per sort), and
`explain = none ↔ effTy.isSome` is then the shape of `Except`. This is the second file beside
both; `fold_of` reads its algebra (`Program/Folds/Checker.lean`). Nothing in the two hand
blocks changed.

Two shapes differ from the hand blocks so that every member is a fold of its sort
(`docs/core/traversal-census.md` §7.5):

- **A statement has a type** (`StmtTy`): a *step* with the state it contributes and the
  variables it binds, a *return* with its answer's check (evaluated once the tail is known to
  be empty, the order `explainStmts` blames in), or *nothing* (`break`). `checkStmts` sequences
  by the statement's type alone; "no statement after a return" is the mode flag `afterRet`,
  set by a return for its tail and carrying the return's path, as `inLoop` is set by a loop.
- **The layers of a `mergeAll` are a list of signatures**; the nonempty merge and the
  `mergeAllEmpty` refusal are `mergeAll`'s own rule (`LayerTy.mergeNonempty`).

The answer join never refuses (`EffTy.joinAnswer_eq`), so the fold joins with `Ty.join` and
merges generator states with `GenTy.mergeT`; the hand blocks' `Option` there is history.
-/

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)

/-- The type of one statement of a generator body. -/
inductive StmtTy where
  /-- A statement that contributes a state (its error and requirements, and for a branch or a
  loop its body's answer) and binds `binds` for the statements after it. -/
  | step (state : GenTy) (binds : List Ty)
  /-- `return`: the body's answer, checked once the tail is known to be empty; terminal. -/
  | ret (answer : Except TypeRefusal Ty)
  /-- `break`: nothing. -/
  | pass

namespace GenTy

/-- `joinAnswer` without the refusal it never makes. -/
def joinAnswerT : Option Ty → Option Ty → Option Ty
  | none, b => b
  | a, none => a
  | some a, some b => some (Ty.join a b)

theorem joinAnswer_eq (a b : Option Ty) : joinAnswer a b = some (joinAnswerT a b) := by
  cases a <;> cases b <;> rfl

/-- `merge` without the refusal it never makes. -/
def mergeT (a b : GenTy) : GenTy :=
  ⟨joinAnswerT a.answer b.answer, a.error.join b.error, a.requires.union b.requires⟩

theorem merge_eq (a b : GenTy) : merge a b = some (mergeT a b) := by
  unfold merge mergeT
  rw [joinAnswer_eq]
  rfl

end GenTy

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

/-- A term's type at a node, or its refusal there (`termRefusal`). -/
def term? (sig : Signature Op) (env : TyEnv) (p : List Nat) (t : Term) : Except TypeRefusal Ty :=
  match termTy sig env t with
  | none => .error ⟨p, .term t⟩
  | some ty => .ok ty

/-- The refusal of a check, when it refuses. -/
def refusal {α : Type} : Except TypeRefusal α → Option TypeRefusal
  | .error r => some r
  | .ok _ => none

mutual
  /-- `effTy` and `explainEff` as one: the type, or the located refusal. -/
  def check (sig : Signature Op) (env : TyEnv) (p : List Nat) : Eff Op → Except TypeRefusal EffTy
    | .succeed value => do
      let t ← term? sig env p value
      pure (EffTy.pure t)
    | .fail error => do
      let e ← term? sig env p error
      if admittedErrTy e then pure ⟨.never, e, Requirement.empty⟩
      else throw ⟨p, .errorNotAdmitted e⟩
    | .failCause cause =>
      match causeTy sig env cause with
      | none => throw ⟨p, .cause cause⟩
      | some e => pure ⟨.never, e, Requirement.empty⟩
    | .sync thunk => do
      let t ← term? sig env p thunk
      pure (EffTy.pure t)
    | .suspend body => check sig env (p ++ [0]) body
    | .perform op request => do
      let r ← term? sig env p request
      let row := sig.rowOf op
      if sig.dom op = false then throw ⟨p, .outsideDomain row.name⟩
      else if Ty.sub r.normalize row.request.normalize then
        pure ⟨row.answer, row.error, Requirement.ofList row.requires⟩
      else throw ⟨p, .requestNotSubtype row.name r row.request⟩
    | .bind first rest => do
      let f ← check sig env (p ++ [0]) first
      let r ← check sig (env ++ [f.answer]) (p ++ [1]) rest
      pure ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩
    | .gen body => do
      let g ← checkStmts sig env false none (p ++ [0]) body
      pure ⟨g.answer.getD .unit, g.error, g.requires⟩
    | .catchCause body handler => do
      let b ← check sig env (p ++ [0]) body
      let h ← check sig (env ++ [.causeOf b.error]) (p ++ [1]) handler
      pure ⟨Ty.join b.answer h.answer, h.error, b.requires.union h.requires⟩
    | .catchIf test body handler => do
      let b ← check sig env (p ++ [0]) body
      let predicate ← term? sig (env ++ [b.error]) p test
      if predicate = .bool then
        let h ← check sig (env ++ [b.error]) (p ++ [1]) handler
        pure ⟨Ty.join b.answer h.answer, catchIfError test env.length b.error h.error,
          b.requires.union h.requires⟩
      else throw ⟨p, .predicateNotBool predicate⟩
    | .select s d a0 a1 => do
      let t ← term? sig env p s
      match d.arms t with
      | none => throw ⟨p, selectRefusal d t⟩
      | some (e0, e1) => do
        let t0 ← check sig (env ++ e0) (p ++ [0]) a0
        let t1 ← check sig (env ++ e1) (p ++ [1]) a1
        pure ⟨Ty.join t0.answer t1.answer, t0.error.join t1.error, t0.requires.union t1.requires⟩
    | .matchCause body onValue onCause => do
      let b ← check sig env (p ++ [0]) body
      let v ← check sig (env ++ [b.answer]) (p ++ [1]) onValue
      let c ← check sig (env ++ [.causeOf b.error]) (p ++ [2]) onCause
      pure ⟨Ty.join v.answer c.answer, v.error.join c.error,
        (b.requires.union v.requires).union c.requires⟩
    | .onExit body finalizer => do
      let b ← check sig env (p ++ [0]) body
      let f ← check sig (env ++ [.exitOf b.answer b.error]) (p ++ [1]) finalizer
      pure ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩
    | .exit body => do
      let b ← check sig env (p ++ [0]) body
      pure ⟨.exitOf b.answer b.error, .never, b.requires⟩
    | .uninterruptible body => check sig env (p ++ [0]) body
    | .interruptible body => check sig env (p ++ [0]) body
    | .iterate cursorTy initial test step result body => do
      let c0 ← term? sig env p initial
      let cursor := cursorTy.getD c0
      let t ← term? sig (env ++ [cursor]) p test
      let b ← check sig (env ++ [cursor]) (p ++ [0]) body
      let c1 ← term? sig (env ++ [cursor, b.answer]) p step
      let d ← term? sig (env ++ [cursor]) p result
      if t = .bool ∧ Ty.sub c0.normalize cursor.normalize = true
          ∧ Ty.sub c1.normalize cursor.normalize = true then pure ⟨d, b.error, b.requires⟩
      else if ¬ t = .bool then throw ⟨p, .predicateNotBool t⟩
      else if Ty.sub c0.normalize cursor.normalize = true then throw ⟨p, .stepNotCursor c1 cursor⟩
      else throw ⟨p, .initialNotCursor c0 cursor⟩
    | .yieldNow _ => pure (EffTy.pure .unit)
    | .awaitFiber fiber mode => do
      let t ← term? sig env p fiber
      match fiberTy t with
      | none => throw ⟨p, .notFiber t⟩
      | some (value, error) =>
        match mode with
        | .joinEffect => pure ⟨value, error, Requirement.empty⟩
        | .awaitValue => pure (EffTy.pure (.exitOf value error))
    | .withFiber action => checkAction sig env (p ++ [0]) action
    | .scoped body => do
      let t ← check sig env (p ++ [0]) body
      pure { t with requires := bodyRequires sig t }
    | .acquireRelease acquire release => do
      let a ← check sig env (p ++ [0]) acquire
      let r ← check sig (env ++ [a.answer, .exitOf a.answer a.error]) (p ++ [1]) release
      pure ⟨a.answer, a.error,
        (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩
    | .provideLayer layer _ body => do
      let l ← checkLayer sig (p ++ [0]) layer
      let b ← check sig env (p ++ [1]) body
      pure ⟨b.answer, b.error.join l.error, Row.union l.requires (Row.diff b.requires l.out)⟩
    | .service key =>
      match sig.serviceTy key with
      | none => throw ⟨p, .serviceUnknown key⟩
      | some ty => pure ⟨ty, .never, Requirement.single key⟩
    | .provideService key value body =>
      match sig.serviceTy key with
      | none => throw ⟨p, .serviceUnknown key⟩
      | some ty => do
        let v ← term? sig env p value
        let b ← check sig env (p ++ [0]) body
        if Ty.sub v.normalize ty.normalize then
          pure ⟨b.answer, b.error, Row.diff b.requires (Requirement.single key)⟩
        else throw ⟨p, .valueNotSubtype key v ty⟩

  /-- `layerTy` and `explainLayer` as one. -/
  def checkLayer (sig : Signature Op) (p : List Nat) : LayerTerm Op → Except TypeRefusal LayerTy
    | .succeed key value =>
      match litVal value with
      | none => throw ⟨p, .literalOutsideAlphabet value⟩
      | some _ => pure ⟨Requirement.single key, .never, Requirement.empty⟩
    | .effect key body => do
      let t ← check sig [] (p ++ [0]) body
      pure ⟨Requirement.single key, t.error, bodyRequires sig t⟩
    | .effectDiscard body => do
      let t ← check sig [] (p ++ [0]) body
      pure ⟨Requirement.empty, t.error, bodyRequires sig t⟩
    | .provide self that => do
      let s ← checkLayer sig (p ++ [0]) self
      let t ← checkLayer sig (p ++ [1]) that
      pure (s.provide t)
    | .provideMerge self that => do
      let s ← checkLayer sig (p ++ [0]) self
      let t ← checkLayer sig (p ++ [1]) that
      pure (s.provideMerge t)
    | .merge left right => do
      let a ← checkLayer sig (p ++ [0]) left
      let b ← checkLayer sig (p ++ [1]) right
      pure (a.merge b)
    | .fresh inner => checkLayer sig (p ++ [0]) inner
    | .orDie inner => do
      let l ← checkLayer sig (p ++ [0]) inner
      pure l.orDie
    | .ref target => throw ⟨p, .layerReference target⟩
    -- the layers' signatures, then the nonempty merge (`Layer.ts:1652`, at least one)
    | .mergeAll layers => do
      let ls ← checkLayers sig (p ++ [0]) layers
      match LayerTy.mergeNonempty ls with
      | none => throw ⟨p ++ [0], .mergeAllEmpty⟩
      | some l => pure l

  /-- The signatures of a list of layer terms, in order, or the first refusal. -/
  def checkLayers (sig : Signature Op) (p : List Nat) :
      LayerTerms Op → Except TypeRefusal (List LayerTy)
    | .nil => pure []
    | .cons head tail => do
      let h ← checkLayer sig (p ++ [0]) head
      let t ← checkLayers sig (p ++ [1]) tail
      pure (h :: t)

  /-- The type of one statement (`StmtTy`), or its refusal. -/
  def checkStmt (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat) :
      Stmt Op → Except TypeRefusal StmtTy
    | .bindYield effect => do
      let t ← check sig env (p ++ [0]) effect
      pure (.step ⟨none, t.error, t.requires⟩ [t.answer])
    | .yieldDiscard effect => do
      let t ← check sig env (p ++ [0]) effect
      pure (.step ⟨none, t.error, t.requires⟩ [])
    | .ret value => pure (.ret (term? sig env p value))
    | .ifElse test thenB elseB => do
      let t ← term? sig env p test
      if t = .bool then
        let a ← checkStmts sig env inLoop none (p ++ [0]) thenB
        let b ← checkStmts sig env inLoop none (p ++ [1]) elseB
        pure (.step (a.mergeT b) [])
      else throw ⟨p, .predicateNotBool t⟩
    | .whileTrue body => do
      let b ← checkStmts sig env true none (p ++ [0]) body
      pure (.step b [])
    | .breakLoop => if inLoop then pure .pass else throw ⟨p, .breakOutsideLoop⟩

  /-- A generator body, statement by statement; `inLoop` admits `break`, `afterRet` (the path
  of the return that ended the body) refuses every statement. -/
  def checkStmts (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (afterRet : Option (List Nat))
      (p : List Nat) : Stmts Op → Except TypeRefusal GenTy
    | .nil => pure ⟨none, .never, Requirement.empty⟩
    | .cons head rest =>
      match afterRet with
      | some ret => throw ⟨ret, .returnNotLast⟩
      | none => do
        let s ← checkStmt sig env inLoop (p ++ [0]) head
        match s with
        | .step g binds => do
          let r ← checkStmts sig (env ++ binds) inLoop none (p ++ [1]) rest
          pure (g.mergeT r)
        | .ret answer => do
          let _ ← checkStmts sig env inLoop (some (p ++ [0])) (p ++ [1]) rest
          let t ← answer
          pure ⟨some t, .never, Requirement.empty⟩
        | .pass => checkStmts sig env inLoop none (p ++ [1]) rest

  /-- Race entrants: every entrant's answer joins, the errors union. -/
  def checkEffs (sig : Signature Op) (env : TyEnv) (p : List Nat) : Effs Op → Except TypeRefusal EffTy
    | .nil => pure ⟨.never, .never, Requirement.empty⟩
    | .cons head tail => do
      let h ← check sig env (p ++ [0]) head
      let t ← checkEffs sig env (p ++ [1]) tail
      pure ⟨Ty.join h.answer t.answer, h.error.join t.error, h.requires.union t.requires⟩

  /-- `actionTy` and `explainAction` as one. -/
  def checkAction (sig : Signature Op) (env : TyEnv) (p : List Nat) :
      ActionTerm Op → Except TypeRefusal EffTy
    | .fork program _ => do
      let t ← check sig env (p ++ [0]) program
      pure ⟨.fiberOf t.answer t.error, .never, t.requires⟩
    | .forkIn program _ scope => do
      let t ← check sig env (p ++ [0]) program
      let s ← term? sig env p scope
      if s = Ty.scope then pure ⟨.fiberOf t.answer t.error, .never, t.requires⟩
      else throw ⟨p, .scopeExpected s⟩
    | .forkScoped program _ => do
      let t ← check sig env (p ++ [0]) program
      pure ⟨.fiberOf t.answer t.error, .never,
        t.requires.union (Requirement.single sig.scopeKey)⟩
    | .runIn target scope => do
      let t ← term? sig env p target
      match fiberTy t with
      | none => throw ⟨p, .notFiber t⟩
      | some _ => do
        let s ← term? sig env p scope
        if s = Ty.scope then pure (EffTy.pure .unit) else throw ⟨p, .scopeExpected s⟩
    | .interrupt target => do
      let t ← term? sig env p target
      match fiberTy t with
      | none => throw ⟨p, .notFiber t⟩
      | some _ => pure (EffTy.pure .unit)
    | .interruptScoped target => do
      let t ← term? sig env p target
      match fiberTy t with
      | none => throw ⟨p, .notFiber t⟩
      | some _ => pure (EffTy.pure .unit)
    | .interruptAll targets interruptor => do
      let ts ← term? sig env p targets
      match ts with
      | .list inner =>
        match fiberTy inner with
        | none => throw ⟨p, .notFiber inner⟩
        | some _ =>
          match interruptor with
          | none => pure (EffTy.pure .unit)
          | some who => do
            let w ← term? sig env p who
            if w = .nat then pure (EffTy.pure .unit) else throw ⟨p, .natExpected w⟩
      | _ => throw ⟨p, .listOfFibersExpected ts⟩
    | .awaitAll targets => do
      let ts ← term? sig env p targets
      match ts with
      | .list inner =>
        match fiberTy inner with
        | none => throw ⟨p, .notFiber inner⟩
        | some (value, error) => pure (EffTy.pure (.list (.exitOf value error)))
      | _ => throw ⟨p, .listOfFibersExpected ts⟩
    | .awaitAllFailFast targets => do
      let ts ← term? sig env p targets
      match ts with
      | .list inner =>
        match fiberTy inner with
        | none => throw ⟨p, .notFiber inner⟩
        | some (value, error) => pure (EffTy.pure (.list (.exitOf value error)))
      | _ => throw ⟨p, .listOfFibersExpected ts⟩
    | .snapshotChildren =>
      pure (EffTy.pure (.list (.fiberOf (.handle "unknown") (.handle "unknown"))))
    | .awaitNewChildren snapshot => do
      let s ← term? sig env p snapshot
      if s = .list (.fiberOf (.handle "unknown") (.handle "unknown")) then pure (EffTy.pure .unit)
      else throw ⟨p, .snapshotExpected s⟩
    | .raceAll entrants => checkEffs sig env (p ++ [0]) entrants
    | .setContext context => do
      let c ← term? sig env p context
      if c = Ty.context then pure (EffTy.pure .unit) else throw ⟨p, .contextExpected c⟩
    | .getContext => pure (EffTy.pure Ty.context)
    | .getId => pure (EffTy.pure .nat)
    | .closeScope scope exit => do
      let s ← term? sig env p scope
      let e ← term? sig env p exit
      match e with
      | .exitOf _ _ => if s = Ty.scope then pure (EffTy.pure .unit) else throw ⟨p, .scopeExpected s⟩
      | _ => throw ⟨p, .exitExpected e⟩
end

end Checker

end Effect4.Program
