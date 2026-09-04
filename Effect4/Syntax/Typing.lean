import Effect4.Syntax.Eff
import Effect4.Deep.Context

/-!
# Syntax.Typing — `typeOf` (lane A1, §2.2 of the AST relation plan)

A type assignment `typeOf : Eff Op → Option EffTy` over a typing environment (one `Ty` per
positional variable): the answer type `A`, the error type `E` (a canonical union, `Ty.join`),
and the requirement row `R` (`Effect4.Deep.Requirement`, the keys the program performs
against). Well-typed means `typeOf e = some _`. The two receipts on it — progress (a
well-typed program's compile never reaches `PrimInterp.notImplemented`) and the host type
receipt (the printed module type-checks at the pin) — belong to lanes A3 and A2.

The typing is structural and total; refusals are `none`. Where rc.112 admits a union of
answer types (`catchCause`, `matchCauseEffect`, `raceAll`, a branch) the answers must join
(`EffTy.joinAnswer`): equal, or one of them `never`.
-/

namespace Effect4.Syntax

open Effect4 (ServiceKey)
open Effect4.Deep.Env (Requirement)

abbrev TyEnv := List Ty

/-- `Effect<A, E, R>`. -/
structure EffTy where
  answer : Ty
  error : Ty
  requires : Requirement
deriving DecidableEq

namespace EffTy

def pure (answer : Ty) : EffTy := ⟨answer, .never, Requirement.empty⟩

/-- Two answer types agree when equal or when one is `never`. -/
def joinAnswer (a b : Ty) : Option Ty :=
  if a = b then some a
  else if a.isNever then some b
  else if b.isNever then some a
  else none

end EffTy

/-- What typing consults beside the program: the rows of the alphabet, the pure atoms
(parameter types and answer), and the `Scope` service key of this signature. -/
structure Signature (Op : Type) where
  rowOf : Op → Row
  /-- The answer type of a pure atom applied to arguments of the given types; `none` refuses
  the application. Atoms are typed by their arguments so a polymorphic atom (`pair`) is one
  name. -/
  atomOf : String → List Ty → Option Ty
  scopeKey : ServiceKey

variable {Op : Type}

mutual
  /-- The type of a pure term. -/
  def termTy (sig : Signature Op) (env : TyEnv) : Term → Option Ty
    | .var index => env[index]?
    | .lit value => some value.ty
    | .app atom args => do
      let tys ← termsTy sig env args
      sig.atomOf atom tys
  def termsTy (sig : Signature Op) (env : TyEnv) : Terms → Option (List Ty)
    | .nil => some []
    | .cons head tail => do
      let t ← termTy sig env head
      let rest ← termsTy sig env tail
      some (t :: rest)
end

/-- The error type a cause carries: its `fail` reasons; defects and interrupts contribute
none (`Cause.die` and `Cause.interrupt` are outside `E`). -/
def causeTy (sig : Signature Op) (env : TyEnv) : CauseTerm → Option Ty
  | .fail error => termTy sig env error
  | .die defect => (termTy sig env defect).map fun _ => .never
  | .interrupt none => some .never
  | .interrupt (some who) => do
    let t ← termTy sig env who
    if t = .nat then some .never else none
  | .both left right => do
    let l ← causeTy sig env left
    let r ← causeTy sig env right
    some (l.join r)

/-- The typing state of a generator body: the answer its `return`s agree on (none before
the first), the errors and requirements so far. -/
structure GenTy where
  answer : Option Ty
  error : Ty
  requires : Requirement

namespace GenTy

def joinAnswer : Option Ty → Option Ty → Option (Option Ty)
  | none, b => some b
  | a, none => some a
  | some a, some b => (EffTy.joinAnswer a b).map some

def merge (a b : GenTy) : Option GenTy := do
  let answer ← joinAnswer a.answer b.answer
  some ⟨answer, a.error.join b.error, a.requires.union b.requires⟩

end GenTy

/-- The fiber handle a term must denote. -/
def fiberTy : Ty → Option (Ty × Ty)
  | .fiberOf value error => some (value, error)
  | _ => none

mutual
  /-- `typeOf` over the environment, structural in the program. -/
  def effTy (sig : Signature Op) (env : TyEnv) : Eff Op → Option EffTy
    | .succeed value => (termTy sig env value).map EffTy.pure
    | .fail error => (termTy sig env error).map fun e => ⟨.never, e, Requirement.empty⟩
    | .failCause cause => (causeTy sig env cause).map fun e => ⟨.never, e, Requirement.empty⟩
    | .yieldError error => (termTy sig env error).map fun e => ⟨.never, e, Requirement.empty⟩
    | .sync thunk => (termTy sig env thunk).map EffTy.pure
    | .suspend body => effTy sig env body
    | .perform op request => do
      let row := sig.rowOf op
      let r ← termTy sig env request
      if r = row.request then some ⟨row.answer, row.error, Requirement.ofList row.requires⟩
      else none
    | .bind first rest => do
      let f ← effTy sig env first
      let r ← effTy sig (env ++ [f.answer]) rest
      some ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩
    | .gen body => do
      let g ← stmtsTy sig env false body
      some ⟨g.answer.getD .unit, g.error, g.requires⟩
    | .catchCause body handler => do
      let b ← effTy sig env body
      let h ← effTy sig (env ++ [.causeOf b.error]) handler
      let answer ← EffTy.joinAnswer b.answer h.answer
      some ⟨answer, h.error, b.requires.union h.requires⟩
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
    | .branch test thenB elseB => do
      let t ← termTy sig env test
      if t = .bool then
        let a ← effTy sig env thenB
        let b ← effTy sig env elseB
        let answer ← EffTy.joinAnswer a.answer b.answer
        some ⟨answer, a.error.join b.error, a.requires.union b.requires⟩
      else none
    | .whileLoop initial test step body => do
      let cursor ← termTy sig env initial
      let t ← termTy sig (env ++ [cursor]) test
      let b ← effTy sig (env ++ [cursor]) body
      let s ← termTy sig (env ++ [cursor, b.answer]) step
      if t = .bool ∧ s = cursor then some ⟨.unit, b.error, b.requires⟩ else none
    | .yieldNow _ => some (EffTy.pure .unit)
    | .callback register request => do
      let row := sig.rowOf register
      let r ← termTy sig env request
      if row.kind = .async ∧ r = row.request then
        some ⟨row.answer, row.error, Requirement.ofList row.requires⟩
      else none
    | .awaitFiber fiber mode => do
      let t ← termTy sig env fiber
      let (value, error) ← fiberTy t
      match mode with
      | .joinEffect => some ⟨value, error, Requirement.empty⟩
      | .awaitValue => some (EffTy.pure (.exitOf value error))
    | .withFiber action => actionTy sig env action
    | .scoped body => effTy sig env body
    | .acquireRelease acquire release => do
      let a ← effTy sig env acquire
      let r ← effTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release
      some ⟨a.answer, a.error, (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩
    | .choose _ left right => do
      let l ← effTy sig env left
      let r ← effTy sig env right
      let answer ← EffTy.joinAnswer l.answer r.answer
      some ⟨answer, l.error.join r.error, l.requires.union r.requires⟩

  /-- A generator body, statement by statement; `inLoop` admits `break`. A `return` ends
  the body: statements after it are refused. -/
  def stmtsTy (sig : Signature Op) (env : TyEnv) (inLoop : Bool) : Stmts Op → Option GenTy
    | .nil => some ⟨none, .never, Requirement.empty⟩
    | .cons (.bindYield effect) rest => do
      let t ← effTy sig env effect
      let r ← stmtsTy sig (env ++ [t.answer]) inLoop rest
      some ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩
    | .cons (.yieldDiscard effect) rest => do
      let t ← effTy sig env effect
      let r ← stmtsTy sig env inLoop rest
      some ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩
    | .cons (.ret value) rest =>
      match rest with
      | .nil => (termTy sig env value).map fun t => ⟨some t, .never, Requirement.empty⟩
      | .cons _ _ => none
    | .cons (.ifElse test thenB elseB) rest => do
      let t ← termTy sig env test
      if t = .bool then
        let a ← stmtsTy sig env inLoop thenB
        let b ← stmtsTy sig env inLoop elseB
        let r ← stmtsTy sig env inLoop rest
        let ab ← a.merge b
        ab.merge r
      else none
    | .cons (.whileTrue body) rest => do
      let b ← stmtsTy sig env true body
      let r ← stmtsTy sig env inLoop rest
      b.merge r
    | .cons .breakLoop rest =>
      if inLoop then stmtsTy sig env inLoop rest else none

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

/-- `typeOf` at the empty environment. -/
def typeOf (sig : Signature Op) (program : Eff Op) : Option EffTy := effTy sig [] program

/-- A program is well-typed when `typeOf` answers. -/
def WellTyped (sig : Signature Op) (program : Eff Op) : Prop := (typeOf sig program).isSome

instance (sig : Signature Op) (program : Eff Op) : Decidable (WellTyped sig program) := by
  unfold WellTyped; infer_instance

end Effect4.Syntax
