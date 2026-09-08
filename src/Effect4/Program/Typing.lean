import Effect4.Program.Eff
import Effect4.Machine.Context

/-!
# Syntax.Typing — `typeOf` (lane A1, §2.2 of the AST relation plan)

A type assignment `typeOf : Eff Op → Option EffTy` over a typing environment (one `Ty` per
positional variable): the answer type `A`, the error type `E` (a canonical union, `Ty.join`),
and the requirement row `R` (`Effect4.Machine.Requirement`, the keys the program performs
against). Well-typed means `typeOf e = some _`. The two receipts on it — progress (a
well-typed program's compile never reaches `PrimInterp.notImplemented`) and the host type
receipt (the printed module type-checks at the pin) — belong to lanes A3 and A2.

The typing is structural and total; refusals are `none`. Where rc.112 admits a union of
answer types (`catchCause`, `matchCauseEffect`, `raceAll`, a branch) the answers must join
(`EffTy.joinAnswer`): equal, or one of them `never`.
-/

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)

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
  /-- The service table (the join, 2026-09-07): the carrier type of the service a key names,
  `none` for a key the signature does not type. `Effect.service(key)` answers it and
  `Effect.provideService(self, key, value)` types `value` at it; a layer's own leaves are
  typed by their bodies (`layerTy`), not by the table. -/
  serviceTy : ServiceKey → Option Ty

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

/-! ## The layer signature (the join, 2026-09-07; before it `Program/Provision.lean`)

`Layer<ROut, E, RIn>` (`Layer.ts:54`) as three rows: what the layer provides, its error type,
and what it requires. `LayerTy`'s four operations are the requirement algebra of the four
combinators; their laws stay in `Program/Provision.lean`, restated on the term now inside
`Eff`. -/

/-- A literal as a value of the machine's alphabet; strings are not layer values
(`PROV-FB-STRING-VALUE`, `Test/Program/ProvisionContract.lean`). -/
def litVal : Lit → Option Effect4.Machine.Env.Val
  | .unit => some .unit
  | .nat n => some (.nat n)
  | .bool b => some (.bool b)
  | .str _ => none

/-- `Layer<ROut, E, RIn>` (`Layer.ts:54`). -/
structure LayerTy where
  out : Requirement
  error : Ty
  requires : Requirement
deriving DecidableEq

namespace LayerTy

/-- `self.pipe(Layer.provide(that))` (`Layer.ts:2258`): `Layer<ROut, E | E2,
RIn2 | Exclude<RIn, ROut2>>` — the dependency discharges what it provides. -/
def provide (self that : LayerTy) : LayerTy :=
  ⟨self.out, self.error.join that.error,
    Row.union (Row.diff self.requires that.out) that.requires⟩

/-- `self.pipe(Layer.provideMerge(that))` (`Layer.ts:2704`): the same requirement column, both
outputs kept. -/
def provideMerge (self that : LayerTy) : LayerTy :=
  ⟨Row.union self.out that.out, self.error.join that.error,
    Row.union (Row.diff self.requires that.out) that.requires⟩

/-- `Layer.merge(a, b)` (`Layer.ts:1850`): siblings share nothing — the outputs and the
requirements both union. -/
def merge (a b : LayerTy) : LayerTy :=
  ⟨Row.union a.out b.out, a.error.join b.error, Row.union a.requires b.requires⟩

/-- `Layer.orDie(l)` (`Layer.ts:3327`): the error column becomes `never`. -/
def orDie (l : LayerTy) : LayerTy := ⟨l.out, .never, l.requires⟩

/-- A layer is closed when it requires nothing: `Layer<_, _, never>`. -/
def Closed (l : LayerTy) : Prop := l.requires = Requirement.empty

instance (l : LayerTy) : Decidable (Closed l) := by unfold Closed; infer_instance

end LayerTy

/-- The scope-free requirement row of a layer body: `Exclude<R, Scope.Scope>` (`Layer.ts:1438`,
`:1512`): the layer's own scope answers the body's `Scope` requirement. -/
def bodyRequires (sig : Signature Op) (t : EffTy) : Requirement :=
  Row.diff t.requires (Requirement.single sig.scopeKey)

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
    -- value typed at the key's carrier
    | .provideService key value body => do
      let ty ← sig.serviceTy key
      let v ← termTy sig env value
      let b ← effTy sig env body
      if v = ty then some ⟨b.answer, b.error, Row.diff b.requires (Requirement.single key)⟩
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

/-! ### The row plane sees no duplicate (the join review, 2026-09-08) -/

/-- Discharging a key twice discharges it once. -/
theorem Row.diff_single_twice (r : Requirement) (key : ServiceKey) :
    Row.diff (Row.diff r (Requirement.single key)) (Requirement.single key) =
      Row.diff r (Requirement.single key) := by
  rw [← Row.diff_union_right, Row.union_idem]

/-- Requiring a key twice requires it once. -/
theorem Requirement.union_single_self (key : ServiceKey) :
    Row.union (Requirement.single key) (Requirement.single key) = Requirement.single key :=
  Row.union_idem _

/-- Nested `provideService` at one key types exactly as the inner one does: the outer provision
discharges a key the inner already discharged, and the row plane sees no difference. -/
theorem effTy_provideService_twice (sig : Signature Op) (env : TyEnv) (key : ServiceKey)
    (near far : Term) (body : Eff Op) {ty : Ty} (hty : sig.serviceTy key = some ty)
    (hnear : termTy sig env near = some ty) {inner : EffTy}
    (hinner : effTy sig env (.provideService key far body) = some inner) :
    effTy sig env (.provideService key near (.provideService key far body)) = some inner := by
  have hreq : Row.diff inner.requires (Requirement.single key) = inner.requires := by
    simp only [effTy, hty, Option.bind_eq_bind, Option.bind_some] at hinner
    cases hfar : termTy sig env far with
    | none => rw [hfar] at hinner; cases hinner
    | some v =>
      rw [hfar, Option.bind_some] at hinner
      cases hbody : effTy sig env body with
      | none => rw [hbody] at hinner; cases hinner
      | some b =>
        rw [hbody, Option.bind_some] at hinner
        split at hinner
        · cases Option.some.inj hinner
          exact Row.diff_single_twice _ _
        · cases hinner
  generalize hI : Eff.provideService key far body = I at hinner ⊢
  simp only [effTy, hty, Option.bind_eq_bind, Option.bind_some, hnear, hinner, if_true]
  rw [hreq]

/-- A layer is well-typed when `layerTy` answers. -/
def WellTypedLayer (sig : Signature Op) (l : LayerTerm Op) : Prop :=
  (layerTy sig l).isSome = true

instance (sig : Signature Op) (l : LayerTerm Op) : Decidable (WellTypedLayer sig l) := by
  unfold WellTypedLayer; infer_instance

/-- A program is well-typed when `typeOf` answers. -/
def WellTyped (sig : Signature Op) (program : Eff Op) : Prop := (typeOf sig program).isSome

instance (sig : Signature Op) (program : Eff Op) : Decidable (WellTyped sig program) := by
  unfold WellTyped; infer_instance

end Effect4.Program
