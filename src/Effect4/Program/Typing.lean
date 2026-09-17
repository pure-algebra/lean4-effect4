import Effect4.Program.Refs
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
answer types (`catchCause`, `matchCauseEffect`, `raceAll`, a branch) the answers join as the
least upper bound (`EffTy.joinAnswer`, the canonical union `Ty.join`; S4c, part 4).

The literal rule (DI-15, `litArgTy`) and subsumption (`Ty.sub` at row requests, service
provision and the arguments of fixed-signature atoms) are part 4 (2026-09-12).
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

/-- Answer joining is the least upper bound (S4c, DI-15 clause (4), part 4 commit 2,
2026-09-12): rc.112's `A_then | A_else`, the canonical union `Ty.join`. It never refuses; the
`Option` stays so that `GenTy.joinAnswer`'s `Option (Option Ty)` keeps a successful absent
generator answer distinct from a refusal. Before this commit it compared normalized answers
and refused two distinct non-`never` answers. -/
def joinAnswer (a b : Ty) : Option Ty := some (Ty.join a b)

theorem joinAnswer_eq (a b : Ty) : joinAnswer a b = some (Ty.join a b) := rfl

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
  /-- The row positions admitted by this signature. -/
  dom : Op → Bool := fun _ => true
  /-- The atoms whose parameters are const-generic (the prelude's `pair<const A, const B>`,
  DI-55): a string literal argument of such an atom keeps its literal type (`litArgTy`, the
  literal rule of DI-15). No atom is const-generic unless the signature says so. -/
  constAtom : String → Bool := fun _ => false

variable {Op : Type}

/-- The literal rule (DI-15, amended 2026-09-11: "mirror TypeScript"). A string literal types
as `string` in general position (`Lit.ty`, the rule `termTy` uses) and keeps its literal type
`lit s` exactly as a direct argument of a const-generic atom (`Signature.constAtom`), which is
TypeScript's `const` type-parameter rule: `pair("A", m)` is `readonly ["A", string]`,
`succeed "x"` stays `string`. Every other literal is its `Lit.ty` in both positions. The rule
is stated once, here; `termsTy` applies it to the direct arguments of an application and
nowhere else. -/
def litArgTy (const : Bool) : Lit → Ty
  | .str s => if const then .lit s else .string
  | .unit => .unit
  | .nat _ => .nat
  | .bool _ => .bool

mutual
  /-- The type of a pure term. An application's arguments are typed under the atom's
  const-generic flag (`Signature.constAtom`), so a string literal argument of `pair` is a
  `lit` and a string literal argument of any other atom is a `string`. -/
  def termTy (sig : Signature Op) (env : TyEnv) : Term → Option Ty
    | .var index => env[index]?
    | .lit value => some value.ty
    | .app atom args => do
      let tys ← termsTy sig env (sig.constAtom atom) args
      sig.atomOf atom tys
  /-- The argument types of an application: a literal argument by the literal rule
  (`litArgTy`, under the atom's const flag), every other argument by `termTy`. -/
  def termsTy (sig : Signature Op) (env : TyEnv) (const : Bool) : Terms → Option (List Ty)
    | .nil => some []
    | .cons (.lit value) tail => do
      let rest ← termsTy sig env const tail
      some (litArgTy const value :: rest)
    | .cons (.var index) tail => do
      let t ← termTy sig env (.var index)
      let rest ← termsTy sig env const tail
      some (t :: rest)
    | .cons (.app atom args) tail => do
      let t ← termTy sig env (.app atom args)
      let rest ← termsTy sig env const tail
      some (t :: rest)
end

/-- The type of one argument of an application: the literal rule for a literal, `termTy` for
a variable or a nested application. `termsTy` is this, argument by argument
(`termsTy_cons`). -/
def argTy (sig : Signature Op) (env : TyEnv) (const : Bool) : Term → Option Ty
  | .lit value => some (litArgTy const value)
  | .var index => termTy sig env (.var index)
  | .app atom args => termTy sig env (.app atom args)

/-- `termsTy` on a cons (`argTy` for the head), as nested `Option.bind`s. -/
theorem termsTy_cons (sig : Signature Op) (env : TyEnv) (const : Bool) (head : Term)
    (tail : Terms) :
    termsTy sig env const (.cons head tail) =
      (argTy sig env const head).bind fun t =>
        (termsTy sig env const tail).bind fun rest => some (t :: rest) := by
  cases head <;> rfl

/-- The general rule for a literal in argument position, read back: outside a const-generic
atom the literal rule is `Lit.ty`. -/
theorem litArgTy_false (value : Lit) : litArgTy false value = value.ty := by
  cases value <;> rfl

/-- `argTy` answers either by the literal rule or by `termTy`: the case split the term laws
take instead of a case split on the term. -/
theorem argTy_cases (sig : Signature Op) (env : TyEnv) (const : Bool) (head : Term) (t : Ty)
    (h : argTy sig env const head = some t) :
    (∃ value, head = .lit value ∧ t = litArgTy const value) ∨ termTy sig env head = some t := by
  cases head with
  | lit value => exact Or.inl ⟨value, rfl, (Option.some.inj h).symm⟩
  | var index => exact Or.inr h
  | app atom args => exact Or.inr h

/-- The error type a cause carries: its `fail` reasons; defects and interrupts contribute
none (`Cause.die` and `Cause.interrupt` are outside `E`). A `die` carries an admitted error
value, the same domain as `fail` (DI-74: what is admitted here is what `causeOf` evaluates,
`src/Effect4/Program/Compile.lean`); an interruptor is a natural, rc.112's fiber id. -/
def causeTy (sig : Signature Op) (env : TyEnv) : CauseTerm → Option Ty
  | .fail error => do
    let e ← termTy sig env error
    if admittedErrTy e then some e else none
  | .die defect => do
    let d ← termTy sig env defect
    if admittedErrTy d then some .never else none
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

/-! ## The tag residual of `catchIf` (DI-39, DI-17; part 4 commit 3, 2026-09-12)

The first failure determines the branch, but every failure in a retained cause must fit E.
An unconditional tag subtraction is therefore invalid for a mixed error column. A canonical
tag test can remove the body's column when its residual is empty: every typed failure then
matches, even when the cause contains several of them. Otherwise keep both error columns.
Literal `true` also keeps the handler's alone. The general miss/handler membership laws are
in `Laws/Program/Residual.lean`. Its single-failure residual theorem remains available for
future precision whose execution premise has actually been established. -/

/-- The tag test `tagIs("A", aN)` on the caught error variable `caught`. -/
def tagTest (tag : String) (caught : Nat) : Term :=
  .app "tagIs" (.cons (.lit (.str tag)) (.cons (.var caught) .nil))

/-- The tag a `catchIf` test names, when it is `tagTest tag caught` — the atom `tagIs` applied
to a string literal and exactly the caught error variable; `none` for every other test. -/
def tagTest? (test : Term) (caught : Nat) : Option String :=
  match test with
  | .app atom (.cons (.lit (.str tag)) (.cons (.var index) .nil)) =>
    if atom = "tagIs" ∧ index = caught then some tag else none
  | _ => none

theorem tagTest?_tagTest (tag : String) (caught : Nat) :
    tagTest? (tagTest tag caught) caught = some tag := by
  simp [tagTest?, tagTest]

/-- DI-17: all failures fit the error column, including later failures in a retained cause.
Remove the body's column only for literal true or a tag test whose residual is empty.
Neither rule assumes a bound on the number of failures. -/
def catchIfError (test : Term) (caught : Nat) (bodyError handlerError : Ty) : Ty :=
  if test = .lit (.bool true) then handlerError
  else match tagTest? test caught with
    | some tag => if Ty.diffTag tag bodyError.normalize = .never then handlerError
        else bodyError.join handlerError
    | none => bodyError.join handlerError

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
      let g ← stmtsTy sig env false body
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
    | .mergeAll layers => layersTy sig layers

  /-- The layers of a `mergeAll` (`Layer.ts:1652`, at least one): their signatures merged as
  siblings, `merge` folded to the right. -/
  def layersTy (sig : Signature Op) : LayerTerms Op → Option LayerTy
    | .nil => none
    | .cons head .nil => layerTy sig head
    | .cons head tail => do
      let h ← layerTy sig head
      let t ← layersTy sig tail
      some (h.merge t)

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

/-- `typeOf` at the empty environment. Structural: a layer reference (`LayerTerm.ref`) types
as nothing here; `typeOfProgram` is the whole program's typing. -/
def typeOf (sig : Signature Op) (program : Eff Op) : Option EffTy := effTy sig [] program

/-- The type of a whole program, its layer references resolved (the host rows slice): when
the references are well formed (`Eff.layerRefsWF`, `Program/Refs.lean`: every target a
non-reference layer that precedes its reference) the program is expanded to its
reference-free twin (`Eff.expandRefs`) and typed structurally; otherwise `none`. A program
with no references is `typeOf` itself. -/
def typeOfProgram (sig : Signature Op) (program : Eff Op) : Option EffTy :=
  if program.layerRefsWF && (program.expandRefs.refSites []).isEmpty then
    typeOf sig program.expandRefs
  else none

/-! ### Inserting an environment slot -/

private theorem lookup_weaken {α : Type} (pre post : List α) (inserted : α) (index : Nat) :
    (pre ++ inserted :: post)[Var.weaken pre.length index]? = (pre ++ post)[index]? := by
  induction pre generalizing index with
  | nil => simp [Var.weaken]
  | cons head pre ih =>
    cases index with
    | zero => simp [Var.weaken]
    | succ index =>
      by_cases h : index < pre.length
      · simpa [Var.weaken, h] using ih index
      · simpa [Var.weaken, h] using ih index

mutual
  /-- Inserting a slot preserves the whole term-typing result, including refusal. -/
  theorem termTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (term : Term) :
      termTy sig (pre ++ inserted :: post) (Term.weaken pre.length term) =
        termTy sig (pre ++ post) term :=
    match term with
    | .var index => lookup_weaken pre post inserted index
    | .lit _ => rfl
    | .app atom args => by
      simp only [Term.weaken, termTy, termsTy_weaken sig pre post inserted _ args]

  theorem termsTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (const : Bool) (terms : Terms) :
      termsTy sig (pre ++ inserted :: post) const (Terms.weaken pre.length terms) =
        termsTy sig (pre ++ post) const terms :=
    match terms with
    | .nil => rfl
    | .cons (.lit _) tail => by
      simp only [Terms.weaken, Term.weaken, termsTy, termsTy_weaken sig pre post inserted const tail]
    | .cons (.var index) tail => by
      simp only [Terms.weaken, Term.weaken, termsTy, termTy, lookup_weaken,
        termsTy_weaken sig pre post inserted const tail]
    | .cons (.app atom args) tail => by
      simp only [Terms.weaken, Term.weaken, termsTy, termTy,
        termsTy_weaken sig pre post inserted _ args,
        termsTy_weaken sig pre post inserted const tail]
end

theorem causeTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
    (cause : CauseTerm) :
    causeTy sig (pre ++ inserted :: post) (CauseTerm.weaken pre.length cause) =
      causeTy sig (pre ++ post) cause := by
  induction cause with
  | fail _ | die _ => simp only [CauseTerm.weaken, causeTy, termTy_weaken]
  | interrupt who => cases who <;> simp only [CauseTerm.weaken, causeTy, Option.map,
      termTy_weaken]
  | both left right ihl ihr => simp only [CauseTerm.weaken, causeTy, ihl, ihr]

/-- The tag test survives an inserted slot: the caught variable is the last position, so it
shifts by exactly one when the environment grows by one, and every other test stays `none`. -/
theorem tagTest?_weaken (cut : Nat) (test : Term) (caught : Nat) (h : cut ≤ caught) :
    tagTest? (Term.weaken cut test) (caught + 1) = tagTest? test caught := by
  cases test with
  | var _ => rfl
  | lit _ => rfl
  | app atom args =>
    cases args with
    | nil => rfl
    | cons head tail =>
      cases head with
      | var _ => rfl
      | app _ _ => rfl
      | lit value =>
        cases value with
        | unit | nat _ | bool _ => rfl
        | str tag =>
          cases tail with
          | nil => rfl
          | cons second rest =>
            cases second with
            | lit _ => rfl
            | app _ _ => rfl
            | var index =>
              cases rest with
              | cons _ _ => rfl
              | nil =>
                simp only [Term.weaken, Terms.weaken, tagTest?, Var.weaken]
                by_cases hlt : index < cut
                · -- `index < cut ≤ caught`: neither the old nor the new caught position
                  -- (`omega` does not see through the `Var` abbreviation, so the `Nat` lemmas)
                  have h1 : index ≠ caught := Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt h)
                  have h2 : index ≠ caught + 1 :=
                    Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hlt h))
                  simp [hlt, h1, h2]
                · simp [hlt]

/-- The `catchIf` error column survives an inserted slot (`tagTest?_weaken` at the caught
position, which is the environment's length). -/
theorem catchIfError_weaken (pre post : TyEnv) (inserted : Ty) (test : Term) (b h : Ty) :
    catchIfError (Term.weaken pre.length test) (pre ++ inserted :: post).length b h =
      catchIfError test (pre ++ post).length b h := by
  have hlen : (pre ++ inserted :: post).length = (pre ++ post).length + 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  have hle : pre.length ≤ (pre ++ post).length := by
    simp only [List.length_append]
    omega
  simp only [catchIfError, Term.weaken_eq_lit, hlen, tagTest?_weaken pre.length test _ hle]

mutual
  /-- Inserting one slot preserves the entire typing result. Local binders still
  append after the old environment; closed layer bodies retain their empty one.
  This equality covers ill-typed programs as well as successful typings. -/
  theorem effTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (program : Eff Op) :
      effTy sig (pre ++ inserted :: post) (Eff.weaken pre.length program) =
        effTy sig (pre ++ post) program :=
    match program with
    | .succeed _ | .fail _ | .failCause _ | .sync _ | .suspend _
    | .perform _ _ | .bind _ _ | .gen _ | .catchCause _ _ | .catchIf _ _ _ | .matchCause _ _ _
    | .onExit _ _ | .exit _ | .uninterruptible _ | .interruptible _
    | .yieldNow _ | .awaitFiber _ _
    | .withFiber _ | .scoped _ | .acquireRelease _ _
    | .provideLayer _ _ _ | .service _ | .provideService _ _ _ | .select _ _ _ _
    | .iterate _ _ _ _ _ _ => by
      simp only [Eff.weaken, effTy, termTy_weaken, causeTy_weaken, Term.weaken_eq_lit,
        catchIfError_weaken, List.append_assoc, List.cons_append, effTy_weaken, stmtsTy_weaken,
        actionTy_weaken]

  theorem stmtsTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (inLoop : Bool) (body : Stmts Op) :
      stmtsTy sig (pre ++ inserted :: post) inLoop (Stmts.weaken pre.length body) =
        stmtsTy sig (pre ++ post) inLoop body :=
    match body with
    | .nil => rfl
    | .cons (.ret _) rest => by
      cases rest <;> simp only [Stmts.weaken, Stmt.weaken, stmtsTy, termTy_weaken]
    | .cons (.bindYield _) _ | .cons (.yieldDiscard _) _
    | .cons (.ifElse _ _ _) _ | .cons (.whileTrue _) _ | .cons .breakLoop _ => by
      simp only [Stmts.weaken, Stmt.weaken, stmtsTy, termTy_weaken,
        List.append_assoc, List.cons_append, effTy_weaken, stmtsTy_weaken]

  theorem effsTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (entrants : Effs Op) :
      effsTy sig (pre ++ inserted :: post) (Effs.weaken pre.length entrants) =
        effsTy sig (pre ++ post) entrants :=
    match entrants with
    | .nil => rfl
    | .cons _ _ => by simp only [Effs.weaken, effsTy, effTy_weaken, effsTy_weaken]

  theorem actionTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (action : ActionTerm Op) :
      actionTy sig (pre ++ inserted :: post) (ActionTerm.weaken pre.length action) =
        actionTy sig (pre ++ post) action :=
    match action with
    | .interruptAll _ who => by
      cases who <;> simp only [ActionTerm.weaken, actionTy, Option.map, termTy_weaken]
    | .fork _ _ | .forkIn _ _ _ | .forkScoped _ _ | .runIn _ _ | .interrupt _
    | .interruptScoped _ | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren
    | .awaitNewChildren _ | .raceAll _ | .setContext _ | .getContext | .getId
    | .closeScope _ _ => by
      simp only [ActionTerm.weaken, actionTy, termTy_weaken, effTy_weaken, effsTy_weaken]
end

/-- A closed program may be placed under a new surrounding binder without
changing its type. The inserted slot is unused by the shifted program. -/
theorem typeOf_weaken (sig : Signature Op) (inserted : Ty) (program : Eff Op) :
    effTy sig [inserted] (Eff.weaken 0 program) = typeOf sig program :=
  effTy_weaken sig [] [] inserted program

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
  simp only [effTy, hty, Option.bind_eq_bind, Option.bind_some, hnear, hinner, Ty.sub_refl,
    if_true]
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
