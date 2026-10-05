module

public import Effect4.Program.Refs
public import Effect4.Program.Formation
public import Effect4.Program.Record
public import Effect4.Program.Tuple
public import Effect4.Machine.Context

/-!
# Program.Typing.Rules — the type algebra and the rules the checker applies

What a type assignment needs beside the program: the effect type `EffTy` (`A`, `E` as a
canonical union, the requirement row `R`), the signature `Signature Op`, the environment
`TyEnv` (one `Ty` per positional variable), the term typer (the fold `argTy`/`argsTy`; `termTy` its
projection outside a const-generic atom), the
cause typer, the generator state `GenTy` and the layer signature `LayerTy` with their
operations, the first-failure residual of `catchIf`, the scope discharge `bodyRequires`, and
the weakening lemmas of terms and causes. The checker itself is `Program/Checker.lean` and its
success projections `effTy`, `layerTy`, … are `Program/Typing.lean`; this module is what both
read and is imported by both.
-/

@[expose] public section

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

/-- The binder term an operation carries (decisions row 43), with its type over the row's
parameters: the term runs at `env ++ [current]`, the current value at `param` and its answer at
`result` (the state plan's T3b). The templates sit beside the term, not in `Row`: no host row
takes a function, and `Row`'s codec stays as it is. -/
structure BinderTerm where
  term : Term
  param : Ty
  result : Ty
deriving DecidableEq

/-- The binder term weakened at a cut, its templates unchanged. -/
def BinderTerm.weaken (cut : Nat) (b : BinderTerm) : BinderTerm :=
  { b with term := Term.weaken cut b.term }

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
  /-- The binder term an operation carries, with its templates (the state plan's T3b); `none`
  for an operation that carries none. The checker types the term at the node's environment
  extended by the current value (`termUse`, `checkRow`). -/
  termOf : Op → Option BinderTerm := fun _ => none
  /-- An operation's own data written for a node of level `src`, as data for a node of level
  `dst`. A binder term reads its current value at the node's level, so the faces print and read
  an operation as its form at level 0 (`Codegen/Templates.lean`, `Codegen/Read.lean`). `none`
  where the faces have no form for it (the state plan's T3b, until T5). The identity by
  default. -/
  opAtLevel : Nat → Nat → Op → Option Op := fun _ _ op => some op

variable {Op : Type}

/-- The literal rule (DI-15, amended 2026-09-11: "mirror TypeScript"). A string literal types
as `string` in general position (`Lit.ty`, what `termTy` answers) and keeps its literal type
`lit s` exactly as a direct argument of a const-generic atom (`Signature.constAtom`), which is
TypeScript's `const` type-parameter rule: `pair("A", m)` is `readonly ["A", string]`,
`succeed "x"` stays `string`. Every other literal is its `Lit.ty` in both positions. The rule
is stated once, here; `argsTy` applies it to the direct arguments of an application and
nowhere else. -/
def litArgTy (const : Bool) : Lit → Ty
  | .str s => if const then .lit s else .string
  | .unit => .unit
  | .nat _ => .nat
  | .bool _ => .bool

mutual
  /-- The type of a term in argument position, as a fold: a variable from the environment, the
  literal rule under the enclosing atom's const-generic flag, an application by its atom at its
  arguments' types under the atom's own flag (`Signature.constAtom`). A const-generic atom
  retains direct string literals; other atoms widen them to `string`.
  The flag is the accumulator; `fold_of` reads the algebra (`Program/Folds/Term.lean`). -/
  def argTy (sig : Signature Op) (env : TyEnv) (const : Bool) : Term → Option Ty
    | .var index => env[index]?
    | .lit value => some (litArgTy const value)
    | .app atom args => do
      let tys ← argsTy sig env (sig.constAtom atom) args
      sig.atomOf atom tys
    | .record fields names values =>
      match Formation.check (Formation.sites false [] (.record fields)) with
      | some _ => none
      | none => do
        let types ← argsTy sig env true values
        Record.check fields names types
    | .field mode target name => do
      let type ← argTy sig env false target
      Record.fieldType (mode = .optional) type name
    | .recordSet target name value => do
      let targetType ← argTy sig env false target
      let valueType ← argTy sig env true value
      Record.setType targetType name valueType
    | .tupleAt target index => do
      let targetType ← argTy sig env false target
      Tuple.typeAt targetType index
  /-- The argument types of an application, argument by argument. -/
  def argsTy (sig : Signature Op) (env : TyEnv) (const : Bool) : Terms → Option (List Ty)
    | .nil => some []
    | .cons head tail => do
      let t ← argTy sig env const head
      let rest ← argsTy sig env const tail
      some (t :: rest)
end

/-- The type of a pure term: the fold outside any const-generic atom, where the literal rule
is `Lit.ty` (`litArgTy_false`). -/
def termTy (sig : Signature Op) (env : TyEnv) (t : Term) : Option Ty :=
  argTy sig env false t

/-- How one use of a row types its operation's binder term: the term's parameter and result
templates, and the term's type at a parameter type. -/
structure TermUse where
  param : Ty
  result : Ty
  typeAt : Ty → Option Ty

/-- The use of an operation's binder term at a node of environment `env`: the term typed at
`env ++ [A]`, its current value `A` at the node's level (`ScopedOp`'s convention, decisions row
43). `none` for an operation that carries no term. -/
def Signature.termUse (sig : Signature Op) (env : TyEnv) (op : Op) : Option TermUse :=
  (sig.termOf op).map fun b => ⟨b.param, b.result, fun A => termTy sig (env ++ [A]) b.term⟩

/-- A request mismatch and malformed instantiated columns are distinct refusals, and so are the
two ways an operation's binder term fails: no type at the parameter, and a type outside the
result template's instance. -/
inductive RowTypingRefusal where
  | requestNotSubtype
  | formation (why : FormationRefusal)
  /-- The binder term has no type at the instantiated parameter (appended, the state plan's
  T3b). -/
  | term (param : Ty)
  /-- The binder term's type is not below the result template's instance at the request's
  bindings (appended, the state plan's T3b). -/
  | resultNotSubtype (result expected : Ty)
  deriving DecidableEq, Repr

/-- The bindings a row use's binder term extends: the term typed at the parameter's instance,
its type matched against the result template from the request's bindings `σ`. The match reads
the term's raw type: its normal form distributes a product over a union, where the first member
would bind a parameter the guard then refuses (the T3b design note, F6). -/
def bindTerm (σ : Ty.Subst) : Option TermUse → Except RowTypingRefusal Ty.Subst
  | none => .ok σ
  | some use =>
    let param := (use.param.normalize.instantiate σ).normalize
    match use.typeAt param with
    | none => .error (.term param)
    | some r =>
      match Ty.matchTemplate σ use.result.normalize r with
      | some σ' => .ok σ'
      | none => .error (.resultNotSubtype r (use.result.normalize.instantiate σ).normalize)

/-- Match the request, then bind the operation's binder term (`bindTerm`), then check all raw
instantiated columns before normalization. Request mismatch retains precedence when several
checks would fail (rows 42 and 193). The checker and `rowTy` project this one result. -/
def checkRow (row : Row) (request : Ty) (use : Option TermUse := none) :
    Except RowTypingRefusal EffTy :=
  match Ty.matchTemplate [] row.request.normalize request.normalize with
  | none => .error .requestNotSubtype
  | some σ =>
    match bindTerm σ use with
    | .error why => .error why
    | .ok bindings =>
      match Formation.check (Formation.instantiatedSites row bindings) with
      | some why => .error (.formation why)
      | none => .ok ⟨(row.answer.instantiate bindings).normalize,
          (row.error.instantiate bindings).normalize, Requirement.ofList row.requires⟩

/-- The type projection of the row check. A closed, raw formed row reduces to
subsumption and its own columns (`rowTy_closed`, `Laws/Program/Template.lean`). -/
def rowTy (row : Row) (request : Ty) (use : Option TermUse := none) : Option EffTy :=
  (checkRow row request use).toOption

/-- The part of a row the row check reads (`checkRow`): its request, answer and error columns
and its requirements. The name, spelling, shape, trailing names, type arguments, citation and
registration are the faces' and the runner's. -/
def Row.columns (row : Row) : Ty × Ty × Ty × List ServiceKey :=
  (row.request, row.answer, row.error, row.requires)

/-- Two rows with the same columns check alike: the row check reads nothing else. A step of
`check_weaken` (`Program/Typing.lean`), whose signature premise compares columns. -/
theorem checkRow_columns {row row' : Row} (h : row.columns = row'.columns) (request : Ty)
    (use : Option TermUse) : checkRow row request use = checkRow row' request use := by
  simp only [Row.columns, Prod.mk.injEq] at h
  obtain ⟨hreq, hans, herr, hrequires⟩ := h
  simp only [checkRow, Formation.instantiatedSites, hreq, hans, herr, hrequires]

/-- `rowTy` at two rows with the same columns. -/
theorem rowTy_columns {row row' : Row} (h : row.columns = row'.columns) (request : Ty)
    (use : Option TermUse) : rowTy row request use = rowTy row' request use := by
  simp only [rowTy, checkRow_columns h request use]

/-- The row judgment and diagnostic worker accept the same type. The checker
inversion and completeness laws consume this projection of `checkRow`. -/
theorem rowTy_eq_some_iff (row : Row) (request : Ty) (use : Option TermUse) (ty : EffTy) :
    rowTy row request use = some ty ↔ checkRow row request use = .ok ty := by
  cases checked : checkRow row request use with
  | error why => simp only [rowTy, checked, Except.toOption, reduceCtorEq]
  | ok result => simp only [rowTy, checked, Except.toOption, Option.some.injEq, Except.ok.injEq]

/-- An operation with no binder term binds nothing: the request's bindings stand. -/
@[simp] theorem bindTerm_none (σ : Ty.Subst) : bindTerm σ none = .ok σ := rfl

/-- The use of an operation that carries no term is no use. -/
theorem Signature.termUse_eq_none {sig : Signature Op} {op : Op} (h : sig.termOf op = none)
    (env : TyEnv) : sig.termUse env op = none := by
  simp only [Signature.termUse, h, Option.map_none]

/-- `argsTy` on a cons, as nested `Option.bind`s. -/
theorem argsTy_cons (sig : Signature Op) (env : TyEnv) (const : Bool) (head : Term)
    (tail : Terms) :
    argsTy sig env const (.cons head tail) =
      (argTy sig env const head).bind fun t =>
        (argsTy sig env const tail).bind fun rest => some (t :: rest) :=
  rfl

/-- The general rule for a literal in argument position, read back: outside a const-generic
atom the literal rule is `Lit.ty`. -/
theorem litArgTy_false (value : Lit) : litArgTy false value = value.ty := by
  cases value <;> rfl

/-- `argTy` answers either by the literal rule or by `termTy` (the flag reaches a literal
argument and nothing else): the case split the term laws take instead of a case split on the
term. -/
theorem argTy_cases (sig : Signature Op) (env : TyEnv) (const : Bool) (head : Term) (t : Ty)
    (h : argTy sig env const head = some t) :
    (∃ value, head = .lit value ∧ t = litArgTy const value) ∨ termTy sig env head = some t := by
  cases head with
  | lit value => exact Or.inl ⟨value, rfl, (Option.some.inj h).symm⟩
  | var index => exact Or.inr h
  | app atom args => exact Or.inr h
  | record fields names values => exact Or.inr h
  | field mode target name => exact Or.inr h
  | recordSet target name value => exact Or.inr h
  | tupleAt target index => exact Or.inr h

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
the first), the errors and requirements so far, and two reachability bits over the statements'
syntax: `completes`, the end of the statements is reachable (control falls off it), and
`breaks`, a `break` of the innermost enclosing `while (true)` is reachable in them. A `gen`
whose body's end is reachable answers `void` there (`walkR`, `Compile.runStmts`), so its answer
type includes `void` (`genAnswer`; seat M6E's finding, owner option (a), 2026-10-02). The bits
over-approximate the walk's paths: a test is never evaluated. -/
structure GenTy where
  answer : Option Ty
  error : Ty
  requires : Requirement
  completes : Bool
  breaks : Bool

namespace GenTy

def joinAnswer : Option Ty → Option Ty → Option (Option Ty)
  | none, b => some b
  | a, none => some a
  | some a, some b => (EffTy.joinAnswer a b).map some

/-- An `if`'s two branches: the answers join, the errors and requirements union, and the end or a
`break` is reachable when it is in either branch. -/
def merge (a b : GenTy) : Option GenTy := do
  let answer ← joinAnswer a.answer b.answer
  some ⟨answer, a.error.join b.error, a.requires.union b.requires, a.completes || b.completes,
    a.breaks || b.breaks⟩

/-- A statement's state `s`, then its tail's `r`: the tail runs only when the statement completes,
so the end is reachable when both are, and a `break` is reachable in the statement or, once it
completes, in the tail. The answers, errors and requirements cover both (a dead tail is checked
too). -/
def seq (s r : GenTy) : Option GenTy := do
  let answer ← joinAnswer s.answer r.answer
  some ⟨answer, s.error.join r.error, s.requires.union r.requires, s.completes && r.completes,
    s.breaks || (s.completes && r.breaks)⟩

/-- `while (true)` around a body with state `b`: the loop completes exactly when a `break` of its
own is reachable in the body, and a `break` inside it leaves it, not an enclosing loop. -/
def loop (b : GenTy) : GenTy :=
  ⟨b.answer, b.error, b.requires, b.breaks, false⟩

/-- `break` before a tail with state `r`: the end is not reachable through it, a `break` is. -/
def broken (r : GenTy) : GenTy :=
  ⟨r.answer, r.error, r.requires, false, true⟩

/-- The answer of `Effect.gen` over a body with state `g` (`:1184`): the `return`s' answer, joined
with `void` when the body's end is reachable (TS infers `T | undefined` for such a body), and
`void` when the body has no `return`. -/
def genAnswer (g : GenTy) : Ty :=
  match g.answer with
  | none => .unit
  | some t => if g.completes then Ty.join t .unit else t

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
  /-- Inserting a slot preserves the whole term-typing result, including refusal, under either
  flag. -/
  theorem argTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (const : Bool)
      (term : Term) :
      argTy sig (pre ++ inserted :: post) const (Term.weaken pre.length term) =
        argTy sig (pre ++ post) const term :=
    match term with
    | .var index => lookup_weaken pre post inserted index
    | .lit _ => rfl
    | .app atom args => by
      simp only [Term.weaken, argTy, argsTy_weaken sig pre post inserted _ args]
    | .record fields names values => by
      simp only [Term.weaken, argTy, argsTy_weaken sig pre post inserted true values]
    | .field mode target name => by
      simp only [Term.weaken, argTy, argTy_weaken sig pre post inserted false target]
    | .recordSet target name value => by
      simp only [Term.weaken, argTy, argTy_weaken sig pre post inserted false target,
        argTy_weaken sig pre post inserted true value]
    | .tupleAt target index => by
      simp only [Term.weaken, argTy, argTy_weaken sig pre post inserted false target]

  theorem argsTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (const : Bool) (terms : Terms) :
      argsTy sig (pre ++ inserted :: post) const (Terms.weaken pre.length terms) =
        argsTy sig (pre ++ post) const terms :=
    match terms with
    | .nil => rfl
    | .cons head tail => by
      simp only [Terms.weaken, argsTy, argTy_weaken sig pre post inserted const head,
        argsTy_weaken sig pre post inserted const tail]
end

/-- `termTy`'s weakening: the fold's at `false`. -/
theorem termTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (term : Term) :
    termTy sig (pre ++ inserted :: post) (Term.weaken pre.length term) =
      termTy sig (pre ++ post) term :=
  argTy_weaken sig pre post inserted false term

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
  | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _ => rfl
  | app atom args =>
    cases args with
    | nil => rfl
    | cons head tail =>
      cases head with
      | var _ => rfl
      | app _ _ => rfl
      | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _ => rfl
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
            | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _ => rfl
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
                  simp only [hlt, ↓reduceIte, h1, h2, and_false]
                · simp only [hlt, ↓reduceIte, Nat.add_right_cancel_iff]

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

end Effect4.Program
