module

public import Effect4.Program.NativeAtom
public import Effect4.Program.ErrorImage
public import Effect4.Program.Typing
public import Effect4.Program.ScopedOp
public import Effect4.Program.FnName
public import Effect4.Machine.Stores

/-!
# Syntax.Native — the native row alphabet over the stores (lane A3, first cut)

Plan: `docs/research/2026-09-04-eff-compile.md` §1-§2. The native route performs the
standard library's store operations (`git:62c04d9:src/Effect4/StdLib/Links.lean`: `Ref.*`, `Deferred.*`,
`Scope.make`) against the reference machine's stores (`src/Effect4/Machine/Stores.lean`). This
module owns:

* `NativeOp`, the positions of that table, each with its `Row` (spelling, shape, kind, the
  request and answer types, the rc.112 line);
* the atoms' types (`nativeAtomTy`); the terms, their values and their evaluation are
  `Machine/Term.lean`, below the stores, since L1 of the language push;
* `SyncOp.ofRow`, the decoding of a row and a request value into the store operation the
  machine runs.

The `Ref` rows without a function and the `Deferred` rows are templates over their type
parameters (decisions row 42, the state plan's T3a): `Ref<A>` is `refOf (var 0)` and
`Deferred<A, E>` is `deferredOf (var 0) (var 1)`, and the checker instantiates them at the
request's type (`checkRow`, `Typing/Rules.lean`). `Deferred.make`'s request fixes no parameter,
so its operation carries its type arguments (`deferredMakeOf`), as rc.112's
`Deferred.make<A, E>()` does. The faces print them on the call's head, each through the type
printer, and read them back (`NativeOp.typeArgs`, `NativeOp.withTypeArgs`; the state plan's T5,
part B): the row spells none. The eight read-modify-write rows carry their function as a binder
term *in the operation* (decisions row 43, the state plan's T3b): rc.112 takes a JavaScript
function, and DB-02 forbids storing one. The term runs at `env ++ [current]`, in the one store
step `syncOpOf` decodes the row to, and the checker types it at the instance's element type
(`nativeSignature`'s `termOf`). The rows are templates too: `Ref.modify` answers its own
parameter `B`, bound from the term's type. The faces print a term as a function of the current
value, after the row's request (`Codegen/Templates.lean`, the state plan's T5): a term row's
spelling key names the row alone, and `NativeOp.withTerm` installs the function a reader read.
The Layer and Context rows (`RowKind.program`) are not in this first cut.
-/

@[expose] public section

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## The atoms' types (their values and evaluation are `Machine/Term.lean`) -/
/-- The atoms' types, by their argument types, from the same exhaustive owner. -/
def nativeAtomTy (name : String) (types : List Ty) : Option Ty :=
  (NativeAtom.ofName? name).bind (fun atom => atom.typeOf types)

/-- Which atoms are const-generic, by name, from the same owner (`NativeAtom.constGeneric`):
the literal rule's flag for `argsTy`. An unknown name is not. -/
def nativeConstAtom (name : String) : Bool :=
  (NativeAtom.ofName? name).any NativeAtom.constGeneric

theorem nativeConstAtom_pair : nativeConstAtom "pair" = true := by decide

theorem nativeAtomTy_strings (tys : List Ty) :
    nativeAtomTy "strings" tys =
      if tys.all (·.sub .string) then some (.list .string) else none := rfl
/-! ## The rows -/

/-- The native operations this cut performs: the `Ref`, `Deferred` and `Scope.make` rows of
the standard library that the stores model. Wire tags 5 to 12 and 13 are retired
(`tools/Effect4Gen/wire-tags.json`): the eight rows that named their function, and
`deferredMake`. -/
inductive NativeOp
  | refMake
  | refGet
  | refSet
  | refGetAndSet
  | refSetAndGet
  | deferredIsDone
  | deferredPoll
  | deferredSucceed
  | deferredFail
  | deferredAwait
  | scopeMake (strategy : FinalizerStrategy)
  /-- `Effect.sleep(duration)` (`internal/effect.ts:6114-6116`; `ClockImpl.sleepMillis`
  `:6052-6066`): the timer, A4. The request is the millis: `0` is `yieldNow`, the rest parks on
  the logical clock (`Machine/Timer.lean`, DB-14). -/
  | sleep
  /-- `Effect.currentTimeMillis` (`internal/effect.ts:6118`): the logical clock, read
  (`SyncOp.clockNow`). -/
  | clockNow
  /-- A position in the row table supplied beside the program. -/
  | external (index : Nat)
  /-- `Deferred.make<A, E>()` (`vendor/effect-4.0.0-rc.112/src/Deferred.ts:171`) with its type
  arguments: the request is `unit`, so no parameter of the row is fixed by it, and the operation
  carries them (decisions row 42). An unbound template is never defaulted to rc.112's
  `Deferred<unknown, never>`. Appended: `deferredMake`, which carried none, is retired at wire
  tag 13 (`tools/Effect4Gen/wire-tags.json`). -/
  | deferredMakeOf (value error : Ty)
  /-- `Ref.update(self, f)` (`vendor/effect-4.0.0-rc.112/src/Ref.ts:1273-1276`): `f` is a binder
  term run at `env ++ [current]` (decisions row 43). Appended at wire tag 24: `refUpdate`, which
  named its function, is retired at 5 (decisions row 210), and so are its seven siblings at 6 to
  12, each replaced by the constructor below at 25 to 31. -/
  | refUpdateWith (f : Term)
  /-- `Ref.getAndUpdate(self, f)` (`Ref.ts:496-501`). -/
  | refGetAndUpdateWith (f : Term)
  /-- `Ref.updateAndGet(self, f)` (`Ref.ts:1368`). -/
  | refUpdateAndGetWith (f : Term)
  /-- `Ref.updateSome(self, pf)` (`Ref.ts:1502-1508`): the term answers an option. -/
  | refUpdateSomeWith (f : Term)
  /-- `Ref.getAndUpdateSome(self, pf)` (`Ref.ts:635-643`). -/
  | refGetAndUpdateSomeWith (f : Term)
  /-- `Ref.updateSomeAndGet(self, pf)` (`Ref.ts:1639-1646`). -/
  | refUpdateSomeAndGetWith (f : Term)
  /-- `Ref.modify(self, f)` (`Ref.ts:896-901`): the term answers a pair `[b, a]`; the row answers
  `b`, at its own type `B`, and stores `a`. -/
  | refModifyWith (f : Term)
  /-- `Ref.modifySome(self, pf)` (`Ref.ts:1159-1163`): the term answers `[b, Option<a>]`. -/
  | refModifySomeWith (f : Term)
  /-- **The invocation of a definition** (decisions row 328): definition `index` of the program's
  definition block (`Eff.defs`). Its row is the definition's declared row, which the block's
  signature supplies (`Signature.withDefs`); the definition's body answers it on the invoking
  fiber. No host answers it. Appended at wire tag 32. -/
  | call (index : Nat)
  /-- **The run of a parameter** (decisions row 340): parameter `index` of the definition whose
  body performs it, at the request. Its row is the parameter's declared row, which the body's
  signature supplies (`Signature.withParams`); the program that the call passed answers it, on
  the fiber that runs the body. No host answers it. Appended at wire tag 33. -/
  | param (index : Nat)
deriving DecidableEq

namespace NativeOp

/-- The binder term an operation carries, with the shape of its row's function type; `none` for
an operation that carries none. With `withTerm`, the one place that names the eight term rows
by case. -/
def binder? : NativeOp → Option (FnShape × Term)
  | refUpdateWith f | refGetAndUpdateWith f | refUpdateAndGetWith f => some (.update, f)
  | refUpdateSomeWith f | refGetAndUpdateSomeWith f | refUpdateSomeAndGetWith f =>
    some (.updateSome, f)
  | refModifyWith f => some (.modify, f)
  | refModifySomeWith f => some (.modifySome, f)
  | refMake | refGet | refSet | refGetAndSet | refSetAndGet | deferredIsDone | deferredPoll
  | deferredSucceed | deferredFail | deferredAwait | scopeMake _ | sleep | clockNow | external _
  | deferredMakeOf _ _ | call _ | param _ => none

/-- The operation with its binder term replaced; an operation that carries none is unchanged. -/
def withTerm : NativeOp → Term → NativeOp
  | refUpdateWith _, t => refUpdateWith t
  | refGetAndUpdateWith _, t => refGetAndUpdateWith t
  | refUpdateAndGetWith _, t => refUpdateAndGetWith t
  | refUpdateSomeWith _, t => refUpdateSomeWith t
  | refGetAndUpdateSomeWith _, t => refGetAndUpdateSomeWith t
  | refUpdateSomeAndGetWith _, t => refUpdateSomeAndGetWith t
  | refModifyWith _, t => refModifyWith t
  | refModifySomeWith _, t => refModifySomeWith t
  | refMake, _ => refMake
  | refGet, _ => refGet
  | refSet, _ => refSet
  | refGetAndSet, _ => refGetAndSet
  | refSetAndGet, _ => refSetAndGet
  | deferredIsDone, _ => deferredIsDone
  | deferredPoll, _ => deferredPoll
  | deferredSucceed, _ => deferredSucceed
  | deferredFail, _ => deferredFail
  | deferredAwait, _ => deferredAwait
  | scopeMake strategy, _ => scopeMake strategy
  | sleep, _ => sleep
  | clockNow, _ => clockNow
  | external index, _ => external index
  | deferredMakeOf value error, _ => deferredMakeOf value error
  | call index, _ => call index
  | param index, _ => param index

/-- Replacing the term keeps the shape and installs the term. -/
theorem binder?_withTerm (op : NativeOp) (t : Term) :
    (op.withTerm t).binder? = op.binder?.map fun b => (b.1, t) := by
  cases op <;> rfl

/-- Replacing the term twice is replacing it once. -/
theorem withTerm_withTerm (op : NativeOp) (t t' : Term) :
    (op.withTerm t).withTerm t' = op.withTerm t' := by
  cases op <;> rfl

/-- Replacing an operation's term by itself is the operation. -/
theorem withTerm_binder? {op : NativeOp} {s : FnShape} {t : Term}
    (h : op.binder? = some (s, t)) : op.withTerm t = op := by
  cases op <;> cases h <;> rfl

/-- An operation that carries no term is fixed by `withTerm`. -/
theorem withTerm_of_none {op : NativeOp} (h : op.binder? = none) (t : Term) :
    op.withTerm t = op := by
  cases op <;> cases h <;> rfl

/-- The type arguments an operation carries on its printed call's head: the two types of
`Deferred.make<A, E>()` (decisions row 42). `Deferred.make` must be *called* with them: the
export's own parameters have defaults (`Deferred<unknown, never>`), so without them the host
types the cell at those defaults and rejects every later use (`E4-CHECK-CE-013`,
`vendor/effect-4.0.0-rc.112/src/Deferred.ts:171`). No other operation carries one: every other
row's parameters are fixed by its request or by its binder term. With `withTypeArgs`, the one
place that names the operations that carry type arguments by case. -/
def typeArgs : NativeOp → List Ty
  | deferredMakeOf value error => [value, error]
  | refMake | refGet | refSet | refGetAndSet | refSetAndGet | deferredIsDone | deferredPoll
  | deferredSucceed | deferredFail | deferredAwait | scopeMake _ | sleep | clockNow | external _
  | refUpdateWith _ | refGetAndUpdateWith _ | refUpdateAndGetWith _ | refUpdateSomeWith _
  | refGetAndUpdateSomeWith _ | refUpdateSomeAndGetWith _ | refModifyWith _
  | refModifySomeWith _ | call _ | param _ => []

/-- The operation at other type arguments; an operation that carries none is unchanged.
`Deferred.make` takes a list of two. At a list of another length it answers the instance that
`NativeOp.spelled` holds for the row's key, `(nat, nat)`: the face a reader's `spell` answers
(`Signature.face`). No reading yields that face as it stands: a reader installs two type
arguments read from the call's head, and refuses a call that carries another count
(`installTypeArgs`, `typeFree`, `Codegen/Read.lean`). -/
def withTypeArgs : NativeOp → List Ty → NativeOp
  | deferredMakeOf _ _, [value, error] => deferredMakeOf value error
  | deferredMakeOf _ _, _ => deferredMakeOf .nat .nat
  | refMake, _ => refMake
  | refGet, _ => refGet
  | refSet, _ => refSet
  | refGetAndSet, _ => refGetAndSet
  | refSetAndGet, _ => refSetAndGet
  | refUpdateWith f, _ => refUpdateWith f
  | refGetAndUpdateWith f, _ => refGetAndUpdateWith f
  | refUpdateAndGetWith f, _ => refUpdateAndGetWith f
  | refUpdateSomeWith f, _ => refUpdateSomeWith f
  | refGetAndUpdateSomeWith f, _ => refGetAndUpdateSomeWith f
  | refUpdateSomeAndGetWith f, _ => refUpdateSomeAndGetWith f
  | refModifyWith f, _ => refModifyWith f
  | refModifySomeWith f, _ => refModifySomeWith f
  | deferredIsDone, _ => deferredIsDone
  | deferredPoll, _ => deferredPoll
  | deferredSucceed, _ => deferredSucceed
  | deferredFail, _ => deferredFail
  | deferredAwait, _ => deferredAwait
  | scopeMake strategy, _ => scopeMake strategy
  | sleep, _ => sleep
  | clockNow, _ => clockNow
  | external index, _ => external index
  | call index, _ => call index
  | param index, _ => param index

/-- Replacing the type arguments by a list of the operation's own arity installs the list. -/
theorem typeArgs_withTypeArgs (op : NativeOp) (tys : List Ty)
    (h : tys.length = op.typeArgs.length) : (op.withTypeArgs tys).typeArgs = tys := by
  cases op with
  | deferredMakeOf value error =>
    rcases tys with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · cases h
    · cases h
    · rfl
    · exact absurd (Nat.succ.inj (Nat.succ.inj h)) (Nat.succ_ne_zero _)
  | _ => exact (List.eq_nil_of_length_eq_zero h).symm

/-- The arity is fixed: an operation carries as many type arguments after any replacement. -/
theorem length_typeArgs_withTypeArgs (op : NativeOp) (tys : List Ty) :
    (op.withTypeArgs tys).typeArgs.length = op.typeArgs.length := by
  cases op with
  | deferredMakeOf value error => rcases tys with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl
  | _ => rfl

/-- Replacing an operation's type arguments by themselves is the operation. -/
theorem withTypeArgs_typeArgs (op : NativeOp) : op.withTypeArgs op.typeArgs = op := by
  cases op <;> rfl

/-- Replacing the type arguments twice is replacing them once. -/
theorem withTypeArgs_withTypeArgs (op : NativeOp) (tys tys' : List Ty) :
    (op.withTypeArgs tys).withTypeArgs tys' = op.withTypeArgs tys' := by
  cases op with
  | deferredMakeOf value error =>
    rcases tys with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      rcases tys' with _ | ⟨a', _ | ⟨b', _ | ⟨c', rest'⟩⟩⟩ <;> rfl
  | _ => rfl

/-- The two updates commute: no native operation carries both a binder term and type arguments,
and the law is stated for every operation. -/
theorem withTypeArgs_withTerm (op : NativeOp) (tys : List Ty) (t : Term) :
    (op.withTerm t).withTypeArgs tys = (op.withTypeArgs tys).withTerm t := by
  cases op with
  | deferredMakeOf value error => rcases tys with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl
  | _ => rfl

/-- Replacing the type arguments leaves the binder term as it is. -/
theorem binder?_withTypeArgs (op : NativeOp) (tys : List Ty) :
    (op.withTypeArgs tys).binder? = op.binder? := by
  cases op with
  | deferredMakeOf value error => rcases tys with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl
  | _ => rfl

/-- Replacing the binder term leaves the type arguments as they are. -/
theorem typeArgs_withTerm (op : NativeOp) (t : Term) : (op.withTerm t).typeArgs = op.typeArgs := by
  cases op <;> rfl

end NativeOp

/-- The scope of a native operation's own data (`Program/ScopedOp.lean`): the binder term of a
read-modify-write row, checked at `n + 1` by `ScopedOp`'s convention, the current value at index
`n` and an outer capture below it. An operation that carries no term is in scope at every level:
`Deferred.make`'s type arguments are types, which bind no term variable. The term map replaces
the term (`NativeOp.withTerm`), so weakening shifts it with the rest of the program. The term's
reading view is the same term, so the raw annotation collector reads what the row runs. The type
arguments' reading view is the operation's own (`NativeOp.typeArgs`), so the collector reads the
types that the faces print on the call's head. -/
instance : ScopedOp NativeOp where
  scopedAt op n := op.binder?.all fun b => b.2.scoped (n + 1)
  mapTerm g op :=
    match op.binder? with
    | some (_, t) => op.withTerm (g t)
    | none => op
  term? op := op.binder?.map (·.2)
  typeArgs op := op.typeArgs

/-- A native operation that carries no term is in scope at every level: the hypothesis the
operation lift's scope lemma (`Authoring.perform_scoped`) asks of an operation, discharged once
for the term-free rows of the native alphabet. -/
theorem NativeOp.scopedAt_eq_true (op : NativeOp) (h : op.binder? = none) (n : Nat) :
    ScopedOp.scopedAt op n = true := by
  show (op.binder?.all fun b => b.2.scoped (n + 1)) = true
  rw [h]
  rfl

/-- A term row is in scope exactly when its term is, one level up: `ScopedOp`'s convention at
the native alphabet. -/
theorem NativeOp.scopedAt_of_binder {op : NativeOp} {s : FnShape} {t : Term}
    (h : op.binder? = some (s, t)) (n : Nat) : ScopedOp.scopedAt op n = t.scoped (n + 1) := by
  show (op.binder?.all fun b => b.2.scoped (n + 1)) = t.scoped (n + 1)
  rw [h]
  rfl

/-- Rows are unit content beside the program's bytes. -/
abbrev RowTable := List Row

namespace NativeOp

/-- The two external service handles of the host rows slice (service type codes 8 and 9,
`nativeServiceTy`; the package tables of `Program/Packages`): a SQL client and a key-value
store. Written once, here. -/
def sqlTarget : String := "SqlClient.SqlClient"
def sqlTy : Ty := .handle sqlTarget
def kvTarget : String := "KeyValueStore.KeyValueStore"
def kvTy : Ty := .handle kvTarget

/-- An absent external position cannot type as a callback. Its empty spelling is
outside the admitted table domain. -/
def externalPlaceholder : Row :=
  { name := "external", spelling := "", shape := .value, kind := .program,
    request := .never, answer := .never, cite := "", registration := .external }

/-- The row of an invocation read without its block. Its empty spelling is outside every
domain: only a block's signature (`Signature.withDefs`) gives `call k` the row that definition
`k` declares. -/
def callPlaceholder : Row :=
  { name := "call", spelling := "", shape := .call, kind := .program,
    request := .never, answer := .never, cite := "" }

/-- The row of a parameter's run read outside a body. Its empty spelling is outside every domain:
only a body's signature (`Signature.withParams`) gives `param i` the row that parameter `i`
declares. -/
def paramPlaceholder : Row :=
  { name := "param", spelling := "", shape := .call, kind := .program,
    request := .never, answer := .never, cite := "" }

/-- The scheduling kind of each operation: `.async` for `deferredAwait` and `sleep`, `.program`
for external placeholders, and `.sync` for every heap and deferred operation. Split off `row`
so the compiler and engine closure do not drag `Row` or `Ty` into native engine headers (plan 3.5). -/
@[simp] def kind : NativeOp → RowKind
  | deferredAwait | sleep => .async
  | external _ | call _ | param _ => .program
  | refMake | refGet | refSet | refGetAndSet | refSetAndGet
  | refUpdateWith _ | refGetAndUpdateWith _ | refUpdateAndGetWith _
  | refUpdateSomeWith _ | refGetAndUpdateSomeWith _ | refUpdateSomeAndGetWith _
  | refModifyWith _ | refModifySomeWith _
  | deferredIsDone | deferredPoll | deferredSucceed | deferredFail | deferredMakeOf _ _
  | scopeMake _ | clockNow => .sync

/-- The row of each operation.

Three rows model an *unsafe* or *private* form of the operation they are named after, and the
`cite` names the public export rather than the implementation, because a citation is a claim
about the declaration the row transcribes (DI-96, DI-99, DI-100):

* `deferredIsDone` cites `Deferred.isDone`, whose body is `sync (() => isDoneUnsafe(self))`;
  the machine answers the synchronous `isDoneUnsafe` value, which is what `isDone` wraps.
* `scopeMake` cites `Scope.make`, which is `internal/effect.ts`'s `scopeMake`; the machine
  models the unsafe form `scopeMakeUnsafe`, which is what `scopeMake` wraps.
* `deferredAwait` cites the export `_await as await`; the implementation is the private
  `_await` above it, whose `callback` shape is the one the machine models.

Two more rows disagree with rc.112 in their answer column and are signed exceptions, not
citation errors: `deferredPoll` answers `bool` where `poll` answers
`Effect<Option<Effect<A, E>>>` (DI-97 — the language has no carrier for an `Effect` as a
value, so the machine answers its `isSome`), and `refSet` answers the cell where `Ref.set`
answers `void` (DI-98 — the machine answers the cell, `Stores.refStep`, and restating it is a
machine change scheduled with L4).

The `Ref` and `Deferred` rows are templates (decisions row 42): `A` is `var 0` and `E` is
`var 1`. Every request parameter first occurs as the direct argument of an invariant handle
(row 55), except `Ref.make`'s bare `A`, which the match binds to the whole request. The eight
read-modify-write rows take a cell at any element type, `refOf (var 0)`. The three that answer
nothing answer `unit` and the three that answer the cell's value answer `var 0`. `Ref.modify`
and `Ref.modifySome` answer `var 1`, the parameter `B` their request does not mention: the
checker binds it from the binder term's type (`bindTerm`, `Typing/Rules.lean`). A term row
does not depend on its term: the faces print the term as a function after the request
(`Codegen/Templates.lean`), so the row carries no trailing name for it. `Deferred.make`'s row
does depend on its operation's type arguments, in its answer column alone. It declares none
(`Row.typeArgs`): the faces derive them from the operation (`NativeOp.typeArgs`) and print each
through the type printer, so no instance is spelled by hand (the state plan's T5, part B). -/
def row (op : NativeOp) : Row :=
  match op with
  | refMake =>
    ⟨"refMake", "Ref.make", .call, [], kind op, .var 0, .refOf (.var 0), .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:173", [], .deferred⟩
  | refGet =>
    ⟨"refGet", "Ref.get", .call, [], kind op, .refOf (.var 0), .var 0, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:200", [], .deferred⟩
  | refSet =>
    ⟨"refSet", "Ref.set", .tupleCall, [], kind op, .prod (.refOf (.var 0)) (.var 0),
      .refOf (.var 0), .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:306-307", [], .deferred⟩
  | refGetAndSet =>
    ⟨"refGetAndSet", "Ref.getAndSet", .tupleCall, [], kind op, .prod (.refOf (.var 0)) (.var 0),
      .var 0, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:399-404", [], .deferred⟩
  | refSetAndGet =>
    ⟨"refSetAndGet", "Ref.setAndGet", .tupleCall, [], kind op, .prod (.refOf (.var 0)) (.var 0),
      .var 0, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:747", [], .deferred⟩
  | refUpdateWith _ =>
    ⟨"refUpdateWith", "Ref.update", .call, [], kind op, .refOf (.var 0),
      .unit, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1273-1276",
      [], .deferred⟩
  | refGetAndUpdateWith _ =>
    ⟨"refGetAndUpdateWith", "Ref.getAndUpdate", .call, [], kind op,
      .refOf (.var 0), .var 0, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:496-501",
      [], .deferred⟩
  | refUpdateAndGetWith _ =>
    ⟨"refUpdateAndGetWith", "Ref.updateAndGet", .call, [], kind op,
      .refOf (.var 0), .var 0, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1368",
      [], .deferred⟩
  | refUpdateSomeWith _ =>
    ⟨"refUpdateSomeWith", "Ref.updateSome", .call, [], kind op,
      .refOf (.var 0), .unit, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1502-1508",
      [], .deferred⟩
  | refGetAndUpdateSomeWith _ =>
    ⟨"refGetAndUpdateSomeWith", "Ref.getAndUpdateSome", .call, [],
      kind op, .refOf (.var 0), .var 0, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:635-643", [], .deferred⟩
  | refUpdateSomeAndGetWith _ =>
    ⟨"refUpdateSomeAndGetWith", "Ref.updateSomeAndGet", .call, [],
      kind op, .refOf (.var 0), .var 0, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:1639-1646", [], .deferred⟩
  | refModifyWith _ =>
    ⟨"refModifyWith", "Ref.modify", .call, [], kind op, .refOf (.var 0),
      .var 1, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:896-901",
      [], .deferred⟩
  | refModifySomeWith _ =>
    ⟨"refModifySomeWith", "Ref.modifySome", .call, [], kind op,
      .refOf (.var 0), .var 1, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1159-1163",
      [], .deferred⟩
  | deferredMakeOf value error =>
    ⟨"deferredMakeOf", "Deferred.make", .call, [], kind op, .unit, .deferredOf value error,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:171", [], .deferred⟩
  | deferredIsDone =>
    ⟨"deferredIsDone", "Deferred.isDone", .call, [], kind op, .deferredOf (.var 0) (.var 1),
      .bool, .never, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:1366", [], .deferred⟩
  | deferredPoll =>
    ⟨"deferredPoll", "Deferred.poll", .call, [], kind op, .deferredOf (.var 0) (.var 1), .bool,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:1414-1416", [], .deferred⟩
  | deferredSucceed =>
    ⟨"deferredSucceed", "Deferred.succeed", .tupleCall, [], kind op,
      .prod (.deferredOf (.var 0) (.var 1)) (.var 0), .bool, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:1514", [], .deferred⟩
  | deferredFail =>
    ⟨"deferredFail", "Deferred.fail", .tupleCall, [], kind op,
      .prod (.deferredOf (.var 0) (.var 1)) (.var 1), .bool, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:669", [], .deferred⟩
  | deferredAwait =>
    ⟨"deferredAwait", "Deferred.await", .call, [], kind op, .deferredOf (.var 0) (.var 1),
      .var 0, .var 1, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:223", [], .deferred⟩
  | scopeMake .sequential =>
    ⟨"scopeMake", "Scope.make", .call, [], kind op, .unit, Ty.scope, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Scope.ts:240", [], .deferred⟩
  | scopeMake .parallel =>
    ⟨"scopeMake", "Scope.make", .call, [.str "parallel"], kind op, .unit, Ty.scope, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Scope.ts:240", [], .deferred⟩
  | sleep =>
    ⟨"sleep", "Effect.sleep", .call, [], kind op, .nat, .unit, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6114-6116", [], .deferred⟩
  | clockNow =>
    ⟨"clockNow", "Effect.currentTimeMillis", .value, [], kind op, .unit, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6118", [], .deferred⟩

  | external _ => externalPlaceholder
  | call _ => callPlaceholder
  | param _ => paramPlaceholder

@[simp] theorem row_kind (op : NativeOp) : (row op).kind = kind op := by
  cases op
  case scopeMake s => cases s <;> rfl
  all_goals rfl

/-- The store operation a row runs on a request value at a point's environment `env`; `none` is
a request of the wrong shape, which the compile turns into the `badName` defect (`Deep.Stores`
does the same for a continuation applied to the wrong value). Any value is a cell's initial
value, a written value and a deferred's success, as at the template rows (decisions row 42); a
failed value becomes its error through `errOf` (`Machine/Term.lean`, decisions row 120's
carrier), which the checker keeps inside the error alphabet by the deferred's formation rule
(`Formation.HeadFormed`). A read-modify-write row hands the store its own binder term and the
point's environment: the store step evaluates the term at `env ++ [current]`
(`refStep`, `Machine/Stores.lean`; decisions row 43), so the term reads the values bound around
the node below the node's level and the cell's value at it. -/
def syncOpOf : NativeOp → List Val → Val → Option SyncOp
  | refMake, _, v => some (SyncOp.refMake v)
  | refGet, _, Val.cell ⟨k⟩ => some (SyncOp.refGet ⟨k⟩)
  | refSet, _, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refSet ⟨k⟩ v)
  | refGetAndSet, _, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refGetAndSet ⟨k⟩ v)
  | refSetAndGet, _, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refSetAndGet ⟨k⟩ v)
  | refUpdateWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refUpdate ⟨k⟩ f env)
  | refGetAndUpdateWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refGetAndUpdate ⟨k⟩ f env)
  | refUpdateAndGetWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refUpdateAndGet ⟨k⟩ f env)
  | refUpdateSomeWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refUpdateSome ⟨k⟩ f env)
  | refGetAndUpdateSomeWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refGetAndUpdateSome ⟨k⟩ f env)
  | refUpdateSomeAndGetWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refUpdateSomeAndGet ⟨k⟩ f env)
  | refModifyWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refModify ⟨k⟩ f env)
  | refModifySomeWith f, env, Val.cell ⟨k⟩ => some (SyncOp.refModifySome ⟨k⟩ f env)
  | deferredMakeOf _ _, _, Val.unit => some SyncOp.deferredMake
  | deferredIsDone, _, Val.promise ⟨k⟩ => some (SyncOp.deferredIsDone ⟨k⟩)
  | deferredPoll, _, Val.promise ⟨k⟩ => some (SyncOp.deferredPoll ⟨k⟩)
  | deferredSucceed, _, .list [Val.promise ⟨k⟩, v] =>
    some (SyncOp.deferredCompleteWith ⟨k⟩ (Completion.ofExit (Exit.success v)))
  | deferredFail, _, .list [Val.promise ⟨k⟩, v] =>
    some (SyncOp.deferredCompleteWith ⟨k⟩ (Completion.ofExit (Exit.failure (Cause.fail (errOf v)))))
  | scopeMake strategy, _, Val.unit => some (SyncOp.scopeMake strategy)
  | clockNow, _, Val.unit => some SyncOp.clockNow
  | _, _, _ => none

/-- The deferred an `await` row registers on. -/
def awaitCellOf : Val → Option DeferredKey
  | Val.promise ⟨k⟩ => some ⟨k⟩
  | _ => none

/-- The millis a `sleep` row registers for (the timer, A4). -/
def sleepMillisOf : Val → Option Nat
  | Val.nat n => some n
  | _ => none

end NativeOp

/-- The `Scope` service key of the native signature. -/
def nativeScopeKey : ServiceKey := ⟨⟨0⟩, ⟨0⟩⟩

/-- Exact reserved service bindings. The native checker and generated readers consume
this same table; reserved names do not acquire the ordinary code-based bindings. -/
def nativeReservedServiceTypes : List (ServiceKey × Ty) := [(nativeScopeKey, .scope)]

/-- Service carriers available under a free name. This is the finite owner of the
code-to-carrier mapping, also projected into the source-reader profile. -/
def nativeServiceTypes : List (Nat × Ty) :=
  [(4, .nat), (5, .bool), (6, .unit), (7, .refOf .nat),
   (8, NativeOp.sqlTy), (9, NativeOp.kvTy)]

/-- The native signature's service table (the join, 2026-09-07), read off the key: the ambient
`Scope` under its reserved key, nothing under the other reserved names (`Env.firstFreeName`:
the scheduler's two references and `CurrentMemoMap` are the machine's, not a program's), and
for a free name the carrier its type code spells — `4` a number, `5` a boolean, `6` unit, `7`
a cell at `nat` (`refOf nat`, printed `Ref.Ref<number>`), `8` a `SqlClient.SqlClient` handle and `9` a
`KeyValueStore.KeyValueStore` handle. A key is typed by its own data, which is what `Machine/Key.lean`
means a `ServiceTypeCode` to be read as. -/
def nativeServiceTy (key : ServiceKey) : Option Ty :=
  match nativeReservedServiceTypes.find? (fun entry => entry.1 == key) with
  | some (_, ty) => some ty
  | none =>
    if key.name.value < Effect4.Machine.Env.firstFreeName then none
    else (nativeServiceTypes.find? (fun entry => entry.1 == key.service.value)).map Prod.snd

/-- The eight term rows' constructors, each with the shape of its function type, row by row. -/
def NativeOp.termRows : List ((Term → NativeOp) × FnShape) :=
  [(.refUpdateWith, .update), (.refGetAndUpdateWith, .update), (.refUpdateAndGetWith, .update),
   (.refUpdateSomeWith, .updateSome), (.refGetAndUpdateSomeWith, .updateSome),
   (.refUpdateSomeAndGetWith, .updateSome), (.refModifyWith, .modify),
   (.refModifySomeWith, .modifySome)]

/-- One native operation per spelling key (`rowKey`, `Program/Table.lean`): every operation
that carries no type argument, each read-modify-write row at its face (row by row, the order
the tools' profiles print), and `Deferred.make` at its face, the instance `(nat, nat)`
(`NativeOp.withTypeArgs`). A term row's face holds the unit literal for its term
(`Signature.face`, `Program/Typing/Rules.lean`): the row's key does not show the term, and a
reader installs the function it read (`NativeOp.withTerm`). `Deferred.make`'s key does not show
its type arguments either: a reader installs the two it read from the call's head, and no
reading yields the face as it stands. No list holds every operation, since
`deferredMakeOf` ranges over `Ty` and a term row over `Term`; these are the operations the rows
spell, so the built-in keys are this list's (`NativeOp.rowKey_mem`). The table's collision
check, the reader's `nativeSpell` and the tools' enumerations read it. -/
def NativeOp.spelled : List NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet]
  ++ NativeOp.termRows.map (fun row => row.1 (.lit .unit))
  ++ [.deferredMakeOf .nat .nat, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail,
      .deferredAwait, .scopeMake .sequential, .scopeMake .parallel, .sleep, .clockNow]

/-- An external index reads its supplied row. Built-ins keep their original row. -/
def nativeRowOf (table : RowTable) : NativeOp → Row
  | .external i => (table[i]?).getD NativeOp.externalPlaceholder
  | op => op.row

@[simp] theorem nativeRowOf_nil (op : NativeOp) : nativeRowOf [] op = op.row := by
  cases op <;> rfl

/-- The native signature uses the same canonical linked-row types as external preparation
and admission (`externalRow`). Raw table entries retain their source spelling/provenance. -/
def nativeSignature (table : RowTable := []) : Signature NativeOp :=
  { rowOf := fun op => (nativeRowOf table op).normalizeTypes, atomOf := nativeAtomTy, scopeKey := nativeScopeKey,
    serviceTy := nativeServiceTy,
    dom := fun op => match op with
      | .external i => decide (i < table.length)
      | .call _ | .param _ => false
      | _ => true,
    constAtom := nativeConstAtom,
    -- a read-modify-write row's binder term, at its shape's parameter and result templates
    termOf := fun op => op.binder?.map fun b => ⟨b.2, b.1.param, b.1.result⟩,
    -- a reader installs the function it read in the operation its row spells
    withTerm := NativeOp.withTerm,
    -- and the type arguments it read on the call's head (`Deferred.make<A, E>()`)
    typeArgsOf := NativeOp.typeArgs,
    withTypeArgs := NativeOp.withTypeArgs,
    -- an invocation names its definition; outside a block it is outside the domain
    callOf := fun | .call k => some k | _ => none
    -- a parameter's run names its parameter; outside a body it is outside the domain
    paramOf := fun | .param i => some i | _ => none }

/-- **The native signature types an operation alike once its binder term is weakened**
(`Signature.WeakenNatural`, `Program/Typing.lean`): weakening replaces a term row's term and
nothing else, a row's columns do not depend on its term, and the domain reads only an external
position. The premise of `check_weaken` at every native signature; its consumers are the forms'
typing laws that insert a slot (`effTy_insert`, `Laws/Codegen/Forms.lean`). -/
theorem nativeSignature_weakenNatural (table : RowTable := []) :
    (nativeSignature table).WeakenNatural := by
  intro cut op
  cases op <;> exact ⟨rfl, rfl, rfl⟩

/-! ## Which supplied tables this runner can register (v2 DI-61 (b))

`LawfulTable` (`src/Effect4/Codegen/Read.lean`) is about *names*: unique keys, no built-in
collision, no dropped trailing name, no captured binder. It says nothing about how a row is
answered, so a table can be lawful, type a program and print it, and still supply no runnable
registration — the row with `registration := .deferred` of
`docs/research/foundation-probes/Admission.lean:13` parks with its answer unused and refuses
an explicit `answerAsync` as `notExternal`. `checkTable` is that missing decision, with the
position of the first row this runner cannot register. `LawfulTable` is unchanged. -/

/-- A row a supplied table cannot be registered by, and where it sits. The two conditions are
`externalRow`'s (`src/Effect4/Program/Compile.lean`), read in its order: who answers the row
first, then whether it is asynchronous at all. -/
inductive TableRefusal
  /-- The row at this position is not answered by the external oracle. -/
  | notExternal (index : Nat)
  /-- The row at this position is answered externally but is not an asynchronous row. -/
  | notAsync (index : Nat)
deriving DecidableEq, Repr

/-- The first position of a supplied table this runner cannot register, `none` when every row
is `(registration := .external, kind := .async)`. An empty table is accepted: a program with
no external call needs no row. -/
def checkTable (table : RowTable) : Option TableRefusal :=
  (List.range table.length).findSome? fun index =>
    match table[index]? with
    | some row =>
      if row.registration ≠ .external then some (.notExternal index)
      else if row.kind ≠ .async then some (.notAsync index)
      else none
    | none => none

/-- A program of the native route. -/
abbrev NativeEff := Eff NativeOp

end Effect4.Program
