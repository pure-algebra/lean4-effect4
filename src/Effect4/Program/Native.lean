module

public import Effect4.Program.NativeAtom
public import Effect4.Program.ErrorImage
public import Effect4.Program.Typing
public import Effect4.Program.ScopedOp
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
`Deferred.make<A, E>()` does. The read-modify-write rows carry their pure function as a
`FnName` *in the operation* (`Ref.update(ref, incr)` is the row `refUpdate FnName.incr` on the
request `ref`) and stay closed at `refOf nat`: rc.112 takes a JavaScript function, and DB-02
forbids storing one. The store runs binder terms (decisions row 43), so `syncOpOf` hands it the
name's lowering at the row's shape; the rows carry terms themselves at T3b. The Layer and
Context rows (`RowKind.program`) are not in this first cut.
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
the standard library that the stores model. -/
inductive NativeOp
  | refMake
  | refGet
  | refSet
  | refGetAndSet
  | refSetAndGet
  | refUpdate (f : FnName)
  | refGetAndUpdate (f : FnName)
  | refUpdateAndGet (f : FnName)
  | refUpdateSome (f : FnName)
  | refGetAndUpdateSome (f : FnName)
  | refUpdateSomeAndGet (f : FnName)
  | refModify (f : FnName)
  | refModifySome (f : FnName)
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
deriving DecidableEq

/-- The scope of a native operation's own data (`Program/ScopedOp.lean`). No native operation
carries a term yet: a read-modify-write row names its function (`FnName`), which has no
variable, and `Deferred.make`'s type arguments are types, which bind no term variable. So every
native operation is in scope at every level. State plan T3b gives the read-modify-write rows
binder terms, and this instance then checks each at `n + 1`, by `ScopedOp`'s convention. -/
instance : ScopedOp NativeOp := ⟨fun _ _ => true⟩

/-- No native operation carries a variable: the hypothesis the operation lift's scope lemma
(`Authoring.perform_scoped`) asks of an operation, discharged once for the native alphabet. -/
theorem NativeOp.scopedAt_eq_true (op : NativeOp) (n : Nat) : ScopedOp.scopedAt op n = true :=
  rfl

/-- Rows are unit content beside the program's bytes. -/
abbrev RowTable := List Row

namespace NativeOp

/-- The type arguments `Deferred.make` is printed with, as legacy target spellings
(`Row.typeArgs`), until T5 derives them from the instance. `Deferred.make` must be *called* with
them: the export's own parameters have defaults (`Deferred<unknown, never>`), so without them the
host types the cell at those defaults and rejects every later use (`E4-CHECK-CE-013`,
`Deferred.ts:171`). Only today's instance, `(nat, nat)`, has a spelling the readers read back.
Another instance carries the empty spelling, which no reading parses (`parseLegacy_empty`), so the
printer refuses the row by name (`PrintRefusal.typeSpelling "Deferred.make"`) and no reader yields
it (the state plan's T3a). -/
def deferredTypeArgs (value error : Ty) : List String :=
  if value = .nat ∧ error = .nat then ["number", "number"] else [""]

/-- The two external service handles of the host rows slice (service type codes 8 and 9,
`nativeServiceTy`; the package tables of `Program/Packages`): a SQL client and a key-value
store. Written once, here. -/
def sqlTarget : String := "SqlClient.SqlClient"
def sqlTy : Ty := .handle sqlTarget
def kvTarget : String := "KeyValueStore.KeyValueStore"
def kvTy : Ty := .handle kvTarget

/-- The printed name of a pure function, `Ref.update(ref, incr)`. -/
def fnSpelling : FnName → String
  | .incr => "incr"
  | .double => "double"
  | .zeroWhenPositive => "zeroWhenPositive"
  | .noChange => "noChange"
  | .takeAndBump => "takeAndBump"

/-- An absent external position cannot type as a callback. Its empty spelling is
outside the admitted table domain. -/
def externalPlaceholder : Row :=
  { name := "external", spelling := "", shape := .value, kind := .program,
    request := .never, answer := .never, cite := "", registration := .external }

/-- The scheduling kind of each operation: `.async` for `deferredAwait` and `sleep`, `.program`
for external placeholders, and `.sync` for every heap and deferred operation. Split off `row`
so the compiler and engine closure do not drag `Row` or `Ty` into native engine headers (plan 3.5). -/
@[simp] def kind : NativeOp → RowKind
  | deferredAwait | sleep => .async
  | external _ => .program
  | refMake | refGet | refSet | refGetAndSet | refSetAndGet
  | refUpdate _ | refGetAndUpdate _ | refUpdateAndGet _
  | refUpdateSome _ | refGetAndUpdateSome _ | refUpdateSomeAndGet _
  | refModify _ | refModifySome _
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

The `Ref` rows without a function and the `Deferred` rows are templates (decisions row 42): `A`
is `var 0` and `E` is `var 1`. Every request parameter first occurs as the direct argument of an
invariant handle (row 55), except `Ref.make`'s bare `A`, which the match binds to the whole
request. The eight read-modify-write rows stay closed at `refOf nat` until T3b. -/
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
  | refUpdate f =>
    ⟨"refUpdate", "Ref.update", .call, [fnSpelling f], kind op, .refOf .nat, .unit, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:1273-1276", [], .deferred⟩
  | refGetAndUpdate f =>
    ⟨"refGetAndUpdate", "Ref.getAndUpdate", .call, [fnSpelling f], kind op, .refOf .nat, .nat,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:496-501", [], .deferred⟩
  | refUpdateAndGet f =>
    ⟨"refUpdateAndGet", "Ref.updateAndGet", .call, [fnSpelling f], kind op, .refOf .nat, .nat,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1368", [], .deferred⟩
  | refUpdateSome f =>
    ⟨"refUpdateSome", "Ref.updateSome", .call, [fnSpelling f], kind op, .refOf .nat, .unit,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1502-1508", [], .deferred⟩
  | refGetAndUpdateSome f =>
    ⟨"refGetAndUpdateSome", "Ref.getAndUpdateSome", .call, [fnSpelling f], kind op, .refOf .nat,
      .nat, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:635-643", [], .deferred⟩
  | refUpdateSomeAndGet f =>
    ⟨"refUpdateSomeAndGet", "Ref.updateSomeAndGet", .call, [fnSpelling f], kind op, .refOf .nat,
      .nat, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1639-1646", [], .deferred⟩
  | refModify f =>
    ⟨"refModify", "Ref.modify", .call, [fnSpelling f], kind op, .refOf .nat, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:896-901", [], .deferred⟩
  | refModifySome f =>
    ⟨"refModifySome", "Ref.modifySome", .call, [fnSpelling f], kind op, .refOf .nat, .nat,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1159-1163", [], .deferred⟩
  | deferredMakeOf value error =>
    ⟨"deferredMakeOf", "Deferred.make", .call, [], kind op, .unit, .deferredOf value error,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:171", deferredTypeArgs value error,
      .deferred⟩
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
    ⟨"scopeMake", "Scope.make", .call, ["\"parallel\""], kind op, .unit, Ty.scope, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Scope.ts:240", [], .deferred⟩
  | sleep =>
    ⟨"sleep", "Effect.sleep", .call, [], kind op, .nat, .unit, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6114-6116", [], .deferred⟩
  | clockNow =>
    ⟨"clockNow", "Effect.currentTimeMillis", .value, [], kind op, .unit, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6118", [], .deferred⟩

  | external _ => externalPlaceholder

@[simp] theorem row_kind (op : NativeOp) : (row op).kind = kind op := by
  cases op
  case scopeMake s => cases s <;> rfl
  all_goals rfl

/-- The store operation a row runs on a request value; `none` is a request of the wrong
shape, which the compile turns into the `badName` defect (`Deep.Stores` does the same for a
continuation applied to the wrong value). Any value is a cell's initial value, a written value
and a deferred's success, as at the template rows (decisions row 42); a failed value becomes its
error through `errOf` (`Machine/Term.lean`, decisions row 120's carrier), which the checker keeps
inside the error alphabet by the deferred's formation rule (`Formation.HeadFormed`). A
read-modify-write row runs its name's lowering at the row's shape, with the environment `[]`
(`FnName.updateTerm` and its three siblings, `Machine/Stores.lean`). -/
def syncOpOf : NativeOp → Val → Option SyncOp
  | refMake, v => some (SyncOp.refMake v)
  | refGet, Val.cell ⟨k⟩ => some (SyncOp.refGet ⟨k⟩)
  | refSet, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refSet ⟨k⟩ v)
  | refGetAndSet, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refGetAndSet ⟨k⟩ v)
  | refSetAndGet, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refSetAndGet ⟨k⟩ v)
  | refUpdate f, Val.cell ⟨k⟩ => some (SyncOp.refUpdate ⟨k⟩ f.updateTerm [])
  | refGetAndUpdate f, Val.cell ⟨k⟩ => some (SyncOp.refGetAndUpdate ⟨k⟩ f.updateTerm [])
  | refUpdateAndGet f, Val.cell ⟨k⟩ => some (SyncOp.refUpdateAndGet ⟨k⟩ f.updateTerm [])
  | refUpdateSome f, Val.cell ⟨k⟩ => some (SyncOp.refUpdateSome ⟨k⟩ f.updateSomeTerm [])
  | refGetAndUpdateSome f, Val.cell ⟨k⟩ =>
    some (SyncOp.refGetAndUpdateSome ⟨k⟩ f.updateSomeTerm [])
  | refUpdateSomeAndGet f, Val.cell ⟨k⟩ =>
    some (SyncOp.refUpdateSomeAndGet ⟨k⟩ f.updateSomeTerm [])
  | refModify f, Val.cell ⟨k⟩ => some (SyncOp.refModify ⟨k⟩ f.modifyTerm [])
  | refModifySome f, Val.cell ⟨k⟩ => some (SyncOp.refModifySome ⟨k⟩ f.modifySomeTerm [])
  | deferredMakeOf _ _, Val.unit => some SyncOp.deferredMake
  | deferredIsDone, Val.promise ⟨k⟩ => some (SyncOp.deferredIsDone ⟨k⟩)
  | deferredPoll, Val.promise ⟨k⟩ => some (SyncOp.deferredPoll ⟨k⟩)
  | deferredSucceed, .list [Val.promise ⟨k⟩, v] =>
    some (SyncOp.deferredCompleteWith ⟨k⟩ (Completion.ofExit (Exit.success v)))
  | deferredFail, .list [Val.promise ⟨k⟩, v] =>
    some (SyncOp.deferredCompleteWith ⟨k⟩ (Completion.ofExit (Exit.failure (Cause.fail (errOf v)))))
  | scopeMake strategy, Val.unit => some (SyncOp.scopeMake strategy)
  | clockNow, Val.unit => some SyncOp.clockNow
  | _, _ => none

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

def fnNames : List Effect4.Machine.FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- One native operation per spelling key (`rowKey`, `Program/Table.lean`): every operation
whose row carries no type argument, each read-modify-write row at each of the five names (row by
row, the order the tools' profiles print), and `Deferred.make` at the one instance the faces
spell until T5 (`deferredTypeArgs`). No list holds every operation, since `deferredMakeOf`
ranges over `Ty`; a row's key does not depend on the type arguments its operation carries
(`NativeOp.rowKey_mem`), so the built-in keys are this list's. The table's collision check, the
reader's `nativeSpell` and the tools' enumerations read it. -/
def NativeOp.spelled : List NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet]
  ++ ([.refUpdate, .refGetAndUpdate, .refUpdateAndGet, .refUpdateSome, .refGetAndUpdateSome,
       .refUpdateSomeAndGet, .refModify, .refModifySome] :
      List (Effect4.Machine.FnName → NativeOp)).flatMap
      (fun con => fnNames.map con)
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
    dom := fun | .external i => decide (i < table.length) | _ => true,
    constAtom := nativeConstAtom }

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
