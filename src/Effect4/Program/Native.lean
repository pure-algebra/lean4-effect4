import Effect4.Program.Typing
import Effect4.Machine.Stores

/-!
# Syntax.Native — the native row alphabet over the stores (lane A3, first cut)

Plan: `docs/research/2026-09-04-eff-compile.md` §1-§2. The native route performs the
standard library's store operations (`git:62c04d9:src/Effect4/StdLib/Links.lean`: `Ref.*`, `Deferred.*`,
`Scope.make`) against the reference machine's stores (`src/Effect4/Machine/Stores.lean`). This
module owns:

* `NativeOp`, the positions of that table, each with its `Row` (spelling, shape, kind, the
  request and answer types, the rc.112 line);
* the value side: terms evaluate to the stores' `Val`, tuples as the carrier's `list` (the
  one list-shaped `Val`, the frame an exit list is too), the pure atoms as a closed table;
* `SyncOp.ofRow`, the decoding of a row and a request value into the store operation the
  machine runs.

The read-modify-write rows carry their pure function as a `FnName` *in the operation*
(`Ref.update(ref, incr)` is the row `refUpdate FnName.incr` on the request `ref`): rc.112
takes a JavaScript function, DB-02 forbids storing one, and the store already interprets the
names. The Layer and Context rows (`RowKind.program`) are not in this first cut.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## Values -/

/-- A tuple of values: the carrier's `list` frame, the one list-shaped value
(`src/Effect4/Machine/Stores.lean`; an awaited exit list, `exitsVal`, is the same frame). -/
abbrev Val.tuple (values : List Val) : Val := .list values

def Val.tuple? : Val → Option (List Val)
  | .list values => some values
  | _ => none

theorem Val.tuple?_tuple (vs : List Val) : Val.tuple? (Val.tuple vs) = some vs := rfl

theorem Val.tuple?_exact {v : Val} {vs : List Val} (h : Val.tuple? v = some vs) : v = Val.tuple vs := by
  unfold Val.tuple? at h
  split at h
  · injection h with h
    rw [h]
  · exact nomatch h

/-- A literal as a machine value: `unit`, `nat` and `bool` against the carrier's frames, and
`str` against its `string` frame. Strings are machine values on the native route since the
host rows slice (2026-09-08, DB-15): a canonical row's request and answer carry them, so a
`str` literal evaluates like every other literal (`Lit.toVal_isSome`,
`src/Effect4/Laws/Program/Typed.lean`). -/
def Lit.toVal : Lit → Option Val
  | .unit => some Val.unit
  | .nat n => some (Val.nat n)
  | .bool b => some (Val.bool b)
  | .str s => some (Val.str s)

/-- `strings(s₁, …, sₙ)`: the one list a term can build, a list of strings, for the bind
parameters of a host row (DB-15: `list string`, every parameter JSON text). Variadic, and
typed at strings so that `strings()` has a type. -/
def stringsAtom (vs : List Val) : Option Val :=
  if vs.all (fun | Val.str _ => true | _ => false) then some (Val.list vs) else none

/-- The pure atoms of the native route: a closed table, interpreted here, typed by
`nativeAtomTy`. -/
def nativeAtom : String → List Val → Option Val
  | "succ", [Val.nat n] => some (Val.nat (n + 1))
  | "pred", [Val.nat n] => some (Val.nat (n - 1))
  | "isZero", [Val.nat n] => some (Val.bool (n = 0))
  | "not", [Val.bool b] => some (Val.bool (!b))
  | "add", [Val.nat a, Val.nat b] => some (Val.nat (a + b))
  | "lt", [Val.nat a, Val.nat b] => some (Val.bool (decide (a < b)))
  | "eq", [Val.nat a, Val.nat b] => some (Val.bool (a = b))
  | "pair", [a, b] => some (Val.tuple [a, b])
  | "fst", [.list (a :: _)] => some a
  | "snd", [.list (_ :: b :: _)] => some b
  | "strings", vs => stringsAtom vs
  | _, _ => none

theorem nativeAtom_strings (vs : List Val) : nativeAtom "strings" vs = stringsAtom vs := rfl

/-- The atoms' types, by their argument types. -/
def nativeAtomTy : String → List Ty → Option Ty
  | "succ", [.nat] => some .nat
  | "pred", [.nat] => some .nat
  | "isZero", [.nat] => some .bool
  | "not", [.bool] => some .bool
  | "add", [.nat, .nat] => some .nat
  | "lt", [.nat, .nat] => some .bool
  | "eq", [.nat, .nat] => some .bool
  | "pair", [a, b] => some (.prod a b)
  | "fst", [.prod a _] => some a
  | "snd", [.prod _ b] => some b
  | "strings", tys => if tys.all (· == .string) then some (.list .string) else none
  | _, _ => none

theorem nativeAtomTy_strings (tys : List Ty) :
    nativeAtomTy "strings" tys = if tys.all (· == .string) then some (.list .string) else none := rfl

mutual
  /-- A term's value in a positional environment. -/
  def evalTerm (env : List Val) : Term → Option Val
    | .var index => env[index]?
    | .lit value => value.toVal
    | .app atom args => do
      let values ← evalTerms env args
      nativeAtom atom values
  def evalTerms (env : List Val) : Terms → Option (List Val)
    | .nil => some []
    | .cons head tail => do
      let v ← evalTerm env head
      let rest ← evalTerms env tail
      some (v :: rest)
end

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
  | deferredMake
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
deriving DecidableEq

/-- Rows are unit content beside the program's bytes. -/
abbrev RowTable := List Row

namespace NativeOp

/-- The handle types this cut spells: cells hold numbers, deferreds carry numbers and fail
with numbers (the error alphabet's `Err.tag`). Each spelling is written once, here; the
typing arms (`Program/Typed.lean`) and the service table below read these names. -/
def refTarget : String := "Ref.Ref<number>"
def refTy : Ty := .handle refTarget
/-- The type arguments of the `Deferred` handle this cut spells, in order. They are what
`Deferred.make` must be *called* with: the export's own parameters have defaults
(`Deferred<unknown, never>`), so without them the host types the cell at those defaults and
rejects every later use at this row's declared types (`E4-CHECK-CE-013`,
`Deferred.ts:171`). -/
def deferredTypeArgs : List String := ["number", "number"]
def deferredTarget : String := "Deferred.Deferred<number, number>"
def deferredTy : Ty := .handle deferredTarget
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

/-- The row of each operation. -/
def row : NativeOp → Row
  | refMake => ⟨"refMake", "Ref.make", .call, [], .sync, .nat, refTy, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:173", [], .deferred⟩
  | refGet => ⟨"refGet", "Ref.get", .call, [], .sync, refTy, .nat, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:200", [], .deferred⟩
  | refSet =>
    ⟨"refSet", "Ref.set", .tupleCall, [], .sync, .prod refTy .nat, refTy, .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:306-307", [], .deferred⟩
  | refGetAndSet =>
    ⟨"refGetAndSet", "Ref.getAndSet", .tupleCall, [], .sync, .prod refTy .nat, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:399-404", [], .deferred⟩
  | refSetAndGet =>
    ⟨"refSetAndGet", "Ref.setAndGet", .tupleCall, [], .sync, .prod refTy .nat, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:747", [], .deferred⟩
  | refUpdate f =>
    ⟨"refUpdate", "Ref.update", .call, [fnSpelling f], .sync, refTy, .unit, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:1273-1276", [], .deferred⟩
  | refGetAndUpdate f =>
    ⟨"refGetAndUpdate", "Ref.getAndUpdate", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:496-501", [], .deferred⟩
  | refUpdateAndGet f =>
    ⟨"refUpdateAndGet", "Ref.updateAndGet", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:1368", [], .deferred⟩
  | refUpdateSome f =>
    ⟨"refUpdateSome", "Ref.updateSome", .call, [fnSpelling f], .sync, refTy, .unit, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:1502-1508", [], .deferred⟩
  | refGetAndUpdateSome f =>
    ⟨"refGetAndUpdateSome", "Ref.getAndUpdateSome", .call, [fnSpelling f], .sync, refTy, .nat,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:635-643", [], .deferred⟩
  | refUpdateSomeAndGet f =>
    ⟨"refUpdateSomeAndGet", "Ref.updateSomeAndGet", .call, [fnSpelling f], .sync, refTy, .nat,
      .never, [], "vendor/effect-4.0.0-rc.112/src/Ref.ts:1639-1646", [], .deferred⟩
  | refModify f =>
    ⟨"refModify", "Ref.modify", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:896-901", [], .deferred⟩
  | refModifySome f =>
    ⟨"refModifySome", "Ref.modifySome", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Ref.ts:1159-1163", [], .deferred⟩
  | deferredMake =>
    ⟨"deferredMake", "Deferred.make", .call, [], .sync, .unit, deferredTy, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:171", deferredTypeArgs, .deferred⟩
  | deferredIsDone =>
    ⟨"deferredIsDone", "Deferred.isDone", .call, [], .sync, deferredTy, .bool, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:1382", [], .deferred⟩
  | deferredPoll =>
    ⟨"deferredPoll", "Deferred.poll", .call, [], .sync, deferredTy, .bool, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:1414-1416", [], .deferred⟩
  | deferredSucceed =>
    ⟨"deferredSucceed", "Deferred.succeed", .tupleCall, [], .sync, .prod deferredTy .nat, .bool, .never,
      [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:1514", [], .deferred⟩
  | deferredFail =>
    ⟨"deferredFail", "Deferred.fail", .tupleCall, [], .sync, .prod deferredTy .nat, .bool, .never, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:669", [], .deferred⟩
  | deferredAwait =>
    ⟨"deferredAwait", "Deferred.await", .call, [], .async, deferredTy, .nat, .nat, [],
      "vendor/effect-4.0.0-rc.112/src/Deferred.ts:173-186", [], .deferred⟩
  | scopeMake .sequential =>
    ⟨"scopeMake", "Scope.make", .call, [], .sync, .unit, Ty.scope, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3914-3922", [], .deferred⟩
  | scopeMake .parallel =>
    ⟨"scopeMake", "Scope.make", .call, ["\"parallel\""], .sync, .unit, Ty.scope, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3914-3922", [], .deferred⟩
  | sleep =>
    ⟨"sleep", "Effect.sleep", .call, [], .async, .nat, .unit, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6114-6116", [], .deferred⟩
  | clockNow =>
    ⟨"clockNow", "Effect.currentTimeMillis", .value, [], .sync, .unit, .nat, .never, [],
      "vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6118", [], .deferred⟩

  | external _ => externalPlaceholder

/-- The store operation a row runs on a request value; `none` is a request of the wrong
shape, which the compile turns into the `badName` defect (`Deep.Stores` does the same for a
continuation applied to the wrong value). -/
def syncOpOf : NativeOp → Val → Option SyncOp
  | refMake, Val.nat n => some (SyncOp.refMake (Val.nat n))
  | refGet, Val.cell ⟨k⟩ => some (SyncOp.refGet ⟨k⟩)
  | refSet, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refSet ⟨k⟩ v)
  | refGetAndSet, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refGetAndSet ⟨k⟩ v)
  | refSetAndGet, .list [Val.cell ⟨k⟩, v] => some (SyncOp.refSetAndGet ⟨k⟩ v)
  | refUpdate f, Val.cell ⟨k⟩ => some (SyncOp.refUpdate ⟨k⟩ f)
  | refGetAndUpdate f, Val.cell ⟨k⟩ => some (SyncOp.refGetAndUpdate ⟨k⟩ f)
  | refUpdateAndGet f, Val.cell ⟨k⟩ => some (SyncOp.refUpdateAndGet ⟨k⟩ f)
  | refUpdateSome f, Val.cell ⟨k⟩ => some (SyncOp.refUpdateSome ⟨k⟩ f)
  | refGetAndUpdateSome f, Val.cell ⟨k⟩ => some (SyncOp.refGetAndUpdateSome ⟨k⟩ f)
  | refUpdateSomeAndGet f, Val.cell ⟨k⟩ => some (SyncOp.refUpdateSomeAndGet ⟨k⟩ f)
  | refModify f, Val.cell ⟨k⟩ => some (SyncOp.refModify ⟨k⟩ f)
  | refModifySome f, Val.cell ⟨k⟩ => some (SyncOp.refModifySome ⟨k⟩ f)
  | deferredMake, Val.unit => some SyncOp.deferredMake
  | deferredIsDone, Val.promise ⟨k⟩ => some (SyncOp.deferredIsDone ⟨k⟩)
  | deferredPoll, Val.promise ⟨k⟩ => some (SyncOp.deferredPoll ⟨k⟩)
  | deferredSucceed, .list [Val.promise ⟨k⟩, Val.nat n] =>
    some (SyncOp.deferredCompleteWith ⟨k⟩ (Completion.ofExit (Exit.success (Val.nat n))))
  | deferredFail, .list [Val.promise ⟨k⟩, Val.nat n] =>
    some (SyncOp.deferredCompleteWith ⟨k⟩ (Completion.ofExit (Exit.failure (Cause.fail (Err.tag n)))))
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

/-- The native signature's service table (the join, 2026-09-07), read off the key: the ambient
`Scope` under its reserved key, nothing under the other reserved names (`Env.firstFreeName`:
the scheduler's two references and `CurrentMemoMap` are the machine's, not a program's), and
for a free name the carrier its type code spells — `4` a number, `5` a boolean, `6` unit, `7`
a `Ref.Ref<number>` handle, `8` a `SqlClient.SqlClient` handle and `9` a
`KeyValueStore.KeyValueStore` handle. A key is typed by its own data, which is what `Machine/Key.lean`
means a `ServiceTypeCode` to be read as. -/
def nativeServiceTy (key : ServiceKey) : Option Ty :=
  if key = nativeScopeKey then some Ty.scope
  else if key.name.value < Effect4.Machine.Env.firstFreeName then none
  else
    match key.service.value with
    | 4 => some .nat
    | 5 => some .bool
    | 6 => some .unit
    | 7 => some NativeOp.refTy
    | 8 => some NativeOp.sqlTy
    | 9 => some NativeOp.kvTy
    | _ => none

def fnNames : List Effect4.Machine.FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- Every native operation, once. -/
def NativeOp.all : List NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet]
  ++ fnNames.flatMap (fun f =>
      [.refUpdate f, .refGetAndUpdate f, .refUpdateAndGet f, .refUpdateSome f,
       .refGetAndUpdateSome f, .refUpdateSomeAndGet f, .refModify f, .refModifySome f])
  ++ [.deferredMake, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail,
      .deferredAwait, .scopeMake .sequential, .scopeMake .parallel, .sleep, .clockNow]

/-- An external index reads its supplied row. Built-ins keep their original row. -/
def nativeRowOf (table : RowTable) : NativeOp → Row
  | .external i => (table[i]?).getD NativeOp.externalPlaceholder
  | op => op.row

@[simp] theorem nativeRowOf_nil (op : NativeOp) : nativeRowOf [] op = op.row := by
  cases op <;> rfl

/-- The native signature: the rows above, the atoms and the service table, for `typeOf` and
`print`. -/
def nativeSignature (table : RowTable := []) : Signature NativeOp :=
  { rowOf := nativeRowOf table, atomOf := nativeAtomTy, scopeKey := nativeScopeKey,
    serviceTy := nativeServiceTy,
    dom := fun | .external i => decide (i < table.length) | _ => true }

/-- A program of the native route. -/
abbrev NativeEff := Eff NativeOp

end Effect4.Program
