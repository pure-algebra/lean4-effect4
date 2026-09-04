import Effect4.Program.Typing
import Effect4.Machine.Stores

/-!
# Syntax.Native — the native row alphabet over the stores (lane A3, first cut)

Plan: `docs/research/2026-09-04-eff-compile.md` §1-§2. The native route performs the
standard library's store operations (`Effect4/StdLib/Links.lean`: `Ref.*`, `Deferred.*`,
`Scope.make`) against the reference machine's stores (`Effect4/Deep/Stores.lean`). This
module owns:

* `NativeOp`, the positions of that table, each with its `Row` (spelling, shape, kind, the
  request and answer types, the rc.112 line);
* the value side: terms evaluate to the stores' `Val`, tuples through the reified-exit list
  cells (the one list-shaped `Val`), the pure atoms as a closed table;
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

/-- A tuple of values, spelled with the reified-exit list cells: a `List Val` field would make
`Val` a nested inductive (`Effect4/Deep/Stores.lean`, state note §3.5), and `exitNil`/`exitCons`
are the list cells the alphabet already has. -/
def Val.tuple : List Val → Val
  | [] => Val.exitNil
  | v :: rest => Val.exitCons v (Val.tuple rest)

def Val.tuple? : Val → Option (List Val)
  | Val.exitNil => some []
  | Val.exitCons head tail => (Val.tuple? tail).map (head :: ·)
  | _ => none

theorem Val.tuple?_tuple (vs : List Val) : Val.tuple? (Val.tuple vs) = some vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp [Val.tuple, Val.tuple?, ih]

/-- A literal as a machine value. Strings are not machine values on the native route (the
alphabet has none); a `str` literal is refused here and admitted only by the typing of the
service route's spellings. -/
def Lit.toVal : Lit → Option Val
  | .unit => some Val.unit
  | .nat n => some (Val.nat n)
  | .bool b => some (Val.bool b)
  | .str _ => none

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
  | "fst", [Val.exitCons a _] => some a
  | "snd", [Val.exitCons _ (Val.exitCons b _)] => some b
  | _, _ => none

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
  | _, _ => none

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
deriving DecidableEq

namespace NativeOp

/-- The handle types this cut spells: cells hold numbers, deferreds carry numbers and fail
with numbers (the error alphabet's `Err.tag`). -/
def refTy : Ty := .handle "Ref.Ref<number>"
def deferredTy : Ty := .handle "Deferred.Deferred<number, number>"

/-- The printed name of a pure function, `Ref.update(ref, incr)`. -/
def fnSpelling : FnName → String
  | .incr => "incr"
  | .double => "double"
  | .zeroWhenPositive => "zeroWhenPositive"
  | .noChange => "noChange"
  | .takeAndBump => "takeAndBump"

/-- The row of each operation. -/
def row : NativeOp → Row
  | refMake => ⟨"refMake", "Ref.make", .call, [], .sync, .nat, refTy, .never, [], "Ref.ts:173"⟩
  | refGet => ⟨"refGet", "Ref.get", .call, [], .sync, refTy, .nat, .never, [], "Ref.ts:200"⟩
  | refSet =>
    ⟨"refSet", "Ref.set", .call, [], .sync, .prod refTy .nat, refTy, .never, [], "Ref.ts:306-307"⟩
  | refGetAndSet =>
    ⟨"refGetAndSet", "Ref.getAndSet", .call, [], .sync, .prod refTy .nat, .nat, .never, [],
      "Ref.ts:399-404"⟩
  | refSetAndGet =>
    ⟨"refSetAndGet", "Ref.setAndGet", .call, [], .sync, .prod refTy .nat, .nat, .never, [],
      "Ref.ts:747"⟩
  | refUpdate f =>
    ⟨"refUpdate", "Ref.update", .call, [fnSpelling f], .sync, refTy, .unit, .never, [],
      "Ref.ts:1273-1276"⟩
  | refGetAndUpdate f =>
    ⟨"refGetAndUpdate", "Ref.getAndUpdate", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "Ref.ts:496-501"⟩
  | refUpdateAndGet f =>
    ⟨"refUpdateAndGet", "Ref.updateAndGet", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "Ref.ts:1368"⟩
  | refUpdateSome f =>
    ⟨"refUpdateSome", "Ref.updateSome", .call, [fnSpelling f], .sync, refTy, .unit, .never, [],
      "Ref.ts:1502-1508"⟩
  | refGetAndUpdateSome f =>
    ⟨"refGetAndUpdateSome", "Ref.getAndUpdateSome", .call, [fnSpelling f], .sync, refTy, .nat,
      .never, [], "Ref.ts:635-643"⟩
  | refUpdateSomeAndGet f =>
    ⟨"refUpdateSomeAndGet", "Ref.updateSomeAndGet", .call, [fnSpelling f], .sync, refTy, .nat,
      .never, [], "Ref.ts:1639-1646"⟩
  | refModify f =>
    ⟨"refModify", "Ref.modify", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "Ref.ts:896-901"⟩
  | refModifySome f =>
    ⟨"refModifySome", "Ref.modifySome", .call, [fnSpelling f], .sync, refTy, .nat, .never, [],
      "Ref.ts:1159-1163"⟩
  | deferredMake =>
    ⟨"deferredMake", "Deferred.make", .call, [], .sync, .unit, deferredTy, .never, [],
      "Deferred.ts:171"⟩
  | deferredIsDone =>
    ⟨"deferredIsDone", "Deferred.isDone", .call, [], .sync, deferredTy, .bool, .never, [],
      "Deferred.ts:1382"⟩
  | deferredPoll =>
    ⟨"deferredPoll", "Deferred.poll", .call, [], .sync, deferredTy, .bool, .never, [],
      "Deferred.ts:1414-1416"⟩
  | deferredSucceed =>
    ⟨"deferredSucceed", "Deferred.succeed", .call, [], .sync, .prod deferredTy .nat, .bool, .never,
      [], "Deferred.ts:1514"⟩
  | deferredFail =>
    ⟨"deferredFail", "Deferred.fail", .call, [], .sync, .prod deferredTy .nat, .bool, .never, [],
      "Deferred.ts:669"⟩
  | deferredAwait =>
    ⟨"deferredAwait", "Deferred.await", .call, [], .async, deferredTy, .nat, .nat, [],
      "Deferred.ts:173-186"⟩
  | scopeMake .sequential =>
    ⟨"scopeMake", "Scope.make", .call, [], .sync, .unit, Ty.scope, .never, [],
      "internal/effect.ts:3914-3922"⟩
  | scopeMake .parallel =>
    ⟨"scopeMake", "Scope.make", .call, ["\"parallel\""], .sync, .unit, Ty.scope, .never, [],
      "internal/effect.ts:3914-3922"⟩

/-- The store operation a row runs on a request value; `none` is a request of the wrong
shape, which the compile turns into the `badName` defect (`Deep.Stores` does the same for a
continuation applied to the wrong value). -/
def syncOpOf : NativeOp → Val → Option SyncOp
  | refMake, Val.nat n => some (SyncOp.refMake (Val.nat n))
  | refGet, Val.cell k => some (SyncOp.refGet k)
  | refSet, Val.exitCons (Val.cell k) (Val.exitCons v Val.exitNil) => some (SyncOp.refSet k v)
  | refGetAndSet, Val.exitCons (Val.cell k) (Val.exitCons v Val.exitNil) =>
    some (SyncOp.refGetAndSet k v)
  | refSetAndGet, Val.exitCons (Val.cell k) (Val.exitCons v Val.exitNil) =>
    some (SyncOp.refSetAndGet k v)
  | refUpdate f, Val.cell k => some (SyncOp.refUpdate k f)
  | refGetAndUpdate f, Val.cell k => some (SyncOp.refGetAndUpdate k f)
  | refUpdateAndGet f, Val.cell k => some (SyncOp.refUpdateAndGet k f)
  | refUpdateSome f, Val.cell k => some (SyncOp.refUpdateSome k f)
  | refGetAndUpdateSome f, Val.cell k => some (SyncOp.refGetAndUpdateSome k f)
  | refUpdateSomeAndGet f, Val.cell k => some (SyncOp.refUpdateSomeAndGet k f)
  | refModify f, Val.cell k => some (SyncOp.refModify k f)
  | refModifySome f, Val.cell k => some (SyncOp.refModifySome k f)
  | deferredMake, Val.unit => some SyncOp.deferredMake
  | deferredIsDone, Val.promise k => some (SyncOp.deferredIsDone k)
  | deferredPoll, Val.promise k => some (SyncOp.deferredPoll k)
  | deferredSucceed, Val.exitCons (Val.promise k) (Val.exitCons (Val.nat n) Val.exitNil) =>
    some (SyncOp.deferredCompleteWith k (Completion.ofExit (Exit.success (Val.nat n))))
  | deferredFail, Val.exitCons (Val.promise k) (Val.exitCons (Val.nat n) Val.exitNil) =>
    some (SyncOp.deferredCompleteWith k (Completion.ofExit (Exit.failure (Cause.fail (Err.tag n)))))
  | scopeMake strategy, Val.unit => some (SyncOp.scopeMake strategy)
  | _, _ => none

/-- The deferred an `await` row registers on. -/
def awaitCellOf : Val → Option DeferredKey
  | Val.promise k => some k
  | _ => none

end NativeOp

/-- The `Scope` service key of the native signature. -/
def nativeScopeKey : ServiceKey := ⟨⟨0⟩, ⟨0⟩⟩

/-- The native signature: the rows above and the atoms, for `typeOf` and `print`. -/
def nativeSignature : Signature NativeOp := ⟨NativeOp.row, nativeAtomTy, nativeScopeKey⟩

/-- A program of the native route. -/
abbrev NativeEff := Eff NativeOp

end Effect4.Program
