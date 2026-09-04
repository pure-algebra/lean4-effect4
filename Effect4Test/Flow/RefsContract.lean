/-
Contract packet: the `Refs` family (`docs/TRACE-DAG.md`, the `refs` edge),
lowering lane L3.

Kernel receipts for the Lean face: the twelve rows of rc.112's `Ref` surface,
the exact rows of each of the eleven goldens under `generated/traces/ref/`, and
the projection lemma that says the handler *is* the Ref heap's step.

These are `#guard`s, evaluated by the kernel, not proofs. Nothing here is a
statement about the host: the same rows are compared with rc.112 by
`scripts/check-trace-host.sh`'s `ref` section through
`harness/trace/ref-tail.ts`, and that comparison is evidence, never a theorem.

The corpus is imported rather than restated. A second copy of the handler in
this file could drift from the one the goldens are generated from and every
receipt here would still pass, which would make the whole battery worthless.
Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Stateful.RefFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.RefsContract

open Effect4.RefFamily

#check @Effect4.RefFamily.Refs
#check (@Effect4.RefFamily.Refs.rows : Effect4.Target.EffectV4.ServiceRow)
#check @Effect4.RefFamily.refStep
#check @Effect4.RefFamily.refsLive
#check @Effect4.RefFamily.erefsLive
#check @Effect4.RefFamily.refGoldenLog

/-! ## The twelve rows, one per rc.112 entry point -/

#guard Refs.rows.name = "Refs"

#guard Refs.rows.ops.map (·.name) =
  [ "make", "get", "set", "getAndSet", "setAndGet", "update", "getAndUpdate", "updateAndGet"
  , "modify", "getAndUpdateSome", "updateSomeAndGet", "modifySome" ]

-- The declared spellings the generated module is built from. `set` answers the
-- cell (`Ref.ts:307`, `MutableRef.ts:1067-1070`) and `update` answers `void`
-- (`Ref.ts:1273-1276`); the pair is the whole content of
-- `ref.set-void-returns-cell`. counterexample: E4-SEM-CE-009
#guard Refs.rows.ops.map (fun row => (row.name, row.tsAnswer)) =
  [ ("make", "Ref.Ref<number>"), ("get", "number"), ("set", "Ref.Ref<number>")
  , ("getAndSet", "number"), ("setAndGet", "number"), ("update", "void")
  , ("getAndUpdate", "number"), ("updateAndGet", "number"), ("modify", "number")
  , ("getAndUpdateSome", "number"), ("updateSomeAndGet", "number"), ("modifySome", "number") ]

-- Every read-modify-write row takes a *named* function, spelled `RefFn` on the
-- host: DB-02 keeps a Lean function out of canonical content, so the argument
-- is a table index and never a closure.
#guard Refs.rows.ops.map (fun row => (row.name, row.tsParams.map Prod.snd)) =
  [ ("make", ["number"])
  , ("get", ["Ref.Ref<number>"])
  , ("set", ["Ref.Ref<number>", "number"])
  , ("getAndSet", ["Ref.Ref<number>", "number"])
  , ("setAndGet", ["Ref.Ref<number>", "number"])
  , ("update", ["Ref.Ref<number>", "RefFn"])
  , ("getAndUpdate", ["Ref.Ref<number>", "RefFn"])
  , ("updateAndGet", ["Ref.Ref<number>", "RefFn"])
  , ("modify", ["Ref.Ref<number>", "RefFn"])
  , ("getAndUpdateSome", ["Ref.Ref<number>", "RefFn"])
  , ("updateSomeAndGet", ["Ref.Ref<number>", "RefFn"])
  , ("modifySome", ["Ref.Ref<number>", "RefFn"]) ]

#guard ERefs.rows.ops.map (fun row => (row.name, row.tsAnswer)) =
  [ ("make", "Ref.Ref<number>")
  , ("tryTake", "Result.Result<number, string>")
  , ("get", "number") ]

-- Every operation but `make` takes the handle first.
#guard (Refs.rows.ops.filter (fun row => row.name != "make")).all
  (fun row => row.tsParams.head?.map Prod.snd == some "Ref.Ref<number>")

-- No operation of either family declares an error channel: every failure in
-- this lane is data, and no golden of it ends `{"failure":…}`.
#guard (Refs.rows.ops ++ ERefs.rows.ops).all (fun row => row.error.isNone)

/-! ## The named functions, on both faces

`RefFns` is one declaration per function: the Lean handle, the host index, and
the row that renders it into `atoms.ts`. -/

#guard RefFns.rows.map (·.name) =
  ["fnIncr", "fnDouble", "fnTakeAndBump", "fnNoChange", "fnZeroWhenPositive"]

#guard RefFns.rows.map (·.tsAnswer) = ["RefFn", "RefFn", "RefFn", "RefFn", "RefFn"]

#guard RefFns.rows.map (·.body) = ["0", "1", "2", "3", "4"]

-- The Lean atom and the host body name the same table position.
#guard [fnIncr 0, fnDouble 0, fnTakeAndBump 0, fnNoChange 0, fnZeroWhenPositive 0].map
    Effect4.Meta.Handle.index = [0, 1, 2, 3, 4]

-- And reading a handle back is the identity on the table.
#guard [RefFn.incr, RefFn.double, RefFn.takeAndBump, RefFn.noChange, RefFn.zeroWhenPositive].all
  (fun f => RefFn.ofHandle ⟨f.index⟩ == f)

/-! ## The handler is the heap's step

The projection lemma of `Effect4/Stateful/RefFamily.lean`, cited here as the
shape every golden below rests on. -/

#check @Effect4.RefFamily.refsLive_is_refStep
#check @Effect4.RefFamily.refsLive_of_step
#check @Effect4.RefFamily.refStep_make
#check @Effect4.RefFamily.refStep_set
#check @Effect4.RefFamily.refStep_update
#check @Effect4.RefFamily.set_answer_ne_update_answer
#check @Effect4.RefFamily.refStep_setAndGet
#check @Effect4.RefFamily.refStep_modifySome_none
#check @Effect4.RefFamily.refStep_updateSomeAndGet_none
#check @Effect4.RefFamily.updateSomeAndGet_ne_getAndUpdateSome

/-! ## The corpus -/

#guard refPrograms.length == 11

#guard refPrograms.map (·.name) ==
  [ "makeGet", "setGet", "updateTwice", "modifyOld", "getAndSetOld", "setAndGet", "updateAndGet"
  , "someContrast", "modifySomeNoReread", "twoRefs", "takeUnderflow" ]

/-! ## The rows of each golden

The wire rows of one program's Lean log are written inline in each receipt: a
`def` rendering rows would reach `Classical.choice` through the renderer and the
axiom gate scans test declarations too, while a `#guard` is a command and not a
declaration. -/

/-- The log the `ref-golden` arm emits for one program. An unknown name answers
a row no golden can carry, so a misspelt receipt fails instead of passing
vacuously. -/
def logOf (name : String) : Effect4.Trace.Log :=
  match refPrograms.find? (·.name == name) with
  | some entry => entry.log
  | none => [.op "no-such-ref-program" .unit]

-- `ref/makeGet.tsv`. The handle a `make` answers is the one the `get` names:
-- index 0 on both faces, because the ref only ever leaves the host as the
-- answer of the `make` that produced it.
#guard logOf "makeGet" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "get" (.nat 0), .answer "get" (.nat 7)
  , .done (.success (.nat 7)) ]

-- `ref/setGet.tsv`. `set` answers the very cell it wrote, which is what
-- `MutableRef.set` returns (`MutableRef.ts:1067-1070`), and the read after it
-- sees the write. counterexample: E4-SEM-CE-009
#guard logOf "setGet" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "set" (.pair (.nat 0) (.nat 9)), .answer "set" (.nat 0)
  , .op "get" (.nat 0), .answer "get" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/updateTwice.tsv`. Two identical requests naming `fnIncr`, two identical
-- unit answers, and a read that shows both landed. `Ref.update`'s arrow is a
-- block, so `undefined` really is its value (`Ref.ts:1273-1276`).
#guard logOf "updateTwice" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "update" (.pair (.nat 0) (.nat 0)), .answer "update" .unit
  , .op "update" (.pair (.nat 0) (.nat 0)), .answer "update" .unit
  , .op "get" (.nat 0), .answer "get" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/modifyOld.tsv`. `modify` answers the function's first component (7) and
-- the read after it shows the second (8): `fnTakeAndBump` is `a ↦ [a, a + 1]`
-- (`Ref.ts:896-901`). counterexample: E4-SEM-CE-015
#guard logOf "modifyOld" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "modify" (.pair (.nat 0) (.nat 2)), .answer "modify" (.nat 7)
  , .op "get" (.nat 0), .answer "get" (.nat 8)
  , .done (.success (.nat 7)) ]

-- `ref/getAndSetOld.tsv`. The same separation for `getAndSet`.
#guard logOf "getAndSetOld" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "getAndSet" (.pair (.nat 0) (.nat 100)), .answer "getAndSet" (.nat 7)
  , .op "get" (.nat 0), .answer "get" (.nat 100)
  , .done (.success (.nat 7)) ]

-- `ref/setAndGet.tsv`. `setAndGet` succeeds with the assignment expression, so
-- it answers the value written and never reads the cell twice (`Ref.ts:747`).
#guard logOf "setAndGet" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "setAndGet" (.pair (.nat 0) (.nat 9)), .answer "setAndGet" (.nat 9)
  , .op "get" (.nat 0), .answer "get" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/updateAndGet.tsv`. `getAndUpdate` answers the value before the write
-- (`Ref.ts:496-501`) and `updateAndGet` the value after it (`Ref.ts:1368`), on
-- the same named function.
#guard logOf "updateAndGet" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "getAndUpdate" (.pair (.nat 0) (.nat 0)), .answer "getAndUpdate" (.nat 7)
  , .op "updateAndGet" (.pair (.nat 0) (.nat 0)), .answer "updateAndGet" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/someContrast.tsv`. `getAndUpdateSome` answers the value it read
-- (`Ref.ts:635-643`); `updateSomeAndGet` on a point the partial function does
-- not change answers that same value and writes nothing (`Ref.ts:1639-1646`).
#guard logOf "someContrast" =
  [ .op "make" (.nat 3), .answer "make" (.nat 0)
  , .op "getAndUpdateSome" (.pair (.nat 0) (.nat 4)), .answer "getAndUpdateSome" (.nat 3)
  , .op "updateSomeAndGet" (.pair (.nat 0) (.nat 4)), .answer "updateSomeAndGet" (.nat 0)
  , .done (.success (.nat 0)) ]

-- `ref/modifySomeNoReread.tsv`. On `None`, `modifySome` writes back the value
-- `modify` already read, never a re-read (`Ref.ts:1159-1163`).
#guard logOf "modifySomeNoReread" =
  [ .op "make" (.nat 1), .answer "make" (.nat 0)
  , .op "modifySome" (.pair (.nat 0) (.nat 3)), .answer "modifySome" (.nat 1)
  , .op "get" (.nat 0), .answer "get" (.nat 1)
  , .done (.success (.nat 1)) ]

-- `ref/twoRefs.tsv`. Two handles, named 0 and 1 in creation order; a write
-- through the first is invisible through the second.
#guard logOf "twoRefs" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "make" (.nat 8), .answer "make" (.nat 1)
  , .op "set" (.pair (.nat 0) (.nat 0)), .answer "set" (.nat 0)
  , .op "get" (.nat 1), .answer "get" (.nat 8)
  , .op "update" (.pair (.nat 1) (.nat 0)), .answer "update" .unit
  , .op "get" (.nat 0), .answer "get" (.nat 0)
  , .op "get" (.nat 1), .answer "get" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/takeUnderflow.tsv`. The refusal is an answer, not an abort: the program
-- continues, and the read after it sees exactly what the successful take left.
#guard logOf "takeUnderflow" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "tryTake" (.pair (.nat 0) (.nat 2)), .answer "tryTake" (.pair (.bool true) (.nat 5))
  , .op "tryTake" (.pair (.nat 0) (.nat 9))
  , .answer "tryTake" (.pair (.bool false) (.str "underflow"))
  , .op "get" (.nat 0), .answer "get" (.nat 5)
  , .done (.success (.nat 5)) ]

/-! ## What the family fixes about a handle -/

-- A handle crosses the wire as its index and as nothing else.
#guard Refs.encodeAnswer .make ⟨3⟩ = Effects.Trace.Val.nat 3

-- A request carrying a handle and a number is the pair, in that order; a
-- request carrying two handles is the pair of their indices.
#guard Refs.encodeParam .set (⟨2⟩, 9) = Effects.Trace.Val.pair (.nat 2) (.nat 9)
#guard Refs.encodeParam .update (⟨2⟩, ⟨1⟩) = Effects.Trace.Val.pair (.nat 2) (.nat 1)

#guard refPrograms.all (fun entry => entry.log.all (fun event =>
  match event with
  | .done (.success _) => true
  | .done _ => false
  | _ => true))

/-! ## Forgetting the log is the plain run

The P-T1 law instantiated at this family: the traced service is an
around-wrapper, so the rows above are wrapped around the answers `refsLive`
gives on its own. -/

example := Effects.Family.Service.interpret_traced_fst (δ := Nat) (ρ := Nat)
  Refs.Name.spelling Refs.encodeParam Refs.encodeAnswer refsLive (refMakeGet 7) []

-- Every golden agrees with itself under every registered mask; agreement is a
-- projection equality and never more.
#guard refPrograms.all (fun entry =>
  Effect4.Trace.maskTable.all (fun mask => Effect4.Trace.agree mask.2 entry.log entry.log))

end Effect4Test.Flow.RefsContract
