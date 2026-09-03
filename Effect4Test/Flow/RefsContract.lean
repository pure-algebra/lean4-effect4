/-
Contract packet: the `Refs` family (`docs/TRACE-DAG.md`, the `refs` edge).
Kernel receipts for the Lean face: the exact rows of each of the seven goldens
under `generated/traces/ref/`, and the declared spellings the generated module
is built from.

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
#check @Effect4.RefFamily.refsLive
#check @Effect4.RefFamily.erefsLive
#check @Effect4.RefFamily.refGoldenLog

/-! ## The corpus -/

#guard refPrograms.length == 7

#guard refPrograms.map (·.name) ==
  [ "makeGet", "setGet", "updateTwice", "modifyOld", "getAndSetOld", "twoRefs", "takeUnderflow" ]

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

-- `ref/setGet.tsv`. `set` is declared `Unit` and answers unit. rc.112's
-- `Ref.set` resolves to the underlying `MutableRef` at runtime; the row is unit
-- because answers are recorded as typed. counterexample: E4-SEM-CE-009
#guard logOf "setGet" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "set" (.pair (.nat 0) (.nat 9)), .answer "set" .unit
  , .op "get" (.nat 0), .answer "get" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/updateTwice.tsv`. Two identical requests, two identical unit answers,
-- and a read that shows both landed. rc.112's `Ref.update` answers `undefined`
-- rather than the `MutableRef` its sibling `Ref.set` answers; neither runtime
-- value is what these rows are read off.
#guard logOf "updateTwice" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "update" (.pair (.nat 0) (.nat 1)), .answer "update" .unit
  , .op "update" (.pair (.nat 0) (.nat 1)), .answer "update" .unit
  , .op "get" (.nat 0), .answer "get" (.nat 9)
  , .done (.success (.nat 9)) ]

-- `ref/modifyOld.tsv`. `modify` answers the value before the write (7) and the
-- read after it shows the write (12). The amount is non-zero on purpose: the
-- answer and the new state have the same type, so nothing but this golden
-- separates them. counterexample: E4-SEM-CE-013
#guard logOf "modifyOld" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "modify" (.pair (.nat 0) (.nat 5)), .answer "modify" (.nat 7)
  , .op "get" (.nat 0), .answer "get" (.nat 12)
  , .done (.success (.nat 7)) ]

-- `ref/getAndSetOld.tsv`. The same separation for `getAndSet`.
#guard logOf "getAndSetOld" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "getAndSet" (.pair (.nat 0) (.nat 100)), .answer "getAndSet" (.nat 7)
  , .op "get" (.nat 0), .answer "get" (.nat 100)
  , .done (.success (.nat 7)) ]

-- `ref/twoRefs.tsv`. Two handles, named 0 and 1 in creation order; a write
-- through the first is invisible through the second.
#guard logOf "twoRefs" =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "make" (.nat 8), .answer "make" (.nat 1)
  , .op "set" (.pair (.nat 0) (.nat 0)), .answer "set" .unit
  , .op "get" (.nat 1), .answer "get" (.nat 8)
  , .op "update" (.pair (.nat 1) (.nat 1)), .answer "update" .unit
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

-- A request carrying a handle and a number is the pair, in that order.
#guard Refs.encodeParam .set (⟨2⟩, 9) = Effects.Trace.Val.pair (.nat 2) (.nat 9)

-- The declared spellings the generated module is built from: the handle prints
-- rc.112's own opaque type, a `Unit` answer prints `void`, and an `Except`
-- answer is data rather than an error channel.
#guard Refs.rows.ops.map (fun row => (row.name, row.tsAnswer)) =
  [ ("make", "Ref.Ref<number>"), ("get", "number"), ("set", "void")
  , ("update", "void"), ("modify", "number"), ("getAndSet", "number") ]

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
