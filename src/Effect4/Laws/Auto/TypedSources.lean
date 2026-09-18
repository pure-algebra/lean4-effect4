import Lean
import Effect4.Laws.Program.Typed.Vocabulary

/-!
# Laws.Auto.TypedSources — reading the source table as an expression

The typed-state source table is a plain list, `Effect4.Program.Typed.sources : List Row`
(`Typed/Sources.lean`). The totality gate and the skeleton emitter need it as data at meta
level, and the trust gate refuses every way of *running* it (`unsafe`, `implemented_by`,
`initialize` for an environment extension). So the table is **read, not run**: the constant is
reduced to its constructor form and decoded, a string literal at a time
(`docs/research/2026-09-18-metaprogramming-review.md` §1, the `whnf` and expression-matching
API). A row the decoder does not recognise is a loud error, never a skipped row.
-/

open Lean Meta
open Effect4.Program.Typed

namespace Effect4.Laws.Auto.TypedSources

/-- A string literal, after reduction. -/
private def decodeString (e : Expr) : MetaM String := do
  match (← whnf e) with
  | .lit (.strVal s) => return s
  | e => throwError "typed sources: not a string literal: {e}"

private def decodeOptString (e : Expr) : MetaM (Option String) := do
  let e ← whnf e
  match e.getAppFn with
  | .const ``Option.some _ => return some (← decodeString e.appArg!)
  | .const ``Option.none _ => return none
  | _ => throwError "typed sources: not an optional string: {e}"

private def decodeExpected (e : Expr) : MetaM Expected := do
  let e ← whnf e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Expected.fiber _ => return .fiber (← decodeString args[0]!)
  | .const ``Expected.promise _ => return .promise (← decodeString args[0]!)
  | .const ``Expected.refColumn _ => return .refColumn
  | .const ``Expected.row _ => return .row (← decodeString args[0]!)
  | .const ``Expected.checker _ => return .checker (← decodeString args[0]!)
  | .const ``Expected.inherited _ => return .inherited
  | .const ``Expected.const _ => return .const (← decodeString args[0]!)
  | _ => throwError "typed sources: not an expectation: {e}"

private def decodeSource (e : Expr) : MetaM Source := do
  let e ← whnf e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Source.program _ => return .program (← decodeExpected args[0]!)
  | .const ``Source.continuation _ => return .continuation (← decodeExpected args[0]!)
  | .const ``Source.value _ => return .value (← decodeExpected args[0]!)
  | .const ``Source.exit _ => return .exit (← decodeExpected args[0]!)
  | .const ``Source.cause _ => return .cause (← decodeExpected args[0]!)
  | .const ``Source.hook _ => return .hook (← decodeOptString args[0]!)
  | .const ``Source.column _ => return .column (← decodeString args[0]!)
  | .const ``Source.journal _ => return .journal
  | .const ``Source.custom _ => return .custom (← decodeString args[0]!)
  | .const ``Source.refused _ => return .refused (← decodeString args[0]!)
  | .const ``Source.nested _ => return .nested (← decodeExpected args[0]!)
  | _ => throwError "typed sources: not a source: {e}"

/-- The rows of a `List Row` expression, reduced one cell at a time; bounded by a length. -/
private def decodeRows : Nat → Expr → MetaM (List Row)
  | 0, e => throwError "typed sources: more rows than the reader's bound at {e}"
  | fuel + 1, e => do
    let e ← whnf e
    let args := e.getAppArgs
    match e.getAppFn with
    | .const ``List.nil _ => return []
    | .const ``List.cons _ =>
      let cell ← whnf args[1]!
      let pair := cell.getAppArgs
      unless cell.getAppFn.isConstOf ``Prod.mk do
        throwError "typed sources: not a row: {cell}"
      let key ← decodeString pair[2]!
      let src ← decodeSource pair[3]!
      return (key, src) :: (← decodeRows fuel args[2]!)
    | _ => throwError "typed sources: not a list: {e}"

/-- The table, read from the environment: `Effect4.Program.Typed.sources`. -/
def readRows : MetaM (List Row) := do
  -- named without resolution: the table is in the module that runs the gate, not in this reader
  let e := mkConst `Effect4.Program.Typed.sources
  decodeRows 10000 e

end Effect4.Laws.Auto.TypedSources
