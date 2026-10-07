import Effect4.Laws.Program.Typing.Check
import Effect4.Program.Native

namespace Test.Program.TypingCheckContract
open Effect4.Program Conform.Effect4.Typing

def accepted : Eff NativeOp := .succeed (.lit (.nat 7))
def refused : Eff NativeOp := .fail (.lit (.bool true))

#guard (checkTyping nativeSignature [] accepted).toOption.map (·.val) =
  some (EffTy.pure .nat)
#guard (checkTyping nativeSignature [] refused).toOption.isNone
#guard (assessTyping nativeSignature [] accepted).remaining =
  [.valueModel, .targetRepresentation, .executionRelation, .hostBehavior]

/-- The returned proof is indexed by this exact input, rather than a reported theorem name. -/
theorem returned_judgment (sig : Signature Op) (env : TyEnv) (program : Eff Op)
    (result : { t : EffTy // HasTy sig env program t }) : HasTy sig env program result.val :=
  result.property

/-! ## The eleven tests at a fixed type read the order

Each test compares the type of one term with a fixed type: `.bool`, `.nat` or a handle type. It
asks that the term's normal type is below the fixed type (`Ty.sub`). Below each of these fixed
types stand `never` and the type itself. So each test has two green controls, a term at `never`
and a term at a raw union with `never`, and one red control at a type that is not below. The
compiler's verdict on each printed form is a line of `harness/truth/term-rows.typecheck.ts`. -/

open Effect4.Program.Checker

-- 1. catchIf (fixed type: .bool)
-- green 1: at never. The test reads the body's error, and `succeed` fails with nothing
#guard (check nativeSignature [] [] (.catchIf (.var 0) (.succeed (.lit .unit)) (.succeed (.lit .unit)))).isOk
-- green 2: at raw union
#guard (check nativeSignature [.union .bool .never] [] (.catchIf (.var 0) (.succeed (.lit .unit)) (.succeed (.lit .unit)))).isOk
-- red: not below .bool
#guard (check nativeSignature [.string] [] (.catchIf (.var 0) (.succeed (.lit .unit)) (.succeed (.lit .unit)))).isOk = false

-- 2. iterate (fixed type: .bool)
-- green 1: at never
#guard (check nativeSignature [.never] [] (.iterate none (.var 0) (.var 0) (.var 1) (.var 0) (.succeed (.lit .unit)))).isOk
-- green 2: at raw union
#guard (check nativeSignature [.union .bool .never] [] (.iterate none (.var 0) (.var 0) (.var 1) (.var 0) (.succeed (.lit .unit)))).isOk
-- red: not below .bool
#guard (check nativeSignature [.string] [] (.iterate none (.var 0) (.var 0) (.var 1) (.var 0) (.succeed (.lit .unit)))).isOk = false

-- 3. ifElse (fixed type: .bool)
-- green 1: at never
#guard (checkStmts nativeSignature [.never] false none [] (Stmts.cons (Stmt.ifElse (.var 0) .nil .nil) .nil)).isOk
-- green 2: at raw union
#guard (checkStmts nativeSignature [.union .bool .never] false none [] (Stmts.cons (Stmt.ifElse (.var 0) .nil .nil) .nil)).isOk
-- red: not below .bool
#guard (checkStmts nativeSignature [.nat] false none [] (Stmts.cons (Stmt.ifElse (.var 0) .nil .nil) .nil)).isOk = false

-- 4. Decision.arms .bool (fixed type: .bool)
-- green 1: at never
#guard Decision.arms .bool .never == some ([], [])
-- green 2: at raw union
#guard Decision.arms .bool (.union .bool .never) == some ([], [])
-- red: not below .bool
#guard Decision.arms .bool .nat == none

-- 5. restore (fixed type: Ty.maskRestore)
-- green 1: at never
#guard (check nativeSignature [.never] [] (.restore (.var 0) (.succeed (.lit .unit)))).isOk
-- green 2: at raw union
#guard (check nativeSignature [.union Ty.maskRestore .never] [] (.restore (.var 0) (.succeed (.lit .unit)))).isOk
-- red: not below Ty.maskRestore
#guard (check nativeSignature [.bool] [] (.restore (.var 0) (.succeed (.lit .unit)))).isOk = false

-- 6. forkIn (fixed type: Ty.scope)
def forkOpts : Effect4.Supervision.ForkOptions := { startImmediately := true, daemon := false, maskMode := .interruptible }
-- green 1: at never
#guard (checkAction nativeSignature [.never] [] (.forkIn (.succeed (.lit .unit)) forkOpts (.var 0))).isOk
-- green 2: at raw union
#guard (checkAction nativeSignature [.union Ty.scope .never] [] (.forkIn (.succeed (.lit .unit)) forkOpts (.var 0))).isOk
-- red: not below Ty.scope
#guard (checkAction nativeSignature [.nat] [] (.forkIn (.succeed (.lit .unit)) forkOpts (.var 0))).isOk = false

-- 7. runIn (fixed type: Ty.scope)
-- green 1: at never
#guard (checkAction nativeSignature [.fiberOf .unit .never, .never] [] (.runIn (.var 0) (.var 1))).isOk
-- green 2: at raw union
#guard (checkAction nativeSignature [.fiberOf .unit .never, .union Ty.scope .never] [] (.runIn (.var 0) (.var 1))).isOk
-- red: not below Ty.scope
#guard (checkAction nativeSignature [.fiberOf .unit .never, .nat] [] (.runIn (.var 0) (.var 1))).isOk = false

-- 8. closeScope (fixed type: Ty.scope)
-- green 1: at never
#guard (checkAction nativeSignature [.never, .exitOf .unit .never] [] (.closeScope (.var 0) (.var 1))).isOk
-- green 2: at raw union
#guard (checkAction nativeSignature [.union Ty.scope .never, .exitOf .unit .never] [] (.closeScope (.var 0) (.var 1))).isOk
-- red: not below Ty.scope
#guard (checkAction nativeSignature [.nat, .exitOf .unit .never] [] (.closeScope (.var 0) (.var 1))).isOk = false

-- 9. setContext (fixed type: Ty.context)
-- green 1: at never
#guard (checkAction nativeSignature [.never] [] (.setContext (.var 0))).isOk
-- green 2: at raw union
#guard (checkAction nativeSignature [.union Ty.context .never] [] (.setContext (.var 0))).isOk
-- red: not below Ty.context
#guard (checkAction nativeSignature [.nat] [] (.setContext (.var 0))).isOk = false

-- 10. interruptAll (fixed type: .nat)
-- green 1: at never
#guard (checkAction nativeSignature [.list (.fiberOf .unit .never), .never] [] (.interruptAll (.var 0) (some (.var 1)))).isOk
-- green 2: at raw union
#guard (checkAction nativeSignature [.list (.fiberOf .unit .never), .union .nat .never] [] (.interruptAll (.var 0) (some (.var 1)))).isOk
-- red: not below .nat
#guard (checkAction nativeSignature [.list (.fiberOf .unit .never), .bool] [] (.interruptAll (.var 0) (some (.var 1)))).isOk = false

-- 11. causeTy .interrupt (some who) (fixed type: .nat)
-- green 1: at never
#guard causeTy nativeSignature [.never] (.interrupt (some (.var 0))) == some .never
-- green 2: at raw union
#guard causeTy nativeSignature [.union .nat .never] (.interrupt (some (.var 0))) == some .never
-- red: not below .nat
#guard causeTy nativeSignature [.bool] (.interrupt (some (.var 0))) == none

end Test.Program.TypingCheckContract
