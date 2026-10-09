import Effect4.Laws.Program.Typing.Rebase
import Effect4.Program.Native
import Effect4.Program.Definitions

open Effect4.Program
namespace RebaseProbe

def q : List Nat := [8,9]
def p : List Nat := [3]
def good : Eff NativeOp := .succeed (.lit (.nat 7))
def bad : Eff NativeOp := .bind good (.succeed (.var 2))
def badRet : Stmt NativeOp := .ret (.var 0)
def badReturnBody : Stmts NativeOp := .cons badRet .nil
def returnWithTail : Stmts NativeOp := .cons badRet (.cons (.yieldDiscard good) .nil)
def block : Eff NativeOp := .defs [] .nil good

def statementPaths : Except TypeRefusal StmtTy → List (List Nat)
  | .error refusal => [refusal.path]
  | .ok (.ret (.error refusal)) => [refusal.path]
  | _ => []

def refusalPath {A : Type} (result : Except TypeRefusal A) : Option (List Nat) :=
  match result with
  | .error refusal => some refusal.path
  | .ok _ => none

-- Reader: a real successful program at a nonempty base.
example : Checker.check nativeSignature [] (q ++ p) good =
    (Checker.check nativeSignature [] p good).mapError (TypeRefusal.rebase q) :=
  Checker.check_rebase nativeSignature q [] p good
#guard (Checker.check nativeSignature [] (q ++ p) good).toOption =
  (Checker.check nativeSignature [] p good).toOption

-- Refused recursive child: transport the location but keep the refused reason.
#guard refusalPath (Checker.check nativeSignature [] p bad) = some [3,1]
#guard refusalPath (Checker.check nativeSignature [] (q ++ p) bad) = some [8,9,3,1]
#guard Checker.check nativeSignature [] (q ++ p) bad =
  (Checker.check nativeSignature [] p bad).mapError (TypeRefusal.rebase q)

-- Delayed return failure: changing only the outer Except misses the nested refusal.
#guard statementPaths (Checker.checkStmt nativeSignature [] false p badRet) = [[3]]
#guard statementPaths (Checker.checkStmt nativeSignature [] false (q ++ p) badRet) = [[8,9,3]]
#guard statementPaths (Checker.checkStmt nativeSignature [] false (q ++ p) badRet) !=
  statementPaths ((Checker.checkStmt nativeSignature [] false p badRet).mapError (TypeRefusal.rebase q))
example : Checker.checkStmt nativeSignature [] false (q ++ p) badRet =
    ((Checker.checkStmt nativeSignature [] false p badRet).map (StmtTy.rebase q)).mapError
      (TypeRefusal.rebase q) :=
  Checker.checkStmt_rebase nativeSignature q [] false p badRet
#guard refusalPath (Checker.check nativeSignature [] (q ++ p) (.gen badReturnBody)) = some [8,9,3,0,0]

-- A following statement earns returnNotLast before the invalid return term is read.
#guard match Checker.checkStmts nativeSignature [] false none (q ++ p) returnWithTail with
  | .error refusal => refusal.path == [8,9,3,0] && refusal.reason == .returnNotLast
  | .ok _ => false
#guard refusalPath (Checker.checkStmts nativeSignature [] false (some [8,9,4])
  (q ++ p) (.cons .breakLoop .nil)) = some [8,9,4]
#guard (Checker.checkStmts nativeSignature [] false (some [8,9,4]) (q ++ p) .nil).toOption.isSome

-- The table transports refused answers and unreached nodes, with context fixed.
def unreachable : Eff NativeOp := .bind (.succeed (.var 0)) good
example : tableAt nativeSignature (some (.env [])) (.eff unreachable) (q ++ p) =
    (tableAt nativeSignature (some (.env [])) (.eff unreachable) p).map (Table.Entry.rebase q) :=
  tableAt_rebase nativeSignature (some (.env [])) (.eff unreachable) q p
#guard tableAt nativeSignature (some (.env [])) (.eff unreachable) (q ++ p) =
  (tableAt nativeSignature (some (.env [])) (.eff unreachable) p).map (Table.Entry.rebase q)
#guard (tableAt nativeSignature (some (.env [])) (.eff unreachable) (q ++ p)).any fun entry =>
  entry.path == [8,9,3,1] && entry.env.isNone && entry.result.isNone
#guard (tableAt nativeSignature none (.eff good) (q ++ p)).all fun entry =>
  entry.env.isNone && entry.result.isNone

-- Base transport does not change layer targets, admit blocks, or change the variable context.
#guard match Checker.checkLayer nativeSignature (q ++ p) (.ref [2]) with
  | .error refusal => refusal.path == [8,9,3] && refusal.reason == .layerReference [2]
  | .ok _ => false
#guard (Checker.checkModule nativeSignature block).toOption.isSome
#guard (Checker.check nativeSignature [] (q ++ p) block).toOption.isNone
#guard (Checker.check nativeSignature [.nat] p (.succeed (.var 0))).toOption.isSome
#guard (Checker.check nativeSignature [] (q ++ p) (.succeed (.var 0))).toOption.isNone
end RebaseProbe
