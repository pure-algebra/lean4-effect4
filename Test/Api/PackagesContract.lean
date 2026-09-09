import Effect4.Api
import TypeScript.Render

/-!
# Packages contract — the two canonical package tables, crossed through the application face

The tables are lawful, their programs type, print and read back only under their own table,
the `strings` atom spells a parameter list, and a run over an oracle tape answers the shapes
the host answers (finite receipts; the table-premised laws carry the general claims).
-/

namespace Test.Api.PackagesContract
open Effect4 Effect4.Program Effect4.Program.Packages Effect4.Machine
open TypeScript (house0)

set_option maxRecDepth 8192

-- the tables
#guard LawfulTable sqliteBun
#guard LawfulTable keyValueStoreMemory
#guard sqliteBun.length = 3
#guard keyValueStoreMemory.length = 5
#guard Packages.all.map (·.service) = [8, 9]
#guard Packages.all.map (·.target) = [NativeOp.sqlTarget, NativeOp.kvTarget]
#guard (Packages.all.map (·.rows)).all LawfulTable
-- the canonical table (both, in package order) is lawful: the foreign readers read under it
#guard Packages.table = sqliteBun ++ keyValueStoreMemory
#guard LawfulTable Packages.table
#guard Packages.table.length = 8
#guard Packages.all.map (·.module) = ["unstable/sql", "unstable/persistence"]
-- the sqlite rows' error channels: `make` is typed `never` (a file that cannot be opened is a
-- defect, not a `SqlError`), a statement fails with `SqlError`, the release cannot fail
#guard sqliteBun.map (·.error) = [.never, sqlError, .never]
-- every cite is a repository-relative path (decision 10; the citation gate resolves them)
#guard (sqliteBun ++ keyValueStoreMemory).all fun row => row.cite.startsWith "vendor/effect-4.0.0-rc.112/src/"
#guard NativeOp.all.all fun op => op.row.cite.startsWith "vendor/effect-4.0.0-rc.112/src/"

-- the strings atom: the one list a term builds
#guard nativeAtomTy "strings" [] = some (.list .string)
#guard nativeAtomTy "strings" [.string] = some (.list .string)
#guard nativeAtomTy "strings" [.string, .string] = some (.list .string)
#guard nativeAtomTy "strings" [.nat] = none
#guard nativeAtomTy "strings" [.string, .nat] = none
#guard nativeAtom "strings" [] = some (.list [])
#guard nativeAtom "strings" [.str "7", .str "\"x\""] = some (.list [.str "7", .str "\"x\""])
#guard nativeAtom "strings" [.nat 1] = none

def strs (xs : List String) : Term := .app "strings" (xs.foldr (fun s t => .cons (.lit (.str s)) t) .nil)
def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def answer (v : Val) : Completion Val Err Defect FiberId Ann := .ofExit (.success v)

/-- The sqlite fixture: open, create, insert, select, close (the scope's release). -/
def pSqlite : Api.Program :=
  .scoped (.bind (.acquireRelease (.callback (.external 0) (.lit (.str ":memory:")))
                                  (.callback (.external 2) (.var 0)))
    (.bind (.callback (.external 1) (pair (.var 0) (pair (.lit (.str "CREATE TABLE t (a INTEGER, b TEXT)")) (strs []))))
      (.bind (.callback (.external 1) (pair (.var 0) (pair (.lit (.str "INSERT INTO t (a, b) VALUES (?, ?)")) (strs ["7", "\"x\""]))))
        (.callback (.external 1) (pair (.var 0) (pair (.lit (.str "SELECT a, b FROM t")) (strs [])))))))

def selected : Val := .list [.list [.list [.str "a", .str "7"], .list [.str "b", .str "\"x\""]]]
def sqliteAnswers : List (Completion Val Err Defect FiberId Ann) :=
  [answer (.nat 0), answer (.list []), answer (.list []), answer selected, answer .unit]

#guard Api.wellTyped pSqlite sqliteBun
#guard (Api.typeOf pSqlite sqliteBun).map (fun t => (t.answer, t.error)) = some (sqlRows, sqlError)
#guard !Api.wellTyped pSqlite
#guard !Api.wellTyped pSqlite keyValueStoreMemory
#guard Api.roundTrip pSqlite sqliteBun = .ok pSqlite
#guard (Api.run pSqlite 1000 [] sqliteAnswers sqliteBun).exit = some (.success selected)
#guard (Api.run pSqlite 1000 [] sqliteAnswers sqliteBun).stores.externals.allocated = [NativeOp.sqlTarget]
-- a wrong-shaped row set is refused at the answer type: a cell that is not a pair
#guard match Api.replayChecked pSqlite 1000 [Api.evaluate] [] [answer (.nat 0), answer (.list [.list [.str "a"]])] sqliteBun with
  | .inr (_, _, .oracleType _ _, _) => true
  | _ => false

-- The printed image: the method row on the handle binder, the parameters through `strings`.
-- Rendering stays inside `#guard` (as `ApiContract` does): the renderer is behind the classical
-- implementation boundary, and a `def` in the test tree that reached it would fail the audit.
#guard match Api.print pSqlite sqliteBun with
  | .ok e =>
    let text := TypeScript.Render.expr house0 0 e
    (text.splitOn "a0.unsafe(\"INSERT INTO t (a, b) VALUES (?, ?)\", strings(\"7\", \"\\\"x\\\"\"))").length == 2 &&
    (text.splitOn "Sql.open(\":memory:\")").length == 2 &&
    (text.splitOn "Sql.close(a0)").length == 2 &&
    (text.splitOn "strings()").length == 3
  | .error _ => false

/-- The key-value fixture: make, set, get, has, remove; the answer is the (get, has) pair. -/
def pKv : Api.Program :=
  .bind (.callback (.external 0) (.lit .unit))
    (.bind (.callback (.external 2) (pair (.var 0) (pair (.lit (.str "k")) (.lit (.str "1")))))
      (.bind (.callback (.external 1) (pair (.var 0) (.lit (.str "k"))))
        (.bind (.callback (.external 4) (pair (.var 0) (.lit (.str "k"))))
          (.bind (.callback (.external 3) (pair (.var 0) (.lit (.str "k"))))
            (.succeed (pair (.var 2) (.var 3)))))))

def kvAnswers : List (Completion Val Err Defect FiberId Ann) :=
  [answer (.nat 0), answer .unit, answer (.some (.str "1")), answer (.bool true), answer .unit]

#guard Api.wellTyped pKv keyValueStoreMemory
#guard (Api.typeOf pKv keyValueStoreMemory).map (fun t => (t.answer, t.error)) =
  some (.prod (.option .string) .bool, kvError)
#guard Api.roundTrip pKv keyValueStoreMemory = .ok pKv
#guard (Api.run pKv 1000 [] kvAnswers keyValueStoreMemory).exit =
  some (.success (.list [.some (.str "1"), .bool true]))

#guard match Api.print pKv keyValueStoreMemory with
  | .ok e =>
    let text := TypeScript.Render.expr house0 0 e
    (text.splitOn "a0.set(\"k\", \"1\")").length == 2 &&
    (text.splitOn "a0.get(\"k\")").length == 2 &&
    (text.splitOn "a0.has(\"k\")").length == 2 &&
    (text.splitOn "a0.remove(\"k\")").length == 2
  | .error _ => false

-- a tagged package failure is admitted at the error column and reaches the exit; the scope
-- still releases the client on the way out, which consumes the close row's oracle answer.
-- The pair is rc.112's two-level form (ruling G1, 2026-09-09): the reason's tag and the
-- driver's message under it, the outer `"SqlError"` implied by the row. `SqlError.message`
-- itself is the constant `"Failed to execute statement"` for a missing table, a syntax error,
-- a constraint violation and a closed database alike, so the literal `(_tag, message)` pair
-- distinguished nothing; a constraint violation reads `("ConstraintError", "UNIQUE constraint
-- failed: u.a")` (observed 2026-09-09, `harness/truth/tapes/pSqlFail.jsonl`)
def sqlFailed : Err := .tagged "UnknownError" "no such table: missing"
def failed : Completion Val Err Defect FiberId Ann := .ofExit (.failure (Cause.fail sqlFailed))
#guard (Api.run pSqlite 1000 [] [answer (.nat 0), failed, answer .unit] sqliteBun).exit =
  some (.failure (Cause.fail sqlFailed))
-- without that answer the release parks at a frontier and the program has no exit yet
#guard (Api.run pSqlite 1000 [] [answer (.nat 0), failed] sqliteBun).exit = none

/-- The failing statement under an open client the scope releases (`Truth.lean`'s
`sqlClient`/`sqlMissing`, whose tapes carry the real answers). -/
def sqlMissing : Api.Program :=
  .callback (.external 1) (pair (.var 0) (pair (.lit (.str "SELECT a FROM missing")) (strs [])))
def sqlClient (body : Api.Program) : Api.Program :=
  .scoped (.bind (.acquireRelease (.callback (.external 0) (.lit (.str ":memory:")))
                                  (.callback (.external 2) (.var 0)))
    body)
def sqlAnswers : List (Completion Val Err Defect FiberId Ann) := [answer (.nat 0), failed, answer .unit]

-- the failure caught: the handler's value is the program's, and the release still runs; the
-- two arms share one answer type (`Ty` has no union), so the body answers a string too
def pSqlCatch : Api.Program :=
  sqlClient (.catchCause (.bind sqlMissing (.succeed (.lit (.str "rows")))) (.succeed (.lit (.str "recovered"))))
#guard Api.wellTyped pSqlCatch sqliteBun
#guard (Api.typeOf pSqlCatch sqliteBun).map (fun t => (t.answer, t.error)) = some (.string, .never)
#guard (Api.run pSqlCatch 1000 [] sqlAnswers sqliteBun).exit = some (.success (.str "recovered"))
-- the failure reified is well typed at the exit type, and it escapes at the pair
#guard (Api.typeOf (sqlClient (.exit sqlMissing)) sqliteBun).map (fun t => (t.answer, t.error)) =
  some (.exitOf sqlRows sqlError, .never)
#guard (Api.typeOf (sqlClient sqlMissing) sqliteBun).map (fun t => (t.answer, t.error)) = some (sqlRows, sqlError)
-- the failure reified: the program succeeds with the exit, the tagged pair its one reason
#guard match (Api.run (sqlClient (.exit sqlMissing)) 1000 [] sqlAnswers sqliteBun).exit with
  | some (.success (Value.exitErr written)) =>
    (causeImage.ofVal written).map (·.reasons.map fun | .fail e _ => some e | _ => none) = some [some sqlFailed]
  | _ => false
-- a failed answer is refused where the row's error channel is empty (the open row): at the
-- oracle's position on the registration path, at the token on the delayed path
#guard match Api.replayChecked (sqlClient sqlMissing) 1000 [Api.evaluate] [] [failed] sqliteBun with
  | .inr (0, _, .oracleType 0 .never, _) => true
  | _ => false
#guard match Api.replayChecked (sqlClient sqlMissing) 1000 [Api.evaluate, .answerAsync Api.root 0 failed] [] [] sqliteBun with
  | .inr (1, _, .errorType _ 0 .never, _) => true
  | _ => false

end Test.Api.PackagesContract
