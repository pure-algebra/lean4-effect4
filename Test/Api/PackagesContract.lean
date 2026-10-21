import Effect4.Api.Codegen
import TypeScript.Render
import Test.Api.HostList

/-!
# Packages contract — the two canonical package tables, crossed through the application face

The tables are lawful, their programs type, print and read back only under their own table,
the `strings` atom spells a parameter list, and a run under a host that answers from a list
(`Test.Api.HostList`) answers the shapes the host answers (finite receipts; the table-premised
laws carry the general claims).

The package fixtures are defined here once (`pSqlite`, `pKv`, and the SQL error paths, listed in
`sqlitePrograms`). The truth corpus prints them (`tools/Drivers/Truth.lean`), and the compiler's
group `sql` emits the SQL programs with the adapter (`Compiler.Groups`).
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
#guard NativeOp.spelled.all fun op => op.row.cite.startsWith "vendor/effect-4.0.0-rc.112/src/"

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

/-- The sqlite fixture over the canonical `SqliteBun` table (host rows step 6): open the
`:memory:` client, create, insert through `strings` parameters (JSON text, decoded by the host
before binding), select, and close at the scope's end. rc.112's answers were its tape
(`git:fa7bdc304:harness/truth/tapes/pSqlite.jsonl`), deleted with the differential. -/
def pSqlite : Api.Program :=
  .scoped (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                                  (.perform (.external 2) (.var 0)))
    (.bind (.perform (.external 1) (pair (.var 0) (pair (.lit (.str "CREATE TABLE t (a INTEGER, b TEXT)")) (strs []))))
      (.bind (.perform (.external 1) (pair (.var 0) (pair (.lit (.str "INSERT INTO t (a, b) VALUES (?, ?)")) (strs ["7", "\"x\""]))))
        (.perform (.external 1) (pair (.var 0) (pair (.lit (.str "SELECT a, b FROM t")) (strs [])))))))

def selected : Val := .list [.list [.list [.str "a", .str "7"], .list [.str "b", .str "\"x\""]]]
def sqliteExits : List ExitV :=
  [.success (.nat 0), .success (.list []), .success (.list []), .success selected, .success .unit]

#guard Api.wellTyped pSqlite sqliteBun
#guard (Api.typeOf pSqlite sqliteBun).map (fun t => (t.answer, t.error)) = some (sqlRows, sqlError)
#guard !Api.wellTyped pSqlite
#guard !Api.wellTyped pSqlite keyValueStoreMemory
#guard Api.roundTrip pSqlite sqliteBun = .ok pSqlite
#guard Test.Api.HostList.exit pSqlite sqliteBun sqliteExits = some (.success selected)
#guard (Test.Api.HostList.stores pSqlite sqliteBun sqliteExits).map (·.externals.allocated) =
  some [NativeOp.sqlTarget]
-- a wrong-shaped row set is refused at the answer type: a cell that is not a pair
#guard match Api.replayChecked pSqlite 1000 [Api.evaluate, .answerAsync Api.root 0 (answer (.nat 0)),
    .answerAsync Api.root 1 (answer (.list [.list [.str "a"]]))] sqliteBun with
  | .inr (.decision 2 _ (.answerType _ 1 _) _) => true
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

/-- The key-value fixture over the canonical `KeyValueStoreMemory` table: make, set, get, has,
remove; the answer is the `(get, has)` pair. rc.112's answers were its tape
(`git:fa7bdc304:harness/truth/tapes/pKv.jsonl`), deleted with the differential. -/
def pKv : Api.Program :=
  .bind (.perform (.external 0) (.lit .unit))
    (.bind (.perform (.external 2) (pair (.var 0) (pair (.lit (.str "k")) (.lit (.str "1")))))
      (.bind (.perform (.external 1) (pair (.var 0) (.lit (.str "k"))))
        (.bind (.perform (.external 4) (pair (.var 0) (.lit (.str "k"))))
          (.bind (.perform (.external 3) (pair (.var 0) (.lit (.str "k"))))
            (.succeed (pair (.var 2) (.var 3)))))))

def kvExits : List ExitV :=
  [.success (.nat 0), .success .unit, .success (.some (.str "1")), .success (.bool true), .success .unit]

#guard Api.wellTyped pKv keyValueStoreMemory
#guard (Api.typeOf pKv keyValueStoreMemory).map (fun t => (t.answer, t.error)) =
  some (.prod (.option .string) .bool, kvError)
#guard Api.roundTrip pKv keyValueStoreMemory = .ok pKv
#guard Test.Api.HostList.exit pKv keyValueStoreMemory kvExits =
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
-- still releases the client on the way out, which takes the close row's answer.
-- The pair is rc.112's two-level form (ruling G1, 2026-09-09): the reason's tag and the
-- driver's message under it, the outer `"SqlError"` implied by the row. `SqlError.message`
-- itself is the constant `"Failed to execute statement"` for a missing table, a syntax error,
-- a constraint violation and a closed database alike, so the literal `(_tag, message)` pair
-- distinguished nothing; a constraint violation reads `("ConstraintError", "UNIQUE constraint
-- failed: u.a")` (observed 2026-09-09, `git:fa7bdc304:harness/truth/tapes/pSqlFail.jsonl`)
def sqlFailed : Err := .tagged "UnknownError" "no such table: missing"
def failedExit : ExitV := .failure (Cause.fail sqlFailed)
def failed : Completion Val Err Defect FiberId Ann := .ofExit failedExit
#guard Test.Api.HostList.exit pSqlite sqliteBun [.success (.nat 0), failedExit, .success .unit] =
  some failedExit
-- without that answer the release parks at a frontier and the program has no exit yet
#guard (Test.Api.HostList.run pSqlite sqliteBun [.success (.nat 0), failedExit]).map (·.exit) =
  some none

/-! ### The error paths (2026-09-09, after the slice): what a real `SqlError` does

`sql.unsafe` on a missing table fails with rc.112's `SqlError`; the recorder posted the pair of
DB-15 in rc.112's two-level form, the reason's tag and the driver's message under it,
`("UnknownError", "no such table: missing")`, the outer `"SqlError"` implied by the row (ruling
G1), and the machine replays it as `Err.tagged`. Each way a program has of meeting such a failure
is one fixture over the same client and statement: it escapes through the scope, whose release
still runs (`pSqlFail`); it is caught (`pSqlCatch`); it is reified into the answer (`pSqlExit`); a
layer built over it dies under `Layer.orDie` (`pSqlOrDie`: both faces retain the adapter's exact
two-string pair inside the defect, compared as represented error data). rc.112's answers were the
tapes `pSql*.jsonl` (`git:fa7bdc304:harness/truth/tapes`), deleted with the differential. -/

/-- The statement that fails: no table `missing`, on the client the scope opened (`.var 0`). -/
def sqlMissing : Api.Program :=
  .perform (.external 1) (pair (.var 0) (pair (.lit (.str "SELECT a FROM missing")) (strs [])))
/-- `body` under an open client (`.var 0`) that the scope's end releases, as `pSqlite`. -/
def sqlClient (body : Api.Program) : Api.Program :=
  .scoped (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                                  (.perform (.external 2) (.var 0)))
    body)
def sqlExits : List ExitV := [.success (.nat 0), failedExit, .success .unit]

/-- The failure escapes through the scope, whose release still runs. -/
def pSqlFail : Api.Program := sqlClient sqlMissing
/-- The failure reified into the answer. -/
def pSqlExit : Api.Program := sqlClient (.exit sqlMissing)

-- the failure caught: the handler's value is the program's, and the release still runs; the
-- two arms share one answer type (`Ty` has no union), so the body answers a string too
def pSqlCatch : Api.Program :=
  sqlClient (.catchCause (.bind sqlMissing (.succeed (.lit (.str "rows")))) (.succeed (.lit (.str "recovered"))))
#guard Api.wellTyped pSqlCatch sqliteBun
#guard (Api.typeOf pSqlCatch sqliteBun).map (fun t => (t.answer, t.error)) = some (.string, .never)
#guard Test.Api.HostList.exit pSqlCatch sqliteBun sqlExits = some (.success (.str "recovered"))
-- the failure reified is well typed at the exit type, and it escapes at the pair
#guard (Api.typeOf pSqlExit sqliteBun).map (fun t => (t.answer, t.error)) =
  some (.exitOf sqlRows sqlError, .never)
#guard (Api.typeOf pSqlFail sqliteBun).map (fun t => (t.answer, t.error)) = some (sqlRows, sqlError)
-- the failure reified: the program succeeds with the exit, the tagged pair its one reason
#guard match Test.Api.HostList.exit pSqlExit sqliteBun sqlExits with
  | some (.success (Value.exitErr written)) =>
    (causeImage.ofVal written).map (·.reasons.map fun | .fail e _ => some e | _ => none) = some [some sqlFailed]
  | _ => false
-- a failed answer is refused where the row's error channel is empty (the open row), at the
-- call's token
#guard match Api.replayChecked pSqlFail 1000 [Api.evaluate, .answerAsync Api.root 0 failed] sqliteBun with
  | .inr (.decision 1 _ (.errorType _ 0 .never) _) => true
  | _ => false

/-- The key of the layer that `pSqlOrDie` builds. -/
def kSql : ServiceKey := ⟨⟨8⟩, ⟨4⟩⟩

/-- DI-31: the actual package pair survives layer orDie, after its client is released. A layer
whose build acquires the client on the layer scope, fails on the statement, and releases when the
failed build's scope closes; `Layer.orDie` turns the tagged failure into a defect on both faces. -/
def pSqlOrDie : Api.Program :=
  .provideLayer (.orDie (.effect kSql
      (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                              (.perform (.external 2) (.var 0)))
        (.bind sqlMissing (.succeed (.lit (.nat 1)))))))
    false (.service kSql)
#guard Api.wellTyped pSqlOrDie sqliteBun
#guard Test.Api.HostList.exit pSqlOrDie sqliteBun sqlExits =
  some (.failure (Cause.die (.error sqlFailed)))
#guard (Test.Api.HostList.run pSqlOrDie sqliteBun [.success (.nat 0), failedExit]).map (·.exit) =
  some none

/-- **The programs over the SQLite table**, by name, in the truth corpus's order: the fixture and
its four error paths. -/
def sqlitePrograms : List (String × Api.Program) :=
  [("pSqlite", pSqlite), ("pSqlFail", pSqlFail), ("pSqlCatch", pSqlCatch), ("pSqlExit", pSqlExit),
   ("pSqlOrDie", pSqlOrDie)]

end Test.Api.PackagesContract
