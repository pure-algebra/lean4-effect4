import Effect4.Program.Packages.SqliteBun
import Effect4.Program.Packages.KeyValueStoreMemory

/-!
# Program.Packages — the canonical package tables, as one list

Each package is a service the pinned host provides (its rc.112 key string and service type
code, the handle spelling its rows share) and the `RowTable` of the rows a program may
perform against it. `all` is what `tools/Tools/TsGen.lean` projects to `ts/eff/packages.gen.ts`
for the TypeScript readers, in this order; a table's identity is its rows in their order, since
an external index is a position in the link table supplied beside the program (`Read.lean`
`nativeSpell`; DI-22, and `table` below).
-/

namespace Effect4.Program.Packages

structure Package where
  name : String
  /-- The rc.112 key string (`Context.Service(…)`'s argument), the `sourceId` of a foreign
  key declaration. -/
  key : String
  /-- The `effect` subpath the service's module lives under (`effect/unstable/sql`), as the
  foreign readers' import resolution spells it: a foreign `SqlClient.SqlClient` bound through
  `import { SqlClient } from "effect/unstable/sql"` resolves to `<module>.<target>`. -/
  module : String
  /-- The service type code (`nativeServiceTy`): 8 the SQL client, 9 the key-value store. -/
  service : Nat
  /-- The handle target spelling every row of the table shares. -/
  target : String
  rows : RowTable
deriving Repr

def all : List Package :=
  [ { name := "SqliteBun", key := sqlKey, module := "unstable/sql", service := 8,
      target := NativeOp.sqlTarget, rows := sqliteBun }
  , { name := "KeyValueStoreMemory", key := kvKey, module := "unstable/persistence", service := 9,
      target := NativeOp.kvTarget, rows := keyValueStoreMemory } ]

/-- Every package's rows, in package order: **one** link table, the one the foreign readers
read under, so an external index *they* emit is a position in this concatenation. It is not
"the canonical table" (DI-22, `docs/DESIGN-ISSUES.md`): an external index is a position in
whichever `RowTable` is supplied beside the program to `Api` — its link table — and this is
one such table. Each truth fixture's per-package table (`harness/truth/Truth.lean`,
`hostInputs`) is another, and a published program carries the link table it was written
against (DI-05). The two conventions the register called live were always this one; they
coincide on the sqlite rows only because that package is first here.

`LawfulTable` of the concatenation is what makes the spellings a function
(`Test/Api/PackagesContract.lean`); `checkTable` (`src/Effect4/Program/Native.lean`) is what
says this runner can register its rows. -/
def table : RowTable := all.flatMap (·.rows)

end Effect4.Program.Packages
