import Effect4.Program.Packages.SqliteBun
import Effect4.Program.Packages.KeyValueStoreMemory

/-!
# Program.Packages — the canonical package tables, as one list

Each package is a service the pinned host provides (its rc.112 key string and service type
code, the handle spelling its rows share) and the `RowTable` of the rows a program may
perform against it. `all` is what `tools/Tools/TsGen.lean` projects to `ts/eff/packages.gen.ts`
for the TypeScript readers, in this order; a table's identity is its rows in their order, since
an external index is a position (`Read.lean` `nativeSpell`).
-/

namespace Effect4.Program.Packages

structure Package where
  name : String
  /-- The rc.112 key string (`Context.Service(…)`'s argument), the `sourceId` of a foreign
  key declaration. -/
  key : String
  /-- The service type code (`nativeServiceTy`): 8 the SQL client, 9 the key-value store. -/
  service : Nat
  /-- The handle target spelling every row of the table shares. -/
  target : String
  rows : RowTable
deriving Repr

def all : List Package :=
  [ { name := "SqliteBun", key := sqlKey, service := 8, target := NativeOp.sqlTarget, rows := sqliteBun }
  , { name := "KeyValueStoreMemory", key := kvKey, service := 9, target := NativeOp.kvTarget,
      rows := keyValueStoreMemory } ]

end Effect4.Program.Packages
