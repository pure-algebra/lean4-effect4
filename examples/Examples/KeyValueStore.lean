import Effect4.Author
import Effect4.Program.Authoring.Application
import Effect4.Library.Ref.Cache

/-!
# A key-value store over a storage service, with a cache of its entries in front of the storage

The storage is a service of four host rows. The API reads, writes and deletes one key, and lists
every entry. The library's Ref cache (`Effect4.Ref.Cache.block`) is imposed on the service:
`entries` reads through it, and each write or removal empties it after it succeeds.
-/

set_option autoImplicit false

namespace Examples.KeyValueStore

open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (pair)

/-! ## The data -/

eff_record Entry where key : .string, value : .string
eff_failure MissingKey where key : .string
eff_failure StorageError message

/-! ## The storage -/

/-- The storage's service key. -/
def storageKey : ServiceKey := ⟨⟨32⟩, ⟨6⟩⟩

eff_rows Storage key storageKey error StorageError.ty cite "the key-value store" where
  read(.string) : .option .string,
  write(.prod .string .string) : .unit,
  remove(.string) : .bool,
  entries(.unit) : .list Entry.ty

/-! ## The API -/

/-- `lookup(key)`: the key's value; a missing key fails with the key. -/
def lookup (key : TermSrc) : Src NativeOp := eff do
  let found ← Storage.read key
  selectOptionWith found (MissingKey.raise key) fun value => succeed value

/-- `put(key, value)`: the key holds the value. -/
def put (key value : TermSrc) : Src NativeOp := Storage.write (pair key value)

/-- `remove(key)`: a missing key fails with the key. -/
def remove (key : TermSrc) : Src NativeOp := eff do
  let removed ← Storage.remove key
  if removed then succeed unit else MissingKey.raise key

/-- `entries()`: every entry. -/
def entries : Src NativeOp := Storage.entries unit

/-! ## The cache -/

/-- `entries`' method reads through the cache, with the entry's program as the loader. -/
def readingThrough (cache : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  Def.invokeWith "listCacheGet" [cache] [fun _ => body]

/-- A write's method empties the cache after the entry's program succeeds. A failure skips it. -/
def invalidatingAfter (cache : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  bindWith body fun answer =>
    andThen (Def.invoke "listCacheInvalidate" [cache]) (succeed answer)

/-- The cache at the entries' types. -/
def entriesCache : Application.Imposed NativeOp where
  block := Effect4.Ref.Cache.block Entry.ty StorageError.ty
  stateTy := Effect4.Ref.Cache.cellTy Entry.ty
  make := "listCacheMake"
  around := [("entries", readingThrough), ("put", invalidatingAfter), ("remove", invalidatingAfter)]

/-! ## The application -/

/-- The store: the storage's rows, the four programs, and the cache. -/
def application : Application NativeOp :=
  { name := "keyValueStore"
    rows := Storage.rows
    imposed := [entriesCache]
    entries :=
      [ { name := "lookup", params := [("key", .string)], body := lookup (var "key") }
      , { name := "put", params := [("key", .string), ("value", .string)]
          body := put (var "key") (var "value") }
      , { name := "remove", params := [("key", .string)], body := remove (var "key") }
      , { name := "entries", body := entries } ] }

end Examples.KeyValueStore
