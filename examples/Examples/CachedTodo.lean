import Examples.Todo
import Effect4.Library.Ref.Cache

/-!
# The to-do list with a verified cache of its list in front of the repository

The library's Ref cache (`Effect4.Ref.Cache.block`) is imposed on the to-do's service. Its cell
is made once, beside the service's context. `list` reads through it, and each write empties it
after the write succeeds. The entries are the to-do's, unchanged.
-/

set_option autoImplicit false

namespace Examples.CachedTodo

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- `list`'s method reads through the cache: `get` at the cache's cell, with the entry's program,
`TodoRepo.all()`, as its loader. -/
def readingThrough (cache : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  Def.invokeWith "listCacheGet" [cache] [fun _ => body]

/-- A write's method empties the cache after the entry's program succeeds. A failure skips it. -/
def invalidatingAfter (cache : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  bindWith body fun answer =>
    andThen (Def.invoke "listCacheInvalidate" [cache]) (succeed answer)

open Examples.Todo in
/-- The cache at the to-do's types: `list` reads through it, and `add`, `complete` and `remove`
empty it. -/
def listCache : Application.Imposed NativeOp where
  block := Effect4.Ref.Cache.block Todo.ty SqlError.ty
  stateTy := Effect4.Ref.Cache.cellTy Todo.ty
  make := "listCacheMake"
  around := [("list", readingThrough), ("add", invalidatingAfter),
    ("complete", invalidatingAfter), ("remove", invalidatingAfter)]

/-- The cached to-do application: the to-do's rows, protocols and entries, with the cache. -/
def application : Application NativeOp :=
  { Examples.Todo.application with name := "cachedTodo", imposed := [listCache] }

end Examples.CachedTodo
