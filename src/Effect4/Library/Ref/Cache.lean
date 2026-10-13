module

public import Effect4.Program.Authoring.Ascribe

/-!
# Ref.Cache — a cache of a list beside storage, as a definition block

The banked module of the vertical slice (decisions row 378 (1) and (18)): Ref used as a cache of
a list that storage holds. The block is first-order `Eff` data over Ref's native operations
(`refMake`, `refGet` and `refSet`; `src/Effect4/Library/Ref.lean`). It has the shape of the
library's service blocks (`Semaphore.serviceDefs`, `src/Effect4/Library/Semaphore/Defs.lean`):

* `make`, the service's initial program, makes the cell, holding nothing;
* `get` reads through the cache. A held list answers at once. An empty cache runs the loader
  once, holds the list that it loads and answers it. A failure of the loader is the answer, and
  the cache stays empty;
* `invalidate` empties the cache. An application calls it after each write to storage.

**The loader is a program parameter of `get`** (decisions row 340, slice HO-1). The caller
passes storage's read at each call, so the block calls no host row and names no application.
Its bodies hold no row position and no definition position, so its bytes do not depend on where
an application places it. The element type and the loader's error type are the block's two type
parameters. The bank records the block at the types of the to-do's `list`
(`Test/Dogfood/Bank.lean`).

The independent model is `Effect4.Ref.Cache.Model` (`src/Effect4/Library/Ref/CacheModel.lean`).
The agreement law is `cache_agrees` (`src/Effect4/Laws/Library/Ref/Cache.lean`).

What the block lacks today:

* a print as an Effect service: `printServices` (`src/Effect4/Codegen/Print.lean`) refuses a
  method with a parameter until slice HO-5 forwards its programs (`serviceFaultOf`, Codex's
  HO3-SVC-01);
* an authoring form for its call: a caller writes `Eff.invoke` with the loader as its program,
  and the authoring surface has no invocation with programs yet.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Ref.Cache

open Effect4.Program

/-- What the cache holds: the list, once loaded. -/
def cachedTy (A : Ty) : Ty := .option (.list A)

/-- The service's state: the cell that holds the cache. -/
def cellTy (A : Ty) : Ty := .refOf (cachedTy A)

/-- The loader, the one parameter of `get`: storage's read of the list, from no request. Its
error is the error of `get`. -/
def loadParam (A E : Ty) : ParamDecl :=
  { name := "load", request := .unit, answer := .list A, error := E }

/-- `none` at a declared type: the record of an ascription and its field read, the tree that
`Authoring.ascribe t (app "none" [])` elaborates to (`src/Effect4/Program/Authoring/Ascribe.lean`).
A cell is invariant, so `make` holds its first `none` at the cache's type. -/
def noneAt (t : Ty) : Term :=
  .field .required
    (.record (Authoring.ascribeFields t) ["v"] (.cons (.app "none" .nil) .nil)) "v"

/-- The body of `make`: a cell that holds nothing, at the cache's type. -/
def makeBody (A : Ty) : NativeEff := .perform .refMake (noneAt (cachedTy A))

/-- The body of `get`, at its request, the cell (level 0). It reads the cell (level 1). On
`none` it runs the loader (level 2), writes `some` of the list, and answers the list. On
`some`, it answers the held list (level 2). -/
def getBody : NativeEff :=
  .bind (.perform .refGet (.var 0))
    (.select (.var 1) .option
      (.bind (.perform (.param 0) (.lit .unit))
        (.bind (.perform .refSet
            (.app "pair" (.cons (.var 0) (.cons (.app "some" (.cons (.var 2) .nil)) .nil))))
          (.succeed (.var 2))))
      (.succeed (.var 2)))

/-- The body of `invalidate`, at its request, the cell: it writes `none` and answers `unit`. -/
def invalidateBody : NativeEff :=
  .bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.app "none" .nil) .nil))))
    (.succeed (.lit .unit))

/-- The service's name. -/
def serviceName : String := "ListCache"

/-- The three declarations: `make` as the service's initial program, and `get` and `invalidate`
as its methods, each taking the state alone. `get` declares the loader. -/
def decls (A E : Ty) : List DefDecl :=
  [ { name := "listCacheMake", request := .unit, answer := cellTy A,
      role := .serviceInit serviceName },
    { name := "listCacheGet", request := cellTy A, answer := .list A, error := E,
      role := .serviceMethod serviceName "get" 0, params := [loadParam A E] },
    { name := "listCacheInvalidate", request := cellTy A, answer := .unit,
      role := .serviceMethod serviceName "invalidate" 0 } ]

/-- **The block**: the three definitions and a main of `succeed unit`. An application module has
no main of its own (`docs/research/2026-10-13-emitted-services/README.md`, question 1). -/
def block (A E : Ty) : NativeEff :=
  .defs (decls A E) (.cons (makeBody A) (.cons getBody (.cons invalidateBody .nil)))
    (.succeed (.lit .unit)) .nil

end Effect4.Ref.Cache
