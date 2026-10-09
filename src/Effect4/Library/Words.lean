module

public import Effect4.Program.Authoring.Records
public import Effect4.Program.Authoring.Folds

/-!
# Modules.Words — the words of a step term, shared by the composed modules (decisions row 255)

A composed module writes each step as one pure term over its cell
(`src/Effect4/Library/Queue/Steps.lean`, `src/Effect4/Library/Semaphore/Steps.lean`). This file
holds the pieces of a step term that name no module.

- **`idTy`** is the type of a request's identity, and of a hint that carries nothing.
- **The words** are one application of a native atom each. `minT` is a selection over one.
- **`removeById`** is the removal pass: the entries of a list without the entries of one
  identity. An entry is a record with an `id` field.
- **`single`, `front` and `listOf`** write a list out from terms, with no fold.

A module's own records, passes and steps stay in the module's folder. The laws of the words are
in `src/Effect4/Laws/Step/`: what each word reads (`Reading.lean`), and what each word types
at (`Checking.lean`). Nothing here performs an effect.
-/

@[expose] public section

namespace Effect4.Modules

open Effect4.Program Effect4.Program.Authoring

/-- A request's identity, and a hint that carries nothing: a `Deferred` of nothing that cannot
fail. Two identities are compared by `sameHandle`, and never by a number. -/
def idTy : Ty := .deferredOf .unit .never

/-! ## The words of a step term

Each is one application of a native atom. Their consumers are the passes and the steps of a
composed module. -/

def nilT : TermSrc := app "nil" []
def noneT : TermSrc := app "none" []
def len (xs : TermSrc) : TermSrc := app "length" [xs]
/-- `xs` with `x` behind it. -/
def snoc (xs x : TermSrc) : TermSrc := app "append" [xs, app "cons" [x, nilT]]
def notT (b : TermSrc) : TermSrc := app "not" [b]
def andT (a b : TermSrc) : TermSrc := app "and" [a, b]
def orT (a b : TermSrc) : TermSrc := app "or" [a, b]
def isEmpty (xs : TermSrc) : TermSrc := app "isZero" [len xs]
/-- A selection between two evaluated terms: the atom is strict in both. -/
def ifT (c t f : TermSrc) : TermSrc := app "ite" [c, t, f]
/-- The identity of two handles of one kind (decisions row 229). -/
def same (a b : TermSrc) : TermSrc := app "sameHandle" [a, b]
/-- The empty list at the type of `xs`: no fold has to state its accumulator's type. -/
def noneOf (xs : TermSrc) : TermSrc := app "take" [xs, nat 0]
def minT (a b : TermSrc) : TermSrc := ifT (app "lt" [a, b]) a b

/-! ## The removal by identity

The pass folds with `foldWith`: its two names are minted, so a caller's term keeps its reading
inside the body. The body reads the field `id` of an entry and no other. -/

/-- The entries without the request `id`. -/
def removeById (entries id : TermSrc) : TermSrc :=
  foldWith entries (noneOf entries) fun kept entry =>
    ifT (same (field entry "id") id) kept (snoc kept entry)

/-! ## Lists that a term writes out

`single`, `front` and `listOf` build a list from terms, with no fold. Their first consumer is
Pool (`src/Effect4/Library/Pool/`): the items of the initial value, and a returned item at the
front of the idle items. -/

/-- The list of one element. -/
def single (x : TermSrc) : TermSrc := app "cons" [x, nilT]

/-- `xs` with `x` in front of it. -/
def front (x xs : TermSrc) : TermSrc := app "append" [single x, xs]

/-- The list of the given terms, in order. The empty list is `nilT`, at the empty element
type. -/
def listOf : List TermSrc → TermSrc
  | [] => nilT
  | [x] => single x
  | x :: xs => front x (listOf xs)

end Effect4.Modules
