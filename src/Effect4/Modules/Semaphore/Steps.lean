module

public import Effect4.Modules.Semaphore.Cell
public import Effect4.Program.Authoring.Tuples

/-!
# Modules.Semaphore.Steps — Semaphore's five steps, each one pure term over the cell

A step is the pure part of one operation of Semaphore's first profile (decisions rows 259 to
261): a fixed total, counts that are natural numbers, and the live scan. Each step is the term
of one `Ref.modify`: it answers the pair of its reply and the cell's next value. It takes the
source of the cell's current value last.

| Step | The model's function | Its reply |
| --- | --- | --- |
| `takeStep` | `take` | whether the request took |
| `takeIfAvailableStep` | `takeIfAvailable` | whether the request took |
| `releaseStep` | `release` | `[the free count, whether a waiter is enrolled]` |
| `visitStep` | `visit` | the selected waiter's record, if any |
| `withdrawStep` | `withdraw` | nothing |

The model is `src/Effect4/Laws/Modules/Semaphore/Model.lean`. The rules of a step:

- **A step frames every field that it does not change**: it writes the cell by `recordSet`, or
  it answers the cell as it is.
- **No fold states its accumulator's type.** The empty list at the type of `xs` is `take xs 0`
  (`noneOf`), so every step term is inside the reader's domain.
- **Each pass that folds uses `Authoring.foldWith`**, whose two names are minted. A pass places
  its caller's term in the fold's body. With fixed names a caller's variable of the same name
  would read the folded element (`Test/Program/FoldHygiene.lean`).
- **A visit reserves nothing**: it leaves `taken`. A permit commits in the waiter's own take
  step, which checks the count again (decisions row 259).
- **A release is total**: it subtracts by `sub`, the truncated subtraction, so it releases at
  most what is taken (decisions row 261).

The words of a step term are shared (`src/Effect4/Modules/Words.lean`): one application of a
native atom each. The removal by identity is the shared pass `removeById`, whose term reads the
field `id` of an entry and no other. The term language has no local binding, so a step repeats
its passes.

Nothing here performs an effect, and the module exports no row: `Semaphore.make`, `take`,
`release` and `withPermits` come with the wrapper, after the mask. The laws are in
`src/Effect4/Laws/Modules/Semaphore/`. The batteries are under `Test/Program/`, each named
`Semaphore…`.
-/

@[expose] public section

namespace Effect4.Semaphore

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The words and the passes -/

/-- The free count: the total less what is taken. -/
def freeT (s : TermSrc) : TermSrc := app "sub" [field s "permits", field s "taken"]

/-- Whether a count fits the free count. -/
def fitsT (need s : TermSrc) : TermSrc := notT (app "lt" [freeT s, need])

/-- A waiter's record. -/
def mkWaiter (id need hint stamp : TermSrc) : TermSrc :=
  record waiterFields [("id", id), ("need", need), ("hint", hint), ("stamp", stamp)]

/-- The waiters without the request `id`: the shared removal pass. It folds with minted names,
and its body reads the field `id` of an entry and the caller's `id`. -/
def removeWaiter (waiters id : TermSrc) : TermSrc := removeById waiters id

/-- Whether a visit at a cursor may select the waiter `w`: its stamp is at or after the cursor,
and its count fits the free count. -/
def eligibleT (cursor s w : TermSrc) : TermSrc :=
  andT (notT (app "lt" [field w "stamp", cursor])) (notT (app "lt" [freeT s, field w "need"]))

/-- The waiters from the first one that a visit at the cursor may select: once an entry is
kept, every later entry is kept. The fold's body reads the caller's cursor and the caller's
cell. -/
def fromFirst (cursor s : TermSrc) : TermSrc :=
  foldWith (field s "waiters") (noneOf (field s "waiters")) fun kept w =>
    ifT (orT (notT (isEmpty kept)) (eligibleT cursor s w)) (snoc kept w) kept

/-- A visit's reply and stored value, from the waiters `rest` that start at the selected one.
Where no permit is free it answers nobody and the cell as it is. Otherwise it answers the first
entry of `rest`, if any, and that entry leaves the list. -/
def visitFrom (rest s : TermSrc) : TermSrc :=
  let waiters := field s "waiters"
  ifT (app "isZero" [freeT s])
    (app "pair" [app "get" [noneOf waiters, nat 0], s])
    (app "pair" [app "get" [rest, nat 0],
      recordSet s "waiters"
        (app "append" [app "take" [waiters, app "sub" [len waiters, len rest]],
          app "drop" [rest, nat 1]])])

/-! ## The steps -/

/-- **The model's `take`: take or enrol**, as the term of a `Ref.modify` over the cell `s`.
Reply: whether the request took. Where the count fits the free count, `taken` gains it.
Otherwise the request enrols at the list's end, with its hint, at the stamp `next`.

The request's own entry leaves first. On every state that the wrapper reaches this removal
changes nothing: a visit has already removed a resumed waiter before that waiter runs this
step again. The removal is here so that no step carries a premise on the request. -/
def takeStep (need id hint s : TermSrc) : TermSrc :=
  let rest := removeWaiter (field s "waiters") id
  ifT (fitsT need s)
    (app "pair" [bool true,
      recordSet (recordSet s "taken" (app "add" [field s "taken", need])) "waiters" rest])
    (app "pair" [bool false,
      recordSet (recordSet s "waiters" (snoc rest (mkWaiter id need hint (field s "next"))))
        "next" (app "add" [field s "next", nat 1])])

/-- **The model's `takeIfAvailable`**, as the term of a `Ref.modify`. Reply: whether the
request took. It never enrols. -/
def takeIfAvailableStep (need s : TermSrc) : TermSrc :=
  ifT (fitsT need s)
    (app "pair" [bool true, recordSet s "taken" (app "add" [field s "taken", need])])
    (app "pair" [bool false, s])

/-- **The model's `release`**, as the term of a `Ref.modify`. Reply: `[the free count, whether
a waiter is enrolled]`. `taken` loses the count by `sub`: at most what is taken (decisions row
261). The wrapper posts one helper where a waiter is enrolled. -/
def releaseStep (count s : TermSrc) : TermSrc :=
  let left := app "sub" [field s "taken", count]
  app "pair" [tuple [app "sub" [field s "permits", left], notT (isEmpty (field s "waiters"))],
    recordSet s "taken" left]

/-- **The model's `visit`: one visit of the walk**, as the term of a `Ref.modify`. Reply: the
selected waiter's record, if any. Where no permit is free it selects nobody. Otherwise it
selects the first waiter at or after the cursor whose count fits, and that waiter leaves the
list. `taken` stays: a wake reserves nothing (decisions row 259). The helper resolves the
selected waiter's hint, and it continues at that waiter's stamp plus one. -/
def visitStep (cursor s : TermSrc) : TermSrc := visitFrom (fromFirst cursor s) s

/-- **The model's `withdraw`**, as the term of a `Ref.modify`. Reply: nothing. The request's
entry leaves. A waiter holds nothing, so no other field changes and nobody is woken. -/
def withdrawStep (id s : TermSrc) : TermSrc :=
  app "pair" [unit, recordSet s "waiters" (removeWaiter (field s "waiters") id)]

end Effect4.Semaphore
