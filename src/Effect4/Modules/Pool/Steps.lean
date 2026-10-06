module

public import Effect4.Modules.Pool.Cell
public import Effect4.Program.Authoring.Tuples

/-!
# Modules.Pool.Steps — Pool's five steps, each one pure term over the cell

A step is the pure part of one operation of Pool's first profile (decisions rows 267 to 269):
a fixed size, one borrower for an item, and a wake that selects once. Each step is the term of
one `Ref.modify`: it answers the pair of its reply and the cell's next value. It takes the
source of the cell's current value last.

| Step | The model's function | Its reply |
| --- | --- | --- |
| `leaseStep` | `lease` | `[closed, the leased item's record, if any]` |
| `returnStep` | `giveBack` | `[returned, a wake is owed]` |
| `selectStep` | `select` | the selected waiters' records, in order |
| `withdrawStep` | `withdraw` | nothing |
| `closeStep` | `close` | `[this step began the close, the count of the waiters]` |

The model is `src/Effect4/Laws/Modules/Pool/Model.lean`. The rules of a step:

- **A step frames every field that it does not change**: it writes the cell by `recordSet`, or
  it answers the cell as it is.
- **No fold states its accumulator's type.** The empty list at the type of `xs` is `take xs 0`
  (`noneOf`), and no item at the type of an option of an item is `get (take items 0) 0`. So
  every step term is inside the reader's domain.
- **Each pass that folds uses `Authoring.foldWith`**, whose two names are minted. A pass places
  its caller's term in the fold's body. With fixed names a caller's variable of the same name
  would read the folded element (`Test/Program/FoldHygiene.lean`).
- **The rule of enrolment is on the step**: the lease step adds a waiter only when the pool is
  open and no stamp is idle. An idle item beside enrolled waiters is a state of the cell.
- **A selection reserves nothing**: it changes the waiters alone. A lease commits in the
  borrower's own lease step, which checks again.
- **A return names its lease**: it frees the item only where that lease holds it, and it puts
  the item's stamp at the front of the idle stamps (decisions row 269).

The words of a step term are shared (`src/Effect4/Modules/Words.lean`): one application of a
native atom each. The removal by identity is the shared pass `removeById`. Two stamps are
compared by the atom `eq`. The term language has no local binding, so a step repeats its
passes.

Nothing here performs an effect, and the module exports no row: `Pool.make` and `Pool.use`
come with the public slice, and so does the wake's helper. The laws are in
`src/Effect4/Laws/Modules/Pool/`. The batteries are under `Test/Program/`, each named `Pool…`.
-/

@[expose] public section

namespace Effect4.Pool

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The words and the passes -/

/-- A waiter's record. -/
def mkWaiter (id hint : TermSrc) : TermSrc := record waiterFields [("id", id), ("hint", hint)]

/-- The cell without the request `id`: the shared removal pass over the waiters. It folds with
minted names, and its body reads the field `id` of an entry and the caller's `id`. -/
def withdrawn (id s : TermSrc) : TermSrc :=
  recordSet s "waiters" (removeById (field s "waiters") id)

/-- No item, at the type of an option of an item. -/
def noItem (s : TermSrc) : TermSrc := app "get" [noneOf (field s "items"), nat 0]

/-- The stamp at the front of the idle stamps, or zero where none is idle: one fold over the
first entry. Its body reads no caller's term. -/
def headStamp (s : TermSrc) : TermSrc :=
  foldWith (app "take" [field s "available", nat 1]) (nat 0) fun _ stamp => stamp

/-- An item as a lease of a stamp holds it. -/
def leasedAs (lease it : TermSrc) : TermSrc :=
  recordSet (recordSet it "borrowed" (bool true)) "lease" lease

/-- The items, with the front idle item leased at the stamp `next`. The fold's body reads the
caller's cell: the front stamp and `next`. -/
def marked (s : TermSrc) : TermSrc :=
  foldWith (field s "items") (noneOf (field s "items")) fun out it =>
    snoc out (ifT (app "eq" [field it "stamp", headStamp s]) (leasedAs (field s "next") it) it)

/-- The front idle item as its new lease holds it: a list of at most one item. The fold's body
reads the caller's cell. -/
def leasedOf (s : TermSrc) : TermSrc :=
  foldWith (field s "items") (noneOf (field s "items")) fun kept it =>
    ifT (app "eq" [field it "stamp", headStamp s]) (snoc kept (leasedAs (field s "next") it)) kept

/-- Whether the lease `l` holds the item `i`, at one item's record. -/
def holdsT (i l it : TermSrc) : TermSrc :=
  andT (app "eq" [field it "stamp", i])
    (andT (field it "borrowed") (app "eq" [field it "lease", l]))

/-- Whether the lease `l` holds the item `i`. The fold's body reads the caller's two stamps. -/
def heldBy (i l s : TermSrc) : TermSrc :=
  foldWith (field s "items") (bool false) fun found it => orT found (holdsT i l it)

/-- The items, with the item that the lease `l` holds at the stamp `i` idle again. The fold's
body reads the caller's two stamps. -/
def freed (i l s : TermSrc) : TermSrc :=
  foldWith (field s "items") (noneOf (field s "items")) fun out it =>
    snoc out (ifT (holdsT i l it) (recordSet it "borrowed" (bool false)) it)

/-! ## The steps -/

/-- **The model's `lease`: lease or enrol**, as the term of a `Ref.modify` over the cell `s`.
Reply: `[closed, the leased item's record, if any]`. At a closing pool the reply says that the
pool refused. With no idle stamp the request enrols at the list's end, with its hint.
Otherwise the front idle item leaves `available`, it becomes borrowed at the stamp `next`, and
`next` gains one: the reply holds the item's record as its lease holds it.

The request's own entry leaves first. On every state that the wrapper reaches this removal
changes nothing: a selection has already removed a resumed borrower before that borrower runs
this step again. The removal is here so that no step carries a premise on the request. -/
def leaseStep (id hint s : TermSrc) : TermSrc :=
  ifT (field s "closing")
    (app "pair" [tuple [bool true, noItem s], withdrawn id s])
    (ifT (isEmpty (field s "available"))
      (app "pair" [tuple [bool false, noItem s],
        recordSet s "waiters" (snoc (removeById (field s "waiters") id) (mkWaiter id hint))])
      (app "pair" [tuple [bool false, app "get" [leasedOf s, nat 0]],
        recordSet
          (recordSet (recordSet (withdrawn id s) "items" (marked s)) "available"
            (app "drop" [field s "available", nat 1]))
          "next" (app "add" [field s "next", nat 1])]))

/-- **The model's `giveBack`: a return**, as the term of a `Ref.modify`. Reply: `[returned, a
wake is owed]`. Where the lease `l` holds the item `i`, the item is idle again and its stamp
joins the front of `available` (decisions row 269). A wake is owed where a waiter is enrolled:
the wrapper posts one helper at the count 1 then. Where the lease holds nothing, the step
answers the cell as it is: a stale lease frees no item that was leased again. -/
def returnStep (i l s : TermSrc) : TermSrc :=
  ifT (heldBy i l s)
    (app "pair" [tuple [bool true, notT (isEmpty (field s "waiters"))],
      recordSet (recordSet s "items" (freed i l s)) "available" (front i (field s "available"))])
    (app "pair" [tuple [bool false, bool false], s])

/-- **The model's `select`: one selection of the wake at a count**, as the term of a
`Ref.modify`. Reply: the selected waiters' records, in the order of enrolment. The first
`count` waiters leave the list, and nothing else changes: a wake reserves nothing. The helper
then resolves each selected record's hint, in order. The term folds nothing. -/
def selectStep (count s : TermSrc) : TermSrc :=
  app "pair" [app "take" [field s "waiters", count],
    recordSet s "waiters" (app "drop" [field s "waiters", count])]

/-- **The model's `withdraw`**, as the term of a `Ref.modify`. Reply: nothing. The request's
entry leaves. A waiter holds nothing, so no other field changes and nobody is woken. -/
def withdrawStep (id s : TermSrc) : TermSrc := app "pair" [unit, withdrawn id s]

/-- **The model's `close`: the close's first step**, as the term of a `Ref.modify`. Reply:
`[this step began the close, the count of the waiters]`. The pool refuses new leases from now
on (decisions row 268). The count is the count of the helper that the close posts. -/
def closeStep (s : TermSrc) : TermSrc :=
  app "pair" [tuple [notT (field s "closing"), len (field s "waiters")],
    recordSet s "closing" (bool true)]

end Effect4.Pool
