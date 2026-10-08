module

public import Effect4.Modules.Pool.Data
public import Effect4.Program.Authoring.Tuples

/-!
# Modules.Pool.Steps — Pool's six steps, each one pure term over the cell

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
| `drainStep` | `drain` | whether no lease is outstanding |

The model is `src/Effect4/Laws/Modules/Pool/Model.lean`. The rules of a step:

- **A step frames every field that it does not change**: it writes the cell by `recordSet`, or
  it answers the cell as it is.
- **A pass is Step data.** Its translation resolves the caller's captures before extending a fold scope.
- **An empty item list follows its input type.** No resource annotation enters the translated term.
- **The rule of enrolment is on the step**: the lease step adds a waiter only when the pool is
  open and no stamp is idle. An idle item beside enrolled waiters is a state of the cell.
- **A selection reserves nothing**: it changes the waiters alone. A lease commits in the
  borrower's own lease step, which checks again.
- **A return names its lease**: it frees the item only where that lease holds it, and it puts
  the item's stamp at the front of the idle stamps (decisions row 269).
- **The closer waits as a request** (decisions row 276, point 2): the closer's step enrols the
  closer where a lease is outstanding. It adds no field to the cell.

The words of a step term are shared (`src/Effect4/Modules/Words.lean`): one application of a
native atom each. The removal pass compares deferred keys. Two stamps are
compared by the atom `eq`. The step trees share their passes as data. Their translations resolve captures before
extending a fold's scope.

Nothing here performs an effect, and the module exports no row. The operations over the steps
are `src/Effect4/Modules/Pool/Ops.lean`: `Pool.make`, `Pool.use`, the close and the wake's
helper. The laws are in `src/Effect4/Laws/Modules/Pool/`. The batteries are under
`Test/Program/`, each named `Pool…`.
-/

@[expose] public section

namespace Effect4.Pool

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The words and the passes -/

/-- A waiter's record. -/
def mkWaiter (id hint : TermSrc) : TermSrc :=
  (Data.mkWaiter (.here idTy [idTy]) (.there idTy (.here idTy []))).term
    (Input.source [id, hint])

/-- The cell without the request `id`: the shared removal pass over the waiters. It folds with
minted names, and its body reads the field `id` of an entry and the caller's `id`. -/
def withdrawn (id s : TermSrc) : TermSrc :=
  (Data.withdrawn (.var 0) (.here idTy [cellTy (.var 0)])
    (.there idTy (.here (cellTy (.var 0)) []))).term (Input.source [id, s])

/-- No item, at the type of an option of an item. -/
def noItem (s : TermSrc) : TermSrc :=
  (Data.noItem (.var 0) (.here (cellTy (.var 0)) [])).term (Input.source [s])

/-- The stamp at the front of the idle stamps, or zero where none is idle: one fold over the
first entry. Its body reads no caller's term. -/
def headStamp (s : TermSrc) : TermSrc :=
  (Data.headStamp (.var 0) (.here (cellTy (.var 0)) [])).term (Input.source [s])

/-- An item as a lease of a stamp holds it. -/
def leasedAs (lease it : TermSrc) : TermSrc :=
  (Data.leasedAs (.var 0) (.var (.here .nat [itemTy (.var 0)]))
    (.var (.there .nat (.here (itemTy (.var 0)) [])))).term (Input.source [lease, it])

/-- The items, with the front idle item leased at the stamp `next`. The fold's body reads the
caller's cell: the front stamp and `next`. -/
def marked (s : TermSrc) : TermSrc :=
  (Data.marked (.var 0) (.here (cellTy (.var 0)) [])).term (Input.source [s])

/-- The front idle item as its new lease holds it: a list of at most one item. The fold's body
reads the caller's cell. -/
def leasedOf (s : TermSrc) : TermSrc :=
  (Data.leasedOf (.var 0) (.here (cellTy (.var 0)) [])).term (Input.source [s])

/-- Whether the lease `l` holds the item `i`, at one item's record. -/
def holdsT (i l it : TermSrc) : TermSrc :=
  (Data.holds (.var 0) (.here .nat [.nat, itemTy (.var 0)])
    (.there .nat (.here .nat [itemTy (.var 0)]))
    (.there .nat (.there .nat (.here (itemTy (.var 0)) [])))).term (Input.source [i, l, it])

/-- Whether the lease `l` holds the item `i`. The fold's body reads the caller's two stamps. -/
def heldBy (i l s : TermSrc) : TermSrc :=
  (Data.heldBy (.var 0) (Data.returnStamp (.var 0)) (Data.returnLease (.var 0))
    (Data.returnCell (.var 0))).term (Input.source [i, l, s])

/-- The items, with the item that the lease `l` holds at the stamp `i` idle again. The fold's
body reads the caller's two stamps. -/
def freed (i l s : TermSrc) : TermSrc :=
  (Data.freed (.var 0) (Data.returnStamp (.var 0)) (Data.returnLease (.var 0))
    (Data.returnCell (.var 0))).term (Input.source [i, l, s])

/-- Whether a lease is outstanding: whether a lease holds an item. One fold over the items,
whose body reads no caller's term. -/
def outstanding (s : TermSrc) : TermSrc :=
  (Data.outstanding (.var 0) (.here (cellTy (.var 0)) [])).term (Input.source [s])

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
  (Data.lease (.var 0)).term (Input.source [id, hint, s])

/-- **The model's `giveBack`: a return**, as the term of a `Ref.modify`. Reply: `[returned, a
wake is owed]`. Where the lease `l` holds the item `i`, the item is idle again and its stamp
joins the front of `available` (decisions row 269). A wake is owed where a waiter is enrolled:
the wrapper posts one helper at the count 1 then. Where the lease holds nothing, the step
answers the cell as it is: a stale lease frees no item that was leased again. -/
def returnStep (i l s : TermSrc) : TermSrc :=
  (Data.giveBack (.var 0)).term (Input.source [i, l, s])

/-- **The model's `select`: one selection of the wake at a count**, as the term of a
`Ref.modify`. Reply: the selected waiters' records, in the order of enrolment. The first
`count` waiters leave the list, and nothing else changes: a wake reserves nothing. The helper
then resolves each selected record's hint, in order. The term folds nothing. -/
def selectStep (count s : TermSrc) : TermSrc :=
  (Data.select (.var 0)).term (Input.source [count, s])

/-- **The model's `withdraw`**, as the term of a `Ref.modify`. Reply: nothing. The request's
entry leaves. A waiter holds nothing, so no other field changes and nobody is woken. -/
def withdrawStep (id s : TermSrc) : TermSrc :=
  (Data.withdraw (.var 0)).term (Input.source [id, s])

/-- **The model's `close`: the close's first step**, as the term of a `Ref.modify`. Reply:
`[this step began the close, the count of the waiters]`. The pool refuses new leases from now
on (decisions row 268). The count is the count of the helper that the close posts. -/
def closeStep (s : TermSrc) : TermSrc :=
  (Data.close (.var 0)).term (Input.source [s])

/-- **The model's `drain`: the closer's step** (decisions row 276, point 2), as the term of a
`Ref.modify`. Reply: whether the pool is drained, which says that no lease is outstanding.
Where a lease is outstanding, the closer enrols at the list's end, with its hint: each return's
helper then wakes it, and it runs this step again. Otherwise no entry of the closer stays, and
nothing else changes. The step changes the waiters alone.

The closer's own entry leaves first, as a borrower's does in `leaseStep`. The step reads the
items' flags and not `closing`: the close's first step runs before it. -/
def drainStep (id hint s : TermSrc) : TermSrc :=
  (Data.drain (.var 0)).term (Input.source [id, hint, s])

end Effect4.Pool
