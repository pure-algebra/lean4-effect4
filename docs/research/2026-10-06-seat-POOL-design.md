# 2026-10-06 seat POOL design: Pool's cell, model, steps and statements

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-pool-brief.md`. Card:
`docs/research/2026-10-05-claude-lead/module-cards/pool.md`. Decisions rows 267 to 269 rule
the profile. No Lean file of the slice exists yet.

## 1. The cell, an item and a waiter

The cell is one record at the card's five fields. It has one type parameter, the type `A` of
a resource.

| Record | Field | Type | Meaning |
| --- | --- | --- | --- |
| cell | `items` | a list of items | every item, in the order of acquisition; no step adds or removes one |
| cell | `available` | a list of numbers | the stamps of the idle items, in the order of reuse, the front first |
| cell | `waiters` | a list of waiters, oldest first | the requests that wait |
| cell | `closing` | a Boolean | the close has begun |
| cell | `next` | a number | the stamp of the next lease |
| item | `stamp` | a number | the item's identity: its place in the order of acquisition |
| item | `resource` | `A` | the acquired value; two items may hold equal values |
| item | `borrowed` | a Boolean | a lease holds the item |
| item | `lease` | a number | the stamp of the item's latest lease |
| waiter | `id` | a `Deferred` of nothing | the request's identity, the shared `idTy` |
| waiter | `hint` | a `Deferred` of nothing | the hint that the helper resolves |

**A lease in the cell** is an item's record with `borrowed` true: its `stamp` and its `lease`
are the card's pair. The item keeps the card's flag, and it gains the lease's stamp. So a
return names its lease, and a return of a lease that holds nothing changes nothing.

The alternative is one optional stamp in place of the flag and the number. Its empty value
has a type (`Semaphore.visitFrom` builds one). Each test of it needs `getOrElse` and `isSome`,
and so does the wrapper's read of a lease's stamp. Neither atom has a rule yet. The flag and
the number need `eq` alone, so I take them.

**Outside the cell** stay the borrower's fiber, the body, the return's hook and the item's
finalizer. A helper's count and its selected list stay in the helper. The cell holds no
lease that has returned.

The initial value takes the acquired resources as a list of terms, at a size that the
program states. It gives each resource the stamp of its position, and every item is idle.

## 2. The five steps

Each step is one term for one `Ref.modify`. It answers the pair of its reply and the cell's
next value, and it takes the source of the cell's current value last.

| Step | Arguments | Reply | The cell's change |
| --- | --- | --- | --- |
| `leaseStep` | the identity, the hint | `[closed, the leased item's record, if any]` | The request's own entry leaves first. At a closing pool nothing else changes. With no idle item the request enrols at the list's end. Otherwise the front idle item leaves `available`, it becomes borrowed at the stamp `next`, and `next` gains one |
| `returnStep` | the item's stamp, the lease's stamp | `[returned, a wake is owed]` | Where that lease holds that item, the item becomes idle and joins the front of `available`. Otherwise nothing changes |
| `selectStep` | the count | the selected waiters' records, in order | the first `count` waiters leave the list |
| `withdrawStep` | the identity | nothing | the request's entry leaves |
| `closeStep` | none | `[this step began the close, the count of the waiters]` | `closing` becomes true |

Five choices that the card leaves open:

- **A lease removes its own request's entry first**, as Semaphore's take does. So no step has
  a premise on its request.
- **A return owes a wake** exactly when it returned and a waiter is enrolled. The fixture
  posts one helper with the count 1 then, as the pin posts no task with no waiter.
- **A selection removes what it selects.** A resumed borrower that finds no idle item enrols
  again, at the list's end.
- **The close's first step tells whether it began the close.** A second close then finalizes
  nothing. Its count is the helper's count.
- **A refused lease answers `closed`.** What `use` does with it belongs to the public slice.

The selection is `take` and `drop`, with no fold. The lease and the return fold over the
items, and their bodies compare two stamps by the atom `eq`. The lease's folds read the cell
in their bodies, so the cell's source is a caller's term under a fold there.

## 3. The model

The model is in `Effect4.Pool.Model`. Its state has the cell's five fields. An item is four
numbers and a Boolean: a resource is a number that names its value. A waiter is its identity,
a number. The model holds no handle and no hint.

| Transition | Answer |
| --- | --- |
| `lease s id` | the next state, whether the pool refused, and the leased item, if any |
| `giveBack s item lease` | the next state, whether the lease returned, and whether a wake is owed |
| `select s count` | the next state, and the selected identities |
| `withdraw s id` | the next state |
| `close s` | the next state, whether this step began the close, and the count of the waiters |

Each transition is total. The profile predicate has four parts.

1. The items' stamps are distinct.
2. A stamp is in `available` exactly when an item of that stamp is not borrowed, and no stamp
   is there twice. So the idle items and the leased items together are the items.
3. The stamps of the leases that hold an item are distinct, and each is below `next`.
4. No two waiters share an identity.

An idle item beside enrolled waiters is a state of the profile. The rule is on the step:
`lease` adds a waiter only when the pool is open and `available` is empty.

## 4. The relation

The shared `Table` serves as it is (`src/Effect4/Laws/Modules/Table.lean`): each model
identity's handle and its current hint. A lease that enrols sets its own hint by
`Table.renew`. One more map gives each model resource its value, as the Queue's relation maps
a message. The cell's value is a function of the table, that map and a model state.

## 5. The statements

- **Typing.** At every scope, for caller's terms of the arguments' types, a step has the type
  of the pair of its reply and the cell. The resource's type is its own normal form.
- **Agreement.** At every scope, a step reads the tuple of the model's reply and the model's
  next state through the table. The premises are the table's injectivity where a step tests
  an identity, and `Captured` for each term under a fold. A selection's reply is the selected
  waiters' records, so it names the selected identities and their hints.
- **The model's facts.** The profile is closed under each transition. Four more facts are the
  brief's: the enrolment rule, and the selection's prefix. A return puts its item at the front
  and keeps every item. No lease begins after the close's first step.
- **The store.** `step_updates`, `step_keeps_cell` and `cell_read` join a statement to one
  `Ref.modify` (`src/Effect4/Laws/Modules/Store.lean`).

## 6. The shared pieces

Each piece below is reused as it is.

- `idTy`, the words and `removeById` (`src/Effect4/Modules/Words.lean`).
- `Table`, with `Table.Injective` and `Table.renew`.
- `Reads`, `Captured` and the reading rules (`src/Effect4/Laws/Modules/Reading.lean`).
- `Types`, `TypesEach`, `CapturedTy` and the builder rules
  (`src/Effect4/Laws/Modules/Checking.lean`).
- The three connectors of `Store.lean`, and the record rules of
  `src/Effect4/Laws/Program/Typing/TermIntro.lean`.
- The list facts `foldl_snoc_map`, `foldl_or_any` and `foldl_append_flatMap`
  (`src/Effect4/Data/Constructive.lean`).

The fixtures of part 1 use `posted`, `onInterrupt` and `waitAt`
(`src/Effect4/Modules/Waiting.lean`), and the mask's builder. They do not use `waitRetry`.
Its own mask ends before the body's hook is installed, so the lease and the hook would be two
regions.

Three rules name no module, and each goes where the coordinator allocated it:

| Rule | Shared file | Place |
| --- | --- | --- |
| `nativeAtomTy_eq`: `eq` at two numbers answers a Boolean | `src/Effect4/Laws/Program/Typing/TermIntro.lean` | after `nativeAtomTy_lt` |
| `reads_eq`: what `eq` reads at two numbers | `src/Effect4/Laws/Modules/Reading.lean` | after `reads_lt` |
| `types_eq`: what `eq` types at | `src/Effect4/Laws/Modules/Checking.lean` | after `types_lt` |

The front stamp of `available` is read by one fold over its first entry. So the steps use no
`getOrElse`, and no other shared rule is added.
