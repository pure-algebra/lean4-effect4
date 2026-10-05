# 2026-10-05 the list fold's design: two binders, the identity of a handle, nested handles

Status: research note (history, not authority). Base: `c3263529` (`refactor/phase1-phase3`).
A design for the seat that follows seat T3b. No file of the tree changed.

**The one thing to know first.** Decisions row 228 asks for a pure list fold with two binders,
and row 229 for the identity of a handle inside a term. This note fixes both. The fold is one
constructor of `Term`, with `iterate`'s binder convention and an optional type for its
accumulator. `FoldModel.lean` beside this note writes the six steps of the groundwork plan as
one term each, over the tree's own values and atoms. Its 29 guard checks hold. Three atoms are
proposed, and two of them add no meaning. Nested handles need no new judgment, because the
membership relation already reads through lists and tuples. One cost is not local: the
TypeScript printer of a term must take the environment's length.

## Question

What are the fold's rules, what must stand beside it, and what does the slice touch?

The groundwork plan (`docs/research/2026-10-05-claude-lead/groundwork-plan.md`, F4) accepts the
design on two conditions. Six named steps are each one evaluated term. The note also states:

- the typing rule, the scope rule, weakening and evaluation;
- the laws on handles;
- the wire entry, and the printed and read forms.

## What was read or run

| Item | How |
| --- | --- |
| `Term`, `Term.scoped`, `NativeAtom`, `NativeAtom.eval`, `evalTerm` in `src/Effect4/Machine/Term.lean` | read |
| `ScopedOp` and the binder convention, in seat T3b's design (`docs/research/2026-10-04-seat-T3b-design.md`, F3, F7, F8) | read |
| The `iterate` constructor and its rows in `src/Effect4/Program/Eff.lean` and `src/Effect4/Program/Scoped.lean` | read |
| `printTerm` in `src/Effect4/Codegen/PrintLeaf.lean`; `readLeaf` in `src/Effect4/Codegen/Read.lean` | read |
| `NativeAtom.typeOf` in `src/Effect4/Program/NativeAtom.lean`; `term?` in `src/Effect4/Program/Checker.lean` | read: the signatures |
| `Fits` in `src/Effect4/Laws/Program/Typed/Membership.lean` | read |
| `docs/research/2026-10-05-claude-lead/fold-design/FoldModel.lean` | tested: 29 guard checks hold, and the run exits 0; a copy with one false guard fails |
| The modules that name the newest constructor of `Term`, `tupleAt` | counted: 21 |
| Any Lean file of the tree, any proof | not written |

## Findings

### F1. The constructor and its rules

```
Term.fold (accTy : Option Ty) (list init body : Term)
```

| Rule | Statement |
| --- | --- |
| Binders | `body` is at the fold's level plus two. It reads the accumulator at `var n` and the element at `var (n + 1)`, where `n` is the environment's length at the fold |
| Scope | `list` and `init` are scoped at `n`, and `body` at `n + 2` |
| Capture | `body` reads every outer variable below `n` unchanged |
| Evaluation | `list` and `init` are evaluated once. The body runs once for each element, from the head. An empty list answers `init`, and the body is not evaluated |
| Failure | A body that refuses on one element refuses the whole fold. No partial answer exists |
| Weakening | One map of every variable at or above the cut, bound or free. A binder needs no case of its own, because variables are levels |
| Typing | `list : list A` and `init : B0`. The accumulator's type `B` is `accTy` when it is stated, and `B0` otherwise. `B0` is a subtype of `B`. Under `B` at `n` and `A` at `n + 1`, `body` has a subtype of `B`. The fold has type `B` |

- **The binder order is `iterate`'s.** Its step reads the cursor and then the body's answer. The
  carried value comes first in both.
- **The stated type is `iterate`'s too** (DI-91). An accumulator that starts as the empty list
  has the type `list never`, and its body answers a wider list. One stated type covers both.
- **The fold is pure.** It is a term, so a `Ref.modify` that holds one stays one atomic step
  that answers `B` and stores `A`.
- **The fold has no early exit.** A step that must stop carries a flag in its accumulator. The
  fold still visits every element.

### F2. The six steps, each as one term

The model's term language is the tree's `Term` cut to what the steps need, with `fold` added.
Each atom of a body is evaluated by the tree's `nativeAtom`, on the tree's `Val`.

| Step of the plan | The term | Its accumulator | Checked against |
| --- | --- | --- | --- |
| 1. The queue accepts pending offers into freed room | `acceptT` | room, messages, kept offers, answered identities, a stop flag | `acceptRef`, the Queue contract's `acceptLoop`, on 30 inputs |
| 2. The requests that became ready are named | `nameT` | the list of signals | one trace |
| 3. A semaphore grants permits in order while permits remain | `grantT` | permits, granted, still waiting, a stop flag | `grantRef` on 30 inputs |
| 4. A hub hands one message to every subscriber | `publishT` | the subscribers, each with one message more | one trace; the body reads the message from outside |
| 5. One waiter leaves, by the identity of its handle | `removeT` | the waiters kept | two traces, and the atom's refusal of two kinds |
| 6. The oldest `k` entries leave a cache | `evictT`, `evictFoldT` | a counter and the entries kept | `List.drop` at six values of `k` |

The model also checks the fold's own rules:

- the empty list, and the order of the steps;
- an outer variable in the body;
- a fold inside a fold, whose inner body reads the outer element;
- a failing body;
- the scope check, with two red cases.

Every step keeps its answer under weakening at every cut of its environment. A map that skips
a fold's body does not, which is the red control.

### F3. What the steps needed beside the fold

- **`take` and `drop`.** Step 1 takes the part of a batch that fits and keeps the rest. The
  Queue's consuming step takes a prefix of the buffer. Both atoms are folds with a counter
  (`takeFoldT`, `evictFoldT`), so they add no meaning. Row 228 allows them for a demonstrated
  consumer, and these two steps are the consumers.
- **`sameHandle`.** Step 5 compares two handles. The tree's `eq` reads numbers and strings only.
- **Both arms of a conditional are evaluated.** `ite` is an atom, and an atom's arguments are
  all evaluated first. So each arm of a body must be total. Every body of the model is.
- **A list grows at its end by `append`.** That is one pass for each element, so a fold that
  builds a list is quadratic. The plan's rule holds: a bulk atom is added only for a named
  consumer, and none is proposed here.

### F4. The identity of a handle, and nested handles

| Point | Statement |
| --- | --- |
| The atom | `sameHandle a b` answers whether two handles of one kind have one identity |
| Its typing | Both arguments are at `refOf`, or both at `deferredOf`, at any payload types. It answers `bool` |
| Its evaluation | Two handle values with one kind byte: equal exactly when their keys are equal. It refuses two kinds, and typing excludes that case |
| What it never reads | A payload, a cell's content, or a registration number as a number |

**Nested handles need no new judgment.** `Fits` reads through a list, a tuple and an option, and
at a handle it asks the world for the declaration (`RefDeclared`, `PromiseDeclared`). Take a
cell whose type is a list of pairs of a promise and a number. Its value fits only when every
nested promise is declared at its payload types.

The laws that the slice owes, each over `Fits` and the world's order:

1. `sameHandle` is total on arguments that fit one handle type.
2. It is reflexive and symmetric, and it decides the equality of the two keys.
3. A handle that an allocation just made is equal to no handle in a value that fits the earlier
   world. So a fresh request is a member of no stored list.
4. A later world keeps every answer of `sameHandle` and every membership.
5. The handles in a fold's answer are handles of its environment. `RawHandles.evalTerm_handles`
   (`src/Effect4/Laws/Machine/TermHandles.lean`) states this for the constructors of today.

Each target's relation must map one handle to one host object, so that `sameHandle` prints as
the host's identity test (row 229).

### F5. The faces

- **The printed form** is a call of one prelude function, as every atom prints:
  `fold(xs, init, (aN, aM) => body)`, with `M` one above `N`. A stated type prints as the
  call's type argument. It is printed and not read, as the annotated loop is, because no reader
  of types exists.
- **The term printer must take the environment's length.** `printTerm` has no level today,
  because a variable prints by its own position. The fold's two parameter names are the names of
  levels `n` and `n + 1`, so the printer must know `n`. The reader has it already (`readLeaf`).
  This change passes through every leaf printer and its law. It is the widest part of the
  slice.
- **The wire** gains one tag of `Term`, appended. The retained baseline of the alphabets changes
  by its named promotion (DI-47).
- **The evaluator's clause is structural.** The model's `eval` recurses on the body inside the
  list's own fold, and Lean accepts it with no measure. The lowering to OCaml then passes a
  closure to the list fold. The slice checks that route first.

### F6. A fold inside an operation's term

Seat T3b's convention gives an operation's term one binder at the node's level `n`. A fold
inside that term stands at `n + 1`, so it binds `n + 1` and `n + 2`. The Queue's step is then
one `Ref.modify` whose term folds the pending offers and answers the signals to post.

### F7. The obligations, placed

| Obligation | Concept and requirement | Reach | Not established |
| --- | --- | --- | --- |
| `fold-typed-atomic-update` | store-typing, R4 | The rules of F1 as theorems: scope, weakening, typed evaluation over `Fits`, the printed and read equations of the leaf | Nothing about a module that uses the fold |
| `handle-identity-laws` | store-typing, R4 | The five laws of F4 | No correspondence in a target; that is each target's relation |

Both are open parts of R4 now. The slice states each as a planned goal over its definitions.

### F8. What the slice touches

- 21 modules name `tupleAt`, the newest constructor of `Term`. A new constructor meets the same
  set. It holds the term language, the generated folds, the typing rules and their refusals,
  and the authoring surface. It also holds the leaf printer and reader, the wire, and ten law
  modules.
- Three atoms each add a row of the atom table, a typing scheme and a prelude line. Each also
  adds a case of `NativeAtom.Sound`, the law that an atom's answer has its scheme's type.
- The slice regenerates the groups that seat T3b regenerates, so it starts after T3b's merge.
  It lands before the Queue's first path, whose step is its first consumer.
- Its acceptance is the model's six steps as terms of the tree, in a `Test` fixture.

## Proposals (not rulings)

1. **The fold is one constructor of `Term`,** with an optional type for its accumulator. No
   counted loop and no early exit are added.
2. **The accumulator is the lower binder, and the element the upper,** as in `iterate`.
3. **`take` and `drop` are added,** for the Queue's consuming step and a batch's acceptance.
4. **`sameHandle` is one atom** over two handles of one kind, and `eq` stays as it is.
5. **The fold prints as a prelude call,** and the term printer takes the environment's length.
6. **The slice follows seat T3b's merge and precedes the Queue's first path.**

## What this does not establish

- The model is a finite probe outside the tree. Its term language is a cut of `Term`, and it
  has no typing.
- Each agreement with a direct function holds on the listed inputs only.
- The typing rule and the five laws on handles are stated, not proved. No Lean of the tree was
  written.
- The lowering of the evaluator's clause to OCaml was not run.
- The count of 21 modules is a search for one name. It does not size the proofs.
- The printed form was not checked by tsgo 7.
