# 2026-10-05 the mask's second note: its check, its printed TypeScript form and its steps

Status: research note (history, not authority). Base: `0002ca73` (`refactor/phase1-phase3`).
A design for the owner's sign-off. No file of the tree changed.

**The one thing to know first.** Decisions row 239 asks for five statements before a seat
builds the mask. This note gives them. It also proposes two changes to row 239, because they
make all five simple:

1. the saved state has its own opaque type, so ordinary typing is the whole check;
2. a restore site is one node, and not a selection that holds the body twice.

With these the mask prints row by row in the public API. `read_print` and `read_exact` keep
their statements and gain two rows. The printed form runs the same loop iterations as the
machine, so no relation for erased steps is owed. Seven behaviours of the printed form equal
the native mask's on rc.112 and on 4.0.1, and tsgo 7 types it on both.

## Question

Row 239 owes five statements before any seat:

1. the checked recognition of the whole expansion at program admission;
2. the saved value used only at recognized restore sites;
3. nested masks;
4. the read and print equations, with `read_print` and `read_exact` unchanged in meaning;
5. the behaviour relation for the two extra steps.

What is each one, over the tree's own definitions?

## What was read or run

| Item | How |
| --- | --- |
| `uninterruptible`, `interruptible`, `uninterruptibleMask`, `interruptibleMask`, `setInterruptible`, `setFiberInterruptible` in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts` | read |
| The same declarations in `vendor/effect-4.0.1/src/internal/effect.ts` | read, and compared by `diff`: equal text. The release adds two helpers beside them, `fiberEnterUninterruptibleUnsafe` and `fiberEnterInterruptibleUnsafe` |
| `FrameFiber.uninterruptible`, `interruptibleRegion`, `setFiberInterruptible` in `src/Effect4/Machine/Frames.lean` | read |
| `WithFiberAction` and its evaluation in `src/Effect4/Machine/Fibers.lean` | read |
| `compileEff`, `actionAt`, `suspendBodyAt` in `src/Effect4/Program/Compile.lean` | read |
| `check`, `checkAction` in `src/Effect4/Program/Checker.lean`; `Val.hasTy` in `src/Effect4/Program/Typed.lean`; the named handle types of `src/Effect4/Program/Ty.lean` | read |
| The row table and the printer's fold, `src/Effect4/Codegen/Templates.lean`; the template formers, `src/Effect4/Codegen/Template.lean`; `readRow` and `readArg`, `src/Effect4/Codegen/Read.lean` | read |
| `read_print` in `src/Effect4/Laws/Codegen/ReadPrint.lean`; `readRow_exact` in `src/Effect4/Laws/Codegen/Read.lean` | read: the statements only |
| `LayerTerm.ref` and its docstring in `src/Effect4/Program/Eff.lean` | read |
| `docs/research/2026-10-05-claude-lead/mask-probes/mask-form.ts` on rc.112 and 4.0.1, with bun 1.4.2; each output sits beside it | tested: eight scenarios on each build |
| `docs/research/2026-10-05-claude-lead/mask-probes/mask-form-types.ts`, by tsgo 7.0.0-dev.20260629.1 against each build | tested: one error on each build, the red control |
| Codex's review of the first mask design, `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/w-design-review/mask-review.md` | read |
| Any Lean file of the tree, any proof | not written |

## Findings

### F1. What the pin does

`uninterruptibleMask(f)` reads the fiber's flag once, at entry (reading):

- when the fiber is masked already, it runs `f(identity)`;
- otherwise it masks the fiber, pushes the frame that restores the flag, and runs
  `f(interruptible)`.

So `restore` is one of two known functions, and the entry flag selects it. The saved Boolean
of row 239 is the index of that function. A restore site is the application of the function.
This is the standard first-order reading of a function taken from a closed family: a tag for
the function, and one node for its application.

The frame that restores the flag has one arm for every exit. When it leaves the fiber
interruptible with a pending cause, it fails with that cause (`setInterruptible`).

### F2. Three faults of the ruled selection

Row 239 writes a restore site as `select saved .bool (interruptible e) e`. Three points make
that form a poor image of `restore(e)`.

- **The body is written twice, so it has two sites.** A layer's identity is its path in the
  program (`LayerTerm`'s docstring). The two copies of `e` hold two layer identities, and the
  printed `restore(e)` holds one object. Two runs of one site with different saved values then
  use two memo keys in the machine and one in the target. This is a reading and was not run.
  Fork sites and every other name by path double in the same way.
- **A selection is a suspension, and the call is not.** `compileEff` gives `select` one
  `Prim.suspend` step, as its printed `Effect.suspend(() => …)` runs one. The call `restore(e)`
  runs none. The selection spends one loop iteration more at every site.
- **A row cannot print it.** The site is recognized by a relation between two children: the
  first arm is `interruptible` of the second. A row's classifier reads leaves only (`ArgPat`),
  and the printer is a fold over printed children (`tableLayer`). The form needs a new kind of
  classifier, or a recognizer outside the fold.

A fourth point is Codex's: a saved value typed `bool` can be used as a Boolean, and the target
has no spelling for that use. So the selection also needs a checker of its own.

### F3. The proposal: a type, an action and a node

| Piece | What it is | Its cost |
| --- | --- | --- |
| The type `Ty.maskRestore` | An opaque host type, written `.handle` with its own target, as `Ty.scope` and `Ty.context` are. Its value is the saved Boolean | One named target; one arm of `Val.hasTy` |
| The action `getInterruptible` | The fiber action of row 239. It answers the entry flag at the type `Ty.maskRestore` | One constructor of `ActionTerm`, appended |
| The node `restore saved body` | `body` under `interruptible` when `saved` is true, and `body` as it is otherwise | One constructor of `Eff`, appended |

The mask is then a derived form, with no scoped constructor:

```
uninterruptibleMask body  :=  bind (withFiber getInterruptible) (uninterruptible body)
restore e                 :=  Eff.restore (var saved) e
```

**The action transcribes the pin's mask at a constant body.** It is
`uninterruptibleMask((restore) => succeed(restore))`: it masks the fiber, answers the entry
flag, and the restoring frame pops at the answer. So the action has a line of the pin to name,
and it keeps the frame's test for a pending cause. A bare read of the flag has no public
counterpart.

```
| WithFiberAction.getInterruptible =>
    answer the flag f.frame.interruptible, with the frame f.frame.uninterruptible
```

**The node compiles with no step of its own.** At its point it reads `saved` in the
environment, as `select` reads its scrutinee:

```
compileEff (restore saved body) p :=
  match evalTerm p.env saved with
  | true  => Prim.withFiber (EffThunk.act p)      -- the existing action setInterruptible body true
  | false => compileEff body (p.child 1)
  | _     => badShape
```

**The typing rules** are three lines of `check` and `checkAction`:

- `getInterruptible` answers `Ty.maskRestore`, with no error and no requirement;
- `restore saved body` requires `saved` at `Ty.maskRestore`, and it has the type of `body`;
- no other rule names the type.

**Its law keeps the ruled meaning.** `restore s e` behaves as `interruptible e` when the saved
bit is true and as `e` otherwise. That is row 239's selection without the suspension step.

### F4. The check at program admission is typing

Row 239's first two statements become one: the one whole-program checker types the program.
Checked module production and checked reading run that checker already (`ModuleEmission`,
`admitModule`).

- **A Boolean use is ill-typed.** A Boolean `select`, a `catchIf` test, an `iterate` test and
  an `ifElse` statement each require the type `bool` itself (`Decision.arms`, `check`). The
  saved value is at a handle type, and no subtyping relates the two.
- **A restore of another value is ill-typed.** `restore (lit true) e` is refused at its path.
- **No whole expansion is recognized, because each piece means something alone.** A getter
  outside a mask answers the caller's state. A restore outside its mask applies the saved
  choice to the fiber that runs it, as the pin's function does.
- **The target's type system says the same.** The getter's printed type is the type of the
  restore function. tsgo 7 refuses a Boolean use of it on both builds. That refusal is the one
  error of `mask-form-types.ts`, its red control.

Typing admits one thing that row 227 refuses. The saved value may be passed as data: returned,
stored in a cell, captured by a fork. The target allows the same, because `restore` is a value
there. The probe's S6 is one such run: a mask answers its restore, and a masked child applies it
after the mask ended. Both builds interrupt the child, and the printed form agrees.

The strict alternative keeps row 227's letter. It is a second fold over the program, with one
flag for each variable. It has three located refusals:

- a getter that no `bind` binds;
- a saved variable outside a restore node;
- a restore of an unsaved value.

Proposal 5 asks which one the owner wants.

### F5. The printed form, and the read and print equations

Two rows are added to the table, and both use formers that the template engine has already:

| Constructor | Skeleton | Printed |
| --- | --- | --- |
| `getInterruptible` | a call of `Effect.uninterruptibleMask` on a lambda that answers its own binder | `Effect.uninterruptibleMask((a0) => Effect.succeed(a0))` |
| `restore` | a method call named `pipe` on hole 1, with hole 0 as its argument | `E.pipe(a0)` |

A mask around one wait prints as:

```ts
Effect.flatMap(
  Effect.uninterruptibleMask((a0) => Effect.succeed(a0)),
  (a0) => Effect.uninterruptible(Deferred.await(d).pipe(a0))
)
```

- **Every name is public API.** `pipe` applies its argument, so `E.pipe(a0)` is `a0(E)`.
- **`read_print` and `read_exact` keep their statements.** Both are proved for the table through
  the engine lemmas of the formers. `binderRef`, `lambda` and `method` are formers with those
  lemmas, and the layer rows use `method` now. The slice adds two rows and two reserved heads.
- **Both skeletons are rigid, and their holes are distinct.** The reader commits to a row when
  its skeleton matches, so a hole in the head of a call would capture every call. The method
  skeleton matches only a call of `.pipe` with one argument. No program row has that shape
  today. The row table must refuse a method row spelled `pipe`.
- **`Readable` is unchanged in meaning.** A `restore` reads back for any term that reads back,
  typed or not. The equations are about program syntax, and typing is a separate judgment.
- **An annotated position prints too.** The type's target names one alias of the prelude for the
  restore function's type, as `Ty.scope`'s target names `Scope.Scope`.

**The native spelling is not printed.** `Effect.uninterruptibleMask((restore) => …)` with the
body inside would need a recognizer of three nodes, and it is not exact (F6). If it is ever
wanted, it is a named normaliser on the printed module with two equations of its own. The
ingest of foreign TypeScript stays parked (row 215).

### F6. The steps: nothing is erased

Loop iterations, read from the fiber's operation counter (`mask-form.ts`, S8). Each number is
the form's count less the count of a bare `succeed` in the same generator, which the generator
folds with no iteration. Both builds give the same numbers.

| Form | Iterations |
| --- | --- |
| The getter, under either caller | 2 |
| A restore site whose saved value is true | 1, and the body's |
| A restore site whose saved value is false | the body's |
| The native mask around `succeed` | 2 |
| The printed form around `succeed` | 5 |

- **The printed form runs what the program runs.** The five are the `flatMap`, the getter's
  two, the `uninterruptible` and the `succeed`. The machine's clauses of F3 are the same five
  steps. So row 239's two extra steps are steps of the printed form too.
- **No relation for erased steps is owed** for this printed form. What is owed is ordinary: the
  typed-state and agreement clauses of one action and one node, and a run that compares the
  counts.
- **The native spelling is three iterations short.** So it differs from the machine in where
  the budget's yield lands. That is the second reason not to print it.
- **The form has one window.** Between the getter's answer and the body's mask the fiber is
  interruptible when its caller was. It holds nothing there, so an interrupt at that point
  equals one before the form.

### F7. The behaviour, by scenario

`mask-form.ts` runs each scenario with the native mask and with the printed form. Each pair of
logs is equal, on rc.112 and on 4.0.1.

| Scenario | What both forms do |
| --- | --- |
| S1. What the getter answers | the public `interruptible` under an interruptible caller; a function that answers its argument under a masked caller |
| S2. An interruptible caller is interrupted during a wait at a restore site | the fiber exits interrupted, and the body does not continue |
| S3. A masked caller is interrupted during the same wait | the wait continues; the value arrives; the fiber is interrupted when the outer mask ends |
| S4. An interruptible caller is interrupted with no restore site | the body runs to its end, and the fiber is then interrupted |
| S5. Nested masks: a wait under the inner restore, and one under the outer restore | the inner one is not interruptible; the outer one is |
| S6. A restore that leaves its mask and runs in a masked child | the child's wait is interruptible |
| S7. The caller's flag after a success, a failure and a defect, under both callers | it is what it was |

These seven are the acceptance traces of `saved-mask-restoration`. Its statements, over runs of
the machine:

1. outside a restore site the body's steps run with the flag false;
2. inside a restore site the flag is the saved bit, or true when an enclosing region made it so;
3. at every exit of the form the flag is the entry flag;
4. a cause that is pending when the flag returns to true fails the fiber there.

### F8. Nested masks, escapes and the dual

- **Nested masks need no rule.** Each mask binds its own variable, and a restore names one by
  its binder. An outer restore inside an inner mask is S5's second run.
- **An escape needs no rule either.** The saved value is in the environment that a fork copies,
  so the child reads the parent's entry flag. This is the meaning that row 227's amendment
  describes. S6 is its run.
- **The dual needs its own three pieces.** `interruptibleMask` hands `identity` or
  `uninterruptible`, which are other functions. One Boolean cannot print as both families. No
  consumer needs the dual yet, and its pieces are appended when one does.

### F9. What the slice touches

| Area | Change |
| --- | --- |
| `src/Effect4/Program/Eff.lean`, the binder table | two constructors, appended; neither binds |
| The generated folds, the wire form, the TypeScript and OCaml images | regenerated |
| `src/Effect4/Program/Ty.lean`, `Typed.lean`, `Checker.lean` | the named type, one arm of `Val.hasTy`, three typing clauses, one refusal reason |
| `src/Effect4/Machine/Fibers.lean` | one action and its clause; one value of the interpreter for a flag |
| `src/Effect4/Program/Compile.lean` | three clauses: the node, its action, the getter's action |
| `src/Effect4/Codegen/Templates.lean`, `PrintLeaf.lean` | two rows, two heads |
| The prelude | one type alias |
| The form table and the authoring surface | the derived form and its builder |
| The laws | the typed-state rows of one action and one node; the form's law; the table's side conditions for two rows |
| The runtime census | one row for `uninterruptibleMask`; the frames have theirs (`op.SetInterruptible`, `checkpoint.set-fiber-interruptible`) |
| The truth lane | S2 to S7 as programs, and the count of S8 |

The slice regenerates the groups that seat T3b regenerates. It starts after T3b's merge, and it
lands before the Queue's first path, which uses it.

### F10. The obligations, placed

| Obligation | Concept and requirement | Reach | Not established |
| --- | --- | --- | --- |
| `saved-mask-restoration` | scope-lifetime-finalization, R11 | A typed program; the four statements of F7; every exit | No progress, and nothing about the Queue |
| `scoped-body-substitution-boundary` | residual-program-typing, R4 | The checker's three clauses; a saved variable keeps its type under every binder | No behaviour |
| The read and print claims of the two rows | R8 | Syntax only: `read_print` and `read_exact` at the extended table | No typing, and no behaviour of the target |
| The form's agreement with its expansion | R10 | The derived form's law of row 214 | No agreement with the native spelling |

Each is an open part of its requirement row now. The slice states each as a planned goal over
its definitions before it proves one.

## Proposals (not rulings)

1. **The saved state has its own opaque type** (amends row 239). The value stays a Boolean.
   Typing is the check at program admission, and no expansion is recognized.
2. **A restore site is one node** (amends row 239, which rejected a `restore` constructor for
   now). Its law is the ruled selection without the suspension step. The mask stays a derived
   form over `bind`, and no scoped constructor is added.
3. **The getter transcribes the pin's mask at a constant body.** It masks, answers and pops.
4. **The printed form is two rows of public API.** The native callback spelling is not printed.
5. **The saved value may be passed as data,** because typing admits it and the target does.
   This goes one step past row 227's amendment. The strict alternative is the second fold of F4.
6. **The mask slice follows seat T3b's merge and precedes the Queue's first path.** Its
   acceptance is the eight scenarios and the type check, on the pin and on the release.

## What this does not establish

- Every behaviour here is a finite run on one schedule with bun 1.4.2, or a reading.
- The count of S8 is of the target. The machine's clauses are a sketch, and their counts were
  not run.
- The memo difference of F2 is a reading of two definitions. No program shows it.
- No run places an interrupt in the window of F6, or a pending cause at the getter's pop.
- The laws of the two rows are argued from the formers. No Lean was written.
- tsgo 7 checked four programs and one red control. It did not check a printed module.
- The two builds' mask combinators are equal as text. Their behaviour was compared only on
  the eight scenarios.
- The dual mask is not designed.
