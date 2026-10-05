# 2026-10-05 the mask's second note: its check, its printed TypeScript form and its steps

Status: research note (history, not authority). Base: `0002ca73` (`refactor/phase1-phase3`).
A design for the owner's sign-off. No file of the tree changed.

**Ruled 2026-10-05.** The owner ratified the three directions in session ("yes to all three"),
after Codex's review. They are decisions rows 244 to 246: proposals 1, then 2 to 4, then 5.
Proposal 6 is the coordinator's order under row 237.

**Corrected 2026-10-05, after Codex's review** of this note at its first commit
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/mask-second-review/recommendations.md`).
The review recommends the three directions and finds six faults in the statements. Each was
checked against the tree or run again, and all are repaired here:

- the restore node's body is child 0, and the sketch addressed child 1;
- the new type's name was not reserved, so an external handle could take it;
- a row printed as a method call has no reserved head, so the table's separation proof does
  not cover it;
- two of the four behaviour laws were false for a body that holds a region of its own;
- the count of F6 is of the operation counter, which is not the loop's iterations on 4.0.1;
- the layer argument of F2 was stated as a fact, and it is a reading with a condition.

**The one thing to know first.** Decisions row 239 asks for five statements before a seat
builds the mask. This note gives them. It also proposes two changes to row 239, because they
make all five simple:

1. the saved state has its own opaque type, so ordinary typing is the whole check;
2. a restore site is one node, and not a selection that holds the body twice.

With these the mask prints row by row in the public API. `read_print` and `read_exact` keep
their statements and gain two rows. The printed form is the program's own expansion, so it
erases no step. Nine behaviours of the printed form equal the native mask's on rc.112 and on
4.0.1, and tsgo 7 types it on both. The printed form is not the native mask at two checkpoints
of its entry (F6).

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
| `compileEff`, `actionAt`, `suspendBodyAt` in `src/Effect4/Program/Compile.lean`; the child convention in `src/Effect4/Program/Node.lean` | read |
| `check`, `checkAction` in `src/Effect4/Program/Checker.lean`; `Decision.arms` in `src/Effect4/Program/Decision.lean` | read |
| `Val.hasTy`, `internalHandleTargets`, `externalHandleTarget` in `src/Effect4/Program/Typed.lean`; `findInternalHandle` in `src/Effect4/Program/Columns.lean`; `flatCarrierAlg` in `src/Effect4/Program/SigApp.lean`; `Fits` in `src/Effect4/Laws/Program/Typed/Membership.lean` | read |
| The row table and the printer's fold, `src/Effect4/Codegen/Templates.lean`; the template formers and `Tpl.head?`, `src/Effect4/Codegen/Template.lean`; `readRow` and `readArg`, `src/Effect4/Codegen/Read.lean` | read |
| `read_print`, `rowsApart`, `table_apart`, `table_shape` in `src/Effect4/Laws/Codegen/ReadPrint.lean`; `readRow_exact` in `src/Effect4/Laws/Codegen/Read.lean` | read: the statements only |
| `LayerTerm.ref` and its docstring in `src/Effect4/Program/Eff.lean` | read |
| `docs/research/2026-10-05-claude-lead/mask-probes/mask-form.ts` on rc.112 and 4.0.1, with bun 1.4.2; each output sits beside it | tested: ten scenarios on each build |
| `docs/research/2026-10-05-claude-lead/mask-probes/mask-form-types.ts`, by tsgo 7.0.0-dev.20260629.1 against each build | tested: six programs; one error on each build, the red control |
| Codex's two reviews: `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/w-design-review/mask-review.md`, and the folder `mask-second-review/` beside it, with 24 runtime controls on each build | read; its controls were not rerun here, and five of its flag readings were (S9) |
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

- **A selection is a suspension, and the call is not.** `compileEff` gives `select` one
  `Prim.suspend` step, as its printed `Effect.suspend(() => …)` runs one. The call `restore(e)`
  runs none. The selection spends one loop checkpoint more at every site.
- **A row cannot print it as the call.** The site is recognized by a relation between two
  children: the first arm is `interruptible` of the second. A row's classifier reads leaves
  only (`ArgPat`), and the printer is a fold over printed children (`tableLayer`). The form
  needs a new kind of classifier, or a recognizer outside the fold.
- **A saved value typed `bool` can be used as a Boolean** (Codex's first review). The target
  has no spelling for that use. So the selection also needs a checker of its own.

One more point is a reading with a condition, and it is not a reason by itself. The selection
writes the body twice, so the body has two program sites, and a layer's identity is its path
(`LayerTerm`'s docstring). A printer that collapses the two arms into one call `restore(e)`
would owe a statement. The two sites must share every identity that the one printed site has.
Two copies can share a layer through `LayerTerm.ref`. No program was built that fixes the
allocation sites and the memo map's lifetime, so no divergence is shown. The one node avoids
the question, because it writes the body once.

### F3. The proposal: a type, an action and a node

| Piece | What it is | Its cost |
| --- | --- | --- |
| The type `Ty.maskRestore` | An opaque host type, written `.handle` with its own target, as `Ty.scope` and `Ty.context` are. Its members are the two images of the saved bit, and nothing else | One named target, reserved; one arm of `Val.hasTy`, of `Fits` and of `FlatFits`; the refusals below |
| The action `getInterruptible` | The fiber action of row 239. It answers the entry flag at the type `Ty.maskRestore` | One constructor of `ActionTerm`, appended |
| The node `restore saved body` | `body` under `interruptible` when `saved` is true, and `body` as it is otherwise | One constructor of `Eff`, appended |

The mask is then a derived form, with no scoped constructor:

```
uninterruptibleMask body  :=  bind (withFiber getInterruptible) (uninterruptible body)
restore e                 :=  Eff.restore (var saved) e
```

**The type's name is reserved.** `externalHandleTarget` admits an external handle at every
target that `internalHandleTargets` does not list. So the new target joins that list. Three
refusals follow from the one list, or are added beside it:

- an external allocation may not take the target;
- a host answer column may not introduce it (`findInternalHandle`);
- a service may not carry it in the first profile. `flatCarrierAlg` admits every handle target
  but the context's today, so this refusal is one clause. Lifting it needs the membership of a
  context's services at the type.

**The saved bit has an image of its own.** A raw Boolean value would also fit `bool`, and it
would stay a Boolean after widening to `unknown`. The image is one frame that holds the bit
and that no other type's membership reads. Its exact encoding is the slice's first decision,
before any proof. Membership at the type means exactly the two canonical images. A Boolean
literal still has the type `bool`, so no literal forges the type (Codex's reading of `litArgTy`).

**The action transcribes the pin's mask at a constant body.** It is
`uninterruptibleMask((restore) => succeed(restore))`: it masks the fiber, answers the entry
flag, and the restoring frame pops at the answer. So the action has a line of the pin to name,
and it keeps the frame's test for a pending cause. A bare read of the flag has no public
counterpart.

```
| WithFiberAction.getInterruptible =>
    answer the image of f.frame.interruptible, with the frame f.frame.uninterruptible
```

**The node compiles with no step of its own.** Its body is child 0: a node's children are its
node arguments, and the saved term is not one (`Node`). At its point it reads `saved` in the
environment, as `select` reads its scrutinee:

```
compileEff (restore saved body) p :=
  match evalTerm p.env saved with
  | the image of true  => Prim.withFiber (EffThunk.act p)   -- actionAt: setInterruptible (resolve (p.child 0)) true
  | the image of false => compileEff body (p.child 0)
  | _                  => badShape
```

A body that only succeeds hides a wrong address. The slice's control is each saved choice
around a `bind` that reads an outer variable and then performs an operation. A second control
has a fork and a layer reference in the body, because both resolve program paths.

**The typing rules** are three lines of `check` and `checkAction`:

- `getInterruptible` answers `Ty.maskRestore`, with no error and no requirement;
- `restore saved body` requires `saved` at `Ty.maskRestore`, and it has the type of `body`;
- no other rule names the type.

**Its law keeps the ruled meaning.** `restore s e` behaves as `interruptible e` when the saved
bit is true and as `e` otherwise. That is row 239's selection without the suspension step. A
false bit is the identity on the fiber that runs the node. It does not mask that fiber.

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
there. Two runs show it. In S6 a mask answers its restore, and a masked child applies it after
the mask ended; the child's wait is interruptible. In S10 a saved value of a masked caller is
applied under an interruptible caller, and the fiber stays interruptible.

A value that is passed keeps its meaning through the existing connectors. A cell, a promise,
a tuple and a captured environment each hold it at its type. It holds no activation of its
mask and no cleanup of its parent.

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
| `restore` | a call of the root export `pipe`, with hole 1 and then hole 0 | `pipe(E, a0)` |

A mask around one wait prints as:

```ts
Effect.flatMap(
  Effect.uninterruptibleMask((a0) => Effect.succeed(a0)),
  (a0) => Effect.uninterruptible(pipe(Deferred.await(d), a0))
)
```

- **Every name is public API.** `pipe` applies its second argument to its first, so
  `pipe(E, a0)` is `a0(E)`.
- **Both rows have a reserved head.** The table's separation proof reads a skeleton's head
  (`Tpl.head?`, `rowsApart`), and a row before the row call needs a reserved one. `pipe` and
  `Effect.uninterruptibleMask` join the reserved heads, so no row of a signature takes either
  spelling.
- **The method spelling `E.pipe(a0)` is the alternative, and it costs a proof rule.** A method
  skeleton has no head, so `rowsApart` does not cover it before the row call. It would need a
  rule for method skeletons and its matching lemma. tsgo 7 types both spellings.
- **`read_print` and `read_exact` keep their statements.** Their premises about the table are
  decided again for the extended table (`table_apart`, `table_shape`). The formers' own lemmas
  are not the whole result.
- **`Readable` is unchanged in meaning.** A `restore` reads back for any term that reads back,
  typed or not. The equations are about program syntax, and typing is a separate judgment.
- **An annotated position prints, and it is not read.** The type's target names one alias of
  the prelude for the restore function's type. The reader refuses a local annotation today
  (`readArg`), and `Readable` excludes it. The slice keeps both limits.

**The native spelling is not printed.** `Effect.uninterruptibleMask((restore) => …)` with the
body inside would need a recognizer of three nodes, and it is not the program's expansion (F6).
If it is ever wanted, it is a named normaliser on the printed module with two equations of its
own. The ingest of foreign TypeScript stays parked (row 215).

### F6. The steps, and the two checkpoints of the entry

The fiber's operation counter, read before and after each form (`mask-form.ts`, S8). Each
number is the form's count less the count of a bare `succeed` in the same generator.

| Form | Count on both builds |
| --- | --- |
| The getter, under either caller | 2 |
| A restore site whose saved value is true | 1, and the body's |
| A restore site whose saved value is false | the body's |
| The native mask around `succeed` | 2 |
| The printed form around `succeed` | 5 |

- **The counter is the loop's checkpoints on the pin only.** On 4.0.1 it also counts a value
  that a continuation passes on outside the loop (the audit's F4). For these plain forms both
  measures give 2 and 5 on both builds. For a mapped body Codex's controls differ by build.
  The release has 3 and 6 checkpoints, with counters 4 and 7. The pin has 4 and 7 of both.
- **The printed form is three checkpoints longer than the native mask** in every one of those
  measurements. They are the `flatMap` and the getter's two.
- **The printed form erases nothing of the program.** It is the expansion, node for node. Its
  agreement with the compiled program is still owed, like every row's: for a named release, a
  named body and a named observation. No sketch of this note settles it.

The entry of the printed form has two checkpoints that the native mask does not have:

1. **Inside the getter the fiber is masked for one checkpoint.** An interrupt that is requested
   there stays pending. The getter's restoring frame then fails the fiber, before the body
   starts. The native mask at its matching point runs its whole body first.
2. **Between the getter and the body's mask the fiber is interruptible** when its caller was.
   An interrupt there ends the form before the body starts.

Codex's controls cut a run at each checkpoint with a dispatcher of their own, on both builds.
Both cuts end the printed form before its body, a masked caller still enters the body, and
every control with no interrupt enters it. These are other checkpoints than the native
mask's, so the runs are no test of equality with it.

So the form's contract has one premise for its clients: **nothing is acquired or registered
before the body begins.** The waiting wrapper meets it, because its first step is inside the
body. Under that premise an interrupt at either checkpoint equals an interrupt before the form.

### F7. The behaviour, by scenario

`mask-form.ts` runs each scenario with the native mask and with the printed form. Each pair of
answers is equal, on rc.112 and on 4.0.1.

| Scenario | What both forms do |
| --- | --- |
| S1. What the getter answers | the public `interruptible` under an interruptible caller; a function that answers its argument under a masked caller |
| S2. An interruptible caller is interrupted during a wait at a restore site | the fiber exits interrupted, and the body does not continue |
| S3. A masked caller is interrupted during the same wait | the wait continues; the value arrives; the fiber is interrupted when the outer mask ends |
| S4. An interruptible caller is interrupted with no restore site | the body runs to its end, and the fiber is then interrupted |
| S5. Nested masks: a wait under the inner restore, and one under the outer restore | the inner one is not interruptible; the outer one is |
| S6. A restore that leaves its mask and runs in a masked child | the child's wait is interruptible |
| S7. The caller's flag after a success, a failure and a defect, under both callers | it is what it was |
| S9. The flag at five places of a body | false in the body; true in an `interruptible` region of the body; true in a restore site; false in an `uninterruptible` region inside that site; false in a restore site under a masked caller |
| S10. A saved value applied after its mask | a false choice leaves an interruptible fiber interruptible, and a masked fiber masked; a true choice makes a masked fiber's region interruptible |

These are the acceptance traces of `saved-mask-restoration`. Its statements are at the
boundaries of regions, over runs of the machine. No statement says that every step of the body
has one flag, because a body may hold regions of its own (S9).

1. **At the body's entry** the flag is false.
2. **At a restore site's entry** a true bit makes the flag true. A false bit leaves the flag as
   it is.
3. **A region inside the body follows its own rule,** in a restore site and outside one.
4. **At each completed exit of a region** the flag is what it was at that region's entry. So at
   every exit of the form it is the entry flag.
5. **When an exit leaves the fiber interruptible with a pending cause,** the fiber fails there
   with that cause.

### F8. Nested masks, escapes and the dual

- **Nested masks need no rule.** Each mask binds its own variable, and a restore names one by
  its binder. An outer restore inside an inner mask is S5's second run.
- **An escape needs no rule either.** The saved value is in the environment that a fork copies,
  so the child reads the parent's entry flag. This is the meaning that row 227's amendment
  describes. S6 and S10 are its runs.
- **The dual needs its own three pieces.** `interruptibleMask` hands `identity` or
  `uninterruptible`, which are other functions. One bit cannot print as both families. No
  consumer needs the dual yet, and its pieces are appended when one does.

### F9. What the slice touches

| Area | Change |
| --- | --- |
| `src/Effect4/Program/Eff.lean`, the binder table | two constructors, appended; neither binds |
| The generated folds, the wire form, the TypeScript and OCaml images | regenerated |
| `src/Effect4/Program/Ty.lean`, `Typed.lean`, `Checker.lean` | the named type and its reserved target, the image's arm of `Val.hasTy`, three typing clauses, one refusal reason |
| `src/Effect4/Program/Columns.lean`, `SigApp.lean` | the target refused in a host answer column and as a service carrier |
| `src/Effect4/Machine/Fibers.lean` | one action and its clause; one value of the interpreter for a flag |
| `src/Effect4/Program/Compile.lean` | three clauses: the node, its action, the getter's action |
| `src/Effect4/Codegen/Templates.lean`, `PrintLeaf.lean` | two rows, two reserved heads |
| The prelude | one type alias |
| The form table and the authoring surface | the derived form and its builder |
| The membership laws, `src/Effect4/Laws/Program/Typed/Membership.lean` | the image's arm of `Fits` and of `FlatFits`, with their order and extension lemmas |
| The typed-state laws | `FiberOp` (`Laws/Program/Sched.lean`), `denoteFiberAction` (`Laws/Program/DenoteR.lean`), `FiberCert` with `fiberPre` and `fiberPost` (`Laws/Program/Typed/Residual.lean`), and the getter's answer clause beside `clause_getContext` |
| The table laws, `src/Effect4/Laws/Codegen/ReadPrint.lean` | `table_apart` and `table_shape` for the extended table |
| The runtime census | one row for `uninterruptibleMask`; the frames have theirs (`op.SetInterruptible`, `checkpoint.set-fiber-interruptible`) |
| The truth lane | S2 to S10 as programs, and the two cuts of F6 |

The slice regenerates the groups that seat T3b regenerates. It starts after T3b's merge, and it
lands before the Queue's first path, which uses it.

### F10. The obligations, placed

Codex's review places the same five, with their consumers on the M5 and M6 path.

| Obligation | Concept and requirement | Reach | Not established |
| --- | --- | --- | --- |
| The saved value's membership | store-typing, R4 | The reserved target, the two canonical images, typed stores and environments, a later world | No reply admission |
| The node's path and binders, in `scoped-body-substitution-boundary` | residual-program-typing, R4 | A checked body at child 0, a typed stack and captures, no lookup that fails | No agreement with a target |
| `saved-mask-restoration` | scope-lifetime-finalization, R11 | The five statements of F7: both bits, nested regions, each completed exit, pending causes | No progress, and nothing about the Queue |
| The read and print claims of the two rows | R8 | Program syntax only: `read_print` and `read_exact` at the extended table | No typing, and no behaviour of the target |
| The printed form's behaviour | R10 and R11 | A named release, compatible decisions, the two checkpoints of F6, compiled programs | No equality with the native spelling |

**The semantics registry does not hold all five yet** (Codex's proof scouting of 2026-10-05,
`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/proof-scouting/mask-tooling.md`).
An earlier version of this section said that it did.

- Two parts are there in older words. `saved-mask-restoration` (R11) names a saved state and
  row 227 only. `scoped-body-substitution-boundary` (R4) names a first scoped constructor, and
  the restore node binds nothing.
- Three parts are absent: the saved image's membership (R4), the extended table's premises
  (R8), and the printed form's profile with its entry checkpoints (R10).

The coordinator reconciles the semantics registry with rows 244 to 246 at seat T3b's merge, because that
seat edits the same file now. Every unrelated open part stays. No goal is stated before that.

The order of the proofs, with what each reuses (the same scouting; each name was found in the
tree):

1. **The saved image and its membership,** before anything else: `Fits`, `FlatFits`,
   `fits_hasTy`, `fits_live`, `fits_mono`. An image with no handle reuses
   `live_of_handles_nil`.
2. **The getter's answer and the body at child 0,** on the source-point induction that M5 uses:
   `interruptible_arm`, `uninterruptible_arm`, `pointTyped_child`, `childDenotes_upto`
   (`src/Effect4/Laws/Program/Typed/Denotation.lean`). Both saved choices resolve one checked
   body in one environment.
3. **The five statements of F7,** with one clause each for a success, a failure, a pending
   interrupt and a nested region. `maskFrame` and `clause_mask`
   (`src/Effect4/Laws/Program/Typed/Commands/Evaluate.lean`) prove that the typed state is kept.
   They do not prove the form's behaviour.

A placement in the semantics registry says what a goal is for. It does not show that M5 or M6 uses the
declaration: the receipt checks both, with `#plan_status` on the goal and on its consumer.

## Proposals, and what the owner ruled

1. **The saved state has its own opaque type** (amends row 239). Its name is reserved, and its
   value is the saved bit in an image of its own. Typing is the check at program admission, and
   no expansion is recognized.
2. **A restore site is one node** (amends row 239, which rejected a `restore` constructor for
   now). Its body is child 0. Its law is the ruled selection without the suspension step. The
   mask stays a derived form over `bind`, and no scoped constructor is added.
3. **The getter transcribes the pin's mask at a constant body.** It masks, answers and pops.
4. **The printed form is two rows of public API:** the getter, and `pipe(E, saved)` for a
   restore site. The native callback spelling is not printed.
5. **The saved value may be passed as data,** because typing admits it and the target does.
   This goes one step past row 227's amendment. A service does not carry it in the first
   profile. The strict alternative is the second fold of F4.
6. **The mask slice follows seat T3b's merge and precedes the Queue's first path.** Its
   acceptance has four parts:
   - the ten scenarios, and the two cuts of F6;
   - the control of F3 for the body's address;
   - the type check of one emitted module;
   - two refusals: a Boolean use, and a host answer at the reserved target.

## What this does not establish

- Every behaviour here is a finite run on one schedule with bun 1.4.2, or a reading.
- The count of S8 is of the target. The machine's clauses are a sketch, and no compiled program
  was run.
- The two cuts of F6 are Codex's runs with its own dispatcher. They were read here, not rerun.
- The layer question of F2 is a reading with a condition. No program shows a divergence.
- The laws of the two rows are argued from the formers and the reserved heads. No Lean was
  written, and `table_apart` was not decided for the extended table.
- tsgo 7 checked six hand-written programs and one red control. It did not check an emitted
  module.
- The two builds' mask combinators are equal as text. Their behaviour was compared only on
  the scenarios.
- The image of the saved bit is not chosen.
- The dual mask is not designed.
