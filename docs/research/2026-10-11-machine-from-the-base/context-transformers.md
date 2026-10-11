# Dynamic context and context transformers

Research note, 2026-10-11, base `734368d17` (branch `refactor/phase1-phase3`). It follows point 2
of the [topology note](../2026-10-11-topology-graphs/README.md): the frame stack is a path in the
program tree. Here the subject is what the stack carries besides control: the fiber's dynamic
context. The companion [README](README.md) describes the machine from its base and plans the
proofs. Literature names below are from memory and carry no locator.

## 1. The one thing to know first

**The checker admits a program whose requirement row is closed, and the program dies with
`missingService`.** The object language's `setContext` action writes the fiber's context raw. A
region that provides a service can reset the context to one captured outside it, and then read the
service:

```text
bind (withFiber getContext)                -- capture the root's context, with no services
  (provideService key 1                    -- the checker counts key as provided below
    (bind (withFiber (setContext (var 0))) -- the context is now the root's again
      (service key)))                      -- the lookup fails
```

The probe (`probes/CtxProbe.lean`, output `probes/ctxprobe.out`) checks it, admits it and runs it
at budget 400 on the frame machine. The checker's type has an empty requirement row, program
admission accepts it, and the run's exit is `die missingService`. A definition whose request is a
context does the same inside its body (`resetInBody`).

rc.112 has no such program. Its context reader is typed by its row
(`context: <R>() => Effect<Context<R>, never, R>`, `vendor/effect-4.0.0-rc.112/src/Effect.ts`), and
even its internal `setContext` is a region over a body whose requirement the context must cover
(`setContext`, `provideContext`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`). The object
language transcribes the fiber's method `fiber.setContext`, not the combinator. The printer already
refuses the action (`Codegen/Templates.lean`: no public rc.112 export of that shape), so no emitted
module shows the defect. The checker and the machine do.

Consequences:

- Decisions row 117's part two (no `missingService` at a closed row, R9) is false on the current
  language. It is false for a reason other than the saved-frame transport of `E4-TYPED-CE-008`.
- The proposed counterexample is `E4-CTX-CE-001`. The recommended repair (§4) replaces the two raw
  actions with rc.112's pair: a typed context reader and a providing region.

**The design result.** A passed program runs in the body's context at its site, as rc.112 runs it
(probe `dyn`). So a definition's interface needs, for each parameter, the action of the body's
regions on the context at each site. That action is a fold along the body's path to the site. It
closes HO3-REQ-01, and it prints as Effect's own `Exclude<R, K>` (§6, §7).

## 2. Where the dynamic context lives

A fiber has two parts. The frame part is the five-field `FrameFiber`
(`src/Effect4/Machine/Frames.lean`). The run part is `RunFiber` (`src/Effect4/Machine/Fibers.lean`),
whose field `context : χ` is `Machine.Ctx` at the native instance: the service map and two
budget caches (`src/Effect4/Machine/Stores.lean`).

| Dimension | Where it is | Entry | Restore | At a fork | Law today |
| --- | --- | --- | --- | --- | --- |
| mask | `FrameFiber.interruptible` | `uninterruptible` pushes `setInterruptible saved` | the frame's pass hook (`Prim.ensure`) | `maskMode` | `MaskChain`, `MaskRuns.flag_eq`, `saved_mask_region_bracket` |
| services | `RunFiber.context` | `updateContextAt`: read, then `setCtx next` | an `onExit` frame named `restoreCtx prev`; its finalizer program writes `prev` | `spawn` copies the parent's context | none |
| scope | a service binding (`scopeKey`) and the global `ScopeStore` | `enterScoped` | `exitScoped` writes the previous context | copied with the context | `exitScoped_restores` |
| memo map | a service binding (`currentMemoMapKey`) | a `provideService` region | as services | as services | none |
| call string, parameter display | `Point.call`, `Point.params`, inside names | `invoke`, `perform (.call k)` | carried by the names | the child keeps them | lexical, by construction |
| a release's context | `Capture.ctx` | captured at acquire | `releaseUnder` sets it, `restoreCtx` restores | — | none |

Two kinds stand out:

- **Dynamic dimensions** are fiber fields that a region writes on entry and a frame restores on
  exit: the mask, the services, the scope and the memo map.
- **Lexical dimensions** travel inside names: the environment, the call string, the parameter
  display, a release's captured context.

The compile matches rc.112's `updateContext` line for line. rc.112 reads the previous context,
sets the next, and runs the body under `onExitPrimitive` with a callback that sets the previous
context back (`updateContext`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`). The compile's
chain is `updateContextAt`, `updateThenK`, then `onExit body (restoreCtx prev) false`, with
`finalizerProgram (restoreCtx prev) = withFiber (setCtx prev)` (`src/Effect4/Program/Compile.lean`).

## 3. Dynamic context is a fold of the stack

### 3.1 The mask, proved

`MaskChain` (`src/Effect4/Laws/Machine/MaskDiscipline.lean`) reads the stack top first:

```lean
def MaskChain (base : Bool) : Bool → List (Prim ν σ β ε δ ι α) → Prop
  | flag, [] => flag = base
  | flag, Prim.setInterruptible saved :: rest => flag = !saved ∧ MaskChain base saved rest
  | flag, _ :: rest => MaskChain base flag rest
```

A restoring frame stores the value in force below it. The current value is not on the stack. It
is determined by the top restoring frame, or by the base when there is none
(`MaskChain.flag_eq`). Along a run, every live fiber holds the chain at its start flag
(`saved_mask_chain_runs`, `src/Effect4/Laws/Machine/MaskRuns.lean`).

### 3.2 The services, the same shape

A `restoreCtx prev` frame stores the context in force below the region. So the services have the
same chain, with one change: the current value is related to the top saved value by the region's
update, not by negation.

```text
CtxChain base ctx []                                  := ctx = base
CtxChain base ctx (onExit _ (restoreCtx prev) _ :: s) := Updated prev ctx ∧ CtxChain base prev s
CtxChain base ctx (onExit _ (scopedExit prev _) _ :: s) := Updated prev ctx ∧ CtxChain base prev s
CtxChain base ctx (_ :: s)                            := CtxChain base ctx s
```

`Updated prev ctx` says that `ctx` arises from `prev` by the provisions of the current region
(`ContextUpdate.apply`). Three facts differ from the mask:

1. The restore is a finalizer program, not a pass hook. The region ends after the finalizer's
   `setCtx prev` runs, a few steps after the pop.
2. A fork copies the context but none of the frames. So a child's base is its parent's context at
   the fork (probe `forked`: a child forked inside a region reads the region's value after the
   region has ended).
3. **The object language can write the context raw** (`setContext`). Then `Updated prev ctx` fails
   for any update. This is the finding of §1.

### 3.3 One law for every restoring dimension

Both chains are instances of one relation, over a recognizer of restoring frames
`saved : Prim → Option C` and a relation `R : C → C → Prop` between a saved value and the value in
force above it. The mask takes `R saved flag := flag = !saved`. The services take `Updated`.

Read as algebra, each region is an action on the dimension's values. The value at any point is the
composite of the actions on the path from the fiber's start to that point, applied to the base. That
is a monoid homomorphism from the path to the endomorphisms of the values: a fold. The stack holds
exactly the path's open regions, so the fold of the stack is the dynamic context.

This view gives three things:

- **The region bracket for every dimension from one law.** A region ends at its entry's value,
  whatever its body did, because the restoring frame holds that value.
  `saved_mask_region_bracket` is the mask's instance. The services' instance is open.
- **Decisions row 117's per-position clause.** Presence at a position says that the context's keys
  cover the position's requirement row. With the chain, the context at a frame's continuation is
  the chain's value at that frame. So presence follows from the chain and from each frame's
  continuation requirement. Row 117 records the clause as not preserved by the walk; the chain is
  the invariant the walk preserves.
- **A static reading.** Along one body the actions are known from the tree, so the context at an
  address is a path fold, a second column of the address table beside the environment
  (`Program/PathFold`, `address-composes`).

## 4. The finding, and its repair

| Program | Checker's row | Admitted | Exit (budget 400) |
| --- | --- | --- | --- |
| `reset`: a region provides 1, resets to the outer context, reads | closed | yes | `die missingService` |
| `resetInBody`: a definition sets its request as the context, then runs its parameter | closed | yes | `die missingService` |

The checker types `setContext c` by `Ty.sub c Ty.context` alone (`Checker.checkAction`,
`src/Effect4/Program/Checker.lean`). `Ty.context` carries no row, so no rule relates the written
context to the requirement of the code after it.

Repairs, for the owner:

| Option | What changes | Cost | What it keeps |
| --- | --- | --- | --- |
| **A** (recommended) | Replace `setContext` and `getContext` with rc.112's public pair. `context` reads a context typed by its row (`Ty.context` gains a row). `provideContext c body` merges `c` into the context for `body`, whose row loses `c`'s keys. | one action pair, its checker rules, the generated views, one corpus row, the compile through `updateContextAt` | rc.112's surface; the chain of §3.2; the region discipline |
| B | Keep the raw actions; give `Ty.context` a row; refuse `setContext` where the row misses the continuation's requirement | the continuation's requirement at a non-region write, which the compositional checker does not have | the raw surface, at a design cost |
| C (stopgap) | Refuse `setContext` at program admission | one admission clause | nothing: the language loses the action |

Option A also gives rc.112's internal `setContext` region as the replace action of §6.1. Nothing
under `src/Effect4/Library` uses the raw actions. The printer refuses `setContext` already.

## 5. A passed program runs in the body's context

| Program | Checker's row | Exit |
| --- | --- | --- |
| `dyn`: the body provides 1 around its parameter site; the caller provides 2 | closed | 1 |
| `lexical`: the body provides nothing; the caller provides 2 | closed | 2 |
| `bodyOnly`: the body provides 1; the caller provides nothing | requires the key | 1 |
| `twice`: the parameter runs inside the body's region, then after it | closed | (1, 2) |

A parameter's run moves the point to the call site: path, environment, parameter stack and call
string (`suspendBodyAt`, `src/Effect4/Program/Compile.lean`). It leaves the fiber's context alone.
So the passed program reads the body's services at its site. rc.112 behaves the same way by
construction: `provideService` is an `updateContext` region around whatever runs inside it.

The checker charges a passed program's requirement to the call (`ParamDecl.row`'s docstring,
`src/Effect4/Program/Eff.lean`). That is a lexical reading. It over-approximates (`bodyOnly` runs
but its root row is open, so the closed-row premise of row 117 refuses it). It is unsound wherever
the body can remove a service around a site, which only the raw `setContext` of §4 can do today.
HO3-REQ-01 (`Codegen/CallbackRequirements.lean`) is the printed face of the same gap: tsgo refuses
a call whose callback needs a service against a header that closes the row.

This is what the effects literature calls accidental handling (Zhang and Myers, 2019): a body's
provision silently satisfies a requirement the caller meant to meet. Effect has it by design. The
remedy that keeps Effect's semantics is to make the provision visible in the definition's
interface.

## 6. The design: a context transformer per parameter

### 6.1 The actions

Let `K` be the finite set of service keys of the program. A context action is a pair:

- `(inherit, P)`: the keys become `k ∪ P`;
- `(replace X, P)`: the keys become `X ∪ P`.

Each region is one action:

| Region | Action |
| --- | --- |
| `provideService key v body` | `(inherit, {key})` |
| `provideLayer layer body` | `(inherit, out(layer))` |
| `provideContext (c : Context<X>) body` (option A) | `(inherit, X)` |
| rc.112's internal `setContext (c : Context<X>) body` | `(replace X, ∅)` |
| `scoped body` | `(inherit, {Scope})` |
| any other node | `(inherit, ∅)`, the identity |

Composition, first `a` then `b` inside it:

- `(inherit, P) ; (inherit, Q) = (inherit, P ∪ Q)`;
- `(m, P) ; (replace X, Q) = (replace X, Q)`;
- `(replace X, P) ; (inherit, Q) = (replace X, P ∪ Q)`.

These pairs are a monoid with unit `(inherit, ∅)`. Their action on key sets is a monoid action.
The transformer of a path is the fold of its regions' actions.

The mask has the same structure on a smaller monoid: identity, mask, unmask, with the last region
winning. rc.112's `uninterruptibleMask(restore)` is a replace action: `restore` sets the mask back
to the value captured at the region's entry. Option A's capture-and-replace gives services the same
lexical escape: capture the context at the body's entry, replace around the site, and the callback
sees only what the caller provided.

### 6.2 The transformer of a parameter

For a definition `d` and its parameter `i`, `T(d, i)` is a set of actions, one per way the
parameter can run:

- for each site `perform (.param i)` at path `π` in `d`'s body: the fold of the actions on the path
  from the body's root to `π`;
- for each invocation of a definition `g` at path `σ` in `d`'s body whose passed program `j` runs
  parameter `i` at path `τ` inside it: `fold(σ) ; t ; fold(τ)` for each `t` in `T(g, j)`.

The second clause is the order-two link of the topology note (§4.3): a passed program runs at its
own site, under the frames of the body that runs it. Recursion among definitions makes `T` a least
fixpoint. It exists and is reached in finitely many rounds, because the actions over the finite set
`K` are finite. A declared transformer in the header replaces the fixpoint by a check, as declared
rows already replace inference for recursion (`Signature.withDefs`).

### 6.3 The rule at a call

Let `ρ` be the passed program's requirement row and `B` the body's own row. The call requires

```text
B  ∪  ⋃ { ρ \ P | (inherit, P) ∈ T(d, i) }
```

and it is refused unless `ρ ⊆ X ∪ P` for each `(replace X, P)` in `T(d, i)`. For inherit actions
only their intersection matters: the call requires `ρ \ ⋂ P`. The rule takes the checker's current
rule as its special case `T = {(inherit, ∅)}`, which charges all of `ρ` to the call.

Its soundness statement (proposed, §8): when a passed program starts at a site, the fiber's context
is the site's action applied to the context at the invocation. With the call's requirement met at
the invocation, the passed program's requirement is then met at its start.

### 6.4 How it prints

Effect's types already spell both actions:

- an inherit action is `Exclude`, as in `provideService`'s own signature:
  `<R>(p: Effect<A, E, R>) => Effect<B, E2, Exclude<R, P> | RB>`;
- a replace action is a bound on the type parameter: `<R extends X | P>`.

So HO3-REQ-01 closes by printing the transformer on the header, with tsgo 7 as the oracle, and
HO-4's generics carry the requirement variable.

## 7. What changes for authors and agents

- An author writes a definition once. The checker computes each parameter's transformer as a
  path fold and shows it in the interface: "your callback runs with `Db` provided and masked".
- An agent's hole inside a definition's body gets its dynamic context as a column of the address
  table, next to its environment.
- A definition that must not leak its services to callbacks says so with capture and replace, and
  the transformer shows `replace`.

## 8. Placement

| Item | Concept, property | Question | Reach | Does not establish | Serves |
| --- | --- | --- | --- | --- | --- |
| `E4-CTX-CE-001` (proposed counterexample) | `context-requirements`; presence | a checked, admitted program at a closed row dies with `missingService` | the programs `reset` and `resetInBody` at budget 400, the frame machine, the empty row table | anything about the OCaml route or a printed module (the printer refuses the action) | R5, R9; row 117 part two |
| `ctx-chain` (proposed claim, role invariant) | `context-requirements`; a new property "the context is the chain of its restoring frames" | every live fiber's context is related to its stack by `CtxChain` at its base | every program without raw context writes (option A), the native evaluator, along `Machine.Lift` | presence at any position; liveness | row 117's per-position clause; R9 |
| `region-restores-context` (proposed claim) | `scope-lifetime-finalization`; the region bracket | a providing region ends at its entry's context | as `compiled_region_bracket`, for the services' restoring frames | that the region ends | R5, R11 |
| `param-context-transformer` (proposed claim) | `context-requirements`; a new property "a passed program starts in its site's context" | at a parameter's run, the context is `T`'s action applied to the invocation's context | definitions with parameters (row 340), option A | typing of the call; printing | HO3-REQ-01, HO-4, HO-5 (Pool's service) |
| `call-requirement-transformed` (proposed claim, soundness) | `context-requirements`; `provide-discharges` at calls | the call rule of §6.3 is sound for the machine | as above, with `ctx-chain` | completeness against Effect's types | R5, R9 |

The proof plan and its order are in the [README](README.md), §6.

## 9. What this note does not establish

- The probe is a finite run of six programs on the frame machine at the empty row table. It shows
  nothing about the OCaml route, a printed module or another budget.
- No theorem here is proved. `CtxChain` is a proposed definition. The transformer rule is a
  design, checked only against the probe's four programs of §5.
- rc.112 was read, not run, for §5: its `updateContext` region provides around whatever runs inside
  it. A truth-lane run of `dyn` is owed before the printer relies on it.
- The repair options change the object language. They are the owner's to rule.
