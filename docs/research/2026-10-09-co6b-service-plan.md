# 2026-10-09 Plan: a definition block printed to TypeScript as an Effect service (slice CO-6b)

Status: a plan (history, not authority). Base: `refactor/phase1-phase3` at the commit that adds
this file. Ruling: decisions row 338, item (4), shape (b). The coalgebra note,
`docs/research/2026-10-09-host-coalgebra.md`, sections 5.3 and 5.5, gives the reasons.

## 1. The one thing to know first

A block that declares a service prints as a `Context.Service` class and a `Layer.effect`. The
layer runs the service's initial program once, which builds the service's state, and the
service's methods close over that state. So an Effect TypeScript program uses a verified Queue
through its tag (`yield* NumberQueue`) and never holds the queue's cell. The one choice left for
the owner is where the declaration is stored (section 3); every other part of this plan is
independent of it.

## 2. The printed form

The target is Effect 4.0.0-rc.112. A service class extends `Context.Service<Self, Shape>()("Key")`
(`vendor/effect-4.0.0-rc.112/src/Context.ts`, `Service`). A layer built by an effect is
`Layer.effect(service, effect)`, of type `Layer<I, E, Exclude<R, Scope.Scope>>`
(`vendor/effect-4.0.0-rc.112/src/Layer.ts`, `effect`). For a Queue of numbers:

```ts
export const numberQueueMake = (a0: void): Effect.Effect<QueueCell, never, never> => …
export const queueTake = (a0: QueueCell): Effect.Effect<number, never, never> => …
export const queueOffer = (a0: readonly [QueueCell, number]): Effect.Effect<boolean, never, never> => …
export class NumberQueue extends Context.Service<NumberQueue, {
  readonly take: () => Effect.Effect<number, never, never>
  readonly offer: (a1: number) => Effect.Effect<boolean, never, never>
}>()("NumberQueue") {}
export const NumberQueueLayer = Layer.effect(NumberQueue,
  Effect.map(numberQueueMake(undefined), (a0) => ({
    take: () => queueTake(a0),
    offer: (a1: number) => queueOffer(pair(a0, a1))
  })))
```

The definitions print as they do today (`printDef`, `src/Effect4/Codegen/Print.lean`). The class
and the layer are two more declarations after the definitions. A method's arguments are its
definition's request after the first component, which is the state. The closure rebuilds the
request with `pair`, as the authoring surface builds it (`Authoring.requestOf`). The lean4-typescript
AST already has the class form (`TypeScript.ClassDecl`, whose heritage is an expression), object
types and function types (`TypeScript.TypeRef`).

## 3. Where the declaration lives (the owner's choice)

| | Representation | Cost |
| --- | --- | --- |
| R1 | a fourth field of `Eff.defs`: the block's services | the program family changes: 64 files read `.defs`, the generated algebras and folds, the wire bytes |
| R2 | a role on each definition (`DefDecl.role`): plain, a service's initial program, or a service's method with its arity | one structure field with a default; 34 files read `DefDecl`; a program with no role keeps its bytes when the role is encoded only where it is not plain |
| R3 | outside the program: a service specification passed to the emitter | no program change; the program's bytes and digest do not say that it exports a service |

Recommended: **R2**. The ruling says that the block declares the service, which R3 does not do.
R2 keeps the initial program a definition, so its typing, invocation, printing and laws are the
definitions' own. R1 would add a second list beside the definitions with no gain.

## 4. Formation

A service is well formed when these hold, each refused by name with its path otherwise:

- its name is an export name, distinct from every other declaration of the module;
- exactly one definition is its initial program, with the request `unit`; its answer is the
  service's state type `C`;
- it has at least one method; a method's request is `C`, or `prod C R` with the method's arity
  read off `R`; method names are distinct;
- the definitions it names are in the block.

Roles change no verdict. The admission of a program with a block, its denotation and its machine
runs read no role (a law, section 6).

## 5. Slices, in order

1. **S1, the program syntax** (a day). `DefDecl.role` takes its default. The wire encoding
   appends the role where it is not plain. The authoring surface declares a service
   (`eff_module` gains a `service` clause). Formation checks a service, with its refusals.
   Queue, Semaphore and Pool declare their services. The narrow builds and the program
   batteries that the field reaches run.
2. **S2, the printer and the reader** (a day). `printService`, the class and the layer; the
   reader reads them back and checks them against the roles; name safety. The round trip
   extends `readModule_printModule_defs` to blocks with services.
3. **S3, the truth lane** (a day). Each service gets a fixture: a TypeScript client that
   uses the service through its tag. tsgo 7 checks it and rc.112 runs it. Its run
   is compared with the machine's run of the same client, written as a program over the
   definitions.
4. **Later, shape (c).** The rows that a service's definitions call become the layer's
   requirements, and a typed layer (`Handler.Typed`, `Effects` v0.9.1) prints as
   `Layer<S, never, T>`.

## 6. Placement of the obligations

| Obligation | Concept and role | Reach | Not established | Consumer |
| --- | --- | --- | --- | --- |
| roles are inert: the admission of a program, the denotation and the machine read no role | `translation-simulation`, compatibility | every block | nothing about the printed service | S2's round trip; R2 (conservative extension) |
| formation of a service is decided: `explain = none ↔ wellFormed` | `exact-codecs`, a located refusal | blocks with roles | typing of the client | the printer's domain |
| the round trip of a block with services | `exact-codecs`, compatibility; extends the claim `module-defs-round-trip` | the readable domain of a block | target typing; execution | S3; R5 (services) |
| a client's run through the service equals the machine's run | host-only, finite: the truth lane | the fixtures | any program outside them | R8 (runs and faces as named connections) |

## 7. What this plan does not establish

- No theorem of section 6 exists yet.
- The printed layer is not proved to run as the machine does: that is the truth lane's finite
  evidence, for its fixtures.
- Shape (c) and the typed layer's print are named, not designed.
