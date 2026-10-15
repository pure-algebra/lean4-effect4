# Mathematical contracts for native OCaml interfaces

Status: research proposal following the owner's clarification.
Role: a stronger design target for the OCaml boundary.
Evidence: current source, primary research, and finite native-library probes.
Scope: selected OCaml interfaces, with Eio byte streams as the first concrete consumer.

The target is a mathematical account of an actual native OCaml interface, with generated code that implements that account.
Generated values should inhabit the library's real types.
Existing library clients should accept them directly.
Generated clients should also accept existing providers under explicit behavioral assumptions.

This strengthens the earlier recommendation about adapters and derivation tools.
Those tools supply useful operations, but the central artifact is an interface with mathematical laws.
The laws describe values, relationships between types, permitted effects and resource state.
They are the basis for reusable guarantees about combinations of components.

The investigation creates no production implementation or new proof obligation.
Decisions rows 391 and 392 retain the current LCNF lowering assumptions.
The note proposes properties for future placement, rather than claiming that the present compiler proves them.

## 1. Model the actual library interface

Precise OCaml declarations reveal much more than field layouts.
They expose hidden carrier types, relationships between types, polymorphic operations and permitted resource interfaces.
Those declarations provide the structural part of a mathematical contract.
Behavioral documentation and implementation models provide its laws.

| Part of a native interface | Mathematical meaning | Existing project owner or extension point |
| --- | --- | --- |
| Ordinary data | A carrier, its accepted values and selected encoding | `Ty`, `Modeled`, `Image`, `ValueModel` |
| Abstract types | A hidden carrier with a relation to its abstract meaning | An interpretation of the chosen native module interface |
| Shared types and indexed constructors | Equalities and dependencies that operations must respect | The target type view and its interface checks |
| Polymorphic operations | Operations valid at each permitted type interpretation | The selected native module contract |
| Resource methods | A hidden state together with supported operations | Existing host meaning and context requirements |
| Mutable values and aliases | A shared state relation with explicit permissions | Host resource and buffer contracts |
| Effects and callbacks | Permitted interactions, replies and state changes | Host-session protocol and a named native execution model |

These are parts of one interface contract, not one new stored type language.
Serializable values continue to use the existing data plane.
Native resources remain native objects, related to logical identities and state.
Their mathematical meaning need not be a serialization of their heap layout.

`OCaml5.Ml.Ty` currently represents variables, named applications, arrows, tuples and anonymous annotations.
`OCaml5.Ml.TypeDecl` represents ordinary records, variants, aliases and abstract types.
Both live in `src/OCaml5/Ml/Syntax.lean`.
This target syntax does not yet describe every type form that Eio and Jane Street use.
The precise additions should follow a selected native interface and its generator consumer.

The [native-type analysis](conversions/native-model.md) identifies the required equalities, type parameters and generative identities.
The [generation analysis](lowering/native-contract-model.md) separates structural generation from behavioral assurance.

## 2. Eio resources have a useful mathematical structure

Eio's actual [resource interface](https://ocaml-multicore.github.io/eio/eio/Eio/Resource/index.html) packages hidden backing data with a typed method provider.
The installed source is `eio/resource.mli` in the pinned switch.
Its resource constructor hides the backing type while retaining its relationship with every provider method.

A schematic interpretation of this structure is:

```text
Resource(C) = exists A. (native value of A, method provider for A and interfaces C)
```

This is an interpretation of Eio's existing package, not a proposed replacement representation.
The exact OCaml type parameters, variance and method equalities still matter.
The generated resource should use `Eio.Resource.t` and Eio's provider constructors directly.

A lawful provider adds a semantic condition to that package.
Every advertised method must exist and meet its declared contract.
The existing resource probe shows why provider construction needs this extra condition.
A phantom interface tag alone can advertise a missing method.

Let `W` describe logical resources, their current phases and permitted aliases.
Let `Rel(W, logical resource, native resource)` connect the mathematical resource to the actual Eio value.
The relation changes as calls read, write, close, cancel or transfer ownership.
It does not turn the native resource into stored program syntax.

Ordinary data uses exact conversion laws.
A live resource uses a relation between states and observations.
Both can receive mathematical guarantees, but their statements differ.

## 3. A concrete contract: byte-stream source and sink

The [Eio Flow interface](https://ocaml-multicore.github.io/eio/eio/Eio/Flow/index.html) already defines the native consumer and provider types.
The proposed first model uses those types directly.
It starts with byte streams and copied buffers.
Optional borrowed-buffer methods remain explicit extensions, since they add lifetime conditions.

For a source, model the remaining byte sequence, its lifecycle and the caller's writable buffer slice.
On a successful read, the interface can return a nonempty prefix smaller than the buffer.
A useful proposed success relation is:

```text
remaining_before = returned_bytes ++ remaining_after
0 < length(returned_bytes) <= requested_capacity
buffer_after = buffer_before with the returned prefix written into the requested slice
```

The caller needs the agreed access to that slice during the call.
The relation accounts for aliases to the same underlying buffer.
The first profile requires exclusive access during mutation.
A broader profile needs a more permissive interference contract.

| Operation | Required observations in the proposed contract |
| --- | --- |
| `single_read` | Returned count, consumed prefix, changed buffer region, end-of-input and permitted failures |
| `single_write` | Accepted prefix of the concatenated input buffers and resulting sink state |
| `write` | All requested bytes on success, with partial state retained when a later operation fails |
| `read_exact` | Filled buffer on success, or already-written prefix when end-of-input occurs |
| `shutdown`, when the resource supplies `Shutdown` | Which direction stops accepting operations |
| `close`, when the resource supplies `Close` | Idempotent logical closure and refusal of new operations; pending operations need a separate policy |
| Cancellation | Which effects already happened, which work remains pending and who owns cleanup |

The contract does not promise identical chunk sizes for different providers.
It selects byte sequence, reported outcomes and relevant state changes as observations.
It also states the concurrency restrictions that clients must meet.
Plain source and sink interfaces do not include shutdown or close.
Those operations require their additional native interfaces.

The project already has a host interpretation through `Effects.Comodel` and the row meaning described in `docs/core/semantics.md`.
`RowProtocol`, in `src/Effect4/Program/RowProtocol.lean`, checks a request and its successful answer.
That particular record does not describe buffer mutation, failure-state changes or cancellation interleavings.
Those facts belong in the native operation's stateful contract and its connection to the existing session.
They cannot be inferred from a return type or inserted into `RowProtocol` without a design change.

## 4. Native interoperability works in the finite probe

The [native Flow probe](eio/native-contract/flow_probe.ml) constructs Eio source and sink providers through the actual provider interfaces.
Standard `Eio.Flow.copy` and `Eio.Buf_read` consume those providers unchanged.
The same generic clients also consume Eio's standard providers.
The [independent rerun](eio/native-contract/root-rerun.log) records the observations.

The controls exercise binary data, short reads, short writes and vectored writes.
One case reaches end-of-input during `read_exact` and observes the prefix already written.
Another checks that a read changes only its selected buffer region.
An additional typed method coexists with the standard Flow methods.

The probe also builds an in-memory provider at the real `Eio.Net` stream-socket interface.
Standard Flow operations, shutdown and close dispatch through that provider.
This exercises the socket interface, not an operating-system socket or network delivery.

These examples establish native interoperability for the exercised cases.
The providers are handwritten research examples, not generated or formally proved implementations.
They identify the actual target and useful falsifiers for the proposed generator.

Run the example:

```sh
sh docs/research/2026-10-15-ocaml-seam-probes/eio/native-contract/run.sh
```

## 5. State the reusable guarantee at the interface

The desired composition rule is conditional on both sides' contracts.
A client relies only on the selected interface's operations and meets their preconditions.
A provider implements those operations and meets their postconditions and lifecycle conditions.
Their composition should then meet the client's stated observation contract.

This is stronger than checking each application-specific adapter independently.
Once the interface connection is established, many clients can reuse it.
Existing Eio clients need no special Effect4 value format when the generated values inhabit Eio's real types.

The phrase "any Eio code" has two different reaches.
Native type compatibility applies to clients expecting the interfaces actually provided.
A behavioral theorem also needs the client's and provider's contracts.
An unrelated effect, an additional required interface or a violated buffer-lifetime rule adds an explicit condition.
An arbitrary third-party implementation does not acquire a proof from its type declaration alone.

The useful direction for implementation safety is that observed implementation executions belong to the allowed interface behavior.
Calls covered by the contract must acquire no new stuck state, such as a missing advertised method.
When two implementations have the same observations in both directions, the stronger equal-observation claim becomes available for that fragment.
Termination and eventual network response remain separately stated properties.

## 6. Reuse the verification literature's abstractions

De Vilhena and Pottier's 2021 [A Separation Logic for Effect Handlers](https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf) provides a relevant protocol model.
It combines effect requests and replies with mutable-state assertions and modular reasoning.
Its formal calculus includes one-shot continuations, with explicit limits on concurrency and effect names.
The useful pattern is a protocol plus ownership assertions, rather than a type annotation alone.

De Vilhena, van Collem, Wright and Krebbers' 2026 [A Relational Separation Logic for Effect Handlers](https://simchavc.github.io/papers/blaze.pdf) adds relational reasoning.
Its Blaze development relates effectful implementations in an Iris/Rocq model, including concurrent examples.
The calculus is untyped, and the paper explicitly leaves a typed contextual-refinement statement for future work.
It is relevant methodological evidence, not a theorem about installed Eio or this generator.

Modern OCaml verification also includes Zoo and Osiris.
The [generation analysis](lowering/native-contract-model.md) records their actual languages, toolchains and assumptions.
They improve the available models for selected mutable or concurrent components.
Their existence does not require moving this project's semantic ownership out of Lean.

## 7. Placement and a decisive first slice

The following are proposed questions with consumers, not assigned proof goals.
Existing theorem references retain their current reach.

| Question | Existing concept and requirement | Consumer | Remaining condition |
| --- | --- | --- | --- |
| Does native data implement its selected value image? | `store-typing`, `exact-codecs`; R3 | Stream payload and application-record conversions | Declared data profile and lowering assumptions |
| Does generated code expose the selected native type relationships? | `translation-simulation`; R8 | Actual Eio provider and client interfaces | Structured target description and OCaml type checking |
| Does a provider implement the allowed operation behavior? | `host-session-protocol`; R6 | Source and sink methods | State relation, failures and stated environment behavior |
| Do aliases and cleanup satisfy the resource contract? | `scope-lifetime-finalization`; R11 | Buffers, streams and scoped operations | Permissions and pending-operation policy |
| Can a client reuse a provider through the selected interface? | `context-requirements`, `translation-simulation`; R6 and R8 | Unchanged standard library clients | Both contracts and a named observation |

Start with a mathematical byte-stream contract and a generated in-memory implementation.
Generate the actual Eio provider methods and constructors from that description.
Check their types against the installed library.
Use standard Eio consumers and the retained partial-I/O controls as external observations.
Connect an existing Eio provider through the same interface with its assumptions recorded.

The first result should package the model, native interface, generated implementation, exact data conversions and evidence together.
That establishes a reusable foundation for files, sockets, protocol libraries and task-backed services.
The broader benefit comes from repeating this interface-level construction across the existing OCaml ecosystem.
