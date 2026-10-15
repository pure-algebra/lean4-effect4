# The mathematical model of a generated OCaml interface

Status: proposed interface model, not authority or assigned proof work.
The current LCNF lowering trust boundary of decisions row 391 remains in force.

The useful model separates values, operation interfaces and resource state.
The project already has owners for each part.
This note connects them to ordinary OCaml modules and existing libraries.
The owner's later clarification strengthens the target to actual native interfaces with mathematical laws.
The [native-interface proposal](native-interfaces.md) develops that target, including mutable buffers and ordinary Eio clients.

## Values: an explicit image and a target profile

`Image α` already selects an encoding of a Lean carrier into `Store.Val`.
Its fields include these equations in `src/Effect4/Store/Carrier/Image.lean`:

```text
ofVal (toVal a) = some a
ofVal v = some a  implies  v = toVal a
```

The first equation reconstructs a written value.
The second excludes values outside that selected image.
The choice of image matters even when the endpoint types match.
The [finite Lean probe](ModelProbe.lean) distinguishes stored products from program products, and stored integers from program integers.

`ValueModel` adds a normalized program type and value-dependent allocation premises.
It lives in `src/Effect4/Laws/Program/ValueModel.lean`.
`Model.algAt` generates a carrier and its image together from a type description.
`Modeled` transports that image to a named Lean type.
Those definitions live in `src/Effect4/Schema/Modeled.lean`.

The proposed OCaml data module is a view of that selected model.
Its abstract native type hides values outside the supported boundary profile.
Its constructors and readers return an explicit refusal when an input is outside that profile.
The public signature must hide any raw type equality that would bypass those checks.
A representation re-export alone only adds operations to raw values.

| Part | Meaning | Example |
| --- | --- | --- |
| Program type | Which program values belong | `Ty.nat` |
| Selected image | Which value frames encode the carrier | `Image.nat` |
| Native representation | Which OCaml values carry it | Exact Zarith natural or bounded abstract integer |
| Target profile | Which source values the interface admits | A checked numeric interval |
| Codec admission | Which admitted values the chosen wire can express | JSON's exact-number condition |

A shared runtime type key supplies evidence that the stored and requested native types agree.
Different generative keys can still represent the same OCaml type.
The key does not select a program-value image or prove its profile condition.
A shape digest identifies a declared codec structure.
It does not establish the operation's meaning or replace the canonical content digest.

The existing byte laws also require the encoded value tree's size condition where stated.
`Image.decode_encode` names that premise.
`Image.encode?` checks it before producing bytes.
The proposed adapter should reuse that distinction.

For one data adapter, let `Rep(a, n)` relate a Lean value to its native OCaml value.
Let `P(a)` state the selected target profile, and let `I` be the selected image.
This relation accommodates an abstract native type, Zarith storage or a bounded integer without equating their implementations.
The proposed canonical-byte interface has these design criteria:

```text
P(a) implies there exists n with Rep(a, n)

Rep(a, n) and P(a) and I.encode?(a) = some b
  imply nativeEncode(n) = Ok b
    and there exists n' with nativeDecode(b) = Ok n' and Rep(a, n')

nativeDecode(b) = Ok n
  implies there exists a with P(a), Rep(a, n), and I.decode(b) = some a
```

The exported constructors must produce values related to some profile-admitted Lean value.
The second criterion requires matching bytes and recovery of the represented value.
It gives a direct differential test against the existing Lean encoder.
The third excludes a native decoder that accepts extra canonical-byte values.
S-expression conversion has a different normalization policy, described below.
These equations are proposed interface criteria, not newly assigned Lean proof obligations.

**Placement.** Concept: `store-typing` and `exact-codecs`; property: `modeled-membership` and `modeled-codec`.
**Question.** Can a generated OCaml data module implement the selected image on its declared profile?
**Consumer.** Application request and reply records.
**Reach.** Supported modeled data, named scalar bounds, selected frames and explicit codec admission.
**Does not establish.** Arbitrary `Ty` support, live resources, or correctness of every compiler stage.
**Unlocks.** R3's data interfaces and R8's explicit target connection.

## Normalization: a deliberate part of each format

S-expression readers can accept several spellings for one value.
The observed examples include reordered record fields and hexadecimal integers.
Text whitespace adds another distinction outside the parsed S-expression tree.

For a canonical S-expression-tree interface, the proposed criteria are:

```text
readSexp (writeSexp a) = Ok a
readSexp s = Ok a  implies  normalizeSexp s = writeSexp a
```

The normalizer must be named and idempotent on accepted trees.
Alternatively, a strict reader can reject any tree that differs from its canonical re-emission.
Neither choice retains original formatting.
Generic PPX conversion supplies neither the project's profile check nor an inherited Lean theorem.

An overlapping union needs special care.
An ordinary tagged OCaml sum distinguishes branches that an untagged program union may identify.
The first adapter profile can use disjoint tagged records.
A wider profile needs an explicit branch-normalization or ambiguity policy.

**Placement.** Concept: `exact-codecs`; property: the existing exact-embedding and codec-admission distinction.
**Question.** Which accepted spellings normalize to the chosen value image?
**Consumer.** S-expression configuration, fixtures and inspection tools.
**Reach.** A named format, its accepted domain and its normalizer.
**Does not establish.** Raw-text identity, arbitrary union recovery, NaN payload recovery or resource reconstruction.
**Unlocks.** R3's explicit conversions without replacing canonical storage bytes.

## Operations: a typed interface plus a behavioral contract

An operation already has request, answer and error columns in a row table.
The call's checked instance refines generic columns where required.
`RowProtocol` can express demands on a request and promises about a successful answer.
Those terms are data, and the current protocol does not inspect failing answers.

The proposed OCaml operation module packages those existing facts as a callable interface.
It can contain request, answer and error data modules, a stable operation key and the binding entry point.
First-class modules or functors can pass that bundle through ordinary OCaml code.
Jane Street type witnesses can support heterogeneous native registries.

A native type identity has a different purpose from the stable operation key.
Recreating a native identity from the same display name must not silently authorize a different value.
The native service table should connect both identities explicitly.
Only the stable program and binding identities belong in the recorded protocol.

OCaml typing constrains calls to the interface.
It does not establish that an implementation keeps a declared postcondition.
Generated finite tests can compare the implementation with the existing model's observations.
A Gospel contract is another optional consumer of that model.

**Placement.** Concept: `context-requirements` and `host-session-protocol`; property: reply admission at the checked call instance.
**Question.** Does the selected binding answer the operation that this call requests?
**Consumer.** Generated repository and external-library interfaces.
**Reach.** The declared row table, call instance, binding identity and supported data profile.
**Does not establish.** Provider behavior, permitted global effects, eventual answers or resource ownership merely from an OCaml signature.
**Unlocks.** R6's host interface and R13's recorded inputs.

## Resources: interface support and lifetime are separate

An Eio resource packages private backing data with provider methods.
Its interface tags constrain callers.
Its resource state and finalization behavior remain runtime matters.
The [Eio probe](eio/resource_probe.ml) demonstrates a claimed tag without its provider implementation.
The [lifetime probe](eio/eio_probe.ml) demonstrates a resource used after its switch closes.

A generated factory can hide arbitrary resource construction.
The host resource table still relates a logical resource identity to an actual native object.
That relation records its kind, session, ownership phase and permitted operations.
Native pointers, continuations and resource objects remain outside stored `Eff` syntax.

The existing host-boundary contract separates acquisition, receipt, preparation, application, cleanup and compensation.
The adapter should implement that lifecycle rather than equating a resource type with a live ownership certificate.
A phantom state parameter can improve a client interface.
It cannot prevent an unrestricted OCaml client from retaining an alias to an earlier state.
Runtime checks or a controlled callback interface still matter.

**Placement.** Concept: `scope-lifetime-finalization` and `host-session-protocol`; property: the existing ownership and retirement contract.
**Question.** Which side owns the resource before and after a selected reply application?
**Consumer.** Resource-bearing external operations.
**Reach.** Registered resources, named cleanup behavior, cancellation and transfer phases.
**Does not establish.** Global linearity, exactly-once physical side effects or termination of cleanup.
**Unlocks.** R11's release requirements and R6's resource boundary.

## Concurrency: native jobs implement host transitions

The existing host model is `Effects.Comodel` in the pinned `effects` package.
It answers an operation from private state with an answer and another state, or gives no answer.
The source theory already adopts the runner perspective of Ahman and Bauer's [Runners in Action](https://arxiv.org/abs/1910.11629).
This paper informs the model; its results do not certify Eio or the generated OCaml adapter.

A real asynchronous operation can take several native steps before it answers.
The proposed relation connects those native states to the existing host state and outstanding session calls.
An Eio promise or Picos computation implements a native job behind that relation.
It does not replace a machine fiber or its recorded decisions.

For safety, the proposed direction is:

```text
projected actual native traces  are included in  allowed protocol traces
```

The projection must name its observations.
Candidate observations include requests, accepted replies, selected applications, public results and cleanup outcomes.
Private scheduler steps can be hidden only when their public effects remain accounted for.

This direction excludes extra observable native behavior.
The opposite direction alone would permit an implementation with additional unwanted behaviors.
Equality of all scheduler choices is unnecessary for this first adapter.

Progress requires separate assumptions about execution opportunities, host responses and cleanup termination.
A waiting native job remains unfinished work.
A fuel frontier remains a frontier.
Neither becomes a program failure merely because the adapter has no answer yet.

**Placement.** Concept: `reactive-scheduling`, `host-session-protocol` and `translation-simulation`.
**Question.** Which observed executions of a named native adapter belong to the existing protocol?
**Consumer.** Eio and Picos host adapters, followed by foreign-library callbacks.
**Reach.** Named operations, explicit environment correspondence, recorded decisions and a selected observation.
**Does not establish.** Fairness, universal termination, identical scheduling or whole-compiler correctness.
**Unlocks.** R6, R8, R12 and R13 without introducing a second program representation.

## Generation: one source description, several existing consumers

The existing generated folds already provide a way to produce several views from one signature.
An interface, inspection codec, test generator and binding description are different views.
The runtime type witness can also be generated as a view when dispatch needs it.
It need not become a second manually maintained type language.

Each artifact should name its input description, selected image, profile and generator.
The artifact recipe should compile the interface against its implementation.
Focused controls should detect missing fields, wrong identities, wrong bounds and dropped behavior.

**Placement.** Concept: `initial-algebras-folds`; property: the existing fold construction and agreement machinery.
**Question.** Do the selected producers consume the same constructor and field description?
**Consumer.** Public data modules, adapters and generated contract tests.
**Reach.** The concrete producers and their stated source descriptions.
**Does not establish.** Correctness of PPX expansion, native libraries or every future generated artifact.
**Unlocks.** R3's reusable descriptions and R8's explicit artifact connections.
