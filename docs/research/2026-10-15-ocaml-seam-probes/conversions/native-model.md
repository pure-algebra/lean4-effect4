# Model the actual native interface before deriving its conveniences

A precise native interface model needs abstract carrier families, type-sharing equations, operation meanings and their laws.
Deriving codecs or runtime type descriptions does not supply that model.
The existing `Ty`, `Image`, `ValueModel` and `RowProtocol` provide several required connections, but they do not describe every native type.

Here, a native realization means a selected native module interpreted through its declared carrier relations, operation meanings and observations.
It is a semantic interpretation of an interface, not another stored program or universal native type language.
This addendum proposes its smallest useful form.
It adds no Lean declaration, planned goal, dependency or production implementation.
Decisions rows 391 and 392 continue to govern the LCNF lowering trust boundary.

## Keep the actual distinctions

| Object | Mathematical role | Existing source |
| --- | --- | --- |
| A program `Ty` | Describes program value membership. | `src/Effect4/Program/TyCore.lean` |
| A selected `Image α` | Chooses exact value frames for a carrier. | `src/Effect4/Store/Carrier/Image.lean` |
| `ValueModel α` | Connects an image to a normalized program type under value-dependent allocation premises. | `src/Effect4/Laws/Program/ValueModel.lean` |
| A native static type | Determines which native terms and type-sharing equations the OCaml compiler accepts. | The actual selected `.mli` and OCaml type checker |
| A runtime typed key | Identifies one allocated key, indexed by a native type. | Installed `base/type_equal.mli` |
| A comparator witness | Distinguishes the dictionary used by an ordered collection. | Installed `base/comparator.mli` |
| A binary shape | Describes a selected binary codec structure. | Installed `bin_prot/shape/bin_shape.mli` |
| A host operation contract | Describes admitted requests and successful answers at existing row columns. | `src/Effect4/Program/RowProtocol.lean` |

Do not identify these objects because one generated module exposes them together.
In particular, equal mathematical carrier sets need not mean interchangeable abstract OCaml types.
Two distinct abstract types may both use an integer internally.
Conversely, two distinct runtime typed keys can index the same native static type.

## The smallest semantic record

Choose one actual native module type signature and interpret only its selected public operations.
For that signature, record the following components.

| Component | What it records | Why it is needed |
| --- | --- | --- |
| Carrier family | A mathematical carrier for each abstract type and each type constructor's arguments. | Retains abstraction and parameter relationships. |
| Type-sharing context | Manifest aliases, abstract identities and equality evidence that the signature exposes. | Distinguishes equal layout from native type equality. |
| Runtime identity state | Fresh runtime keys and their associated carrier types. | Models `Type_equal.Id.create` without confusing it with static type creation. |
| Operation interpretation | The selected pure function or state-transition relation for each public operation. | A function type alone does not state its meaning. |
| Realization relation | Relates mathematical values and states to their native representatives. | Connects abstract libraries to their actual implementation. |
| Laws and observations | Equations, allowed failures, state effects, identity observations and progress assumptions. | Defines what an exact native-interface claim would mean. |
| Data connections | Existing `Ty`, selected `Image`, profile and codec admission for serializable members only. | Keeps program data separate from native witnesses and resources. |

The carriers and operation functions belong to the semantic interpretation.
They are not functions stored inside `Eff`, `Ty` or canonical interface syntax.
Start with ordinary Lean structures for the selected signature's mathematical operations and properties, if implementation work is later authorized.
Do not introduce a recursive native-type AST merely to hold this semantic record.

For a mathematical carrier `A` and native values of the selected type, write `R(a, n)` for their realization relation.
The notation does not presume that arbitrary native heap values are already represented inside Lean.
An implementation connection must state how its native observations are modeled or checked.

For immutable data, an interface may promise the following proposed conditions:

```text
decodeNative(encodeNative(a)) = Some a
decodeNative(n) = Some a  implies  n is observationally equal to encodeNative(a)
```

Name the observation and any normalizer in the second condition.
For a record, field values may suffice.
For a native map, public lookups may suffice, while tree balancing and allocation remain outside the observation.
That map relation is not equality of native heap representations.
For an actual resource, the observation also needs identity and ownership state.

## Ordinary data and abstract types

`Model.algAt` produces a carrier and its selected image together in `src/Effect4/Schema/Modeled.lean`.
`Modeled` adds two inverse maps between a named Lean type and that carrier.
This is already a mathematical model for its supported data fragment.
The native realization must additionally connect that carrier to the precise chosen OCaml representation and profile.

For example, a bounded abstract natural has mathematical carrier `{n : Nat | n ≤ bound}`.
Its native implementation may use OCaml integers, but its realization relation excludes negative and oversized integers.
The existing abstract `E4_clock.t` offers a related exact-storage example in `ocaml/clock/e4_clock.mli`.
The native `.mli` controls what a caller can construct through that interface.
It does not by itself prove the implementation checks every bound correctly.

A representation re-export keeps native type equality and exposes ordinary constructors.
It is suitable for adding operations to an existing raw carrier.
A public alias to that raw type cannot additionally prevent callers from using its raw constructors.
A checked interface must hide that equality, expose an admitted-value receipt, or keep validation explicit at each consuming boundary.
Hiding an equality changes the client's static knowledge without requiring a second runtime representation.

## Equality witnesses and existential packages

The installed `Base.Type_equal.t` has this indexed constructor:

```ocaml
type ('a, 'b) t = T : ('a, 'a) t
```

Its mathematical interpretation is an equality witness between the two interpreted native types.
Matching `T` permits transport of a value across that equality.
The proposed operation law is:

```text
transport(Refl, x) = x
```

The indexed result is essential.
Replacing this type by an ordinary unindexed tag or a string loses the relationship that makes transport valid.
The installed API and the [OCaml GADT manual](https://ocaml.org/manual/5.1/gadts.html) supply the source description.
This is a native type-safety connection under the trusted compiler and safe API assumptions.
It supplies no arbitrary value conversion or resource authority.

An existential package hides a carrier while keeping its values and operations tied to that carrier.
The mathematical shape is a dependent pair, such as `Σ A, (A × Operations A)`.
An actual first-class module can expose abstract type components and their sharing constraints.
The [OCaml first-class module manual](https://ocaml.org/manual/5.1/firstclassmodules.html) specifies that package constraints have a restricted form.
The generated interface must use that actual supported package type, rather than pretending OCaml accepts arbitrary dependent packages.

For `Univ_map.Packed`, the installed interface ties a hidden type to both its key and its stored data.
For Eio, `Resource.T` ties a hidden backing type to a handler over that same type.
These are semantic packages of native values and operations.
They need no encoding as stored program values.
Only their explicit data observations cross the existing program boundary.

## Runtime key generation is a state transition

`Type_equal.Id.create` creates a fresh runtime key even when its native type and display name repeat.
Model this allocation in a key world, separate from native static type equality.
For a key `k` indexed by native type `A`, creation extends that world with a fresh key associated with `A`.
The display name is metadata.

The installed `base/type_equal.mli` supports these proposed model equations:

```text
same_witness(k, k) returns an equality witness
same_witness(k1, k2) returns a witness  implies  TypeOf(k1) = TypeOf(k2)
distinct allocated keys return no witness
```

The converse of the second implication is false.
Equal native types can have distinct keys.
The retained ecosystem probe already demonstrates that distinction.

The selected `Core.Univ_map` operation types keep the key and value at the same type parameter:

```ocaml
val set : t -> key:'a Base.Type_equal.Id.t -> data:'a -> t
val find : t -> 'a Base.Type_equal.Id.t -> 'a option
```

For those actual indexed operations, the proposed mathematical laws include:

```text
find(set(m, k, v), k) = Some v
same(k, q) = false  implies  find(set(m, k, v), q) = find(m, q)
find(remove(m, k), k) = None
```

The key indices keep each equation's value type consistent.
The custom-key implementation must return a stable key from `type_id` on repeated calls for the same input.
That premise appears in installed `core/univ_map/univ_map_intf.ml`.
The equations are candidate laws of a selected library realization, not results proved by the probe.

Runtime key freshness does not describe all OCaml module type generation.
The [OCaml generative-functor manual](https://ocaml.org/manual/5.1/generativefunctors.html) distinguishes fresh result types from repeated applicative use of the same module argument.
A precise module model must keep those static sharing rules separately.
Neither mechanism makes a key persistent across processes.
The recorded service identity remains existing first-order data.

## Comparators need a dictionary and its laws

The actual comparator has two indices: the carrier and its comparator witness.
Base maps and sets retain that witness in their own types.
The installed `base/comparator.mli` exposes a private dictionary containing comparison and inspection functions.
Its witness separates dictionaries, rather than proving an ordering law.

The actual map carrier has three parameters, `('key, 'data, 'cmp) Base.Map.t`.
Its selected lookup has the native type:

```ocaml
val find : ('key, 'data, 'cmp) Base.Map.t -> 'key -> 'data option
```

The mathematical carrier family must retain all three parameters.
Erasing `'cmp` would forget which equality and ordering the map uses.

A mathematical comparator model supplies a selected equality relation `≈` and an order on its equivalence classes.
For a pure terminating comparator `c`, the proposed criteria include:

```text
c(x, y) = 0  iff  x ≈ y
sign(c(x, y)) = -sign(c(y, x))
c(x, y) < 0 and c(y, z) < 0  implies  c(x, z) < 0
```

The model also states determinism and the absence of exceptions for admitted values.
An ordinary OCaml comparison signature permits a function that raises, changes with mutable state, or violates transitivity.
Compilation alone excludes none of those implementations.

For a map interpreted by its lookups under that comparator, a proposed operation law is:

```text
find(set(m, k, v), q) =
  if c(q, k) = 0 then Some v else find(m, q)
```

This equation does not choose which representative key survives when two keys compare equal.
If the public interface observes representative keys, its mathematical model must specify that behavior too.
The comparator-witness type prevents mixing incompatible collection dictionaries.
The retained compile rejection demonstrates that static protection.
It does not prove these map or comparator laws for every implementation.

Hashing adds its own compatibility condition:

```text
x ≈ y  implies  hash(x) = hash(y)
```

The hash need not be injective.
Its result does not replace Effect4's canonical content digest.

## Polymorphism and capability rows retain relationships

Native polymorphism is more than a string spelling for a type variable.
For example, a list-map interface relates the callback's input and output types to both list types.
A mathematical interpretation quantifies over those carrier types and their realization relations.
Identity and composition equations require a named pure, terminating callback fragment.
An OCaml polymorphic signature alone does not exclude exceptions, divergence or callback effects.

A higher-rank field quantifies inside the operation dictionary.
The installed `typerep/variant_and_record_intf.ml` has a record-field reader polymorphic in the selected field's type.
Keep that quantifier and field index when modeling the actual dictionary.
Do not erase them into an unrelated untyped field lookup.

Eio capability rows describe which operations a resource type offers.
Installed `eio/flow.mli` and `eio/resource.mli` use polymorphic variant rows and a contravariant resource parameter.
The [OCaml polymorphic-variant manual](https://ocaml.org/manual/5.1/polyvariant.html) distinguishes open lower bounds, upper bounds and fixed rows.
A faithful model retains those bounds and the actual resource parameter's variance.

The semantic resource relation must additionally state that the selected provider implements each required operation at the hidden backing type.
The earlier Eio probe demonstrates why claimed tags alone do not establish provider presence.
No capability row establishes that a resource remains open or owned by this session.
That information belongs in the resource-state relation and the existing host-boundary contract.

`RowProtocol` refines existing program request and successful-answer columns with first-order Boolean terms.
Its current `keepsAt` accepts failing exits without reading their payloads.
It cannot inspect arbitrary native closures, establish comparator purity, or express all native module-sharing equations.
Use it for its actual data-boundary role.
Keep the native interface's additional semantic laws explicit.

## The current target syntax has a real expressiveness limit

`OCaml5.Ml.Ty` in `src/OCaml5/Ml/Syntax.lean` supports variables, applications, arrows, tuples and anonymous types.
`TyBody` supports ordinary records, ordinary variants, aliases and abstract declarations.
`Ctor` records argument types but no indexed result type or existential binder.
`Decl.moduleD` supports named functor parameters and bodies.

These forms do not currently describe indexed GADT constructor results, explicit row constraints, higher-rank fields or first-class package types.
The syntax also lacks a structured signature language for all the module-sharing constraints discussed above.
`rawD` can hold text, but that does not make the type relationships inspectable or checked by the internal syntax model.
`typeParameterIndices` in `src/OCaml5/Lcnf/Types.lean` also drops value and instance parameters.
That existing lowering policy is not an embedding of arbitrary Lean indexed families into native GADTs.

Therefore, precise models for these selected native signatures are proposed additional semantic connections.
They are not already encoded by the current program `Ty` or target syntax.
Start with one actual signature and its direct semantic record.
If generation later needs more target syntax, extend the existing target AST for that consumer.
Do not create another canonical program type language or silently store whole signatures inside a handle name.

## What an exact verified native-interface claim would require

The concrete starting candidate is a typed key, its selected data image and a small immutable map interface.
Its model must retain the actual carrier parameters, key identity, comparator witness and lookup observation.
Its generated `.mli` must retain those same type relationships.
Its implementation connection must bind the exact native code and library artifact to the chosen operation laws.

A mathematical law proved only for the abstract dictionary leaves the dictionary-realization premise open.
A compiled signature proves neither that premise nor its operation equations.
A finite control establishes only its exercised observations.
The current trust ruling accepts the designated generated machine through LCNF with named assumptions.
It does not automatically establish every imported Jane Street implementation's model correspondence.

The proposed placements remain existing concepts and concrete consumers:

| Model part | Existing placement | Concrete consumer and limit |
| --- | --- | --- |
| Data image and admitted native carrier | `store-typing`, `exact-codecs`; R3 | One application record and selected native profile. |
| Typed operation and native dictionary interpretation | `translation-simulation`; R8 | One actual imported interface, with its library realization premise explicit. |
| Shared source description and exact type relationships | `initial-algebras-folds`; R3 and R8 | Selected native facade generation, within its stated signature fragment. |
| Keyed host methods and resource states | `host-session-protocol`, `scope-lifetime-finalization`; R6 and R11 | Native service interfaces, with host behavior and lifecycle premises explicit. |

This is research about the meaning and exact type precision of native interfaces.
The existing executable probes remain finite host evidence.
This addendum runs no new build or proof audit and adds no assigned proof work.
