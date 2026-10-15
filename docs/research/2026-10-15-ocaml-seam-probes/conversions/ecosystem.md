# Reuse Jane Street interfaces at the OCaml boundary

Effect4 can generate ordinary OCaml modules and let existing Jane Street tools add their operations.
The strongest first combination is module abstraction, representation re-export, `Type_equal.Id`, `Univ_map` and comparator witnesses.
These mechanisms supply typed application interfaces without another canonical program carrier.

The finite probe adds derivations to the existing generated `service_key` through a representation re-export.
Its derived reader returns the original generated type directly.
The original generated file needs no PPX annotation or Jane Street dependency.

## Continuity and evidence

The earlier owner request favors Jane Street tooling in `docs/research/2026-09-04-ocaml-packages-plan.md`.
The later resolution keeps Base/Core outside minimal generated code in `docs/research/2026-09-07-ocaml-proposals.md`.
It also keeps canonical bytes as content identity.
This proposal follows that separation.
Those notes contain superseded runtime designs and historical measurements.
This report uses neither as fresh runtime evidence.

Rows 391 and 392 in `docs/core/decisions.md` govern this research.
No new LCNF lowering proof obligation or production change follows from the proposals below.
`note.md` supplies the existing `Ty`, `Modeled`, `Image` and frame-layout source map.

The new artifacts are in `conversions/ecosystem/` beside this report.
`run.log` records actual compiler versions, package versions, case names and diagnostic output.
`provenance.json` hashes installed interfaces, selected compiled libraries, probe artifacts and the copied generated carrier source.
`input-eff-types.ml` retains the exact copied source.
`expanded.ml` retains the PPX expansion that the probe compiles.
The script builds only a temporary dune workspace.

Run the probe:

```sh
python3 docs/research/2026-10-15-ocaml-seam-probes/conversions/ecosystem/run.py
```

The installed interface is the authority for the executable examples.
The reviewed upstream links below provide primary documentation for the mechanisms.
They do not establish compatibility with every feature on upstream's current branch.
The installed package versions are recorded in the log.
They include Base `v0.16.5`, Core `v0.16.2`, and the `v0.16.0` derivation and runtime packages exercised here.

## Recommended mechanisms

| Mechanism | Authoritative description | Effect4 extension seam | Concrete benefit |
| --- | --- | --- | --- |
| Abstract modules, functors and representation re-export | OCaml's module/type checker, exercised by the probe | Generate a facade beside `ocaml/eff/eff_types.ml` from the selected Lean declaration description. | One carrier receives familiar library interfaces without a second value conversion. |
| `Base.Type_equal.Id` and `Core.Univ_map` | Installed `base/type_equal.mli` and `core/univ_map/univ_map_intf.ml`; [Base upstream interface](https://github.com/janestreet/base/blob/master/src/type_equal_intf.ml) | Typed host service tables, resource metadata and per-carrier adapter caches. | Retrieves a value at its actual type through the matching key. |
| `Comparator.Make` and comparator witnesses | Installed `base/comparator.mli`; [upstream interface](https://github.com/janestreet/base/blob/master/src/comparator.mli) | Application maps, sets and canonical-order adapters. | Makes differently ordered collections distinct OCaml types. |
| `ppx_typerep_conv` and `Typerep` | Installed `typerep/std_internal.mli`, `variant_and_record_intf.ml`, `type_generic.mli`; [official deriver](https://github.com/janestreet/ppx_typerep_conv) | Inspection, editors, visitors and per-type runtime generic operations. | Supplies typed field access and handles recursive type descriptions. |
| `ppx_bin_prot` and binary shapes | Installed `bin_prot/shape/bin_shape.mli`; [official shape documentation](https://github.com/janestreet/bin_prot/blob/master/shape/README.md) | An explicitly selected native transport or cache protocol. | Generates efficient codecs and a separate compatibility description. |

The first three mechanisms deserve the first implementation slice.
Runtime generic derivation and another transport format should follow a concrete consumer.

## A generated facade can keep the existing type

An OCaml representation re-export names an existing record or variant while exposing its constructors to a deriver.
It is an identity of OCaml types, not a conversion through an isomorphic copy.
The probe compiles this form against the copied generated carrier:

```ocaml
module Service_key_view = struct
  type t = Eff_types.service_key = { name : int; service : int }
  [@@deriving sexp, sexp_grammar, compare, hash, bin_io, typerep]
end
```

The OCaml compiler checks that the re-export matches the original declaration.
Changing a field incompatibly fails before a converter can run.
The facade producer should read the existing Lean declaration description and its selected target carrier spelling.
It should not infer layouts by parsing generated text with another handwritten type inventory.

This pattern is useful when the generated runtime stays small and the application edge uses richer dependencies.
It can generate `.ml` facade modules and `.mli` interfaces in a separate dune library.
The `.mli` can expose abstract application types and checked construction functions.
It can also expose selected standard interfaces such as `Comparable.S`, `Hashable.S` or `Typerepable.S` when their operations are appropriate.
These named interfaces are proposed output contracts, not artifacts already generated by Effect4.

The probe's `PAYLOAD` signature packages a carrier with its type key, inspection function and matching binary reader/writer.
`inspect_binary` accepts a first-class module at that signature and uses its operations at the carrier's own type.
Application-specific codec modules can instantiate such a functor once.
Only heterogeneous selection needs first-class module packaging at runtime.

The important separation is between a carrier, a selected value image and an operation dictionary.
`Modeled.image` chooses the program-value frames.
PPX supplies operations on the resulting OCaml carrier.
Neither representation re-export nor `Typerep` chooses a different program-value encoding.

The earlier `note.md` gives concrete counterexamples to choosing an image by endpoint type alone.
`Canonical Int`, program integers, structural products and program products do not all share a frame layout.
The facade should therefore name its selected image or existing codec entry explicitly.

## Typed heterogeneous tables already exist

`Type_equal.Id.create` allocates a fresh runtime identity for one OCaml type.
`same_witness` returns typed equality evidence only for the matching identity.
`Core.Univ_map` already implements the heterogeneous map over those keys.
The application does not need an `Obj`-based value cast or a second hand-written heterogeneous map.

The probe stores a request record and recovers it with the original typed key.
A string key with the same display name cannot retrieve it.
A fresh request-record key with the same display name cannot retrieve it either.
Duplicate insertion through the original key is detected.

Generate one key per selected facade module and keep that key stable within the running process.
Do not allocate a fresh key on every lookup.
The custom-key `Univ_map.Make` interface explicitly requires stable `type_id` answers for the same input.

This gives the host resource table two distinct levels.
The persisted service key selects a registered adapter through existing checked metadata.
The adapter's process-local type key selects its actual OCaml value.
The process-local key is neither the persisted service identity nor the machine's allocation index.
It must not appear as content identity or become a serialized resource.

This mechanism can support several practical consumers:

- A host service table stores differently typed service implementations behind generated facade keys.
- An adapter cache stores a typed codec or inspector for each registered carrier.
- A native resource collection stores actual Eio resources while program values retain their existing handle descriptions.

The map establishes no resource ownership, retirement, cancellation or eventual response policy.
The host boundary in `docs/core/host-boundary.md` continues to own those questions.
The probe executes no FFI or Eio resource lifecycle.
An FFI still needs explicit byte or opaque-handle entries and its own ABI description.
LC-7's `Live.startBytes`, `Live.feedBytes` and `Live.viewBytes` remain planned endpoints in the reviewed tree.

Use the installed name `Base.Type_equal.Id` in this implementation slice.
Do not introduce a speculative `Type_id` compatibility layer before an actual package migration needs one.

## Collection order can be part of the type

`Comparator.Make` creates an ordering dictionary and its abstract comparator witness.
Base maps and sets carry that witness in their type.
The probe constructs ascending and descending integer sets.
Both work individually, but OCaml rejects their union because their comparator witnesses differ.
The retained diagnostic names that exact mismatch.

This is a useful existing abstraction for typed keys, environment maps and ordered application data.
It prevents accidentally combining collections that use different order policies.
It does not prove that an arbitrary comparison function satisfies order laws.
Generated comparisons over ordinary concrete data avoid many handwritten cases.
An order that represents a program normalization policy still needs an explicit connection to that policy.

`ppx_compare` generates structural comparison and equality.
`ppx_hash` generates compatible hashing operations for the selected carrier.
Their outputs appear in `expanded.ml` as `compare`, `hash_fold_t` and `hash`.
They are useful for host maps, sets and caches.
Their integer hash result is not Effect4's content address.
The canonical bytes and existing digest operation retain that role.

Do not derive comparison or hashing over an actual Eio resource or a closure-containing runtime state.
Use the resource's explicit host identity and generated metadata instead.
For floating point, select the intended observation before adopting a default comparison or hash policy.
The earlier finite probe demonstrates why NaN payload identity needs special treatment.

## Runtime reflection is a view

`ppx_typerep_conv` generates `typerep_of_t` and `typename_of_t` from the OCaml declaration.
`Typerep` provides typed representations for base types, containers, records, variants, functions and named types.
The probe reads record field names and an integer field through the library's typed field accessor.
It uses no value cast.

The same-shaped independently declared record has a different nominal type witness.
A type alias retains the original type according to `Typerep.same`.
This distinction is useful for heterogeneous dispatch and generic application tooling.
It is different from deciding whether two program `Ty` values normalize to one form.

`Type_generic.Make` already builds computations from type representations.
Its `Named` interface supplies recursive construction, temporary computations and memoization.
Its registration functions select implementations for particular named types.
These facilities could support a generic inspector or editor without a custom recursive OCaml descriptor language.

Prefer direct derivation for a fixed serialization or comparison operation.
Choose `Typerep` when one runtime computation must handle types registered later.
For a fixed record's accessors, the smaller `ppx_fields_conv` interface may suffice.
The new probe does not test `ppx_fields_conv` or a complete custom `Type_generic.Make` computation.

The official deriver documents restrictions on complex types and signature generation.
For example, unconstrained types named `t` can receive named `Typerepable` interfaces in signatures.
Other declarations receive explicit generated bindings instead.
The installed `Typerep` source also exposes internal runtime-layout helpers.
Treat the library implementation and PPX as trusted host tooling.
Do not call it a Lean-verified representation or a C ABI description.

## Binary compatibility is different from type equality

`ppx_bin_prot` generates sizes, readers, writers, type-class dictionaries and binary shape values.
Its official [protocol documentation](https://github.com/janestreet/bin_prot) describes the transport and its supported values.
The expansion retains `bin_size_t`, `bin_write_t`, `bin_read_t`, `bin_writer_t`, `bin_reader_t`, `bin_t` and `bin_shape_t`.

The probe round-trips a record through its matching binary dictionary.
The alias has the same shape digest.
Renaming a field changes the shape digest, while the raw bytes still decode into the renamed record.
The application must check the expected shape separately before selecting that reader.
The bytes do not automatically enforce the shape contract.

The shape digest describes binary representation compatibility.
It is neither a runtime type-equality witness nor a content address.
The installed interface exposes an MD5-backed digest, so do not use it as an adversarial authentication mechanism.
It also does not validate value-level bounds such as program natural membership.
The probe's binary reader reconstructs a negative integer in a field that an application might intend as a natural.

Use this library when a named native channel benefits from its existing protocol and peer tooling.
Keep its protocol distinct from Effect4's canonical framing and content identity.
The present research provides no throughput result and chooses no replacement wire format.

## Grammars and test tooling

`sexp_grammar` supplies machine-readable input grammar for an inspection or configuration UI.
It derives from the same OCaml declaration as the reader.
The installed `Integer` grammar admits integer syntax without a native bit-width bound.
The actual `int` converter still refuses an oversized integer in the probe.
A grammar is therefore useful input assistance, not program value membership or codec admission.

The earlier `note.md` and `run.log` test deterministic Quickcheck generation and shrinking on an ordinary record.
They also retain a failing example for a deliberately discarded field.
Those generators concern the selected OCaml carrier.
A program-facing generator must additionally respect its selected image, bounds and allocation premises.
Derive those constraints from the admitted description instead of filtering arbitrary values until some happen to pass.

## Tractable first slice

Generate a facade for one existing named carrier and one modeled application record.
Keep the generated runtime's dependencies unchanged.

1. Generate representation re-exports and selected named `.mli` interfaces in a separate adapter library.
2. Derive comparison, hashing and inspection where the selected carrier supports them.
3. Allocate one `Type_equal.Id` in each facade module.
4. Use `Core.Univ_map` for one typed host service table with duplicate-key rejection.
5. Bundle the selected existing codec with its carrier through a module signature.
6. Test same-name wrong-type keys, recreated keys, incompatible comparators and malformed or out-of-profile values.

This slice extends the existing estate with library interfaces and typed dispatch.
It does not require another interpreter, canonical program carrier, universal codec, runtime type language or lowering proof programme.

## Evidence limits

The new probe exercises installed native OCaml tooling only.
It contains one generated-carrier re-export, ordinary application records, runtime-key controls and a static comparator-mismatch control.
Its measured case total appears in `ecosystem/run.log`.
No browser, Wasm, FFI, Eio lifecycle, throughput or generic compiler result follows.
The parent report owns the separate investigation of Rocq and other verified tooling.
