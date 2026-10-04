# Maps and tuples after record integration

## Recommendation and scope

Reading base: coordinator worktree `ec5d1375e1717a1775c2787490a1e6ce54fdf6fb`.
Writing base: `eeb44689` on `codex/record-contracts`.
This is an implementation brief, not checked implementation evidence.
No Lean process, generator, or production edit belongs to this preparation.

Land string maps through the existing atom route.
Then add arbitrary-arity tuple construction through a variadic atom and static tuple projection through one new `Term` constructor.
Follow with the JSON and Schema faces; they are still missing and remain part of the data wave.
Keep `Ty`, `Term`, `Eff`, and `Store.Val` as the existing representations.

Authorities are decisions rows 125, 159, 166, 192–195, and DI-78.
Row 125 fixes string keys, sorted distinct entries, and `Readonly<Record<string, V>>`.
Row 159 fixes positional tuples at exact arity and normalization of two items to `prod`.
Row 166 selects atoms for dynamic map keys.
Row 195 retains maps and tuples in slice 2; it does not turn a map into a record.
Probe R's forms table recommends map construction from entries, optional lookup, and update; probe T's table also includes keys.
Probe Q's old constructor counts describe its historical base, not this integration.

## What already exists

| Concern | Current owner and evidence read |
| --- | --- |
| Type data, subtyping, normalization | `Program/TyCore.lean`, `Program/Ty.lean`: `map`, `tuple`, `sub`, `normalize`, `normalize_tuple_pair`; map keys invariant, values covariant, tuple arity exact |
| Raw formation and template use | `Program/Formation.lean`, `Program/Ty.lean`: string-key checks before normalization and after substitution; `infer` descends through maps and tuples |
| Value membership | `Program/Typed.lean`: `keyLt`, `sortedEntries`, `entriesHasTy`, `itemsHasTy`; `Laws/Program/Typed/Membership.lean`: `EntriesFit`, `ItemsFit`, `fits_tuple`, `fits_tuple_pair`, `fits_normalize` |
| Atom schemes | `Program/NativeAtom.lean`: `Scheme.poly`, `Scheme.custom`, `CustomScheme`, `Scheme.apply`; the existing template calculus suffices for the map signatures below |
| Target type projection | `Codegen/Types.lean`: `ofNormalized` already projects string maps and readonly tuples; record integration adds `Codegen/Metadata.lean` for exact raw type data |
| Missing operations | `Machine/Term.lean`: no map atoms, arbitrary tuple atom, or static tuple-index term |
| Missing boundary faces | `Schema/Codec.lean`: `isSupported`, `encodeRaw`, `decodeRaw` still refuse maps and tuples; `Schema/Bridge.lean`: `schema` writes unlowered markers and `reservedFree` refuses them |

Do not reopen the type append or duplicate the existing normalization proofs.
The new work connects executable value operations and their faces to these judgments.

## Proof placement before obligations

Every implementation helper below has one of these placements and an immediate consumer.
A new standalone claim is proposed only where the existing registry has no suitable question.
The coordinator registers such a claim before proving it; no new ledger mechanism is needed.

| Work | Concept and required property | Claim, role, and consumer | Reach and hypotheses | Limits and requirement |
| --- | --- | --- | --- | --- |
| Map operations and tuple construction/projection | Store Typing & Value Membership: typed evaluation and membership | Helpers of `denote-typed`, fundamental property, consumed by `NativeAtom.Sound`, `Typed.AtomFits`, `evalTerm_hasTy`, `evalTerm_isSome`, and world-indexed term evaluation | Accepted native argument types; fitted values in the same world; formed string maps; tuple projection admitted at every union branch | Actual pure-term results, not scheduler progress or host execution; M5, R3 |
| No new handles | Scope Lifetime & Finalization: handle reachability | Helpers of `m7-exit-handles-valid`, preservation, consumed by `nativeAtom_keys`, `evalTerm_keys`, and existing compiler connectors | Every successful raw evaluation; output handle keys are a subset of input keys | No allocation or finalization theorem added; existing M6/M7 consumers, R3 |
| Tuple-index target image | Exact Codecs & Data Plane Embeddings: retraction and exact reading | Proposed registry question `collection-term-print-read`, compatibility; consumers `readTerm_printTerm`, `readTerm_exact`, `ReadPrint`, and checked module reading | Retraction keeps only the existing scope premise; exactness assumes successful structural reading; arbitrary stored natural index retained | Structural TypeScript expressions only, not rendered-source parsing or target execution; R2/R3 |
| JSON faces | Exact Codecs & Data Plane Embeddings: retraction and exact reading | Existing `decode-encode` and `decode-iff`, compatibility/decidability; consumers `Ty.isCodecValue`, boundary admission and session adapters | Existing theorem domains retained, including canonical type and value admission conditions; string map keys and exact tuple arity | No opaque-handle serialization, numeric widening, or host-response totality; R2/R3/R4 |
| Schema faces | Exact Codecs & Data Plane Embeddings: retraction modulo the existing normalizer | Existing `of-schema-schema` and `of-schema-exact`, compatibility; consumers `Ty.schema`, schema documents and boundary profiles | Existing closed/reserved-free domains and annotation policy; plain tuple elements, no rest; string index signatures only | No new Schema transformations, optional tuple elements, or foreign type computation; R3 |
| Typing diagnostics and authoring | Residual Program Typing: admission agrees with the checker | Helpers of `denote-typed` and `raw-formation`; proposed `collection-diagnostics` decidability claim if a new diagnostic completeness theorem is needed; consumers `argTy`, diagnostics and `Authoring.elaborate` | Existing scope resolution and native signature; an index is data, not a value-dependent type | No second authoring tree or replacement checker; M5, R1/R3 |

The term-operation claims leave the machine's scheduler-progress question unchanged.
For source parsing and JavaScript execution, retain finite tests as finite evidence.
Do not describe those tests as a simulation theorem.

## Slice 2m: string maps through atoms

### Carrier and signatures

A machine map value is `Val.list` of **`Val.pair`** entries, strictly increasing by the UTF-8 bytes of each string key.
An ordinary program pair is instead `Val.list [key, value]` (`Val.tuple`).
`mapFromEntries` and `mapEntries` must convert between these two images; copying the input list is wrong.
The target value is an ordinary own-property object with type `Readonly<Record<string, V>>`, not a JavaScript `Map`.

Use these names provisionally in the one `NativeAtom` table; authoring wrappers call `Authoring.app`.
No map-specific `Term` constructor is required.
`A` and `B` below mean separate `Ty.var` parameters, not Lean function fields.

| Atom | Scheme and result | Runtime operation |
| --- | --- | --- |
| `mapEmpty` | `.mono [] (.map .string .never)` | Empty entry list / empty object |
| `mapGet` | `.poly [map string A, string] (option A)` | Find an own key; return outer `none` or `some value` |
| `mapSet` | `.poly [map string A, string, B] (map string (union A B))` | Insert or replace one key; retain sorted, distinct keys; return a fresh target object |
| `mapKeys` | `.poly [map string A] (list string)` | Return keys in UTF-8 order |
| `mapEntries` | `.poly [map string A] (list (prod string A))` | Return ordered ordinary pairs |
| `mapFromEntries` | `.poly [list (prod string A)] (map string A)` | Read ordinary pairs, canonicalize keys, apply the duplicate rule below |

The empty map's `never` value type is useful polymorphic bottom, like existing `listNil` and `optNone`; it is not a fixed `unknown` map.
`mapSet` needs two variables to support a new value type while retaining old entries.
For example, adding a string to a map of naturals gives a map of `nat | string`.
A fixed-key homogeneous map cannot prove that other entries disappeared, so replacing the only known key still conservatively retains the old value type.

Do not implement that result using `.poly` with one repeated variable and `join := true`.
`Ty.infer` only moves a binding when the prior type is a subtype of the new candidate; it never constructs a union of incomparable candidates.
The two-variable answer explicitly expresses the required union, using the existing calculus.
The target helper should likewise declare `<A, B>(map: Readonly<Record<string, A>>, key: string, value: B): Readonly<Record<string, A | B>>`.

An empty entry list leaves its template value variable unbound; `Ty.instantiate` chooses `never`.
The target helper needs a matching default type parameter, so empty construction does not infer `unknown` accidentally.
Existing list builders can supply homogeneous entries.
The current structural `infer` does not automatically handle unions of differently shaped pairs.
Do not claim unrestricted union inference from the map arm alone.
A mixed map can always be built by successive `mapSet` calls without erasing its value type.

### Presence, order and duplicates

`mapGet` must use own-property presence, as `recordOptional` now does.
Missing, present `undefined`, and present `Option.none()` remain three different answers.
Every string key is admitted, including `__proto__`, `constructor`, empty strings and non-identifier names.
Target construction uses `Object.fromEntries` or an equivalent own-property operation; target update uses spread plus a computed key.
Never use bare `__proto__` object-literal property assignment as construction.

`mapKeys` and `mapEntries` must sort by UTF-8 bytes explicitly on the target.
JavaScript enumeration puts integer-like keys first: `"2"` before `"10"`, whereas this map's order puts `"10"` before `"2"`.
Default JavaScript string sorting also uses UTF-16 units, which differs for `"\uE000"` and `"\u{10000}"`.
Use the same byte-order definition in finite controls, not a locale-dependent comparator.

**Implementation proposal for the coordinator to record:** repeated keys supplied to `mapFromEntries` keep their last value.
The rows fix the output's uniqueness and order but do not state whether an input repeat keeps the first value, keeps the last, or refuses.
Probe R's `Object.fromEntries` recommendation implies **last occurrence wins**.
The coordinator will record this rule under the owner's authorization for the approved implementation.
Concrete discriminator: `[("x", 1), ("x", 2)]` produces `get("x") = some 2`.
This policy does not block `mapEmpty`, `mapGet`, `mapSet`, `mapKeys`, or `mapEntries`.
Do not reuse `Field.canonBy` unchanged: it keeps the first occurrence.

Evaluation remains eager and left-to-right through the existing atom argument list.
Typed inputs always produce a result; malformed raw inputs may return evaluator `none`.
No map miss becomes a typed error or machine frontier.

### Immediate proof consumers

First prove the value helpers needed by these atom cases: lookup membership, sorted insertion with overwrite, ordered extraction, and the entries conversion.
Each uses `EntriesFit` and `sortedEntries`; it feeds both coarse `NativeAtom.Sound` and world-indexed `Typed.AtomFits`.
Use `sound_of_poly` and `atomFits_of_poly` for subsumption and substitution, rather than repeating their arguments per atom.
Nested handles must retain their world-indexed membership, not merely pass `Val.hasTy`.
Add successful-evaluation handle-subset helpers for the existing `nativeAtom_keys` case split.

Controls cover empty maps, insertion at each position, overwrite without duplicates, lookup miss, explicit undefined, and nested options and handles.
They also cover duplicate constructor entries and distinct numeric-looking and non-BMP keys.
A map typed at non-string closed keys remains a formation refusal.
An open key in a row template follows row 193's substitution check, unchanged.

## Slice 2t: tuple authoring and static projection

### Smallest coherent stored forms

Add a variadic native atom `tuple`, with `constGeneric := true` and a `CustomScheme.tuple` rule whose answer is `Ty.normalize (.tuple argumentTypes)`.
Its evaluator returns `Val.list values` at every arity.
Its target prelude is a const-generic rest function returning that same readonly tuple.
This uses the current atom representation and requires no tuple-construction `Term` constructor.

Append only `Term.tupleAt (target : Term) (index : Nat)` for static projection.
A runtime natural argument to an ordinary atom has type `nat`, which does not identify the selected tuple column.
A homogeneous atom signature cannot recover that column.
Authoring is `tuple (items : List TermSrc)` and `tupleAt (target : TermSrc) (index : Nat)`.
The former builds an ordinary named atom application; the latter resolves the target and stores the index.
Neither stores callbacks.

The type rule normalizes the target type and selects a tuple item at its exact index.
It handles `prod` at indices 0 and 1, distributes over unions, and joins the selected columns.
The index must be in bounds for every inhabited union alternative; a list or unknown alternative refuses.
Bottom may answer bottom because it supplies no value.
The evaluator reads the same `Val.list` carrier at that index.
Out-of-range access is a located typing refusal, not an optional lookup operation.

Examples:

- `tuple []` has the empty tuple type, not unit or `list never`.
- `tuple [1]` has a one-item tuple type.
- `tuple [1, "x"]` normalizes to a product; existing product consumers such as `fst` can read it.
- `tuple [1, "x", true]` is a flat three-item value; a nested pair is different.
- At index 1, a union of `[nat, string]` and `[bool, string, nat]` answers string.
- At index 2, that same union refuses because its first alternative is too short.

Const tuple construction retains direct string literal columns, matching the existing `pair` discipline.
The proposal changes no general-position string literal rule.
Normalization affects the checked type, never the stored atom application, child order, or arity.

### Target image and raw reading

Construction prints as the ordinary native call `tuple(a, b, c)`.
The prelude supplies tuple inference; a bare array expression without contextual typing would infer an array and is insufficient.
Keep an old `pair(a, b)` and a new `tuple(a, b)` as distinct stored applications even though their checked types and values agree.

Projection prints as `target[index]` using `Expr.index` with a nonnegative `Expr.int`.
The existing record reader accepts only string keys, so the two access forms are structurally disjoint.
Retain every raw natural index, including an out-of-range one, in the structural read/write laws.
Do not add a typing or bounds premise to `readTerm_printTerm`.
The scope premise stays exactly as it is today.

No new type metadata is needed for these recommended tuple forms: construction retains its children as ordinary atom arguments, and projection retains the natural index.
Structural Lean `Expr.int` is unbounded; a JavaScript source parser is not.
The foreign source reader must refuse a numerically inexact index rather than round it.
Arbitrary raw rendered-text reconstruction would require large indices encoded through the existing metadata digits and an explicit raw wrapper.
That extends the source profile; it adds no premise to the structural theorem.

Do not silently broaden row-call conventions in this slice.
`methodArgsRow` currently treats a product as a receiver plus arguments, and `tupleRequestReadable` knows the two-argument `pair` convention.
A three-item tuple returned as one value or passed to a `.call` row works independently of spreading it across a multi-argument host call.
Changing `.tupleCall` to an arbitrary argument vector needs its own request-image contract; it is not a consequence of row 159.

### Immediate proof consumers

Tuple construction uses existing `ItemsFit`, `fits_tuple`, `fits_tuple_pair`, and `fits_normalize`.
Projection needs an exact-arity indexed-membership helper and its union extension.
Feed these into `NativeAtom.Sound`, `Typed.AtomFits`, `evalTerm_hasTy`, `evalTerm_isSome`, the world-indexed term evaluation theorem, and `evalTerm_keys`.
The new term case also reaches scope/weakening, signature congruence, formation/diagnostic traversals, and `ReadLeaf`/`ReadPrint`.
No general substitution library is needed merely to add a term with one child and no binder.

## Slice 2d: the required JSON and Schema faces

Keep this slice explicit after the operations; target type projection is not a JSON codec.

For maps, encode the canonical entry list as a JSON object and decode string-keyed objects into canonical entries.
Refuse duplicate keys in the raw `Json.obj` input: `normJ` sorts but does not erase duplicates, so silently collapsing them would invalidate existing exactness.
This differs intentionally from the recommended program operation `mapFromEntries`, whose input is an ordered collection to be combined.
Host JSON text parsers may already have discarded duplicate keys before this boundary; state that limitation where the host enters.

For tuples, encode and decode JSON arrays at exact arity, including zero and one.
Retain the existing product face at arity two through type normalization.
Extend `layout` recursively so literal widening inside maps and tuple items uses the intended wire layout.
Do not confuse support of a type with representability of every nested value; existing `isCodecValue` remains the stronger boundary.

The Schema image is `Record(String, V)` for maps and `Arrays` with plain fixed elements and no rest for tuples.
Refuse non-string index signatures, optional tuple elements and rest tuples under the current profile.
Read a two-element tuple as `prod` under row 159.
Retain row 179's annotation policy and the existing reserved-handle condition.
Add data-plane laws by extending the existing codec and Schema proofs, with map duplicate and tuple/list-union controls.
Record payloads inside maps depend on the separate record codec landing.
Do not claim that example crosses JSON before it does.

## Dependency order, generation and acceptance

1. Freeze the map operation contract, particularly constructor duplicates, and the tuple signatures above.
2. Land map value helpers and atom cases with their membership, total evaluation, handle-subset proofs and focused target controls.
3. Land tuple atom construction, then append `tupleAt` with its generated companions, typing, diagnostics, proofs and exact structural target image.
4. Land JSON/Schema faces and their existing theorem consumers, coordinating with the record codec work.
5. Add one authored program with runtime map construction, dynamic key lookup, and a three-item tuple result.
   Exercise its checked boundary once the component codecs support it.

Atom additions reach `Machine/Term.lean`'s enum/row/evaluator, `Program/NativeAtom.lean`'s scheme/spec, and the native proof case splits.
`AtomInventory` and `PreludeAtoms` are generated groups in `tools/Effect4Gen/manifest.json`; regenerate them rather than copying lists or prelude code.
Named atom applications do not require new `Term` wire tags.
Tuple projection requires a new tag.
Regenerate `Fold`, the canonical Program codec, reached authoring/fold projections, and reached eff/wire/TS/LCNF mirrors in the coordinator's staged order.
Use the actual diff and manifest to determine downstream groups; the historical Q estimate is not an allowlist.
Run the case census after the changed policy-family matches.
Do not regenerate unrelated families or promote old baselines incidentally.

For each executable slice, check narrow modules, direct consumers, focused Lean controls with axiom queries, and generated-output comparison.
Also check the two TypeScript source walks and the target with pinned tsgo 7.
No full battery or whole-tree sweep is implied by this brief.
Finishing means every new native atom reaches both typing proof families and handle tracing.
The new term reaches every exact reader/printer and core consumer.
Generated artifacts are current.
Boundary support is reported separately until its slice lands.

## Documentation owners to update with the corresponding slice

- `docs/core/api-surface.md` and `README.md`: usable map/tuple builders and examples, when exported.
- `docs/core/semantics.md` and `tools/Tools/SemanticsRegistry.lean`: the placed properties and actual theorem pointers, never copied status prose.
- `docs/core/decisions.md`: only the coordinator's contract freeze or genuine ruling, especially constructor duplicates if not settled elsewhere.
- `docs/core/host-boundary.md`: newly admitted JSON/Schema values and their remaining exclusions, with the codec slice.
- `docs/GENERATED.md` and the traversal census: only changed producers or exemptions, not a general wording pass.
- `docs/STATE.md`: which of operations, target expressions, and boundary codecs is available after each landing.

No production code was changed and no implementation theorem was checked for this brief.
