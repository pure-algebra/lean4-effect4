# JSON data codec receipt

The public codec statements and premises remain unchanged.
The extension covers records, string maps and exact-arity tuples through one generated type fold.
The host JSON text parser remains outside these Lean laws.

## Base and files

The JSON draft starts from `6df3fbba` and integrates against `0e94b2f4`.
Source: `src/Effect4/Schema/Codec.lean`.
Proofs: `src/Effect4/Laws/Schema/Codec.lean` and `src/Effect4/Laws/Program/Folds/Ty.lean`.
Controls: `Test/Codegen/DataCodec.lean`.
The existing semantics registry, test root and touched boundary documentation reference these definitions.

## Placement

Concept: Exact Codecs & Data Plane Embeddings.
Claims: `decode-encode`, `decode-iff` and `record-codec-layout`; requirements R2 and R3.
`wire_type` retains raw union children for the two raw codec laws.
The object helpers establish distinct names, canonical ordering and exact payload reconstruction.
`positions_exact` retains tuple arity and reconstructs every decoded position.
`decodeRaw_normJ` and `decodeRaw_exact` consume these helpers.
`decode_iff` consumes both raw laws and states the public boundary contract for every type.
The existing canonical-type and codec-admission premises remain on their original statements.
No theorem establishes general inhabitance, arbitrary host serialization, target execution or liveness.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Schema.Codec` passes with 244 jobs.
The final focused batch passes with 310 jobs.
It builds `Test.Codegen.DataCodec`, `Test.Codegen.SchemaGenerationContract`, `Effect4.Schema.Bridge`, `Effect4.Laws.Program.Folds.Ty` and `Effect4.Codegen.Diagnostics`.
The first batch mistakenly names an absent `Laws.Schema.Bridge` module; the corrected command names its actual source owner.

The fixture queries the fold, both raw operations, the raw type projection and the object exactness helper.
It also queries both raw laws and the three public reconstruction laws.
The operational declarations report `[propext]`; the seven proof declarations report `[propext, Quot.sound]`.
No new trust exception is required.

Finite controls cover optional absence, nested options, repeated keys, missing required fields and unknown fields.
They cover non-identifier names, `__proto__`, exact tuple arity, sorted string maps and overlapping union images.
An absent optional unsupported field may encode while structural type support remains false.
These checks supplement the universal laws. They establish no target execution.

## Remaining integration

The coordinator refreshes the reached generated reports and compiled-case policy after the data-language sources integrate.
The host-session correspondence slice remains separate.
No full battery, whole axiom gate, push or merge runs in this slice.
