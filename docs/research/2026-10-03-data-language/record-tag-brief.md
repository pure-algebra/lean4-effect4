# Whole-record tag selection

Base: `9daf8add` on `codex/record-contracts`, followed by the coordinator's checked record integration dependencies.
Authority: decisions row 195 and `record-contract.md`, literal-tag selection.
This slice adds `Decision.recordTag tag`; existing pair-tag selection keeps its meaning and image.

## Contract

Every normalized input alternative is a record with a required `_tag` field whose type is one string literal.
A missing, optional, broad-string, or union-valued discriminant refuses the type rule.
The hit type joins alternatives with the requested literal; the miss type joins the remaining alternatives.
An empty side is `never`; an absent requested tag does not refuse an otherwise valid input column.
Both branches bind the original whole value once.
The decision binds one value on each side and adds no binder to the scrutinee.

At runtime, read `_tag` through the existing named-record lookup.
A matching string selects the hit; every other raw lookup result selects the miss.
Both outcomes return the same original value.
Malformed raw input therefore takes the miss; the checker restricts its input to the fragment above.
The compiler and meanings already delegate selection to `Decision.decide`; no new scheduling instruction is introduced.

## Placement before proof work

1. Concept: Residual Program Typing; required property: a typed decision supplies membership for the selected continuation.
   Claim: helper of registry question `denote-typed`, fundamental property.
   Consumers: coarse `Decision.decide_typed`, world-indexed `Typed.decide_fits`, and the existing select case of M5.
   Reach: successful `Decision.arms`, the literal-tag record fragment, and either `Val.hasTy` or `Fits w` for the original value.
   Limits: no arbitrary string refinement, pair payload change, scheduler progress, or host execution claim.
   Requirement: R3, through M5 and the existing M6/M7 route.
2. Concept: Scope Lifetime & Finalization; required property: a decision cannot invent a handle.
   Claim: helper of `m7-exit-handles-valid`, preservation.
   Consumer: `Decision.decide_bound_keys` in `Laws/Program/Handles/Hooks.lean`.
   Reach: every successful raw record-tag decision; its bound value equals its input.
   Limits: no allocation, resource lifetime extension, or finalizer behavior claim.
   Requirement: R3 and the existing M7 handle result.
3. Concept: Exact Codecs & Data Plane Embeddings; required property: structural target expressions retain the stored decision.
   Claim: helper of the existing printed-module reconstruction question, through `read_print` and `read_exact`.
   Consumers: template argument retraction/exactness, `ReadPrint`, and checked module reading.
   Reach: existing theorem hypotheses and readable domains unchanged; the literal tag and both branch binders are retained.
   Limits: rendered-source parsing and JavaScript execution receive finite controls, not these structural proofs.
   Requirements: R2/R3.
4. Concept: Residual Program Typing; required property: branch scope agrees with typing.
   Claim: helper of `denote-typed`, compatibility.
   Consumer: `Decision.arms_length`, generated authoring lifts, and the existing checker.
   Reach: every successful record-tag arm computation; both extension lengths equal one.
   Limits: no substitution framework or new authoring representation.
   Requirements: R1/R3.

The implementation uses existing record lookup membership, `fits_members`, `fits_ofMembers`, and normalization facts.
It proves only helpers consumed by the obligations above.
Empty branches retain ordinary checker behavior; the slice does not erase their stored program syntax or effects.

## Exact target image

Use `caseTagR(value, "Found", aN => hit, aN => miss)`.
Both callbacks receive the whole record.
The target helper suspends branch construction, tests an own `_tag`, and evaluates only the chosen callback.
Its conditional types use `Extract` and `Exclude` on the required literal-tag record fragment.
No claim extends that narrowing to a broad `_tag: string` or a union inside one discriminant field.

The existing pair tag uses a template string capture, `Arg.str`, and `strHole`.
Keep that route unchanged.
The record tag uses an ordinary expression hole capturing `Arg.expr (Expr.str tag)`.
`readLeaf` distinguishes these captures when reconstructing the two decision constructors.
This avoids changing the reader's context or relying on target expression Boolean equality.
The internal capture-kind helper currently assumes every decision in the structural target image uses a string capture.
Extend it to the actual argument's kind, and obtain the row's required kind from its classifier.
This changes an internal helper conclusion while keeping public reconstruction hypotheses and domains unchanged.
The distinct helper head is registered in the existing head and template tables.

Add independent printed-source controls in both TypeScript walks.
Keep foreign recognition's source profile unchanged unless an existing rule already authorizes the new helper.

## Files and coordination

Owned source: `Program/Decision.lean`, `Program/Record.lean`, `Program/Typing/Blame.lean`, needed decision laws and handle law, `Codegen/Templates.lean`, `PrintLeaf.lean`, `Read.lean`, their directly affected law consumers, TypeScript template/read adapters, and focused tests.
A new proof companion may hold the shared record-tag lemmas if import direction requires it.
Owned runtime helper: the existing record helper module and its focused runtime/type controls.
The coordinator owns generated files, manifest, wire tags, binder metadata, root imports, semantics registry entries, and decisions.
`Machine/Term.lean`, native atom files, and map implementation remain outside this seat's edits.

Before dependent builds, request generated `Decision` codec and binder companions from the coordinator.
No new `Eff` or `Term` constructor is added by this slice.
Source stages are reported explicitly before their generated consumers are checked.

## Verification

Done means the core type rule and runtime decision agree on both branch binders; existing theorem premises remain unchanged.
Narrow checks cover decision laws, world membership, handles, structural target reading, and their direct consumers.
Axiom queries remain at `[propext, Quot.sound]` or below.
Finite controls cover hit, miss, absent requested tag, all-hit and empty columns, invalid discriminants, raw decision retention, and nested handles.
Target controls check whole-object identity, own-property testing, one scrutinee evaluation, deferred callbacks, and exact branch types with pinned tsgo 7.
No full sweep or push is part of this slice.
