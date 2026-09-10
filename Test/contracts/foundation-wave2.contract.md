# Foundation Wave 2 contract

Owner-approved 2026-09-09 after the Wave 1/foundation review, base `3709604`.
Decision authority: `docs/DESIGN-ISSUES.md`; representations: `docs/DESIGN-BASIS.md`.
This packet freezes the approved amendments. Implementation receipts carry exact declaration
names, commands and evidence; this file itself is not an implementation or proof receipt.

## Scope and sequence

Finish S0–S6 through the reviewed bounded slices: invocation routing, complete error image,
scope requirements, handler elimination, normalized/literal/subtype/answer-union type algebra,
metadata codecs and shared description consumers, checked scalar replay and resource cleanup.
Keep one stored `Eff`, explicit package tables/allocation, and the existing trust ceiling.
No FFI, stored functions, general CAS publication, whole-machine typing theorem or third
package is required for the bounded foundation checkpoint. Third-package receiver collisions
must be repaired before that package is admitted. A table-aware reference theorem remains a
separately named obligation after protocol stabilization; do not relabel the existing theorem.

S1a-b changes compiler/reference/heads together. S2 follows on their shared surfaces.
S3 local compiler/reference work does not require a general bind law; a neutral-stack law is
decided before any logic layer claims it. S4a, S4b and S4c are separately verified landings,
all authorized by the present ruling. G2's compatibility policy/supplement precedes appends.

## Types

- S2 introduces supported failures only: naturals, text, string pairs, never and supported
  unions, with literal refinements once available. Every failure introduction is checked.
  Append `Err.text` and `Defect.error` together, retain old ordinals, prove conversion recovery
  and cause/failed-exit membership at an explicit allocation table. No `Err.value` escape.
- S1c removes only the Scope requirement from `scoped`, leaving A/E/other requirements and
  body refusal unchanged. Opaque target types need real exported symbols/imports.
- S4a normalizes recursively, with idempotence and value-membership laws, using canonical
  representatives where equality needs them. Changes in inferred types are reported.
  Technical amendment, 2026-09-09: the 13 retained pre-change snapshot probes show that the
  old fiber-snapshot membership inspected the raw list-element type head, making the stated
  deep-normalization law false. Decode the snapshot once and check each represented fiber
  against the element type. Valid empty snapshots satisfy every list element type by empty
  universal membership; malformed snapshots still refuse. Record these membership deltas
  separately from program wire compatibility. This changes no snapshot bytes or allocation.
  Linked rows use one `Row.normalizeTypes` view for signatures, printing, external answer
  preparation and reply validation. The raw table remains the identity/provenance input.
  Accordingly, table-completeness returns the normalized row view. Seven pre-change probes
  witness the otherwise inconsistent unit-call arity and handle-answer preparation.
- S4b appends string-literal `Ty.lit`, with a subtype relation and allocation-parameterized
  membership implication. Literal-preserving pair construction uses const type parameters.
  `prod (lit tag) X` is an error only when X has a supported representation/recovery law.
- S4c changes answer merging only after upper bounds and leastness under the selected
  subtype relation are proved. Successful absent generator answers remain distinct from refusal.
- S3's binder is the first Fail reason, converted once. A first failure with no payload,
  or a predicate miss, retains the original cause. Precise tag sugar follows S4b.

## Target checks

Foreign readers must return one valid verdict each and agree before the inclusion command
classifies admission or refusal. Agreed refusals are visible contract differences; they do
not establish global printed-language inclusion. Both lifts also match the retained printed
oracle up to specified key renumbering. Required-positive and asymmetric/missing/conflicting
negative controls are independent of the implementation.

Native atom names have one enumerable semantic owner. Every accepted native typing lookup
belongs to its exported inventory; consumers and prelude cases cannot silently omit an atom.

T0 queries actual adapter/program types with explicit bindings. Compare both directions for
A, E and full R; compare receiver and request types without assertions that force agreement.
Account for every selected input, diagnostics, optional/rest/overload limits and missing symbols.
Unresolved/accidental-any cases cannot be conformance passes. Known-defect tests may establish
that the tool detects a defect while the conformance command remains nonzero.

Typecheck truth modules, prelude and recorder. Do not describe the mixed rejected typing
corpus as a uniformly valid TypeScript suite. Host results remain finite observations.

## Compatibility

Keep `Test/fixtures/baseline/66ee4657/` unchanged. A supplement records frozen-revision payloads,
field order, byte maps, framing and consumer selection with reproducible provenance.
Reject constructor removal/reorder/reframing and tag reuse. Compare wire/structure, exact old
decoding, admission/types and execution permission separately. Named narrowing/widening in S2/S4
is an explicit policy delta; it does not authorize changing historical bytes or deleting fixtures.
Undeclared execution-permission loss fails. A finite fixture gate is not a universal theorem.

## Host protocol

Host transitions are relational; stronger deterministic laws require fixed determining
decisions. Intermediate state correspondence may include open resources. Terminal cleanup
requires completed-cleanup/ownership premises, not correspondence alone. Preserve state from
failure for finalization. Double close has the selected binding's terminal defect; closure
diagnostics are separate from ordinary use. Late unclaimed acquisitions need adapter cleanup.

Checked replay is incremental over the existing machine. Validate version, session, exact
table, row, request, fiber, token and completion before application. Preflight does not consume;
application must remove the matching guard. Zero fuel and incomplete valid tapes are live
frontiers retaining state/replies. Malformed/stale/duplicate input refuses without mutation.
Use explicit associations between recorder call IDs and replay guards. Stable published IDs
remain a separate decision. Legacy tape migration has provenance, never invented claim fields.

Keep canonical program error projection at the adapter. Saved diagnostics use a bounded,
versioned schema with stated fields/limits, not a lossless-raw-object promise. Preserve selected
reason categories/order; represent or explicitly refuse unsupported cause combinations.
Relate raw host replies, allocation preparation and prepared machine values explicitly.
An acquisition completed by the host but still pending preparation owns a host resource
without a machine allocation yet. Keep that pending ownership explicit; allocation
correspondence applies after preparation. Compensated late acquisitions do not consume
machine allocation indices or excuse leaking the actual physical resource.
Per-row Lean refinement proves the specified model relation; actual JavaScript behavior is
tested under named runtime assumptions. Profile refusal remains outside-profile evidence,
distinct from program errors, defects and pending computation.

## Tooling

Compose existing `Image`/`Canonical` and container traversals in higher-order checking APIs.
Functions and `Expr` remain in tooling/semantics, never stored programs. Source declaration
metadata, ground type data, runtime layout and mono-LCNF each keep their own role and explicit
connection. Pin versions, phases and dependency closure; refuse unsupported extraction.
Constructors/destructors share one layout and preserve nested Option distinctions.

Certificates name exact input-indexed properties and checked theorem statements. Missing laws,
unsupported features, counterexamples and failed automation remain distinguishable. Standard
monadic proof utilities are a bounded, individually audited pilot with a direct-proof fallback;
they do not certify the compiler or host by association. T1 does not block the core repairs.

## Completion

Each slice supplies exact theorem statements/axioms, positive and independent negative controls,
changed identities/verdicts/bytes and reproducible commands on its saved tree. Coordinator
integrates roots/generation and runs the full build and relevant gates under the unchanged
declared-red policy. A ruled decision, generated stamp or compiling finite example does not
replace these obligations.
