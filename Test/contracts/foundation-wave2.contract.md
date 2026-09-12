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

### T-09 / T-12 amendment (owner ruled 2026-09-10)

The protocol is a first-order transition datum with phases idle, awaitingAsync, parked,
and terminated. Its projections provide the Lean session transition check, the TypeScript
adapter table, and the versioned tape record schema. Scheduler controls remain explicit.

Outstanding associations use `(fiber, token)` keys. Call IDs increase when calls bind;
they do not constrain reply arrival. A reply is checked and stored without executing the
machine. A separate keyed application record selects the stored completion to execute.
`reply_commute` states equality after receiving two valid replies for distinct keys in
opposite orders, under unchanged execution state. It makes no claim that resumed programs
with shared effects commute. Per-key duplicate, stale, and malformed replies refuse;
zero fuel retains the pending reply. Cancellation retains unapplied payloads for cleanup.

The older single-fiber oracle tapes remain explicitly legacy evidence. They are not
silently interpreted as version 2 tapes. New multi-fiber comparisons check the recorded
key, row, request, completion, and application sequence against checked Lean replay.

### Result ergonomics amendment (owner ruled 2026-09-10)

`Ty.result value error` abbreviates the existing `Ty.except error value`; no constructor,
ordinal, or stored type is renamed. The target remains `Result.Result<A, E>`. Membership
uses the existing `Image.except` representation: `.ctor 0 [error]` and `.ctor 1 [value]`,
with recursive typing and the caller's allocation table. Wrong branch payloads, tags and
arities refuse. Normalization, subtyping and allocation-extension laws apply to both arms.
`Ty.schema` is not yet implemented; its future Result reflection keeps the already-ratified
value/error order, without adding a second type constructor here.

### Formal foundations amendment (owner ruled 2026-09-11)

Rows DI-15, DI-17, DI-23, DI-39, DI-55, DI-57, DI-58 amended and DI-67 to DI-71 added;
map ticket T-13; the packet is `docs/research/2026-09-11-eff-formal-foundations-implementation.md`
(untracked working note).

**Type identity.** Two types are the same type when each is a subtype of the other. `Ty.sub`
is a proved preorder. Union normalization drops a narrower member beside a wider one
(`Row.antichain sub`) and distributes `prod` over `union` on either side, so a normal form has
no union under a `prod` head; nothing distributes under `list`. On canonical types mutual
subtyping is equality and `join` is the least upper bound. Every store key, schema document,
codec law and printed type is taken of the canonical form. Answer joining is the least upper
bound. A string literal types as `string` in general position and as `lit` as an argument of
`pair`. The printed face of a tag-set column becomes a union of tuples. `sub` stays sound for
membership and deliberately incomplete against value containment beyond these rules.

**P2a resumption amendment (owner ruled 2026-09-11).** Distribution lives only in
`normalize`. Keep the existing `Ty.sub` and `sub_union_right` definitions and
statement unchanged. Delete `sub_prod_union_left`, `sub_prod_union_right` and
`sub_normalize` from the obligations. State `sub_antisymm_canonical`,
`sub_join_left`, `sub_join_right` and `join_least` on `CTy`. Attempt the one-way
normalization law `sub a b = true → sub a.normalize b.normalize = true`; if false,
retain its counterexample and define the public order on canonical types.
The raw relation remains the structural preorder; canonical identity and the
join laws concern the canonical representatives.

The owner approved the necessary helper statement amendments: add maximality to
`normalize_ofMembers_fixed`, and use the sorted antichain in `join_eq_ofMembers`
and `members_join`. The retained witness is `[string, lit "A"]`: both members are
sorted and individually fixed, but their union normalizes to `string`.

Rename the structural error-support predicate `rawSupportedErrTy` and define
`supportedErrTy t := rawSupportedErrTy t.normalize`. Its normalization invariance
follows from `normalize_idem`; demonstrate that `admittedErrTy` is unchanged.
No answer-joining, literal-synthesis or residual changes belong to P2a.

**Tag residual.** The tag test is the native atom `tagIs`, true only on a pair whose first
component is the tag, printed through the prelude. A `catchIf` whose test is that atom types
its error column as the residual joined with the handler's error; any other test keeps the
join. The residual is a fidelity claim to the printed type; its adequacy statement carries the
single-`Fail` premise, and the two-`Fail` miss is a filed counterexample. The first-`Fail`
elimination rule is unchanged.

**Inhabitation.** Every admitted type either normalizes to `never` or has a value under some
allocation table. Under the P2a resumption amendment, `Ty.int` keeps its ordinal and
is refused only at program/table admission with `AdmitRefusal.uninhabited (at : Path)`.
Keep `Ty.ofSchema` and both schema retraction theorems unchanged. A foreign integer
schema parses, and a program using its type is refused at admission with its path.
Canonicality alone does not certify admission. The value alphabet is not extended.

**One run route.** Host answers reach a program only through the keyed session. The
preloaded answer list is deleted after the legacy truth programs run through the session on
version-2 tapes, never before. A refused reply is `submit`'s verdict with the session
unchanged; there is no refused outcome. The agreement target is `session_eq_ref` over a
well-formed tape, with `run_eq_ref` as its empty-table corollary.

**Frontier reasons** (amended 2026-09-11 after the P2b probe). One generated family: command
fuel, compile fuel by fiber, a host call by key, a timer by fiber and wake time, a scheduling
decision. No await-fiber reason. The reasons are observed into a `reasons` field of the run
result from the driver's exhaustion tag (fuel or tape) and the final machine; the outcome type
and the existing agreement theorem keep their statements, and reasons agreement with the
reference is a separately named lemma. The reference's pending-reason type is renamed and
projects to this alphabet. Compile fuel is a separate budget, added with a default. Laws
(corrected 2026-09-12 by the P2b preflight): fuel monotonicity of a finished replay with
compile fuel pinned; the observation laws stated against the predicates the protocol observer
reads, with its host-await priority explicit — awaiting-async iff a host reason is present,
terminated iff no host reason and every fiber has exited, idle iff no host reason and some
fiber is runnable, the decision reason present iff the tag is tape and some fiber is
runnable, and under those two, idle iff the decision reason — never equating terminated with
a finished run without a driver-completion premise; guard persistence for every decision that
is not the key's reply, up to the key's fiber being interrupted or exited, with equality as
the one-fiber corollary; tape completeness as the absence of host and decision reasons.

**Guard reachability amendment (owner approved 2026-09-12).** Both guard laws
start from a machine reachable from `Api.load` by the same program/table
interpreter over an explicit prefix of decisions. The starting program, table,
compile budget, choices and oracle answers are fixed; each prefix step has its
explicit command budget. Every raw decision other than the matching-key reply
remains in scope, including decisions the host protocol does not admit. Prove
the ownership invariant excluding timer, deferred and dispatcher resumes at an
outstanding external key. An arbitrary manually injected timer can reuse that
key, so the unqualified arbitrary-machine law is false; the checked witness and
owner approval are retained in the P2b receipt. The one-fiber equality has this
same reachable scope and excludes cancellations and matching-key replies.
`Interrupted f` remains `interruptPending f = true ∨ f.exit.isSome`.

**Evaluate repair** (owner ruled 2026-09-12). Only a reply or an interruption removes a
guard. A bare evaluate decision on a fiber parked with a guard is a no-op, as it already is
for a running or exited fiber, and the evaluate arm's park-clearing assignment goes. Every
legitimate resume unparks first, and the runtime has no bare evaluate on a suspended fiber.
Regression: the truth gate, the keyed host gate, and a negative fixture in which a bare
evaluate leaves the outstanding request and token unchanged and the later reply is accepted.

The owner approved the two resulting helper amendments on 2026-09-12:
`drive_evaluate_enters` and `driveState_evaluate_enters` require the explicit
premise `f.parked = Parked.notParked`, with the corresponding runtime-coverage
statement check updated. A guarded fiber satisfies the old non-running and
non-exited premises but does not enter evaluation under the repaired driver.

**Row table meaning.** The row table means the algebra package's `Family` through
`Alphabet.toFamily`, and its signature through `toSignature`; the denotation extends to
straight-line programs with external rows on one fiber; a tape is a partial handler whose
missing answer is the host frontier. Fork and scope remain the reference machine's.

**Layer identity.** A layer's identity is its position, with sharing explicit through
`LayerTerm.ref` and unsharing through `LayerTerm.fresh`, as the runtime keys its memo map on
the layer object. Content-addressed layer identity is rejected. Owed: the provide-twice law
over references, the fresh-never-shares law, and agreement of typing by expansion with
compilation by redirect.

**Admission and printing.** Admission certifies that a program can run: unique row keys, no
collision with a built-in, no trailing names on a value row, from `Program/Table.lean`.
Printing certifies that it can print: reserved heads and the binder byte are the printer's
refusal. Admission does not import the reader.

**Generators.** `tools/Effect4Gen` hosts every generator that writes into `src/` or `Test/`;
the seven-family `cata_eq_rec` and the frontier parameter come from the Fold group, not by
hand.


**Fresh map scope** (owner ruled 2026-09-12). `fresh_never_shares` covers
lookups and memo operations routed through the fresh map and its isolated
descendants. Their lookups remain inside that region and their writes leave
enclosing maps unchanged. Independently invoked nested program-level
`provideLayer` operations may select an ambient memo map and are outside this
claim. The checked counterexample and approval are retained in the P2b receipt;
`freshThen`, the compiler, and rc.112 behavior remain unchanged.
