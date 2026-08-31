# Effect Core v1 — breaker contract packet

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

Role: BREAKER specification; no implementation, test, or proof is included

Claim gate: none

Depends on: `PLAN.md`, `ALGEBRA.md`, `CLASSIFICATION.md`

`EXHIBITS-REVIEW.md` fixes the adopted/rejected scope of the kernel-checked
scratch exhibits. `TYPE-CLOSURE.md` owns the per-type proof graph and cutover
predicate. Neither file is implementation evidence for a pending clause here.

Every contract row is explicitly **PROPOSED**. A contract proof, falsifier, or
harness remains **PENDING** unless its row says otherwise. Supporting
counterexamples may already be kernel-checked; their authoritative evidence
state and exact command live in `COUNTEREXAMPLES.md`. This packet is not itself
an implementation or proof artifact.

The evidence-backed §17 rulings freeze conditions 10, 11, 15, 16, 18, 19,
20, and only the classifier half of condition 17 as constraints on a later
Pass B signature. Condition 14 remains open pending a neutral protocol
operation identity and its admission bridge to `Sig.Op`; renderer injectivity,
the second half of condition 17, also remains open. No ruling changes a
PENDING proof, falsifier, or harness into evidence.

## CATEGORIES

| Category | Proposed degree | Boundary |
| --- | --- | --- |
| Domain | total on `CheckedProgram`; diagnostic on `RawProgram` | Only the closed alphabet version is admitted. |
| Contract | total for checker, reference step, finite runner, classifier, lowering, and renderer | Foreign host behavior remains conditional on its registered contract. |
| Adequacy | two-way for raw checker and the three semantic faces; one-way at external tool boundaries until separately proved | TypeScript/Effect diagnostics are evidence, not meaning. |
| Invariant | inductive over every reference-machine step | Types, regions, ownership, handlers, resources, and frames. |
| Termination | structural for checker/pure evaluator/renderer; fuel-bounded for runner; certificate-dependent for programs | Infinite behavior is represented by coherent finite prefixes. |
| Frame | explicit per checker, block, handler, scope, fiber, foreign atom, and CAS embedding | An unknown frame is top, never empty. |
| Abstraction | sound upper bounds required for every classifier dimension; lower-bound completeness only when marked exact | May/must and precision are retained. |
| Conformance | generated target IR is a proof subject; TypeScript, Effect tsgo, compiler, engine, and host are separate evidence layers | No “verified TypeScript” shorthand. |
| Public closure | total over the recursively resolved pinned rc.112 package surface | Every public module, exposure, member, and overload has exactly one disposition before proof completion. |
| Claim scope | G0–G6 individually | Later evidence never silently promotes earlier claims. |

## REQUIRES

### `EC1-K01` — authority and versioning

Status: **PROPOSED CONTRACT CLAUSE**.

1. Decision 9 remains the v0 ruling for wild-source ingestion.
2. Effect Core v1 is a separately versioned authored language.
3. The selected operation alphabet and direct-handler policy are settled
   premises for this packet.
4. CAS law and canonical `PProg` identity remain unchanged.
5. Ratification and promotion are separate operator acts.

### `EC1-K02` — admitted input

Status: **PROPOSED CONTRACT CLAUSE**.

The checker accepts a `RawProgram` only when all identifiers, types, rows,
regions, resumptions, handlers, fibers, resources, foreign entries, exits, and
presentation references satisfy `ProgramWF`. No host function, unregistered
operation, open effect row, or unchecked object enters `CheckedProgram`.
Each block's sequential body is the existing `PProg`; the graph adds typed
parameters, region, and one terminator. A second line/table carrier is rejected.

Quantification is over:

- every raw program over the selected format version;
- every checked graph over the selected alphabet version;
- every typed initial value and admitted initial world;
- every direct handler environment satisfying its interface;
- every finite typed decision tape compatible with the scheduler policy/state
  in the initial configuration;
- every relationally admitted answer and scheduler-enabled choice path;
- every approximation depth and observation mask; and
- every generated target whose foreign and pure atoms have the named pins.

The selected public-source universe is not the authored operation alphabet.
The checker consumes a frozen `PublicSurface` ledger produced by recursive
package-exports and TypeScript symbol/overload closure. Every public row must
map exactly once to the smaller `Alphabet` or to an explicit non-Core boundary.

`ValueTy` restricts/extends the shipped `Cas.Schema.El` value interpretation:
every overlapping inhabited structural code has an explicit equivalence to
`El`, while `El`'s parked/refused empty arms and new effect-specific handles are
listed as insufficiencies with separate proof rows. `Alphabet` is metadata
indexed by an existing `Cas.Lang.Sig.Op` and proves its answer-code agreement
with `Sig.Ans`; it does not replace or modify `Sig`. Semantic-family extension
uses existing `Sig.sum`, preserving the separate `CasSig`, `RootSig`/`StoreSig`,
and `WordSig`/`WordedSig` packages and their non-disturbance laws.

That indexing is only the current Lean-side candidate. Freeze condition 14
remains open until a neutral protocol operation identity and an explicit
admission bridge to existing `Sig.Op`/`Sig.Ans` are specified for Lean-modeled
operations. Host-obligation identities must remain representable without being
misclassified as already admitted Lean operations.

### `EC1-K03` — pure boundary

Status: **PROPOSED CONTRACT CLAUSE**.

Pure calculations are `PureExpr` or modeled `PureAtom` values outside `Flow`.
Graph edges reference pure argument maps. A pure atom is total and
world-independent. Anything ambient, partial through host exceptions, mutable,
asynchronous, random, timed, or capability-bearing is an effect operation.

### `EC1-K04` — direct handler completeness

Status: **PROPOSED CONTRACT CLAUSE**.

For every reachable `perform op`, exactly one direct clause is selected by its
explicit `handlerRoute`: builtin routes use the closed builtin table and
service routes use `HandlerEnv`. The operation's independent, possibly-empty
`requirementRow` determines static `R`. Explicit named parent delegation is
permitted and cycle-checked. Runtime handler search, type-based ambiguity, and
implicit fallthrough are absent.

Graph-backed clauses elaborate to existing `Cas.Lang.Handler` values in an
adequate state/error/machine target that can observe child success and failure
before recovery or cleanup. Named children are `BlockId`s. A scoped handler
targets that adequate machine directly. `Handler.sum` combines signature
families sharing one target; `Handler.through` applies only when an upper
handler has target `Prog T` and is followed by a lower `Handler T M`. No
higher-order handler carrier is admitted. `ReaderT Env (Prog CasSig)` is
explicitly inadequate by
`no_handler_into_ScopeM_catches`. `scopeHandlerR` witnesses catch recovery only
and is inadequate for ensuring because failure discards the word. The frozen
information contract requires state to survive failure; the minimum CAS witness
is `ReaderT Env (ExceptT Refusal (StateT Word Id))`. The scratch exhibit's
`scopeHandler`, `scopeHandlerR`, `scopeHandlerW`, and helper carriers are not
promoted and establish none of this packet's adopted catch, ensuring, scope,
provision, ownership, failure, or finalization semantics.

### `EC1-K05` — observation declaration

Status: **PROPOSED CONTRACT CLAUSE**.

Every equivalence, preservation, refinement, replay, or conformance statement
names an `ObservationMask`. The default full mask contains result/cause, world
projection, public events, resource and fiber lifecycle, foreign receipts, and
daemon obligations. Dropping any component is an explicit quotient.

### `EC1-K06` — external tooling identity

Status: **PROPOSED CONTRACT CLAUSE**.

Any source acceptance result records exact:

- generated bytes and expected `TsCore` identity;
- TypeScript version and configuration;
- `@effect/tsgo` version, patch identity, plugin configuration, and diagnostic
  severities;
- code-action identifiers and formatter/canonicalization configuration; and
- structural-decoder version.

It also records the matching platform package
`@effect/tsgo-<os>-<arch>@0.38.0` (locally
`@effect/tsgo-darwin-arm64@0.38.0`), its integrity and binary hash, the complete
platform `upstream.json` digest, TypeScript `7.0.2` git head
`2bd066d87f5bafd315be9f40889d0a60b9e58e0b`, the equality between that head
and the selected upstream entry, successful `effect-tsgo patch --typescript
--oxlint` receipt, Node/Bun/OS/architecture, complete plugin/rule
configuration, diagnostic and code-action catalog digests, and every generated
input hash.

The record additionally includes the `@effect/tsgo` npm integrity, lockfile
row, resolved path, CLI `--version`, package hash, TypeScript npm integrity,
Effect peer/dependency range and actually resolved Effect version, the exact
expected and reported file sets, and normalized diagnostics, suggestions,
quick fixes, refactors, completions/quick-information probes, and output-edit
hashes. Diagnostic/action JSON is sorted by file, span, rule, action kind, and
edit digest.

The required TS7 successor route is the repository's exact
`typescript@7.0.2` plus `@effect/tsgo@0.38.0`, configured with plugin name
`@effect/language-service`. The old standalone language-service package and
repository are prior-art only for this route. A source/provenance pin for the
successor tool is still PENDING if not resolved in the source lock.

The machine-readable run is exactly:

```text
bun run --cwd experiments/effect-core-surface typecheck
```

The package script fixes `effect-tsgo diagnostics --project tsconfig.json
--format json --strict --list-files` and runs with the experiment directory as
the tool working directory, so the pinned local TypeScript installation is
discoverable. The dedicated tsconfig is a frozen handwritten harness input.
The diagnostic payload must be valid JSON with zero stderr except declared Bun
progress output and exact fields
`diagnostics`, `files`, and `summary`; report
`summary.filesChecked = summary.totalFiles`; list exactly the source set
independently resolved from that tsconfig; and mark every file
`detectedEffect: "v4"` and `supportedEffect: "v4"`. Empty diagnostics with one
missing or extra file are rejection. The current 43/43 library run is a witness
that this route executes, not the future generated-project baseline.

The independent public export/type census runs first and owns symbol identity.
Every Effect symbol named by a diagnostic/action and every import inserted by a
fix must resolve through that census and the package exports map. Two fresh
runs must produce byte-identical normalized JSON. No message-text baseline,
blanket rule disable, or standalone legacy language-service package can satisfy
this clause.

### `EC1-K07` — public-surface and disposition closure

Status: **PROPOSED CONTRACT CLAUSE**.

For pinned `effect@4.0.0-rc.112`, recursive package-export closure defines
every public module, declaration-space exposure, namespace/class/interface
member, and call/construct/index overload. Alias exposures collapse to one
canonical declaration without disappearing. Every row receives exactly one of:

```text
reifiedPrimitive | derivedExpansion | separateSubcalculus
pureOrHostOnlyClosedOutsideProg | projectOwnedReplacementOrForeignOp
targetOnly | excludedInternal
```

No public exposure may be `excludedInternal`. Every effect-bearing row names an
overload-derived `A/E/R` transform, semantic family, constructive mapping,
direct handler or explicit non-Core boundary, observation, and obligation set.
The two deep MultipartParser modules named in `REIFICATION-CHECKLIST.md` must
appear. Closure is permitted while proof statuses remain pending; unresolved,
unclassified, multiply classified, or handlerless effect-bearing rows are not.

### `EC1-K08` — Effect-aware diagnostics and action boundary

Status: **PROPOSED CONTRACT CLAUSE**.

The Effect-aware leg checks its recognized source patterns, including floating
or nested Effect values, missing service requirements, generator yield/return
shape, Effect.fn/map/flatMap/pipe/catch/provide/Layer patterns, unsafe Effect
assertions, raw promises and async functions, try/catch in generators, forbidden
host globals, duplicate Effect packages, and configured canonical refactors.
The dedicated harness enables diagnostics, refactors, quick information,
completions, and code actions. Its recognized host-global controls include
console, date/time, fetch, randomness, timers, `process.env`, abort
controllers, and configured Node builtins; it also covers outdated API forms,
deterministic service keys, service-class shapes, and Schema/Effect source
patterns.
It cannot establish package/symbol/overload closure, canonical source identity,
ledger disposition completeness, `A/E/R` preservation, handler laws, runtime
agreement, compilation preservation, or hosted behavior.

Every positive generated program must parse, typecheck, appear in the exact
`--list-files` set, report Effect v4 support, and have zero unapproved errors,
warnings, or messages. Suggestions are captured even when they do not affect
exit status. An exception is keyed by stable rule code, canonical fixture and
symbol, reason, and expiry pin.

For each admitted action, the harness:

1. starts from canonical fixture bytes and the exact expected diagnostic/action
   set;
2. selects by `(ruleCode, actionKind, targetSpan, descriptionKey)`, never array
   position;
3. applies edits with overlap and ordering checks;
4. parses and typechecks the result;
5. resolves every inserted import through `PublicSurface`;
6. structurally decodes the result and compares the declared pre/post target or
   semantic relation;
7. rerenders canonically;
8. reruns diagnostics and requires the trigger gone with no new unapproved
   result; and
9. repeats the action pipeline and requires zero edits and byte-identical
   output.

A style-only fix must decode to the identical IR. An explicitly semantic fix
names both expected IRs and the intended translation; offering the action does
not by itself establish preservation.

The red battery includes a floating Effect, an Effect executed inside another
Effect, raw promise/async boundaries, generator yield/return/try-catch misuse,
a missing service, unsafe assertion, noncanonical map/flatMap/Effect.fn shape,
Layer dependency defect, forbidden host global, duplicate Effect package,
invalid inserted import, overlapping edits, non-parsing fix, style fix that
changes the decoded target, non-idempotent fix, tool/config/catalog drift, and
both missing-file and extra-file coverage mutations. Each mutant must be caught
by the intended Effect-aware leg; a failure observed only by ordinary
TypeScript or only by the export census does not prove that leg is live.

### `EC1-K09` — per-type proof closure and cutover

Status: **PROPOSED CONTRACT CLAUSE**.

Every relevant existing or proposed type resolves through one annotation in
`EXISTING-TYPES.md` and one generated proof-closure row in the organization
lane. The row has separately checkable constructor, checker/admission,
semantics, classifier, lowering/bridge, and red-control edges. A slice may cut
over an individual type only when all of its required edges are closed. No
packet-wide or implementation-wide cutover is permitted while any required
type row has an open edge.

## ENSURES

### `EC1-K10` — raw/checked adequacy

Status: **PROPOSED CONTRACT CLAUSE**.

Requested equations:

```text
check raw = ok checked        -> ProgramWF raw
check raw = error diagnostic  -> not ProgramWF raw
ProgramWF raw                 -> exists checked, check raw = ok checked
erase checked                 = normalizeRaw (erase checked)
check (erase checked)         = ok (normalizeChecked checked)
```

The second and third equations require a complete decidable `ProgramWF`; if a
future clause is intentionally semantic or undecidable, the contract must be
regraded rather than quietly weakening “error iff invalid.” Diagnostics do not
participate in checked equality.

The checker is fail-fast in one frozen table/clause order. On invalid input it
returns the least condemning clause in that order and proves that clause holds;
it does not claim to report every independently condemning clause. Checked row
normalization is canonical only under duplicate-free keys (or a stronger
checked-row premise). Raw duplicate-key permutations are diagnostics, not a
normalization equivalence.

### `EC1-K11` — type safety and exact static projection

Status: **PROPOSED CONTRACT CLAUSE**.

For `p : CheckedProgram A E R`:

1. every normal exit contains `Value A`;
2. every typed escaping failure is one alternative of `E`;
3. every reached service operation is supplied internally or appears in `R`;
4. defects and interruption remain in `CauseTree E` and do not alter `E`;
5. every reference-machine step preserves program, value, region, fiber,
   handler, and resource well-formedness; and
6. generated target typing exposes exactly normalized
   `Effect.Effect<A,E,R>` for the modeled target IR.

“Exact” here means exact for the checked static judgment, not that every error
or service in a row occurs on every runtime path.
Each source-facing rule is derived from one canonical public overload row.
Builtin handler routing contributes an empty requirement row. Recovery may
union the original and handler result types and retains the unhandled portion
of `E`; service provision applies the overload's normalized `Exclude`/row
difference rather than a handwritten approximation.

### `EC1-K12` — first-order closure

Status: **PROPOSED CONTRACT CLAUSE**.

Every stored continuation, handler body, finalizer, child body, error arm, and
race arm is a `CodeId` plus explicit captures. The serialization walk finds no
function-valued field. Every free value of a source lambda admitted by the
bridge is named in the target block's parameter list. Alpha-renaming code and
block IDs changes no denotation after normalization.

### `EC1-K13` — flow algebra

Status: **PROPOSED CONTRACT CLAUSE**.

Under the full observation mask unless otherwise stated:

```text
seq (close x) k                   ~= instantiate k x
seq p close                       ~= p
seq (seq p k) h                   ~= seq p (seqCont k h)
mapArgs identity p                ~= p
mapArgs (g compose f) p           ~= mapArgs g (mapArgs f p)
catch (close x) h                 ~= injectResultUnion (close x)
catch (raise e) h                 ~= selectedArm h e
ensure p f                        runs f after every registered exit of p
provide H p                       restores the parent HandlerEnv on every exit
feedback body                     ~= one guarded unfold of body
```

`~=` is `ObservationMask`-indexed denotational equality. No unconditional law
states that `par`, `race`, causes, finalizer lists, or traces are commutative.
`ensure p f` is a machine exit rule, not `Prog.bind p (fun _ => f)`: existing
bind interpretation is refusal-strict and does not run `f` after a refusal.

### `EC1-K14` — executable/relational/finite agreement

Status: **PROPOSED CONTRACT CLAUSE**.

For every checked initial configuration:

1. `execStep` with a valid decision produces exactly one corresponding `Step`;
2. every `Step` is reproduced by some valid decision;
3. `execN` yields the same normalized prefix as following those `n` relational
   decisions;
4. the derived `approx n c : FinApprox n c` contains exactly the depth-`n`
   observations admitted by the `Runs` relation;
5. truncating a deeper approximation yields the shallower approximation; and
6. `Denotes p i tr c' : Prop` is exactly `Runs` from `initialConfig p i`, not
   a public behavior, denotation, or coherent-family carrier.

External answer frontiers remain symbolic, so this does not require an
infinite answer type to be enumerated.

The deterministic `Denotes` and big-step coherence exhibit discharges only
stable non-frontier outcomes in the named CAS/block subfragment. It does not
equate fuel-exhausted prefixes or their incidental refusal labels before the
stable result. No clause above asserts global uniqueness of the full-core
relation. `execN` is deterministic only after the complete initial
configuration—including scheduler policy/state—and one compatible decision
tape are fixed; `Runs` retains every admitted answer and scheduler-enabled
choice, and `FinApprox` is only derived observation data.

For a selected deterministic unfolding, coherence is proved at the big-step
`interpretRef`/handler-interpretation face. Fixed-fuel `run` has no general bind
law and is connected separately by one-step and fuel adequacy; it cannot justify
the composition/coherence equation.

### `EC1-K15` — divergence discipline

Status: **PROPOSED CONTRACT CLAUSE**.

There is no `diverge` syntax constructor. A fixed execution diverges when every
finite execution prefix is live and can extend. Relational may-divergence
requires an infinite compatible chain; must-divergence quantifies over every
maximal admitted decision path. Fuel exhaustion is reported only as `running`.
Fuel exhaustion, an external-answer frontier, and a scheduler-choice frontier
are live control states. None is a typed error, `CauseTree`, or CAS `Refusal`.

### `EC1-K16` — direct handler laws

Status: **PROPOSED CONTRACT CLAUSE**.

1. direct lookup is unique and stable inside a region;
2. `provide` affects only its named service keys and restores the parent map;
3. handler clauses receive typed requests and return typed `Exit` values;
4. the machine, not the handler, owns and consumes the one-shot resume;
5. a handler's world changes are within its declared frame;
6. handler clauses represented as core graphs satisfy the same semantics and
   classification contracts recursively; and
7. interpreting sequential composition agrees with sequentially composing
   the interpretations under the same handler environment.

### `EC1-K17` — failure and cause laws

Status: **PROPOSED CONTRACT CLAUSE**.

Typed `catch` observes only selected `CauseTree.fail` leaves. Defects,
interruptions, and unhandled typed leaves propagate unless a cause handler
explicitly selects them. A finalizer failure after a body failure produces
ordered `CauseTree.then body finalizer`. Concurrent child failures produce
ordered `CauseTree.both` in canonical child order. Full model normalization may
not erase the distinction between sequential and parallel nodes.

The stock rc.112 bridge uses the separately named `quotientCause` map into its
flat, stably de-duplicated `Cause.reasons` representation. Under that quotient,
`then x y` and `both x y` may become equal and repeated equal reasons may
collapse. A G4 claim against unmodified rc.112 therefore cannot observe full
tree topology. A full-topology runtime claim requires a separately classified
project-owned adapter and its own trace/conformance evidence.

### `EC1-K18` — scope/resource laws

Status: **PROPOSED CONTRACT CLAUSE**.

For every registered resource:

1. acquisition precedes registration;
2. registration is atomic with respect to interruption delivery;
3. after registration, exactly one release begins on every scope exit;
4. releases run in reverse registration order;
5. the parent cannot leave the scope before releases and owned scoped children
   halt;
6. release observes the resource value acquired by the same registration;
7. no resource token occurs in an outer-region value or daemon capture; and
8. release effects and failures remain visible in classification and
   observations.

If acquisition fails before registration, zero releases run. If a release
diverges, the scope may remain finalizing indefinitely; the contract does not
invent successful cleanup.

### `EC1-K19` — fiber and cancellation laws

Status: **PROPOSED CONTRACT CLAUSE**.

1. every fiber has exactly one owner until ownership is explicitly transferred;
2. scoped fibers are joined or interrupted and finalized before owner exit;
3. `await` succeeds with the child's complete `Exit`, while `join` returns a
   success value or propagates the child's complete failure cause;
4. interruption request sets a persistent pending flag; public
   interruption-and-await resumes only after the target halts following
   cleanup;
5. a mask delays delivery but never clears the flag;
6. unmasking at an interruptible boundary delivers the pending interruption;
7. race starts every declared child, selects one scheduler-enabled first exit
   through the typed `DecisionTape`, interrupts all losers, awaits their finalization, and
   only then resumes the parent;
8. fixed initial configuration, including scheduler policy/state, plus one
   compatible decision tape gives deterministic replay;
9. safety laws require no fairness; and
10. liveness laws name their fairness and handler-progress hypotheses.

### `EC1-K20` — foreign atom laws

Status: **PROPOSED CONTRACT CLAUSE**.

A checked foreign operation has a registry row with request/answer/error types,
requirements, capabilities, world frame, direct model, receipt codec, replay
key, host identity, and observation policy. Modeled execution changes only its
declared frame. Receipt replay is deterministic for the same initial declared
frame and request. A runtime-host agreement statement is conditional on the
pin, codec, and conformance evidence and never follows from registration alone.

### `EC1-K21` — classification soundness

Status: **PROPOSED CONTRACT CLAUSE**.

For every checked graph and every admitted `Denotes` witness, each concrete
semantic fact lies between the classifier's lower and upper bound in its own domain.
Every transfer function is monotone. Every cross-domain reduction preserves
the product concretization. “Exact” is permitted only when lower and upper
bounds coincide by proof.

The complete `ClassProduct` is not required to be invariant under `SemEq`.
Structural dependence/dataflow can differ between programs with the same
selected runtime observations. For an `ObservationMask O`, only the fields
declared observable by `O` owe equal concrete projections; soundness requires
that shared projection to lie in both corresponding concretizations. Every
stronger field-specific invariance theorem names the field and its premises.

### `EC1-K22` — CAS preservation

Status: **PROPOSED CONTRACT CLAUSE**.

For every raw `PProg p`, `admitCas` succeeds exactly when `CasAdmissible p`.
Empty tables, dangling answer indices, or any table lacking a typed Core entry
are rejected without changing their existing raw `runP` behavior. For every
`p : CheckedPProg`, injection checks, projection is a left inverse to `p.val`,
the reference run produces the same status and word, the classifier refines
the existing envelope without weakening its two recorded over-approximation
gaps, and canonical serialization uses the existing CAS content identity. A
new core encoding must not become a competing canonical spelling.

Here “projection” is restricted to `CasImage`, the canonical normalized image
of injection. General `toPProg` is only a partial, sound normal-form recognizer:
if it answers, the graph has the recognized injected form. It may return
`none` on an observationally equal graph with an unreachable tail or relocated
entry. No theorem treats it as a denotational projection from every CAS-only
graph.

CAS refusal-kind classification reuses the complete existing
`Refusal.Clause` and `RefusalMap` family: model-side and host-side totality,
the declared host-only row, host-image disjointness, and model/host wire
uniqueness. No duplicate refusal enum or weaker hand-maintained subset is
admitted. Exact Effect `E` comes
from the injected operation descriptors and checker, not from
`PProg.envelope`. Any exact write-address or world-delta statement quantifies
over the address function `H`. The observation declaration says explicitly
whether a partial word surviving refusal is visible; an existing `ObsEq`-style
mask hides it and cannot support a stronger word-on-refusal claim.

The CAS bridge also preserves `Cas/Lang/Auth.lean`'s
`whole_run_security`/`whole_run_correctness` pair. Security remains at the
existing hash-lattice Level 0: no injectivity assumption on `H`, and the
adversarial branch returns the existing explicit collision witness. Receipt
round trip or replay alone is strictly weaker and cannot stand in for this
pair.

The CAS program-logic bridge reuses existing `wlp` for the EffHOL-style
partial-correctness modality and existing `wp_iff_wlp_and_total` for total
correctness. No duplicate modality, `WPre`/`WPost`, `Triple`, or
`PartialTriple` carrier is admitted. EffHOL Mod-E remains the new
`EC1-T130` theorem obligation, to be derived by specializing the shipped
`wpAux_append`; the estate does not ship `wlp_append`. Its prefix is nonempty
and its suffix receives the answer history produced by that prefix. There is no
unconditional table-only suffix law or restart-at-empty-history rule, and the
scratch `wlp_append` witness is not promoted.

### `EC1-K23` — target lowering and source acceptance

Status: **PROPOSED CONTRACT CLAUSE**.

For every checked graph:

1. `lower` produces a typed `TsCore` with identical canonical-overload-derived
   normalized `A/E/R`;
2. target and source `Observed` relations are equivalent under the declared
   mask; stock rc.112 lowering uses a mask no stronger than
   `effectReasonQuotient`;
3. rendering and structural decoding are inverse up to target normalization;
4. rendered bytes are canonical and rendering is injective on normalized,
   admitted `TsCore` values;
5. emitted source passes exact TypeScript 7 diagnostics;
6. emitted source passes configured Effect diagnostics through exact
   `@effect/tsgo`;
7. admitted code actions reach a canonical second-pass fixed point;
8. pre/post code-action targets are `SemEq` under the declared mask;
9. negative source mutations fail the expected diagnostic or structural
   admission rule; and
10. `AcceptedTs` implies only the checked source-to-target relation, never
    compilation or hosted-runtime preservation.

The first four are model/bridge proof obligations. Plain function
determinism is not counted separately; item 4 is the stronger no-collision
obligation. The next five are required
tooling batteries. The tenth is the trust boundary.
No combination of these clauses licenses a stock-runtime full-`CauseTree`
topology claim.

Item 4's renderer-injectivity component is the still-open half of freeze
condition 17. It remains a proposed proof obligation and is neither frozen nor
supported by inherited evidence.

## DECREASES

### `EC1-K30` — checker and normalization

Status: **PROPOSED CONTRACT CLAUSE**.

- table traversal decreases by unvisited entry count;
- type/value recursion decreases structurally;
- row normalization decreases by remaining input plus inversion count;
- region cycle checking decreases by DFS white-set size;
- direct-handler delegation checking decreases by unvisited handler count; and
- SCC construction terminates on the finite block graph.

### `EC1-K31` — pure evaluation

Status: **PROPOSED CONTRACT CLAUSE**.

`PureExpr` recursion decreases structurally or by an explicit collection-size
measure. A `PureAtom` is admitted only with a total Lean model. There is no
partial or fuel-bounded “pure” evaluator.

### `EC1-K32` — runner and unwinding

Status: **PROPOSED CONTRACT CLAUSE**.

- `execN` decreases strictly on fuel;
- one call/return or block terminator consumes one semantic step;
- a finalizer transition decreases lexicographically by
  `(unstarted finalizers, active-finalizer fuel)` only when the finalizer itself
  has a termination certificate; otherwise global execution remains
  fuel-bounded and possible divergence is explicit;
- race cleanup decreases by live loser count only when a loser halts; and
- scope administrative transitions cannot spin without consuming a step.

No theorem infers program termination from runner termination.

### `EC1-K33` — classifier

Status: **PROPOSED CONTRACT CLAUSE**.

Acyclic folding decreases by unprocessed blocks. SCC iteration either uses a
finite-height domain or a declared widening that stabilizes by its own measure.
Every widening site is recorded as loss of precision. Certificate checking
decreases structurally on the supplied certificate.

### `EC1-K34` — lowering, rendering, and code actions

Status: **PROPOSED CONTRACT CLAUSE**.

Lowering and rendering decrease structurally over finite normalized tables.
The estate does not assume arbitrary language-service code actions terminate.
The harness applies a configured finite action set once, formats, applies it a
second time, and requires byte equality; lack of a fixed point is rejection.

## FRAME

### `EC1-K40` — static passes

Status: **PROPOSED CONTRACT CLAUSE**.

Checking, normalization, classification, lowering, and rendering do not read
or modify the effect world. They change no CAS word, host process, network,
clock, random source, or repository file as part of their semantic function.

### `EC1-K41` — reference step

Status: **PROPOSED CONTRACT CLAUSE**.

A fiber-local pure/control step changes only that fiber, scheduler bookkeeping,
fresh supply, and trace. It leaves unrelated fibers, scopes, handlers, and
world lenses unchanged. Fork/join/race/scope rules name the additional owned
records they may change.

### `EC1-K42` — handler and foreign world

Status: **PROPOSED CONTRACT CLAUSE**.

A direct handler or foreign atom changes only its declared world-write frame;
all other projections are equal before and after. Reads are restricted to its
declared read frame. Unknown or unenforceable host access is classified as top
and cannot support independence or replay claims.

### `EC1-K43` — scope ownership

Status: **PROPOSED CONTRACT CLAUSE**.

A scope may modify only its frame, descendants, registered finalizers, owned
fibers, handler delta, and ancestor wait status. Sibling scopes and their
resource/fiber ownership remain unchanged.

### `EC1-K44` — CAS

Status: **PROPOSED CONTRACT CLAUSE**.

CAS injection adds no world lens beyond the existing word. Under the CAS mask,
unrelated word bindings satisfy the existing `runP_frame_sound` boundary; the
new core may not strengthen it past the known suffix-after-refusal and
duplicate-put gaps without new proof.

### `EC1-K45` — source tooling

Status: **PROPOSED CONTRACT CLAUSE**.

TypeScript and Effect tsgo may read the exact project/toolchain inputs and
produce diagnostics or code actions. Their output changes no Semantic Model
definition and contributes no denotational trust. Code-action mutation occurs
only in an isolated generated fixture; canonical source bytes remain derived
from the renderer.

## FALSIFIER

The future breaker battery must be authored before implementation by a process
other than the implementer. This packet names the equations and expected
failures but, by current authorization, creates no test or script.

### Raw/checker equations

| ID | Status | Mutation | Required observation |
| --- | --- | --- | --- |
| `EC1-F01` | PENDING FALSIFIER | Delete target block. | `check` rejects with dangling-code diagnostic at the exact edge. |
| `EC1-F02` | PENDING FALSIFIER | Swap an answer type in `Resume`. | Type mismatch diagnostic; no checked value. |
| `EC1-F03` | PENDING FALSIFIER | Duplicate a block/operation/handler ID. | Canonical duplicate diagnostic. |
| `EC1-F04` | PENDING FALSIFIER | Capture a resource token in an outer or daemon region. | Region-escape diagnostic. |
| `EC1-F05` | PENDING FALSIFIER | Omit a reachable direct handler clause. | Handler-completeness diagnostic. |
| `EC1-F06` | PENDING FALSIFIER | Add a parent-delegation cycle. | Handler-cycle diagnostic. |
| `EC1-F07` | PENDING FALSIFIER | Reuse one one-shot resume token. | Resume-linearity diagnostic. |
| `EC1-F08` | PENDING FALSIFIER | Put an unregistered host callback in raw content. | Non-first-order-field diagnostic. |
| `EC1-F09` | PENDING FALSIFIER | Claim too-small `E` or `R`. | `AERWF` mismatch with synthesized/declared rows. |
| `EC1-F10` | PENDING FALSIFIER | Normalize an already normalized graph. | Exact byte equality and identical diagnostics. |
| `EC1-F59` | PENDING FALSIFIER | Omit either deep public MultipartParser module from the recursive census. | Public-module closure fails before alphabet selection. |
| `EC1-F60` | PENDING FALSIFIER | Drop or duplicate a public row's seven-way disposition. | Disposition totality/uniqueness fails while proof status remains irrelevant. |
| `EC1-F76` | PENDING FALSIFIER | Store a block body in a new sequential table/line carrier instead of existing `PProg`. | Existing-type and duplicate-identity gate rejects it. |
| `EC1-F80` | PENDING FALSIFIER | Mark a slice or full-core cutover while one required type row has an open constructor, checker, semantics, classifier, lowering, or red-control edge. | Generated proof-closure and gated-AGENTS checks reject the cutover. |
| `EC1-F81` | PENDING FALSIFIER | Give one raw program two independent defects and demand the later diagnostic. | Fail-first checker returns and justifies only the least defect in canonical clause order; completeness still rejects the program. |
| `EC1-F82` | PENDING FALSIFIER | Permute a duplicate-key raw row and assert equal normalization. | Duplicate-free premise is unavailable and admission rejects both rows; no permutation theorem applies. |
| `EC1-F86` | PENDING FALSIFIER | Add a second value meaning for an inhabited `Cas.Schema.El` code or silently inhabit one of `El`'s empty arms. | Existing-type/bridge gate demands the `El` equivalence or a named insufficiency proof row. |
| `EC1-F87` | PENDING FALSIFIER | Add reification metadata to `Sig`, replace `Sig.Op`, flatten `RootSig`/`WordSig` extension arms, or treat a neutral protocol identity as a Lean operation without an admission bridge. | Existing-type and `Sig.sum` gates reject the duplicate family; open freeze condition 14 requires the explicit identity-to-`Sig` bridge. |

### Algebra and semantics equations

| ID | Status | Equation or adversary | Required observation |
| --- | --- | --- | --- |
| `EC1-F11` | PENDING FALSIFIER | `seq (close x) k` vs instantiated `k`. | Equal full denotation. |
| `EC1-F12` | PENDING FALSIFIER | Two parenthesizations of three sequential flows. | Equal normalized denotation and `A/E/R`. |
| `EC1-F13` | PENDING FALSIFIER | Swap `race` arms with ordered public events. | Deliberate inequality; prevents false commutativity. |
| `EC1-F14` | PENDING FALSIFIER | Swap independent `par` arms under full trace and under independence quotient. | Unequal under full trace; equal only under the named quotient if obligations hold. |
| `EC1-F15` | PENDING FALSIFIER | Replay twice from the same initial configuration and compatible typed decision tape. | Byte-identical normalized finite observations; no separate schedule input exists. |
| `EC1-F16` | PENDING FALSIFIER | Remove one relational answer admitted by a handler. | Runner-to-relation completeness fails, proving the test can detect it. |
| `EC1-F17` | PENDING FALSIFIER | Alter `truncate` to retain one depth-`n+1` event. | Approximation coherence test fails. |
| `EC1-F18` | PENDING FALSIFIER | Treat fuel exhaustion as failure. | Divergence witness distinguishes `running` from typed failure. |
| `EC1-F19` | PENDING FALSIFIER | Alpha-rename all code/block IDs. | Equal normalized graph and denotation. |
| `EC1-F20` | PENDING FALSIFIER | Pure atom reads a mutable counter. | Purity mutation test forces rejection/reclassification as foreign effect. |
| `EC1-F61` | PENDING FALSIFIER | Compare `CauseTree.then x y` and `CauseTree.both x y`. | Unequal under full topology; equal only when the declared rc.112 reason quotient erases that distinction. |
| `EC1-F69` | PENDING FALSIFIER | Assert global uniqueness for a full-core program with two admitted answers or scheduler-enabled choices. | Distinct relational branches remain; one compatible complete decision tape selects one executable path, and only stable non-frontier outcomes of the CAS/block specialization have the exhibited outcome uniqueness. |
| `EC1-F70` | PENDING FALSIFIER | Encode fuel exhaustion, external answer, or scheduler choice as a typed failure, `CauseTree`, or CAS `Refusal`. | Frontier-kind invariant rejects the encoding. |
| `EC1-F77` | PENDING FALSIFIER | Promote full-core `denotes_unique`, a public `Behavior` carrier, or fixed-fuel bind coherence. | Nondeterministic branch or existing `run` no-composition counterexample rejects the claim. |
| `EC1-F78` | PENDING FALSIFIER | Add `HHandler` or treat the scratch `scopeHandler` as catch/scope/finalizer semantics. | Existing-handler annotation or scope/catch/finalizer law battery rejects it. |
| `EC1-F83` | PENDING FALSIFIER | Require full `ClassProduct` equality for two `SemEq` programs whose checked graphs have different answer-dataflow edges. | D4 summaries may differ; only mask-selected concrete projections must agree and inhabit both sound concretizations. |
| `EC1-F89` | PENDING FALSIFIER | Use `Handler ScopeSig (ReaderT Env (Prog CasSig))` for typed recovery, or use a target whose failure branch discards state for ensuring. | `no_handler_into_ScopeM_catches` rejects the former; the ensuring information contract requires state to survive failure, witnessed minimally for CAS by `ReaderT Env (ExceptT Refusal (StateT Word Id))`. |
| `EC1-F90` | PENDING FALSIFIER | Implement ensuring-on-refusal as ordinary `Prog.bind`. | Existing refusal-strict interpretation skips the finalizer; `ensuring_never_finalises_a_refusal` detects it. |
| `EC1-F93` | PENDING FALSIFIER | Use a later unique CAS/block result to equate every earlier exhausted/refusal label. | Two pre-completion fuels expose distinct labels; uniqueness begins only at stable non-frontier outcomes. |

### Scope/resource/cancellation equations

| ID | Status | Program | Required trace property |
| --- | --- | --- | --- |
| `EC1-F21` | PENDING FALSIFIER | acquire; register; success | exactly one release after body |
| `EC1-F22` | PENDING FALSIFIER | acquisition typed-fails before register | zero releases |
| `EC1-F23` | PENDING FALSIFIER | acquire A; acquire B; body fails | release B then A, then failed exit |
| `EC1-F24` | PENDING FALSIFIER | body fails; release fails | `CauseTree.then body release` |
| `EC1-F25` | PENDING FALSIFIER | interrupt between acquire and atomic registration boundary | either no acquisition committed or exactly one registered release; never acquired-and-leaked |
| `EC1-F26` | PENDING FALSIFIER | interrupt inside mask; then unmask | no delivery inside; one delivery at boundary |
| `EC1-F27` | PENDING FALSIFIER | race fast child vs resource-owning slow child | loser interruption and release precede parent resume |
| `EC1-F28` | PENDING FALSIFIER | scoped child never halts, no cancellation progress | parent cannot falsely report completed scope |
| `EC1-F29` | PENDING FALSIFIER | daemon child survives program result | root-supervisor obligation remains observable |
| `EC1-F30` | PENDING FALSIFIER | two children fail concurrently | canonical `CauseTree.both`, not schedule-dependent tree order |
| `EC1-F62` | PENDING FALSIFIER | await and join the same failed child | await succeeds with `Exit.failure`; join propagates the child cause |
| `EC1-F63` | PENDING FALSIFIER | interrupt a child with a divergent masked finalizer | request-only returns after setting the flag; interrupt-and-await remains suspended |

### Classification equations

| ID | Status | Adversary | Required outcome |
| --- | --- | --- | --- |
| `EC1-F31` | PENDING FALSIFIER | Effect only in one branch. | may contains it; must does not. |
| `EC1-F32` | PENDING FALSIFIER | Left sequence may fail before right. | right effects absent from must. |
| `EC1-F33` | PENDING FALSIFIER | Empty `E`, explicit defect. | `AER.E` empty; `CauseDomain` includes defect. |
| `EC1-F34` | PENDING FALSIFIER | Acyclic answer selects different operations. | control at least monadic/selective as specified, not applicative. |
| `EC1-F35` | PENDING FALSIFIER | Hash-determined CAS answer dataflow. | remains L-A/applicative flag despite answer edges. |
| `EC1-F36` | PENDING FALSIFIER | Uninterruptible looping finalizer. | possible cleanup divergence. |
| `EC1-F37` | PENDING FALSIFIER | Foreign op with unknown frame. | frame upper bound is top. |
| `EC1-F38` | PENDING FALSIFIER | Finite terminating samples of an infinite loop. | no must-termination promotion. |
| `EC1-F39` | PENDING FALSIFIER | Different operation IDs write same lens. | independence rejected. |
| `EC1-F40` | PENDING FALSIFIER | Constant branch. | unreachable arm removed across all dimensions by a proved reduction. |
| `EC1-F71` | PENDING FALSIFIER | Sequence dependence graphs without reindexing the right operand. | Composite answer-edge indices disagree with the checked graph. |
| `EC1-F72` | PENDING FALSIFIER | Infer semantic commutativity from unioned frame bounds. | Ordered word/world observations distinguish the swapped programs. |
| `EC1-F73` | PENDING FALSIFIER | Merge operation footprint, world delta, and happens-before order into one set. | Duplicate put or interleaving witness separates D1, D2, and D10. |

### CAS equations

| ID | Status | Program | Required outcome |
| --- | --- | --- | --- |
| `EC1-F41` | PENDING FALSIFIER | Empty `PProg`. | `admitCas = none`; the separate raw `runP` refusal/word fixture remains unchanged. |
| `EC1-F42` | PENDING FALSIFIER | Dangling answer index. | `admitCas = none`; the separate raw exact-fuel refusal fixture remains unchanged. |
| `EC1-F43` | PENDING FALSIFIER | Duplicate put. | Existing word/sublist observation preserved; classifier does not claim a prefix. |
| `EC1-F44` | PENDING FALSIFIER | Refusal followed by unreachable suffix. | Envelope keeps the known may over-approximation. |
| `EC1-F45` | PENDING FALSIFIER | Encode same CAS table through both entry points. | Canonical identity is the existing `PProg` identity only. |
| `EC1-F46` | PENDING FALSIFIER | Random small `CasAdmissible` tables with admitted `H`. | `runCore injectCas = runP`; finite test evidence only. |
| `EC1-F74` | PENDING FALSIFIER | Mint a new CAS refusal-kind enum or infer exact Effect `E` from `PProg.envelope`. | Existing-type/bridge gate requires `Refusal.Clause`/`RefusalMap`; checker-derived `OpDesc.errorRow` remains authoritative. |
| `EC1-F75` | PENDING FALSIFIER | Claim exact write addresses without `H`, or compare refusal runs without declaring whether their partial words are masked. | H-dependence or observation-mask gate rejects the claim. |
| `EC1-F79` | PENDING FALSIFIER | Add a second EffHOL-style modality or restate CAS `WPre`/`WPost`. | Existing-type gate requires `wlp` and the existing `wp ↔ wlp ∧ total` bridge. |
| `EC1-F88` | PENDING FALSIFIER | Replace the existing RefusalMap family with a partial table, assume injective `H`, or reduce authenticated computation to receipt replay. | Host-only/disjointness/wire or Level-0 security/correctness bridge fails on the existing counterexample. |
| `EC1-F91` | PENDING FALSIFIER | Apply EffHOL Mod-E to a restarted suffix with empty answer history or omit the nonempty-prefix premise. | The new `EC1-T130` premises are necessary; the suffix can refuse alone while succeeding after its prefix. Shipped `wpAux_append` is the derivation anchor, not a shipped `wlp_append`. |
| `EC1-F92` | PENDING FALSIFIER | Treat `toPProg` as a semantic projection of every observationally CAS-only graph. | Unreachable-tail and relocated-entry graphs are equivalent to injection but the recognizer returns `none`. |

### TypeScript and Effect-tooling equations

| ID | Status | Mutation | Required result |
| --- | --- | --- | --- |
| `EC1-F47` | PENDING FALSIFIER | Render checked target twice. | Byte equality. |
| `EC1-F48` | PENDING FALSIFIER | Decode rendered target. | Target normalization round trip. |
| `EC1-F49` | PENDING FALSIFIER | Change generated result annotation `A`. | TypeScript or structural decoder rejects. |
| `EC1-F50` | PENDING FALSIFIER | Remove required service from `R`. | TypeScript/Effect diagnostic or structural decoder rejects. |
| `EC1-F51` | PENDING FALSIFIER | Replace typed `Effect.fail` with defect-producing escape. | Structural relation rejects even if TypeScript accepts. |
| `EC1-F52` | PENDING FALSIFIER | Insert unregistered `Effect.promise`/host callback. | Structural decoder rejects; clean diagnostics cannot override. |
| `EC1-F53` | PENDING FALSIFIER | Apply admitted Effect code action twice. | Second pass byte-identical after configured formatting. |
| `EC1-F54` | PENDING FALSIFIER | Code action changes effect topology. | Pre/post graph relation or denotation comparison rejects it. |
| `EC1-F55` | PENDING FALSIFIER | Disable the Effect tsgo plugin. | Harness fails closed rather than recording a vacuous clean run. |
| `EC1-F56` | PENDING FALSIFIER | Drift TypeScript or `@effect/tsgo` version. | Pin gate fails before diagnostics run. |
| `EC1-F57` | PENDING FALSIFIER | Source passes TS and Effect diagnostics but has no structural decoder image. | Not `AcceptedTs`. |
| `EC1-F58` | PENDING FALSIFIER | Mutate one lowering constructor's Effect combinator. | Per-constructor semantic differential detects trace or `A/E/R` change. |
| `EC1-F64` | PENDING FALSIFIER | Omit one generated source file from the diagnostics project. | Expected/reported file-set equality fails despite empty diagnostics. |
| `EC1-F65` | PENDING FALSIFIER | Include one unrelated extra diagnostics file. | Expected/reported file-set equality fails in the opposite direction. |
| `EC1-F66` | PENDING FALSIFIER | Report a file without detected/supported Effect v4. | Coverage gate fails even when the diagnostic array is empty. |
| `EC1-F67` | PENDING FALSIFIER | Admit a quick fix that inserts a nonexistent or null-masked import. | Independent package-export census rejects the edit. |
| `EC1-F68` | PENDING FALSIFIER | Drift the platform binary, TypeScript git head, upstream mapping, rule catalog, action catalog, or plugin config. | Pin/config drift fails before source acceptance. |
| `EC1-F85` | PENDING FALSIFIER | Make two distinct normalized admitted `TsCore` values render to the same bytes. | Renderer injectivity/round-trip gate rejects the collision even though repeated calls to the function are deterministic. |

## Positive examples

Status: **PROPOSED EXAMPLE SET**.

1. CAS `put` then `load`, injected without a new canonical spelling.
2. Service operation followed by a pure guard on its answer and two closed
   branches.
3. Tail-recursive retry loop whose attempts are visible and whose ranking is
   intentionally absent, classifying as may-diverge.
4. Scoped acquisition with two LIFO finalizers and a typed body failure.
5. Handler provision whose clause itself performs a lower service operation.
6. Parallel independent reads joined as a product.
7. Race between asynchronous requests with loser cancellation and cleanup.
8. Masked critical section receiving a pending interruption.
9. Foreign request with a typed receipt and replay.
10. Generated TypeScript whose exact `A/E/R`, structural target, diagnostics,
    and normalized model trace all agree.

## Negative examples

Status: **PROPOSED EXAMPLE SET**.

1. Host closure stored as a continuation.
2. Operation absent from the alphabet version.
3. Reachable service absent from both handler environment and `R`.
4. Resource or scoped fiber handle escaping its region.
5. One-shot resume used twice.
6. Finalizer registered after control becomes interruptible.
7. Race resumes before loser finalization.
8. Unknown foreign frame claimed disjoint.
9. TypeScript source clean under diagnostics but outside `TsCore`.
10. Finite fuel sweep described as a termination proof.

## Adversarial examples

Status: **PROPOSED EXAMPLE SET**.

1. A handler answers successfully but mutates an undeclared world lens.
2. A release loops forever under an uninterruptible mask.
3. A race tie changes public log order while returning the same value.
4. A daemon captures a supposedly scoped resource token.
5. A pure atom hides randomness behind a deterministic TypeScript type.
6. A code action is clean on pass one but oscillates on pass two.
7. A generated program typechecks after its service row is widened to
   `unknown`, defeating exact `R` unless the structural relation checks it.
8. A CAS-only graph receives a second byte encoding with identical run output,
   violating identity while fooling observational tests.
9. A scheduler is unfair, so a ready child never runs; no safety theorem may
   assume it eventually does.
10. A foreign receipt replays against the wrong initial world frame and appears
    to match only because the observation mask hid that frame.

## Acceptance stop

This packet is ready for grilling when reviewers can answer, without inventing
new machinery:

- exactly which raw states are rejected and why;
- exactly which graph forms constitute the closed core;
- exactly where pure and foreign host code sit;
- exactly how each scope/resource/fiber transition changes state;
- exactly what the three semantic faces observe and how they agree;
- exactly what each classifier field means and how imprecision is reported;
- exactly how CAS retains its existing semantics and identity;
- exactly what TypeScript and Effect tsgo are required to check; and
- exactly which claim gate each later evidence item could satisfy.

If any answer requires treating diagnostics as semantics, a host callback as
content, fairness as implicit, a finite sweep as proof, or a new CAS spelling
as harmless, the packet must be revised before implementation.
