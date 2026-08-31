# Effect Core v1 — proposed denotational classification

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

Claim gate: none

Depends on: `ALGEBRA.md`

The adopted classification anchors and their limits are fixed by
`EXHIBITS-REVIEW.md`. `TYPE-CLOSURE.md` owns the per-type classifier proof
edges and cutover status. This document defines domains and transfers, not
scratch exhibit carriers or source-tooling verdicts.

Every `EC1-*` identifier introduced here is a **PROPOSED TERM**. Every claimed
property is listed later as a **PENDING THEOREM** or **PENDING FALSIFIER**; no
classification result is currently established.

## 1. Why the classifier is a product

A single label such as “monadic” cannot answer whether a program terminates,
which services it requires, whether a finalizer is guaranteed, how a race may
interleave, or whether a foreign atom is replayable. Conversely, calling a
program concurrent says nothing about its typed error row.

**PROPOSED RULING `EC1-R18` — independent dimensions.** Effect Core v1 uses a
product of abstract domains. Each domain owns its own information order,
sequential operator, branch join, parallel operator, loop solver,
concretization, and reduction checks with other domains. There is no universal
“effect join” assumed to mean all of these things at once.

## 2. Abstract-domain interface

| ID | Status | Proposed term | Meaning |
| --- | --- | --- | --- |
| `EC1-C01` | PROPOSED TERM | `AbsDomain` | One classification dimension and its sound transfer structure. |
| `EC1-C02` | PROPOSED TERM | `Bounds D` | Lower/upper interval in a domain `D`. |
| `EC1-C03` | PROPOSED TERM | `ConcreteFact D` | Fact extracted from one relational `Denotes` witness. |
| `EC1-C04` | PROPOSED TERM | `concretize` | Relational run facts admitted by one abstract value. |
| `EC1-C05` | PROPOSED TERM | `ClassProduct` | Product of all semantic dimensions. |
| `EC1-C06` | PROPOSED TERM | `classify` | Executable fixed-point analysis of a checked graph. |
| `EC1-C07` | PROPOSED TERM | `reduceProduct` | Cross-domain consistency reduction that only increases precision. |
| `EC1-C08` | PROPOSED TERM | `EvidencePlane` | Non-semantic source/tooling evidence kept outside `ClassProduct`. |

`EC1-C01 AbsDomain` has the proposed fields:

```text
Carrier        abstract values
le             information/safety preorder
bottom, top    least and unknown information
unit           empty/closing-flow summary
atom           summary of one graph terminator
seq            sequential transfer
choice         data-dependent alternative transfer
par            parallel transfer
race           first-completer transfer
scope          scope/resource transfer
loop           monotone finite-graph fixed-point solver
concrete       ConcreteFact type
concreteRun    (h : Denotes p i tr c') -> ConcreteFact
gamma          Carrier -> Set ConcreteFact
```

Every transfer is required to be monotone and sound with respect to `gamma`.
Only domains that actually have a commutative join may call `choice` a join.
Trace order, cause order, and resource order are deliberately noncommutative.

`EC1-C02 Bounds D` is an interval `[lower, upper]` with `lower <= upper`.
For set-like domains this reads “must ⊆ actual ⊆ may.” For numeric domains it
reads “guaranteed minimum ≤ actual ≤ possible maximum.” For ordered event
domains it reads “must-happen-before edges ⊆ actual order ⊆ may-order edges.”

Precision order narrows the interval: a larger lower bound and smaller upper
bound is more precise. Unknown is `[bottom, top]`. An exact result has equal
bounds. A classifier must retain whether an answer is exact, bounded, or
unknown rather than flattening them into one set.

`EC1-C05 ClassProduct` is sound when the concrete classification of every
relational run witness of the program lies in the intersection of all
component concretizations. `EC1-C07 reduceProduct` may use one dimension to refine
another—for example, “must terminate before entering the right operand” may
raise the right operand's must-footprint—but may never turn an upper bound into
a lower bound without a theorem.

## 3. Dimensions

### D0 — static Effect type

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C10` | PROPOSED TERM | `AERDomain` | Exact normalized `AER`, selected canonical public overload, and a proof-status marker. |

This dimension is exact for the checked graph's *type*, not for runtime
reachability. `E` names typed errors allowed to escape even if a branch is
unreachable; `R` names services the expression must be provided to typecheck,
not services every execution will call.

Proposed exact transfer:

```text
close x          = (type x, empty, empty)
perform op       = (answerTy op, errorRow op, requirementRow op)
seq p k          = (A_k, E_p union E_k, R_p union R_k)
choice p q       = (common A, E_p union E_q, R_p union R_q)
catch p h        = (unionTy A_p A_h,
                    (E_p minus handled h) union E_h,
                    R_p union R_h)
provide H p      = (A, E_p union E_H,
                    (R_p minus provides H) union requires H)
par p q          = (A_p product A_q, E_p union E_q, R_p union R_q)
race p_i         = (common A, union E_i, union R_i)
scope/loop       = interface declared by the checked body/fixed point
```

Defect and interruption classifications live elsewhere and never enter `E`.
Every source-facing equation is checked against the canonical overload row
which selected it. In particular, builtin routing has an empty requirement row;
catch result unions and residual errors are not inferred from a single generic
handwritten signature.

The descriptor table is metadata indexed by the selected existing
`Cas.Lang.Sig.Op`; its answer code agrees with `Sig.Ans`. Reification grade and
source disposition are not fields on `Sig`. Semantic-family growth uses
`Sig.sum`, retaining the existing `RootSig`/`StoreSig` and
`WordSig`/`WordedSig` packages and their non-disturbance laws.

### D1 — dynamic operation footprint

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C11` | PROPOSED TERM | `OpFootprintDomain` | Must/may operation IDs, service keys, and capability classes, separated by execution phase. |

Phases are `body`, `handler`, `finalizer`, `child`, and `daemon`. A release
operation therefore cannot be mistaken for a body effect. `seq` unions may
sets; it adds the second must set only when the first flow must reach its
normal exit. `choice` unions may sets and intersects must sets unless the guard
is statically decided. `race` includes all started-child operations in may,
but only operations proved to occur before every possible winner in must.

This domain records operation occurrence, not concrete world mutation or event
order. Where multiplicity matters it carries count bounds or ordered site IDs;
it never infers a write merely because a write-capable operation ran.

### D2 — world frame and capability use

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C12` | PROPOSED TERM | `WorldFrameDomain` | Must/may reads, writes, allocations, external capabilities, and independence relation. |

Frames name abstract world lenses owned by direct handlers and foreign
registry entries. Sequential composition unions frames. Parallel composition
also records whether writes conflict or commute. An unknown foreign frame is
`top`, not the empty set. A claimed independent parallel law requires disjoint
writes and a named read/write commutation theorem.

Frame union is a conservative may-read/may-write abstraction. Its commutativity
does not make sequential world deltas, CAS words, or traces commutative. D1
operation occurrence, D2 state/frame change, and D10 happens-before order are
separate facts and cannot share one footprint carrier.

### D3 — minimal control strength

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C13` | PROPOSED TERM | `ControlDomain` | `closing < static < applicative < selective < monadic < recursive`. |

- `closing`: only `close` and pure `ArgMap`s;
- `static`: fixed effect multiset, no answer dataflow;
- `applicative`: acyclic fixed control with answer dataflow that cannot choose
  later topology; the existing hash-determined L-A fragment is recorded by a
  separate flag;
- `selective`: acyclic closed arms chosen by an effect answer;
- `monadic`: a prior answer selects a call, operation, region, or continuation;
- `recursive`: a reachable cycle or recursive `CodeId` call.

The order means expressive requirement, not semantic subtyping. The classifier
returns the least syntactic class it can justify and separately records
semantic reductions, such as a constant branch eliminating a selective node.

### D4 — answer dependence

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C14` | PROPOSED TERM | `DependenceDomain` | Graph from inputs/operation answers/foreign answers to requests, guards, result, and code-point choice. |

Edges are labeled `pure`, `hashDetermined`, `handlerDetermined`,
`foreignDetermined`, or `schedulerDecisionDetermined`. This preserves the exact reason
L-A remains statically analysable: answer dependence alone is not monadic
control when the answer is hash-determined and cannot alter topology.

Sequential composition reindexes every right-operand site and answer edge by
the left graph's site embedding before combining dependence graphs. A raw set
union or list append is not even a conservative graph transfer when local site
indices are reused.

### D5 — termination, divergence, and suspension

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C15` | PROPOSED TERM | `ProgressDomain` | Bounds over `{normal, failure, suspended, diverges}` plus ranking/productivity evidence. |

`mustTerminate` requires a well-founded ranking that decreases across every
reachable internal cycle and a termination contract for every invoked handler
and foreign atom. `mayDiverge` requires a reachable cycle or an external
contract that permits non-return. `mustDiverge` requires exclusion of every
halt/suspension path. “Fuel expired in these examples” proves none of these.

Suspension is separate from divergence: an unresolved asynchronous request is
a finite frontier, while divergence is an unbounded chain of internal steps or
continually answered requests.

Fuel exhaustion, external-answer frontiers, and scheduler-choice frontiers are
also separate from typed failure, `CauseTree`, and CAS `Refusal`. Classifier
reductions may not move a frontier fact into the error/cause domain.

### D6 — choice and determinism source

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C16` | PROPOSED TERM | `ChoiceDomain` | Set of sources: input, handler answer, foreign answer, scheduler-enabled ready-fiber/race selection, clock, random, and the compatible typed decision tape that records those selections. |

The domain also records `deterministicGiven`, the smallest declared decision
interface under which the executable runner is deterministic. A program can
be deterministic under a tape while nondeterministic relationally. A replay
claim must bind the complete initial configuration—including scheduler
policy/state—and the compatible tape. There is no separate schedule input.

The kernel-checked deterministic `Denotes`/coherence exhibit is a fact only
about stable non-frontier outcomes in its CAS/block subfragment. It does not
identify pre-completion exhaustion/refusal labels across fuel. Full-core
`Denotes` is a relation with no global uniqueness fact; a fixed initial
configuration and complete compatible decisions select one deterministic
executable path.

### D7 — scope topology

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C17` | PROPOSED TERM | `ScopeDomain` | Region tree, maximum live depth bound, handler-provision sites, exit coverage, and escape set. |

Acyclic nesting yields an exact finite region tree even when control loops.
Maximum *dynamic* depth is unbounded when recursion enters a new scope; the
upper bound is then infinity. The escape set must be empty for resource tokens
and scoped fibers. Daemon ownership is a root-supervisor obligation, not a
resource escape silently accepted as valid.

### D8 — resource protocol

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C18` | PROPOSED TERM | `ResourceDomain` | Per resource kind: acquire/register/use/release protocol, live-count interval, peak bound, release guarantee, and release order. |

The release guarantee is one of `none`, `onRegisteredExit`, `onNormalOnly`, or
`unknown`. A checked `acquireRelease` elaboration should classify as
`onRegisteredExit`; it does not claim release when acquisition failed before
registration. Sequential finalizer order is an ordered list abstraction, not
a set. Parallel scopes keep per-owner orders plus may-interleaving edges.

### D9 — resumption

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C19` | PROPOSED TERM | `ResumptionDomain` | Bounds on abandon/resume counts and whether a resume crosses a scope boundary. |

For v1, an admitted operation has maximum resume count one. `zero` operations
terminate the current continuation. A checked handler that returns normally
causes the machine to consume exactly one resume; it cannot retain the token.
Any `many` descriptor classifies as refused before `CheckedProgram` exists.

### D10 — temporal and concurrency topology

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C20` | PROPOSED TERM | `TemporalDomain` | Must/may happens-before graph, maximum live-fiber bound, and lifetime modes. |

The graph uses abstract event sites, not runtime fiber IDs. `seq` adds every
normal completion of the left before entry to the right. `par` introduces no
cross-child order except fork-before-child and child-halt-before-join. `race`
adds winner-before-loser-interrupt and all loser-finalizers-before-parent
resume. A loop may make event multiplicity and live-fiber count unbounded.

### D11 — interruption and cancellation

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C21` | PROPOSED TERM | `CancellationDomain` | Interruptible sites, mask nesting, pending-delivery sites, child propagation, and cleanup wait policy. |

This domain distinguishes “can receive interruption,” “can request
interruption,” and “may exit interrupted.” `mask` changes delivery, not the
existence of a pending flag. `race` must record that losers are interrupted
and awaited. An uninterruptible infinite finalizer is classified as a possible
cleanup divergence, never as successful cancellation.

### D12 — failure and cause topology

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C22` | PROPOSED TERM | `CauseDomain` | Must/may typed failure tags, defects, interruptors, ordered project-owned `CauseTree` shapes, and the rc.112 reason quotient. |

This is the dynamic complement of `AERDomain`. `catch` can remove a typed
failure from the may-escape set only when its handler is exhaustive and the
handler itself cannot reproduce the same tag. `ensure` adds finalizer causes
with ordered `CauseTree.then`; `par` can add ordered `CauseTree.both`. Neither
is commutative under the full tree observation.

The domain carries both the full topology bounds and their
`effectReasonQuotient`. The quotient flattens leaves into rc.112
`Fail | Die | Interrupt` reasons and stably de-duplicates equal reasons, so it
cannot distinguish `then` from `both`. Stock-runtime evidence may refine only
the quotient component. It cannot narrow full-topology bounds.

On injected CAS, refusal-kind facts reuse existing `Refusal.Clause` and
`RefusalMap`; this domain does not define a second refusal enum. Those facts do
not synthesize exact `AER.E`, which remains checker-derived from operation
descriptors. A refusal/suspension/frontier boundary is preserved by type.

### D13 — foreignness and reification grade

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C23` | PROPOSED TERM | `ForeignDomain` | Foreign IDs, host pins, receipt coverage, replay status, and declared trust boundary. |
| `EC1-C24` | PROPOSED TERM | `ReificationDomain` | `closed`, `modeledPureAtom`, `modeledForeignEffect`, `receiptOnly`, `unadmitted`. |
| `EC1-C27` | PROPOSED TERM | `SurfaceLinkView` | Non-semantic imported view joining used Core nodes to the total seven-disposition source ledger owned by `REIFICATION-CHECKLIST.md`. |

`closed` means every semantic step is defined by core constructors and direct
handlers. A modeled atom has a Lean meaning and separately owed host
conformance. `receiptOnly` means replay has a checked record but no theorem
relates the real call to the model. `unadmitted` is a RawProgram diagnostic and
cannot occur in a CheckedProgram. These grades are not claim gates.

`SurfaceLinkView` is also not a replacement for these dynamic grades or an
`AbsDomain`.
It joins each used Core node or expansion to canonical public module/member/
overload rows classified as `reifiedPrimitive`, `derivedExpansion`,
`separateSubcalculus`, `pureOrHostOnlyClosedOutsideProg`,
`projectOwnedReplacementOrForeignOp`, `targetOnly`, or `excludedInternal`.
Exactly-one disposition is a source-closure invariant. A public exposure may
not be `excludedInternal`, and a pending proof does not create an eighth value.
The relation is imported from the generated public-surface ledger and joined
to a classification report after `classify`; the classifier neither computes
nor owns source-tooling dispositions.
These grades and links attach to `OpDesc`/public rows keyed by an existing
`Sig.Op`; they never alter the semantic signature to carry classification
metadata.

### D14 — observations and provenance

| ID | Status | Proposed term | Carrier |
| --- | --- | --- | --- |
| `EC1-C25` | PROPOSED TERM | `ObservationDomain` | Exact observation mask plus ordering/quotient policy. |
| `EC1-C26` | PROPOSED TERM | `ProvenanceDomain` | Alphabet, handler, pure/foreign atom, target toolchain, compiler, and host identities required by a claim. |

Two programs are never called equivalent without an `ObservationDomain`.
Possible masks include full semantic trace, result/cause only, CAS status and
word, public log trace, resource/fiber lifecycle, and host receipt projection.
Quotienting independent event order is a named relation with proof
obligations, not default trace sorting.

CAS masks distinguish success-word observation from the partial word left on a
refusal. The existing `ObsEq`-style refusal branch hides that word; a stronger
mask must request it explicitly. Exact CAS write addresses and deltas also bind
the address function `H`; the `H`-free envelope supplies shapes/bounds, not
those addresses.

CAS provenance also records whether the complete existing `RefusalMap` family
and `Auth.lean` security/correctness pair were transported. The authenticated
security edge stays at hash-lattice Level 0 and retains its explicit collision
witness; an injective-`H` assumption or receipt replay is not an equivalent
replacement.

`ProvenanceDomain` is a dependency record, not evidence by itself. Missing pins
remain explicit and bound the maximum claim gate.

## 4. Product shape

The proposed classifier result is:

```text
ClassProduct =
  aer             : AERDomain
  operations      : OpFootprintDomain
  world           : WorldFrameDomain
  control         : ControlDomain
  dependence      : DependenceDomain
  progress        : ProgressDomain
  choice          : ChoiceDomain
  scopes          : ScopeDomain
  resources       : ResourceDomain
  resumptions     : ResumptionDomain
  temporal        : TemporalDomain
  cancellation    : CancellationDomain
  causes          : CauseDomain
  foreign         : ForeignDomain
  reification     : ReificationDomain
  observations    : ObservationDomain
  provenance      : ProvenanceDomain
  precision       : per-field exact | bounds | unknown
```

`EC1-C06 classify` solves equations over the finite block graph. Acyclic
components are folded topologically. Strongly connected components are solved
by monotone iteration with domain-specific widening only where a finite-height
carrier is unavailable. Every widening is recorded in `precision`.

The termination lower bound, exact numeric resource peaks, and must-event
facts may require certificates. Without a certificate, the classifier returns
a safe upper result and says which fact remained unknown. It never guesses a
ranking or promotes a finite execution sample.

`classify` is not factored through `SemEq`: structural fields such as D4
answer-dataflow may differ for programs with equal selected runtime
observations. Soundness is per graph. If `SemEq O p q`, the concrete projection
selected by `O` is shared and must lie in both relevant concretizations; no
whole-`ClassProduct` equality follows unless a separate field-specific theorem
establishes it.

## 5. Proposed transfer matrix

This table is the construction contract. Every row owes a soundness theorem
for every relevant `Denotes` witness.

| Flow form | Static `A/E/R` | May footprint | Must footprint | Temporal/resource/cause effect |
| --- | --- | --- | --- | --- |
| `close x` | exact `(type x, empty, empty)` | empty | empty | immediate normal exit |
| `perform op` | descriptor exact | add `op` in body or handler phase | add only when block is must-reached | request frontier; descriptor errors/cancellation |
| `seq p k` | row unions | union | `must(p)` plus `must(k)` only if `p` must normally reach `k` | all left-normal exits happen before right entry |
| constant `choose` | selected arm | selected arm | selected arm | eliminated branch recorded as reduction |
| unknown `choose` | arm unions | union | intersection plus pre-branch facts | mutually exclusive arm events |
| `feedback` / cycle | checked fixed point | least fixed point | certificate-backed greatest safe facts | possible divergence; multiplicity may become unbounded |
| `catch p h` | handled errors removed; handler rows added | body plus reachable handlers | handler must only if matching failure must occur | typed cause routed; defect/interrupt unchanged |
| `provide H p` | supplied requirements subtracted | body plus handler clauses | conditional on reached operations | region-local direct handler delta |
| `scope p` | body interface | body plus finalizers | registered finalizers become must-on-exit | LIFO, owned children awaited |
| `ensure p f` | error/requirement unions | body plus finalizer | `f` must after successful registration and any exit | finalizer cause sequenced with pending cause |
| `fork child` | child rows union at parent expression | child may set | fork event must at reached site | new ownership/happens-before edges |
| `await child` | returns `Exit<A,E>` with empty typed error | child plus await | await when site must reached | child halt before parent resume; failure remains data |
| `join child` | returns `A` with child `E` | child plus join | join when site must reached | child halt before parent resume; failure cause propagates |
| `requestInterrupt child` | unchanged | interrupt request | request when site must reached | pending flag set; requester need not wait |
| `interruptAwait child` | unchanged | interrupt plus cleanup | request when site must reached | target halt/finalizers before requester resume |
| `par p q` | product result; row unions | union | both must prefixes after both are started | interleaving, ordered `CauseTree.both`, per-owner finalizers; stock target observes reason quotient |
| `race p_i` | common result; row unions | union | only common pre-winner facts | winner, loser interrupt, loser cleanup before resume |
| `mask p` | unchanged | unchanged | unchanged | delivery sites change; pending interruption retained |
| registered foreign op | descriptor exact | declared op/capabilities/frame | only when must-reached | receipt and declared suspension/choice sources |
| admitted CAS injection | existing CAS interface | envelope upper bound | existing proved lower facts only | only `CheckedPProg`; CAS status/word observation; no new lifecycle event |

The compact footprint columns above are D1 only. They do not define D2 world
deltas, D4 dependence, or D10 order. In particular, `seq` reindexes the right
dependence graph; D2 frame union stays conservative; D10 preserves ordered
happens-before edges. CAS exact `E` is read from injected operation descriptors,
write addresses remain `H`-dependent, and refusal-word visibility follows the
selected mask rather than the envelope.
Raw empty or dangling `PProg` values are rejected by `admitCas`; their existing
raw refusal behavior is not classified as a checked Core `Denotes` witness.
Likewise, `toPProg` is only a sound recognizer of the canonical injected graph
normal form. An observationally equal graph with an unreachable tail or moved
entry may remain unrecognized; classification cannot use the recognizer as a
semantic quotient.

The `ensure` transfer is justified by machine unwind semantics that observes
both successful and failed exits. It is not inherited from `Prog.bind`, whose
existing refusal-strict interpretation can skip the finalizer.

## 6. Cross-domain reductions

`EC1-C07 reduceProduct` proposes only theorem-backed reductions:

1. `Progress.mustNormalExit(left)` allows a sequential right-hand must set.
2. A constant `PureExpr` guard removes the unreachable branch from every
   dimension.
3. `WorldFrame.independent(p,q)` plus an event-order quotient may permit a
   parallel commutation theorem; neither alone changes source order.
4. `Scope.escapeSet = empty` and `Resource.onRegisteredExit` imply no halted
   observation contains a live scoped resource.
5. `Control <= applicative` and every answer edge `hashDetermined` permits the
   L-A-style static-envelope analysis; applicative alone does not.
6. `Choice.deterministicGiven = {initialConfiguration, compatibleDecisionTape}`
   plus deterministic pure atoms and direct handlers permits deterministic
   executable replay; scheduler policy/state is already in the configuration.
7. `Foreign.frame = top` forces `WorldFrame` to top; another dimension cannot
   narrow it by absence of observed mutations in samples.
8. A daemon lifetime forces a root-supervisor obligation in both `ScopeDomain`
   and `ObservationDomain`.
9. An uninterruptible cycle in a reachable finalizer raises cleanup divergence
   in `ProgressDomain`.
10. `AER.E = empty` does not remove defect or interruption from `CauseDomain`.

## 7. Source/tooling evidence is a separate plane

`EC1-C08 EvidencePlane` records facts about generated or admitted source:

```text
targetIRIdentity
renderedBytesIdentity
typescriptVersion / git head / config / diagnostic result
effectTsgoVersion / platform package / upstream mapping / patch identity
diagnostic JSON / independently expected files / reported files / Effect version
codeActionSet / canonicalization result / second-pass result
structuralDecode result
negativeMutation results
compiler identity / emitted JavaScript identity
engine and host identity / normalized runtime observations
```

It is not a component of `ClassProduct` and cannot make a semantic interval
narrower. The required v1 tooling route is TypeScript 7 plus `@effect/tsgo`,
not the old standalone language-service package. The current repository
declares `typescript@7.0.2`, `@effect/tsgo@0.38.0`, and the plugin name
`@effect/language-service`; exact source/provenance for the successor tool
still needs a resolved pin before it supports a claim.

`CONTRACT-PACKET.md` owns the exact command and pass/fail verdict. This plane
records its result only when expected and reported file sets are equal, every
file reports detected/supported Effect v4, normalized JSON is byte-stable, and
diagnostic/action symbols and inserted imports resolve through the independent
public census. It cannot compute a seven-way disposition or alter
`ClassProduct` precision.

The generated `PublicSurface`/seven-disposition ledger and `SurfaceLinkView`
are recorded in this plane as frozen inputs. Joining that view to a semantic
classification report changes no abstract-domain fact.

A generated program is source-accepted only when:

1. TypeScript reports no errors under the exact project configuration;
2. Effect tsgo reports no configured error or warning;
3. the structural decoder relates the source to the expected `TsCore`;
4. configured canonicalizing code actions reach a byte-stable second pass;
5. post-action source decodes to an observationally equivalent graph; and
6. negative mutations are rejected by the expected stable diagnostic class or
   by structural admission.

The action loop also requires stable rule/action/span identity, ordered
non-overlapping edits, parse/typecheck, public-import resolution, structural
decode, canonical rerender, disappearance of the trigger without a new
unapproved result, and a zero-edit byte-identical second pass.

A clean diagnostic run is source/tooling evidence only. It does not prove the
handler semantics, `A/E/R` exactness, classifier soundness, compilation
preservation, or hosted execution.

## 8. Classification queries

The product must answer these queries without executing the program:

- Which operation/service/capability sites may occur, must occur, or occur only
  during finalization or in a child?
- What exact `Effect.Effect<A,E,R>` type should generated TypeScript expose?
- What is the least control strength justified by graph topology and dataflow?
- Which prior answers can alter later topology?
- Can the flow halt, suspend, or diverge, and what certificate supports that
  answer?
- Under what initial configuration and compatible typed decision tape is
  replay deterministic?
- Which resources are guaranteed to release after registration, in what order,
  and can cleanup itself diverge?
- Which fibers are scoped, inherited, or daemonized; which joins and
  interruptions happen before parent resumption?
- Which typed failures, defects, and interrupt causes may escape, and in what
  sequential/parallel cause shape?
- Which world frames can each phase read or write, and which parallel branches
  are independent?
- Which semantics are closed, model-backed, receipt-only, or unadmitted?
- Which canonical public rows and exactly-one source dispositions license the
  nodes, expansions, subcalculi, or boundaries used by this graph?
- Which observation mask and external pins bound the statement being made?

## 9. Mandatory counterexamples

These are required witnesses for the later classifier battery:

| ID | Status | Candidate false shortcut | Required witness |
| --- | --- | --- | --- |
| `EC1-FC01` | PENDING FALSIFIER | `may = must` for a branch | One operation in only the untaken arm. |
| `EC1-FC02` | PENDING FALSIFIER | sequence always unions must sets | Left side may fail before right entry. |
| `EC1-FC03` | PENDING FALSIFIER | `E = empty` means cannot fail | Defect and interrupted flows with empty typed row. |
| `EC1-FC04` | PENDING FALSIFIER | acyclic means applicative | Acyclic operation answer selects the next operation. |
| `EC1-FC05` | PENDING FALSIFIER | answer dependence means non-applicative | Existing hash-determined CAS `ans` dataflow. |
| `EC1-FC06` | PENDING FALSIFIER | race is commutative | Ordered public traces or tie policy distinguish swapped children. |
| `EC1-FC07` | PENDING FALSIFIER | cancellation implies prompt halt | Infinite masked finalizer retains pending interruption. |
| `EC1-FC08` | PENDING FALSIFIER | acquire implies release | Acquisition fails before finalizer registration. |
| `EC1-FC09` | PENDING FALSIFIER | a clean Effect diagnostic run admits semantics | Source uses an accepted but structurally unregistered host callback. |
| `EC1-FC10` | PENDING FALSIFIER | finite fuel establishes termination | A loop halts only after the tested fuel bound, and another never halts. |
| `EC1-FC11` | PENDING FALSIFIER | disjoint operation IDs imply independent worlds | Two different foreign operations write the same frame. |
| `EC1-FC12` | PENDING FALSIFIER | CAS core encoding may be canonical independently | Same `PProg` obtains two distinct addresses under dual encodings. |
| `EC1-FC13` | PENDING FALSIFIER | stock rc.112 preserves ordered cause topology | `CauseTree.then x y` and `CauseTree.both x y` differ fully but share the declared reason quotient. |
| `EC1-FC14` | PENDING FALSIFIER | fiber await and join have one static/effect behavior | A failed child is returned as `Exit` by await and propagated by join. |
| `EC1-FC15` | PENDING FALSIFIER | builtin handler selection adds a service requirement | A builtin operation has an empty `requirementRow` despite a direct builtin handler route. |
| `EC1-FC16` | PENDING FALSIFIER | dependence sequence is set union | A right-local answer edge needs a shifted site index after a nonempty left graph. |
| `EC1-FC17` | PENDING FALSIFIER | unioned frames imply semantic commutativity | Swapped writes have equal frame bounds but different ordered world observations. |
| `EC1-FC18` | PENDING FALSIFIER | operation occurrence equals world delta or event order | Duplicate put executes twice, changes the word once, and retains two ordered sites. |
| `EC1-FC19` | PENDING FALSIFIER | CAS envelope determines exact `E`, write addresses, or refusal word | Collision, two address functions, and equal-refusal/different-word witnesses separate all three claims. |
| `EC1-FC20` | PENDING FALSIFIER | `SemEq` implies complete classifier equality | Two run-equivalent CAS tables with distinct answer-dataflow graphs retain different D4 summaries while both remain sound. |
| `EC1-FC21` | PENDING FALSIFIER | every raw `PProg` has an injected classifier result | Empty and dangling tables fail `CasAdmissible`; only their raw CAS refusal semantics remain. |
| `EC1-FC22` | PENDING FALSIFIER | a unique later CAS result stabilizes every earlier fuel label | Two exhausted prefixes carry different labels before the same stable non-frontier outcome. |
| `EC1-FC23` | PENDING FALSIFIER | `toPProg` recognizes every graph in a CAS observational-equivalence class | Unreachable-tail and relocated-entry graphs remain equal under the selected observation but return `none`. |

## 10. Soundness target

The central requested judgment is:

```text
classify p = c
Denotes p i tr c'
---------------------------------------------
concreteClass tr c' isIn gammaProduct c
```

It decomposes into one theorem per domain and one theorem that every
cross-domain reduction preserves concretization. Exact results additionally
owe lower-bound completeness; upper-bound soundness alone may be reported only
as a conservative classification. All signatures and dependencies are listed
as PENDING in `PROOF-DAG.md`.
