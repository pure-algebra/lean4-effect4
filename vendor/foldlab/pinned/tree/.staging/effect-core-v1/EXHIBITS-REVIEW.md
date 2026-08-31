# Effect Core v1 — exhibit and classification-anchor review

Status: **PRE-GRADE / REVIEW RECORD**, 2026-08-31

Claim gate: none

Reviewed inputs:

- `.staging/effect-core-v1/exhibits.lean`;
- `.staging/agent-reports/2026-08-31-effect-core-classification-anchors.lean`;
- the current `Cas.Lang` declarations and theorem names those files import.

This review decides how the exhibits inform the staged packet. It does not
promote their scratch declarations or convert a compiled example into an
Effect Core theorem.

## 1. Verification receipt

Both files were compiled directly against the current `library/cas` project:

```text
cd library/cas
lake env lean ../../.staging/effect-core-v1/exhibits.lean
lake env lean ../../.staging/agent-reports/2026-08-31-effect-core-classification-anchors.lean
```

Both commands exited 0. `exhibits.lean` reports only `propext` and, where the
existing CAS development uses it, `Quot.sound`. The classification anchors
report no axioms for the two dataflow counterexamples; the remaining printed
theorems report `propext`, with `grade_closed_sound` also reporting
`Quot.sound`. No `sorryAx` or `Classical.choice` appeared in those receipts.

This establishes only that the displayed Lean statements elaborate and are
kernel accepted under those axioms. Their applicability is classified below.

## 2. Adopted findings from `exhibits.lean`

### E1 — reuse the existing WP/WLP logic

The EffHOL-style modality that can hold at a false postcondition for a
refusing computation aligns with the estate's existing `wlp`, while `wp`
adds totality. The exhibit proves the discriminator using:

- `wlp_bot_derivable`;
- `wp_bot_never`; and
- `wp_is_modality_and_total`.

Packet consequence: no new generic “effect modality” is introduced before a
specialization theorem relates it to `Cas.Lang.wlp` and `wp`. The existing
`WPre`, `WPost`, `Triple`, and `PartialTriple` types remain the CAS logic
owners.

### E2 — cycles require a bounded execution face

The `runBlocks` construction confirms that a first-order block graph with
back-edges cannot unfold into finite inductive `Prog` by unrestricted
recursion. Fuel-indexed execution or another guarded/coinductive boundary is
required.

Packet consequence: cyclic graph syntax is permitted; the executable runner
is fuel bounded; termination is a separately certified property. This does
not add a `diverge` syntax constructor.

### E3 — CAS injection should reuse `PProg`

The exhibit's one-block injection proves:

- projection after injection;
- syntactic equality with the existing `embed` at positive graph fuel;
- `run` agreement with `runP` at the existing exact bound; and
- `ObsEq` with the existing embedding.

Packet consequence: the promoted implementation should prove the analogous
laws using the packet's actual `RawProgram`/`CheckedProgram` types. The scratch
`GProg`, `GBlock`, and `GTerm` names are not promoted and do not become a
second graph representation.

### E4 — fuel exhaustion is a frontier, not a refusal

`exhausted_is_not_a_refusal` demonstrates that spelling graph-fuel exhaustion
as `Refusal.failed "graph: fuel exhausted"` destroys error-direction
coherence: more fuel can turn that apparent terminal error into successful
progress.

Packet consequence:

- fuel exhaustion is `Frontier.fuel` or existing `Status.running`, depending
  on the semantic face;
- it never enters `Cas.Lang.Refusal`, typed `E`, or `CauseTree`;
- an external unanswered request is `Frontier.externalRequest`;
- an unresolved scheduler/race choice is `Frontier.decision`; and
- a blocked but live fiber is `Frontier.blocked` with its wait reason.

These are observations of an incomplete finite prefix. They say nothing
terminal about the program.

### E5 — first-order child code can use ordinary signatures and handlers

The `Scoped` section typechecks body/finalizer/handler references as
`BlockId`s in an ordinary `Sig`, interpreted by an ordinary `Handler` into a
reader over `Prog`. This is useful representation evidence: opaque higher-order
host callbacks are not required in stored syntax.

Packet consequence: start with the existing `Sig`, `Handler`, `Handler.sum`,
and `Handler.through`. `Handler.sum` is same-target family composition;
`Handler.through` is used only for an upper `Handler S (Prog T)` followed by a
lower `Handler T M`, not to retarget a scoped handler already aimed at its
machine. Introduce no higher-order handler carrier merely to pass named child
blocks. A recovering catch or exit-aware finalizer may require a richer
existing target-monad stack or the reference machine state, but not a new
`HHandler` type: the handler still receives a first-order operation whose
children are code IDs.

### E6 — select `PProg` as each block's sequential body

The useful economy is not “no graph”; arbitrary branches, calls, cycles,
regions, and fibers still need a first-order graph. It is “no second
straight-line language inside the graph.” A selected block contains:

```text
typed parameters + owning region + body : PProg + terminator : Term
```

Pure edge arguments remain outside the effect body. `PProg` keeps its current
canonical identity and existing embedding/runner/classifier facts. The graph
adds only the control and ownership structure `PProg` cannot express.

The self-contained `workshop/EffectCoreProbe.lean` takes the alternate ANF
body branch. It remains useful evidence that raw/check/summary records are
easy to express, but its `RawTerm.perform` sequence is not the selected body
representation and none of its duplicate type names is promoted.

## 3. Boundaries and rejected extrapolations from `exhibits.lean`

### X1 — its denotation is deterministic only for its deterministic fragment

`Denotes` is an existential over successful fuel approximants, and
`denotes_unique` proves a partial-function result. This is correct for the
exhibit's CAS/block language under fixed `H`: it contains no handler-answer
choice, external request, scheduler choice, clock/random choice, fork, race,
or competing finalization.

It is not the denotation of arbitrary Effect Core programs. Promoting the
uniqueness theorem globally would erase the exact behaviors the operator asked
to model. Conversely, this does not require a public `Behavior` datatype. The
full meaning is a judgment/relation over existing programs, configurations,
typed decision streams, and finite observations:

```text
Runs p initial decisions observation : Prop
Denotes p initial observation := exists decisions, Runs p initial decisions observation
```

`FinApprox` is the finite executable observation carrier used to calculate and
check bounded prefixes; it is not a second semantic program language.

The full rule is:

```text
fixed initial configuration (including scheduler policy/state)
  + one complete typed decision tape (including replies/scheduler/ties)
  -> executable replay is deterministic

without those fixed decisions
  -> Step and Denotation retain all admitted branches
```

The deterministic CAS fragment receives a specialization theorem from the
general denotation; it does not select the general carrier.

### X2 — big-step refinement is not the whole semantic triangle

The exhibit correctly uses `interpretRef_bind` because fixed-fuel `run` has no
general composition law. Its `Refines` relation, however, observes successful
big-step results only. It does not preserve refusal payloads, partial refusal
words, suspension, external frontiers, schedule branches, resources, fiber
lifecycle, or cause provenance.

Packet consequence: retain this refinement as a CAS success observation. The
general triangle still relates:

- executable decision-indexed steps;
- a relational labeled transition system; and
- coherent finite observation trees.

### X3 — the scoped handler is a type-shape prototype, not semantics

The scratch `scopeHandler`:

- ignores the catch handler block;
- runs an ensuring finalizer only after normal success;
- does not register resources or combine failures;
- gives `scoped` no ownership/finalization behavior;
- gives `provide` no environment change; and
- models raise through free-form CAS failure.

None of the packet's catch, scope, finalizer, cause, or provision laws follows
from it. Only the “ordinary Handler can receive named blocks” result is
adopted.

### X4 — no scratch public type is promoted by name

The following are local witnesses only: `GTerm`, `GBlock`, `GProg`,
`ScopeE`, `ScopeSig`, `Env`, `ScopeM`, `Grade`, `Denotes`, `Refines`, `Hlen`,
`Hconst`, `zero`, and `far`. Their useful facts map onto packet types and
existing declarations through `TYPE-CLOSURE.md`. Creating public versions
under new names without that mapping is a duplicate-type gate failure.

## 4. Proper nondeterminism model

### 4.1 Sources are explicit

The full model distinguishes these decision sources:

| Source | Relational representation | Executable representation |
| --- | --- | --- |
| pure input/guard | fixed value and pure evaluation | no decision token |
| direct-handler answer | one `Step` branch per admitted answer/outcome | typed answer token |
| registered foreign reply | symbolic request frontier then admitted reply branch | receipt/reply token |
| scheduler | one branch per enabled fiber under policy | schedule token |
| race tie | policy-labeled winner branch | tie token |
| clock/random | handler-state transition and returned sample | handler/tape token |
| interruption arrival | labeled environment event | interrupt token |
| replay | selected recorded branch | fixed recorded token |

Nothing uses implicit host nondeterminism. Every executable choice has a typed
token and every relational branch has a label.

### 4.2 Finite approximations preserve branching

`FinApprox n` is a finite-support observation tree produced from one initial
configuration to depth `n`. Leaves are:

```text
halt     (Exit E A)
frontier (fuel | externalRequest | decision | blocked)
```

Internal nodes record labeled semantic steps or explicit choices. An answer
type may be infinite; the tree retains one symbolic request frontier rather
than enumerating all possible replies. “Finite” refers to the produced tree's
support/size, not to the Lean type having finitely many inhabitants.

### 4.3 May/must and determinism are separate facts

- `may` is the union of facts across admitted branches.
- `must` is the intersection plus facts occurring before every branch point.
- `deterministicGiven` records the decision interface sufficient to select one
  branch.
- fairness is absent from safety theorems and named only for liveness.
- a fixed initial configuration plus complete compatible decision tape yields
  a replay theorem; it does not collapse the
  relational semantics to a function.

There is deliberately no global `denotes_unique`. The admissible uniqueness
boundaries are relational agreement under one fixed compatible decision tape;
the ask-free specialization only when every reachable `Decision` is proved
subsingleton, excluding every other choice source; and the stronger stable
non-frontier deterministic CAS specialization. The workshop
`denotes_unique_on_the_askFree_fragment` supports only its ask-only fragment,
not unqualified ask-free full-core execution.

## 5. Refusal-kind classification without duplicate error types

### 5.1 Existing CAS classification is reused

The CAS runtime already has the exact refusal-kind carrier and host join:

- `Cas.Lang.Refusal` — payload-bearing runtime terminal;
- `Cas.Lang.Refusal.Clause` — six constructor kinds;
- `Refusal.clause` and `Refusal.clause_surjective`;
- `Refusal.admissionClauses`;
- `CasErrorTag` and `Refusal.Clause.hosts`;
- `RefusalMap.table` and its table-agreement/completeness theorems.

Effect Core v1 does not mint `CasRefusalKind`, copy the six constructors into
`CauseTree`, or hand-maintain a second host map. CAS classification references
`Refusal.Clause` directly and the CAS embedding maps the payload-bearing
`Refusal` into the declared Effect Core exit policy.

### 5.2 Boundary classes remain separate

“Refused” is not a universal program outcome. The project retains the owner at
each boundary:

| Boundary | Existing/proposed owner | Classification | Explicitly not |
| --- | --- | --- | --- |
| raw graph admission | `Diagnostic` / `ProgramWF` | checker rejection before a checked value exists | runtime failure |
| pinned source/profile admission | surface/profile refusal code | construct structurally inventoried but this form not admitted | omission from census |
| CAS execution | existing `Refusal` and `Refusal.Clause` | terminal CAS refusal | fuel exhaustion or typed Effect failure |
| typed program failure | `CauseTree.fail E` | typed semantic exit | checker refusal |
| defect/interruption | `CauseTree.die` / `.interrupt` | semantic cause outside `E` | CAS refusal kind |
| incomplete execution | `Frontier` or existing `Status.running` | live finite prefix | refusal, cause, or halt |
| TypeScript/LSP/structural target | diagnostics and `AcceptedTs` failure | source/tool evidence rejection | Semantic Model outcome |
| foreign contract | operation-specific typed error/defect or admission refusal | follows registered schema and policy | arbitrary host exception smuggled into CAS `failed` |

A future cross-boundary report may define a view indexed by boundary, but it
must point to these carriers. It must not become a universal error sum that
loses each owner's payload and laws.

## 6. Adopted findings from the classification anchors

### A1 — dependence sequencing reindexes

`PProg.dataflow` uses absolute line indices. For sequential table composition,
right-side sites must be shifted by the left length; union or raw append is
incorrect. The general `DependenceDomain.seq` therefore uses explicit
code-point renaming/substitution and proves alpha/offset invariance.

### A2 — operation footprint, world frame/delta, and order are different

The anchors show:

- put operations may execute without adding a binding because of duplicate
  content;
- write addresses depend on `H`, while the static envelope holds write
  shapes; and
- reordering puts can change the observed word.

Consequences:

- D1 records operations that may/must execute;
- D2 records read/write lenses, shapes, allocation potential, and conditional
  world deltas;
- D10 and the observation domain retain happens-before and word order.

A commutative union of frame *sets* is allowed only as a conservative D2
upper abstraction. It never establishes program equivalence or erases D10
order. The anchor refutes exactness/commutation, not the use of a safe upper
bound.

### A3 — `A/E/R` does not come from the CAS envelope

The envelope cannot rule out collision or every other refusal. Exact static
rows come from checked `OpDesc` transforms, handler discharge, and control
flow. The CAS bridge separately classifies existing refusals and must not
claim that `Envelope` decides `E`.

### A4 — refusal observations must name the partial-word mask

Existing `ObsEq` observes success result/word and refusal value without the
partial refusal word. The general full mask includes the partial world and the
CAS specialization states when it intentionally projects that component away.
Two programs can therefore be `ObsEq`-related while leaving different partial
words on refusal; this is an explicit quotient, not a contradiction.

### A5 — reification grade must be a live, total classifier

The scratch L-A `Grade` fold is constantly closed because every `PLine` is a
CAS operation. This is a useful positive control, not a useful general
classifier. The general reification/profile classification is total over the
generated `SurfaceRowKey` universe and gains information only when the
alphabet/profile carrier admits another family.

## 7. Packet actions

Before the packet can be frozen again:

1. `CLASSIFICATION.md` must state reindexing for dependence sequencing and
   distinguish operation, frame/delta, and temporal order transfers.
2. `ALGEBRA.md` and `CONTRACT-PACKET.md` must classify fuel/external/scheduler
   frontiers outside refusal/cause.
3. `PROOF-DAG.md` must reuse `Refusal.Clause` for the CAS bridge and state
   fixed-decision versus relational nondeterminism theorems separately.
4. CAS injection must target the packet's one graph representation, not
   promote `GProg`.
5. Scope/catch/finalizer proofs must use the reference machine, not the scratch
   `scopeHandler` clauses.
6. `TYPE-CLOSURE.md` must make every adopted existing type and proposed type's
   bridge edges visible before cutover.

The exhibits are therefore valuable: they close several representation
questions and supply counterexamples. They do not eliminate the need for the
general nondeterministic denotation or the per-type proof graph.
