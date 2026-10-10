# What `Effects` claims, and what it does not

Status: adopted with slice S1 of the split, 2026-09-02. This document is the
repair for findings R1 and R3 of the lean4-effect4 review of 2026-09-02. It
fixes the boundary before the algebra modules arrive in S2, so that no
consumer reads more into a shared signature than the theorems state.

## Claimed

Every claim is a kernel-checked theorem over the structural carrier. Equality
of programs is Lean's structural equality of the inductive `Program`; there
is no behavioural quotient.

| Claim | Statement family | Hypotheses |
| --- | --- | --- |
| Constructor equations | `pure` and `vis` are the defining equations of `Program`; `bind` computes by structural recursion | none |
| Monad laws | `Program S` is a `LawfulMonad` | none |
| Interpretation | `interpret h` is the monad homomorphism induced by handler `h`; `interpret_pure`, `interpret_vis`, `interpret_perform`, `interpret_bind` | the target monad's left unit and associativity, or `LawfulMonad` in the convenience forms |
| Identity | `interpret identityHandler` is the identity; programs equal under every interpretation are equal | none |
| Sums | `Handler.sum` is characterised by its two projections and is unique; `Program.inl`/`inr` are injective monad morphisms; injection handlers compose to the identity | none beyond the sum's shared answer universe |
| Freeness and initiality | a monad morphism out of `Program S` that agrees with a handler on every one-operation program is `interpret` of that handler; `Program S` is initial among monads equipped with an `S`-handler | the target's monad equations, stated per theorem |
| Interpreter pin | the conjunction of pure/bind preservation and operation agreement pins the interpreter; neither half alone does | as above; the two halves are attacked by `E4-ALG-CE-002` and `003` |
| Towers | `Handler.through` composes across signatures; it is associative and unital; a monoid exists only on endomorphisms `Handler S (Program S)` | left unit and associativity of the bottom target |

## Not claimed

- **No equations on a signature.** `Signature` has operations and answer
  types. A standard's state invariants, operation equations, commutation of
  independent operations, scheduling behaviour, or trace relations are not
  carried by the signature and are not implied by `Signature.sum`. A sum
  supplies disjoint operations, nothing more.
- **No theorem transfer between handlers.** Two handlers for one signature
  are two models. A theorem proved about a program under one handler holds
  under another only if the theorem's hypotheses hold for that handler too.
  "Both are handlers for the same signature" is not such a hypothesis.
  Law satisfaction by an implementation, and conformance of a host to a
  standard's corpus, are separate downstream records with their own
  assumptions.
- **No behavioural equivalence.** The library proves structural equalities
  and equalities after interpretation into a stated target. It does not
  define bisimilarity, trace equivalence, or a quotient by any such relation,
  and it makes no congruence claim for one.
- **No serialization or identity.** `Program` stores Lean continuations. It
  is not stored program syntax, has no content hash or decidable equality,
  and is not the carrier for cycles, sharing, or block references
  (`E4-ALG-CE-007`). A first-order representation is a downstream carrier
  with its own embedding theorem.
- **No bounded-runner composition.** A fixed-fuel evaluator receives no bind
  law here (`E4-ALG-CE-006`). Composition is stated at `interpret`.
- **No finiteness.** `Program` is well-founded on every selected branch; it
  need not have finitely many nodes or a uniform depth bound
  (`E4-ALG-CE-008`).
- **No implicit universe lift.** An explicit signature map or universe lift
  is a separate packet with its own coherence laws.
- **No host correspondence.** Nothing here relates a program to a runtime,
  a generated artifact, or a test corpus.

## Where the rest lives

| Concern | Owner |
| --- | --- |
| Operation laws and observation relations for a particular standard | that standard's library, stated over its interpretation |
| State transport through a tower, explicit signature maps | `Effects.Experimental`, an opt-in root with receipts but no contract; the ruling is in "v0.8.0" below |
| First-order flow, relational semantics, logic, realizers, targets | lean4-effect4 and the standard libraries |
| Host admission and conformance | the consumer's host-profile records |

## Axiom admissions

The ceiling for every declaration under `Effects/` and `EffectsTest/` is
`propext` and `Quot.sound`. `Classical.choice` is admitted in exactly two
modules, both the gate's own implementation: `EffectsTest.Audit.AxiomGate`,
because `MetaM` reaches it, and `EffectsTest.Audit.Axioms` (v0.9.0), the exact
axiom walk the gate reads axioms with, whose hash maps over the environment
reach it. There are no declaration-level admissions. A new admission is
recorded here first and in the gate second, and the gate fails if the
admission goes stale.

## v0.2.0 additions

Three generic packets and one move, stood up 2026-09-02 ahead of their
contract packets (the proofs are the one-induction shapes the algebra
already uses; batteries follow):

- `Effects/Morphism.lean`: `Signature.Hom`, `Program.map`, `Handler.pull`,
  `interpret_map`, the sum isomorphisms and `Signature.empty`. The row normal
  form of a requirement set. **Moved at v0.8.0** to
  `Effects/Experimental/Morphism.lean`; see "v0.8.0" below for the ruling.
- `Effects/Transport.lean`: `MonadHom`, `Handler.mapHom`, `interpret_mapHom`,
  `interpretHom`, `through = mapHom (interpretHom ·)` by `rfl`, `MonadHom.stateT`.
  State transport through a tower. **Moved at v0.8.0** to
  `Effects/Experimental/Transport.lean`; see "v0.8.0" below.
- `Effects/Family.lean`: `Family`, `Family.toSignature`, `Family.Service` and
  its round trip with `Handler`, `Alphabet` and `Alphabet.toFamily`. The
  first-order carrier's embedding that the boundary above promised downstream.
- `Effects/Flow/*`: the generic first-order flow and its checked admission,
  moved from lean4-effect4 `de3e2ec` with only the namespace changed.

The claims of the nine algebra modules are unchanged; `generated/algebra-parity.tsv`
still holds.

## v0.3.0: the trace alphabet

`Effects/Trace.lean` adds one service-level observation vocabulary
(`Trace.Event`: operation with request and answer, failure, decision, region
entry and exit, finalizer with its outcome, outcome, frontier), masks as
projections (`m1` keeps operations, answers, failures and the outcome; `m2`
keeps everything), and `Family.Service.traced`, an around-wrapper that logs
each method's request and answer. Its law is `interpret_traced_fst`:
forgetting the log recovers the plain interpretation. Packet:
`test/contracts/trace.contract.md`; attacks `EF-TRACE-CE-001..003`.

v0.3.1 adds `Family.Service.tracedExcept` for the aborting error reading (a
service into `ExceptT ε M`, log outside the error) with the same projection
law, `interpret_tracedExcept_fst`.

Not claimed: any relation between a trace and a host, a frame machine, or a
scheduler; any behavioural equivalence. Agreement between two emitters of this
alphabet is a downstream, executable judgment under a named mask, and it is
stated in lean4-effect4 (`docs/TRACE-DAG.md`), never here. The module
traverses no `String`; rendering a trace to a wire form is a consumer's
admission.

## v0.4.0: first-order flows with block parameters

`Effects/Flow/{Block,Raw,Admission,Checked}.lean` re-freeze the flow admission
packet (`test/contracts/flow-v2.contract.md`, superseding the v1
`flow-admission` packet moved here in v0.2.0). A block now declares a
parameter list; a terminator names its operands by position (`Var`); `jump`
and `choose` pass argument lists; `perform` passes its arguments plus the
operation's answer. Admission has seventeen ordered clauses *at this bump*:
the thirteen v1 clauses (operand typing is now `termTypeMismatch`) and
`unknownVariable`, `argumentArity`, `argumentTypeMismatch`, `unchosenCycle`.
(v0.7.0 makes it eighteen and v0.8.0 nineteen; the live count is in the
v0.8.0 section below and the live pin is
`EffectsTest/Flow/FlowV3Contract.lean`.) The last is the one
global clause: every cycle of the successor graph passes through a `choose`
(`CyclesWF`), decided by the kernel-computable `cyclesChoose` with its law
`cyclesChoose_iff`, so a finite decision tape bounds every run of an admitted
flow. Retained: `admit_sound`, `admit_complete`, `error_iff_not_wf`,
`error_iff_firstDiagnostic`, `admit_error_valid`, `diagnoseAt_some_valid`,
`FirstDiagnostic.valid` and `condemns`, `clause_all_complete`, the erase laws,
and `FlowWF.reachable_declared`. Attacks `EF-FLOW-CE-001..003`
(`test/counterexamples/flow/ATTACKS.md`). Sixteen named theorems have axiom
receipts in `EffectsTest/Flow/FlowV2AxiomReport.lean`; the union is
`propext` and `Quot.sound` (`reachable_declared`, `erase_wf`,
`CheckedFlow.erase_eq_raw`, and `CheckedFlow.ext` need only `propext`).

Not claimed: any run of a flow (the runner, its frontier, and the decision
tape live in lean4-effect4); regions and finalizers (a later bump); any
relation between a flow and a program, a trace, or a host.

## v0.5.0: regions over first-order flows

`Effects/Flow/Region.lean` adds a region layer that erases to Flow v2
(`RegionFlow.erase`): `enter` opens a region, `acquire` performs and registers
a release for its answer in the innermost region, `leave` closes the innermost
region with a value and control continues at the region's `continue_` block.
Fourteen region clauses (`RegionFlow.check`, first failure) check what erasure
forgets: region ownership of every block, the shape of every `enter`,
`acquire` and `leave`, and that no `ret` skips a region; `admitRegions` runs
them and then v2 on the erasure, and `CheckedRegionFlow` carries both proofs.
Packet: `test/contracts/flow-regions.contract.md`; attacks `EF-FLOW-CE-004..006`.

Not claimed: any run of a region flow, the order and the exits its releases
observe, or any relation to a host scope; those are lean4-effect4's
(`docs/TRACE-DAG.md`, packet P-T7). The v0.4.0 surface is unchanged.

## v0.6.0: the trace alphabet re-frozen with `Outcome.defect`

`Effects/Trace.lean` widens `Trace.Outcome` by one constructor,
`defect (error : υ)`: a host defect (an rc.112 `Die`), distinct from
`failure`, which is the program's own typed error channel. It also adds
`Outcome.map`, a payload re-encoding with independent payload universes and no
`ToVal` in its signature, with `Outcome.map_id` and `Outcome.map_comp` (both
axiom-free). Packet: `test/contracts/trace.contract.md`, re-frozen with a
version note; attack `EF-TRACE-CE-004`, "a defect rendered as a failure".

`Trace.Event` and `Trace.Mask` are unchanged in shape, and every v0.3.x law is
retained with the same proposition and the same proof: `Mask.keeps` matches on
an event's *kind* and never on the outcome an event carries, so `Mask.m2_keeps`,
`project_project`, `project_m2`, `project_m1_m2` and `agree_of_agree_m2` are
untouched, and `Handler.Projects`, `interpret_projects_fst`,
`Family.Service.traced_projects`, `Family.Service.interpret_traced_fst`,
`Family.Service.traced_perform`, `Handler.ProjectsExcept`,
`interpret_projectsExcept_fst`, `Family.Service.tracedExcept_projects` and
`Family.Service.interpret_tracedExcept_fst` never mention `Outcome` at all.
`EffectsTest/Trace/TraceContract.lean` carries the executable receipt that
every mask in the packet keeps and drops `done`, `leave` and `finalizer`
identically for all four outcomes.

Not claimed: any producer for `defect` or `interrupted`. Nothing in this
library constructs either constructor; the traced services emit `op`, `answer`
and `failed` rows only, and the outcomes carried by `done`, `leave` and
`finalizer` are supplied by a caller. `defect` and `interrupted` are produced
only by runners and bridges downstream (lean4-effect4's flow and region
runners, and the host bridge in `Effect4/Target/TypeScript/Simulation.lean`),
and this bump claims nothing about when either is correct to emit. In
particular v0.6.0 adds no around-wrapper producing `Outcome.interrupted`. The
v0.4.0 and v0.5.0 flow surfaces are unchanged, and the nine algebra modules
are unchanged.

## v0.7.0: Flow v3, caught failures and value branches

`Effects/Flow/{Block,Raw,Admission}.lean` add two terminators and one
admission clause (`test/contracts/flow-v3.contract.md`, superseding the
terminator list and the two edge clauses of `flow-v2.contract.md`).

`performCatch operation request target args onError errorArgs` is a `perform`
with a failure successor: `successors` is `[target, onError]`, the value edge
receives `args ++ [answer]` and the failure edge `errorArgs ++ [error]`. The
two edges therefore carry different lists and different arities, so
`RawTerm.argsAt` and `RawTerm.arityAt` are keyed by the edge's position in
`successors`, and `ArityWF`, `SlotWF`, `ArgumentsWF` and the clauses
`argumentArity` and `argumentTypeMismatch` are stated over that index. The
value edge keeps `args` and `arity`, and four `rfl` laws (`argsAt_zero`,
`arityAt_zero`, `argsAt_of_ne_one`, `arityAt_of_ne_one`) make "every v2 shape
reads as it did" a theorem. `FlowAlphabet` gains `errorTy : Op → Ty`, the
type of the value bound in the failure successor's last slot.

`branch test site onTrue onFalse args` is taken by the *value* of `test` and
is still a decision *site*: `isChoose` is true for it and `decision?` names
`site`, so `CyclesWF` counts a branch loop, `duplicateDecisionId` sees its
site, and the v0.4.0 tape bound survives verbatim. `FlowAlphabet` gains
`boolTy : Ty`, the spelling the test operand must carry, checked by the one
clause v3 adds: `branchTestType`, between `termTypeMismatch` and
`unknownVariable`, making eighteen ordered clauses. `TermsWF` is five-fold
(`BranchTestWF` is the fifth). `TermFailureValid` gains
`performCatchRequestTypeMismatch` and `ArgumentFailureValid` gains
`catchAnswer` and `catchError`, which type the answer slot and the error slot
apart.

Every v0.4.0 theorem is retained with its proposition and re-proved over the
wider carrier: `admit_sound`, `admit_complete`, `error_iff_not_wf`,
`error_iff_firstDiagnostic`, `admit_error_valid`, `diagnoseAt_some_valid`,
`FirstDiagnostic.valid` and `condemns`, `clause_all_complete` (now eighteen
clauses), the erase laws, `FlowWF.reachable_declared`, and `cyclesChoose_iff`.
The v0.5.0 region layer is unchanged and needs no new rule: it reads
terminators through `RawTerm.successors`, so a `performCatch`'s failure edge
is required to carry the block's own label like any other successor. Attacks
`EF-FLOW-CE-007` (a caught failure unwinds regions) and `EF-FLOW-CE-008` (a
branch on a value escapes the tape bound).

Not claimed: any run. That a `performCatch` continues at its value successor
on `.ok` and at its failure successor on `.error`, that its trace is `op` then
`failed` then the successor's rows and never `done failure`, that a caught
failure does not unwind a region, and that a `branch` reads the tape entry at
its site and refuses a run whose tape disagrees with the tested value are the
design intent this carrier is shaped for and are theorems of lean4-effect4's
runner and denotation, never of this library. Nor is any error algebra
claimed: `errorTy` is one type per operation, never read except to compare,
with no empty type, no error sum, and no relation to a host error; nor any
boolean semantics for `boolTy`, which is a spelling in the consumer's own
`Ty` with no inhabitant count and no exhaustiveness claim for the two
successors. The nine algebra modules, the trace alphabet, and the v0.5.0
region surface are unchanged.

## v0.8.0: the consumer boundary

A release about what the package *shows*, not about a new semantic layer. It
answers findings #36, #38, #39, #40, #42, #43, #44, #45, #46, #48 and #49 of
lean4-effect4's `docs/research/2026-09-03-survey-lean-core.md`. Packet:
`test/contracts/effects-boundary.contract.md`; battery
`EffectsTest/Flow/BoundaryContract.lean`; attacks `EF-FLOW-CE-009` and
`EF-FLOW-CE-010`; full downstream migration in `docs/RELEASE-v0.8.0.md`.

### One new claim

`FlowAlphabet.errorTy` is `Op → Option Ty`, and admission gains a nineteenth
ordered clause, `catchUnfailable`: a `performCatch` names an operation whose
declared error type is `some`. It sits between `branchTestType` and
`unknownVariable`. `TermsWF` is six-fold (`CatchableWF` is the sixth), `FlowWF`
keeps its eight fields, `SlotWF`'s error arm compares only when `errorTy` is
`some`, and every retained theorem holds with its proposition, including
`clause_all_complete` over nineteen clauses.

This is the repair for a claim that was weaker than it read. The v0.7.0
`errorTy : Op → Ty` asked an operation that cannot fail to declare "the
alphabet's own empty spelling" — a convention `Ty`, a code type with no
emptiness predicate, cannot express, and one an alphabet could satisfy with
`errorTy op = answerTy op`. `EF-FLOW-CE-010` is the witness.

Still not claimed, exactly as in v0.7.0: no error algebra. `errorTy` is one
type per operation, never read except to compare; `catchUnfailable` asks only
whether there *is* one. No empty type, no error sum, no subtyping, no relation
to a host error, and no execution semantics for a catch.

### One clause repaired

`acquireRelease` now fires whenever `alphabet.lookup release = none`, whatever
the acquired operation is (`EF-FLOW-CE-009`). Erasure drops the release, so no
v2 clause can see it; keying the arm on the acquired operation let an unknown
release surface only on a second round. `admitRegions` admits exactly what it
admitted before.

### `RegionWF` is a structure

Fourteen fields, one per `RegionClause`, with `regionWF_iff_check` proving the
checker decides exactly them — the region layer's counterpart of
`flowWF_iff_clauses`. It used to be `flow.check alphabet = none`, a statement
about a program rather than about a flow. `CheckedRegionFlow` and
`admitRegions` are unchanged in type.

### Ruling: `Effects.Experimental`

`Effects/Morphism.lean` and `Effects/Transport.lean` move to
`Effects/Experimental/{Morphism,Transport}.lean` behind
`Effects/Experimental.lean`, a root that **`import Effects` does not pull in**.
This is the one place the ruling is stated; `Effects/Experimental.lean`,
`docs/ALGEBRA-DAG.md` and the v0.2.0 section above point here and do not
restate it.

What "experimental" commits this package to:

- The declarations keep the `Effects` namespace, so `handler.mapHom`,
  `handler.pull` and `program.map` still resolve by dot notation. Only the
  module path and the import changed.
- They are inside the axiom ceiling like everything else, and
  `EffectsTest/Experimental/AxiomReport.lean` is the receipt. A consumer who
  opts in is not opting into a weaker trust boundary.
- The trust gate reaches them: the test root imports the report, so the
  module-closure check still covers both files.

What it does not commit to:

- **No frozen surface.** There is no contract packet and no battery. Names,
  argument order and universes may change in a minor bump without a
  supersession note, which is exactly what the other packets promise not to do.
- **No claim beyond the stated theorems.** `interpret_map`, `Program.map_id`,
  `Program.map_comp`, `interpret_mapHom` and `through_eq_mapHom` are what is
  proved. Nothing here says a signature morphism preserves any operation law,
  that a requirement row has a normal form, or that `MonadHom.stateT` is the
  state transport a consumer's tower wants.

They were stood up at v0.2.0 "ahead of their contract packets … batteries
follow". The batteries did not follow, and three documents disagreed about
whether the modules existed. The honest reading is that they are an unfinished
generic packet with no library consumer, so they are labelled rather than
quietly shipped as part of a frozen surface. Writing their contract and
battery would retire the label and move them back.

### Boundary changes with no new claim

- `Effects/ListAux.lean` publishes `length_filter_ne` and
  `length_le_of_nodup_subset`, generic in `α`. `RawFlow`'s saturation
  scaffolding — `insertAll`, `expand`, `saturate`, `allSuccessors` and their
  thirteen lemmas — becomes `private`, and `nodup_reachSet` and
  `reachSet_length_lt_of_edge` are the public conclusions that replace it.
- `reachableNoChoose_trans`, `lookupBlock_id`, `mem_blockIds_of_lookup` and
  `FlowAlphabet.toAlphabet`/`toFamily` move up from lean4-effect4, which had
  been declaring the last of them into this package's own root namespace.
- `Diagnostic.diagnoseAll` reports every failing clause, with
  `diagnoseAll_eq_nil_iff` and `diagnoseAll_valid`. `admit` is unchanged and
  remains the boundary; this is a report, not a second admission path.
- `RegionFlow.checkBlock.checkTerm` is gone: `checkTerm` is a named definition.
  The `RegionWF` fields are the supported replacement for unfolding it.
- Axiom receipts now cover Flow v3, the regions, `Family` and the experimental
  root — twelve exported theorems that had none.
- The library compiles with `autoImplicit` and `relaxedAutoImplicit` off, and
  the axiom gate refuses the same trust tokens lean4-effect4's does.

The nine algebra modules, the trace alphabet, and the flow v3 carrier apart
from `errorTy` are unchanged.

## v0.9.0: the coalgebra layer

The algebra's dual, for consumers that compare a machine or a session with a program's meaning.
Packet: `test/contracts/coalgebra.contract.md`; battery
`EffectsTest/Coalgebra/CoalgebraContract.lean`; attacks `EF-COALG-CE-001` to `EF-COALG-CE-004`.

### New claims

Systems as coalgebras of one step, read through finite unfoldings; bisimulations and simulations
with the unfolding theorems; hosts as comodels, with routing, sharing, renaming, implementation
by programs over another signature, admission, reply tapes and recording, each with its law at
`run`; first-order protocols and meeting; runs of systems against hosts, with
`Program.run_of_sim_program`: one simulation of a system by a program gives agreement against
every host. The packet's ENSURES list states each.

### Not claimed

No coinductive types or equality of infinite behaviours; no fairness, liveness or progress; no
host with effects beyond `Option` failure; no indexed signatures or promises (planned for
v0.10.0); nothing about a concrete machine, session or runtime.

### Promotions

`Signature.Hom`, `Program.map`, `Handler.pull`, `interpret_map`, `Program.map_id` and
`Program.map_comp` move from the opt-in `Effects.Experimental.Morphism` to `Effects.Lens`, under
the coalgebra packet, with their names unchanged. The sum isomorphisms stay experimental.

### The gate

The gate reads axioms with the exact walk (`EffectsTest/Audit/Axioms.lean`), backported from
lean4-effect4 on 2026-10-09: Lean 4.33's `collectAxioms` caches short answers inside dependency
cycles, and it did not read an axiom's type in the walk the gate replaces. Controls:
`EffectsTest/Audit/AxiomWalk.lean`. The walk module is the second admitted `Classical.choice`
module (section "Axiom admissions").

## v0.9.1: typed programs and handlers

An addition to the coalgebra layer: `Effects/Coalgebra/Sat.lean`. Packet: the coalgebra packet,
ENSURES 8 to 11; attack `EF-COALG-CE-005`.

### New claims

A program is typed under a protocol into a postcondition (`Program.Sat`), by structure on the
tree, and the typing is sound for every host that meets the protocol. A handler is typed from an
upper protocol to a lower one when each implementation is typed into the upper protocol's
admission. Typed handlers take typed programs to typed programs, compose, and make a host that
meets the lower protocol meet the upper one. So a stack of layers, each checked against its two
protocols, needs only a host at its foot that meets the last protocol.

### Not claimed

No converse of soundness; nothing of a program that does not finish; no protocol whose answers
open operations. The nine algebra modules are unchanged.

## v0.10.0: indexed signatures

`Effects/Coalgebra/Indexed.lean`: protocols of a higher order, where an answer can open
operations. Packet: the coalgebra packet, ENSURES 12 to 14; attack `EF-COALG-CE-006`.

### New claims

An indexed signature has worlds, the operations each world offers, their answers, and the world
after each answer. Its programs end with a value whose type depends on the final world; its
hosts answer each world's operations from a state; a run returns the final world, the value and
the state. Its protocols type its programs, soundly for every host that meets them. A
first-order signature is the one-world case, and programs and runs embed exactly. The battery's
promise signature shows the higher order: an await's answer type is the code its promise
recorded when it opened.

### Not claimed

No indexed systems, bisimulations or handlers; no host state indexed by the world; no fairness or
progress of a promise. The nine algebra modules are unchanged.
