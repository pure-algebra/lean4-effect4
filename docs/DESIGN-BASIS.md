# Effect4 design basis

Effect4 adopts one well-founded algebraic proof carrier, one checked first-order
reification, relational semantics for open effect flow, and separately gated
host targets. This separation is the basis for the library; the cited
literature motivates its interfaces but does not prove that Effect4 models
Effect TypeScript or any host runtime.

Status: decision record begun 2026-08-31; refreshed 2026-10-01 at `dceae006` (the DESIGN-BASIS
refresh, seat H of the 2026-10-01 landing; receipt
`docs/research/2026-10-01-design-basis-refresh/receipt.md`) and re-pinned at `6b3f2c92`, DB-16
re-read there (decisions row 154; receipt
`docs/research/2026-10-01-design-basis-refresh/receipt-H2.md`). This file owns settled decisions,
their rationale and dated evidence receipts. It owns no live status: a row's status is a link to
the system map's §8 (`docs/core/system-map.md`), which alone owns the status of the
requirements; open decisions live in `docs/core/decisions.md` and `docs/DESIGN-ISSUES.md`. The
program syntax is `Eff` (`src/Effect4/Program/Eff.lean`); the Flow route of DB-02 is history.

## How to read a row

Every row ends in six fields.

- **Decision**: what is decided, in today's names.
- **Witnesses**: theorems with `file:line` at the commit the status line names; a test is named as a
  test, a finite probe as a probe. A theorem a research probe proved and the tree does not hold yet
  is written "witness missing at `6b3f2c92`", with the probe and the seat that proved it.
- **Refusals**: the register ids (`Test/Counterexamples/REGISTER.md` and its archive) and the DI
  numbers the decision rests on.
- **Sources**: research notes by path and section, each marked *tracked* or *untracked*.
- **Literature**: each paper marked *read* (with the note that records the reading), *by name*, or
  *assumed*. The bibliography at the end lists each paper once, with the same mark.
- **Status**: "see system map §8, Rn" or "settled", and the commit at which the witnesses were last
  re-read. No proof or workstream status is restated in a row.

Evidence words. **Proved** is said only of a theorem declared in the tree (or in the pinned
`effects` package) whose statement the last refresh re-read at the stated commit; the kernel
check behind it is the trust gate's, at `[propext, Quot.sound]` (the refresh ran no build). A
`ProofGraph.Obligation` declaration is a declared statement, not a proof, and is called
*declared*. A theorem proved in a research probe keeps the voice of the seat that proved it.
**Tested** is a finite check, **reading** a reading of code or notes, **assumed** not checked.
"Proved" is never said of a paper.

Paths and commits. Tree paths are from the repository root, with lines at `6b3f2c92`, where
decisions row 154 re-pinned them from `dceae006`; a cited line in a file that changed since may have
moved, and this refresh's checker prints where its text sits at a later commit
(`check_citations.py --drift <rev>`, in `docs/research/2026-10-01-design-basis-refresh/`).
`Effects/…` is the pinned `effects` package (`lakefile.toml:126-131`: tag `v0.8.0`, `a4ee7a14`). A
bare `Name.ts:n` is under `vendor/effect-4.0.0-rc.112/src/`. `git:<rev>:<path>` is a path at the
commit named, in earlier history. Decisions rows are cited as `docs/core/decisions.md` holds them at
`6b3f2c92`. Research notes are under `docs/research/`; a note is *tracked* when it is tracked at
`6b3f2c92` or by this refresh.

## Re-review ruling

(Written 2026-08-31. Item 2's `Flow` reads `Eff` since DB-02; item 4 is DB-07's exit value kept
beside the state.)

A fresh review of EffHOL, the current Lean reference pages, and the pinned
Lean 4.33.1 sources does not justify replacing the architecture above with a
larger foundational carrier. It does justify the extraction from Foldlab and
four library-level refinements that are now requirements:

1. The algebra is universe-polymorphic and exposes first-class model
   morphisms, rather than retaining CAS-specific `Type`-only declarations or
   a second morphism predicate.
2. EffHOL separates kinds, types, programs, logical indices, expressions, and
   specifications. Effect4 follows that organization: its program semantics
   precede its logic, while `wlp`, totality, and realizability live in the
   logic/classification layer rather than in `Program` or `Flow`.
3. Lean `Expr` and environment state remain metaprogramming inputs. Persistent
   entries are sorted, serializable first-order rows, and the generated
   declaration/type closure is checked after elaboration. No elaborator
   closure becomes semantic data.
4. The runtime uses an error-and-state result that retains final state.
   Backtracking or rollback is requested explicitly; it is not an accidental
   consequence of transformer order or exception handling.

The online Lean API pages currently describe a newer documentation build than
the project toolchain. API shapes were therefore checked again in the local
4.33.1 sources. The reviewed source digests are:

| Pinned Lean source | SHA-256 | Consequence |
| --- | --- | --- |
| `Lean/Util/CollectAxioms.lean` | `64f340d42f18c51ee83527f03fa69cc26415dd71dcf7fe71031b7760be90007d` | imported declarations use precomputed transitive receipts; the audit still checks every Effect4 declaration directly |
| `Lean/Environment.lean` | `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86` | persistent and asynchronous extension state is an implementation concern; canonical export order is owned by Effect4 |
| `Lean/Expr.lean` | `b9a91d9d170201c2a3622b9c55d694466f54e0e1b8f6068a2d296ff98650169c` | metavariables and elaborator expressions stop at the meta boundary |

This refinement ruling records the original obligations. Current dispositions
and the scope of historical receipts are stated on each DB row below. (2026-10-01: the three
digests were recomputed from the installed `v4.33.1` toolchain and match.)

## Adopted decisions

### DB-01 — `Program` is the well-founded higher-order proof carrier; extension is conservative only under named obligations

The algebra is owned by the pinned `effects` package (`lakefile.toml:126-131`: tag `v0.8.0`,
`a4ee7a14`); DI-90 rules that its consumed core comes in-tree under the same names, and this row
does not restate that plan. This section states the shape Effect4 builds on. The implemented
algebra has the following shape:

```text
Signature.Op     : Type uOp
Signature.Answer : Signature.Op -> Type uAns

Program S A = pure A
            | vis (op : S.Op) (S.Answer op -> Program S A)

Handler S M = (op : S.Op) -> M (S.Answer op)
```

`Program` is higher-order as a representation because `vis` stores a Lean
continuation. It is an inductive, well-founded operation tree suited to monad
laws, interpreter laws, signature sums, handler composition, freeness, and
initiality arguments. It is not necessarily a finite node set or a uniformly
bounded-depth tree: an infinite answer type can index infinitely many distinct
continuation branches whose finite depths are unbounded. Every selected branch
is well-founded, which is the property structural recursion uses. `Program` is
not serializable syntax and receives no content hash, `DecidableEq`, or
generated TypeScript encoding.

This follows the free-model and induced-homomorphism organization in
[Plotkin and Pretnar](https://arxiv.org/abs/1312.1399) and the programming
interpretation demonstrated by
[Bauer and Pretnar's Eff](https://arxiv.org/abs/1203.1539). The literature
licenses the algebraic interface. It does not identify this particular Lean
inductive type with all effectful behavior.

`Handler.sum` is the operation for disjoint signatures. `Handler.through` is
the operation for collapsing an implementation through a second handler.
Categorical composition is stated across signatures; a monoid is available
only for endomorphisms. Implicit universe lifting is excluded. Any explicit
signature map or universe lift requires its own contract and coherence laws.

**The signature parameter and conservative extension** (amended 2026-10-01; rows 111, 115,
116). A full program is checked against `Σ = Σ_core ⊕ Σ_app` as the system map defines it
(`docs/core/system-map.md` §1.1, row 111); this row does not redefine the split. It owns what an
extension of `Σ` must preserve. The paragraph above already asks every signature map for its own
contract and coherence laws: for the binary sum, C1 and C2 below are those laws.

An extension `Σ ⊑ Σ′` is DI-47's relation applied to Σ_app, as system map §1.1 summarizes it
(declared appends only; link positions by DI-22; row identity by DI-64). It is conservative only
when eight obligations hold, each with the qualification Codex's 2026-09-30 audit gave it:

- **C1, syntax.** The injection of programs is an injective monad morphism of free monads. It is
  stated for the binary injections only: along a general signature morphism bind is transported
  but injectivity fails (the audit proved a non-injective morphism, `not_injective`), so another
  map needs its own embedding contract. For Σ_app the obligation is vacuous: rows and service
  keys are data, and a Σ_app extension adds no program syntax.
- **C2, meaning.** Interpreting an injected program under a handler of the larger signature is
  interpreting the original under the restricted handler. For host rows there is no free-monad
  instance until DI-69's row meaning lands; until then the obligation is operational (an old
  program's run against an appended table is its run against its own table) and names its
  observation, its host specification and its tape.
- **C3, checker.** On an old program the checker answers the same under `Σ′` as under `Σ`: the
  monotone half (typing is kept) and its reflection (typing under `Σ′` gives typing under `Σ`).
- **C4, protocol typing.** `Typed_Σ′ w′ Q′ (ι* p) ↔ Typed_Σ (π w′) Q p`. The iff needs the exact
  old operation protocols, or a proved two-way relation: one-way refinement (demand forward,
  promise backward) gives one direction only (the audit proved it, `refinement_not_iff`). For the
  row table it also needs C3 both ways and the host-row entry's domain bit (row 116), without
  which the concrete judgment is not monotone in the table (`typedProg_not_table_monotone`).
- **C5, world.** The new world projects onto the old by a monotone map with the back condition;
  new protocols refine the old ones; the old components' order is not widened. Order and lookup
  stability, the projection and its back condition are kept apart from one-way protocol
  transport: typing is antitone in the order relation (a finer order keeps every derivation,
  `typed_antitone`) and a wider order can lose it (`order_widening_loses_typing`).
- **C6, lawfulness.** `LawfulSig Σ′ ↔ LawfulSig Σ ∧ Fresh ε ∧ LocalLawful ε`, where lawfulness
  is every core clause of R1's one check: table laws, registration, type and template closure and
  scope, service requirements, the integer and internal-handle policies, carriers per service code
  (row 113) and row 114's declaration rules. Freshness includes compatibility with the old
  declarations, and a shorter conjunction is not lawfulness. Name safety stays a per-face check,
  joined at its face, so that admission never imports codegen
  (`src/Effect4/Program/Table.lean:11-13`).
- **C7, representation.** Old bytes and old text read back unchanged. A published program and a
  session are pinned to their complete assembled table, profile and session (row 115;
  `HostSession.start` refuses another table, `src/Effect4/Api/HostSession.lean`); the
  obligation names each selected target's admission and its artifact, header, call, reply and
  journal compatibility. No append claim is made before DI-01's assembly and linking design.
- **C8, forms.** A form adds nothing to Σ, so C1–C7 say nothing about it. Each form owes an
  expansion inside the readable domain (the printer stage's rule; `docs/core/lcnf-route.md` §8
  owns the stage rules) and, with R10, one behaviour law; a readable expansion alone proves no
  behaviour.

Two facts bound what extension means.

- **Σ_core grows only by constructor appends under DI-47's finite gate** (rows 56 and 61). That
  growth is hierarchy-consistent: the old term algebra embeds, with no confusion. It is not
  sufficiently complete: a new constructor adds new terms to old sorts, which is why a function
  with a catch-all arm can change under an append. So it is not a persistent extension in the
  algebraic-specification sense (Ehrig and Mahr, by name; the types verifier's TY-06). DI-47's
  finite gate is the chosen form of the statement, not the only possible one (a theorem form that
  keeps copies of the old functions exists); either way it is a discipline, not a theorem.
- **The sum of the free store and fiber signatures is a coproduct of free monads, not a
  tensor.** The copairing of two monad morphisms out of the summands is the unique monad
  morphism out of the sum (`sum_is_coproduct`), and a left operation followed by a right one is
  a different tree from the reverse (`sum_not_tensor`); typing transports both ways along each
  injection (`Typed.inl_iff`, `Typed.inr_iff`), the generic half of C4. The tree's sums are sums
  of free theories, hence conservative (C1). If the fiber layer ever gains equations, conservativity
  of a sum of theories with
  equations is the question of Hyland, Plotkin and Power (2006), cited by name only: nobody in
  the tree has read it, and every claim about its content here is assumed.

- **Decision.** `Program` (the free monad over a signature) is the one higher-order proof carrier;
  `Eff` is the one program representation it is related to (DB-02). The signature is
  `Σ_core ⊕ Σ_app` (system map §1.1); an extension of Σ_app is conservative only under C1–C8 as
  qualified above; Σ_core grows only under DI-47's finite gate.
- **Witnesses** (re-read at `6b3f2c92`; the package at `a4ee7a14`). Defined or proved, package:
  `Program` (`Effects/Algebra/Program.lean:33`), `Handler` (`Effects/Algebra/Handler.lean:30`),
  `interpret` (`Effects/Algebra/Handler.lean:45`), `Handler.sum`
  (`Effects/Algebra/Handler.lean:51`), `Signature.sum` (`Effects/Algebra/Signature.lean:35`),
  `Handler.through` (`Effects/Algebra/Handler/Composition.lean:27`), `Handler.through_assoc`
  (`Effects/Algebra/Handler/Category.lean:26`), the instance `LawfulMonad`
  (`Effects/Algebra/Laws.lean:45`), `interpret_bind` (`Effects/Algebra/Laws.lean:72`),
  `program_is_free` (`Effects/Algebra/Universal.lean:98`), `program_is_initial_in_models`
  (`Effects/Algebra/Universal.lean:119`), `program_is_initial_in_models_eq`
  (`Effects/Algebra/Universal.lean:215`), `interpret_pinned` (`Effects/Algebra/Universal.lean:243`;
  uniqueness of an interpretation, not additivity). C1 for binary injections: `inl_bind`
  (`Effects/Algebra/Sum.lean:72`), `inl_injective` (`Effects/Algebra/Sum.lean:92`), `inl_unique`
  (`Effects/Algebra/Sum.lean:186`), `sum_unique` (`Effects/Algebra/Sum.lean:36`). C2 for the binary
  sum: `interpret_inl` (`Effects/Algebra/Sum.lean:48`). Proved, tree: `interpret_inl_store`
  (`src/Effect4/Laws/Program/Sched.lean`), `meaning_via_rsig`
  (`src/Effect4/Laws/Program/Sched.lean`), `denoteR_straight`
  (`src/Effect4/Laws/Program/DenoteR.lean`). Proved in research probes, by the seats named:
  `along_bind` (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:239`),
  `interpret_along` (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:253`),
  `typed_along` (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:266`),
  `typed_antitone` (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:198`), and
  the red controls `reflection_needs_back`
  (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:190`),
  `order_widening_loses_typing`
  (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:215`),
  `post_refinement_needed` (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:332`)
  (the model probe's pedigree seat); `c4_iff`
  (`git:f62c972d:docs/research/2026-09-30-model-probe/pedigree/VerifyConservativity.lean:84`), `mono_needed`
  (`git:f62c972d:docs/research/2026-09-30-model-probe/pedigree/VerifyConservativity.lean:143`),
  `pre_refinement_needed`
  (`git:f62c972d:docs/research/2026-09-30-model-probe/pedigree/VerifyConservativity.lean:179`) (its verifier);
  C3's monotone half `hasTy_ext` (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:115`),
  `check_ext` (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:221`), `rows_append`
  (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:247`), `services_append`
  (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:289`), reflection on the looped fragment
  `hasTy_restrict_looped` (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:379`), and the
  red controls `prepend_not_extends` (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:341`),
  `shadow_not_extends` (`git:f62c972d:docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:360`) (the TREE
  seat); `not_injective`
  (`git:f62c972d:docs/research/2026-09-30-codex-review-model-probe/probes/MorphismCollapse.lean:389`),
  `refinement_not_iff`
  (`git:f62c972d:docs/research/2026-09-30-codex-review-model-probe/probes/RefinementNotIff.lean:203`),
  `typedProg_not_table_monotone`
  (`git:f62c972d:docs/research/2026-09-30-codex-review-model-probe/probes/VerifyTreeCurrent.lean:97`) (Codex's
  audit; the last restates the TREE verifier's control after item E). Proved in the tree since
  `a561d604` (landed by seat E from the algebra seat's probes): `sum_is_coproduct`
  (`src/Effect4/Laws/Effects/Sum.lean:103`), `interpret_inl_restrict`
  (`src/Effect4/Laws/Effects/Sum.lean:61`), `interpret_inr_restrict`
  (`src/Effect4/Laws/Effects/Sum.lean:68`), `inl_isMonadMorphism`
  (`src/Effect4/Laws/Effects/Sum.lean:79`), `Typed.inl_iff`
  (`src/Effect4/Laws/Effects/Protocol.lean:159`), `Typed.inr_iff`
  (`src/Effect4/Laws/Effects/Protocol.lean:170`); tested, the red control
  `sum_not_tensor` (`Test/Program/SignatureSum.lean`).
- **Refusals.** Archived and moved to the `effects` package with their witnesses: `E4-ALG-CE-001`,
  `E4-ALG-CE-002`, `E4-ALG-CE-003`, `E4-ALG-CE-004`, `E4-ALG-CE-005`, `E4-ALG-CE-007`,
  `E4-ALG-CE-008` (`Test/Counterexamples/Archive/REGISTER.md`). DI-22, DI-47, DI-64, DI-69, DI-90.
  The extension failures the probes found (insertion re-points calls, a service at a typed key
  retypes old programs, a reserved name, a fresh key's printed text, an unregistrable append, the
  table-monotonicity failure) have no register ids yet; the model probe proposes them as `Test`
  controls with the Σ_app slice (synthesis §6).
- **Sources.** `docs/research/2026-09-30-model-probe/synthesis.md` §2.1, §2.2 (R1, R2), §3.1, §3.3,
  §6 D1 (tracked); `docs/research/2026-09-30-codex-review-model-probe/audit.md` §4, §6 (tracked);
  `docs/research/2026-09-30-model-probe/pedigree/note.md` §3 (tracked);
  `docs/research/2026-09-30-model-probe/pedigree/verify.md` §2 items 8–9 (tracked);
  `docs/research/2026-10-01-formal-pass/synthesis.md` §1 item 9, §2, §4.4 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/note.md` §1 row 1, §2.1 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-06 (tracked);
  `docs/research/2026-10-01-formal-pass/types/note.md` §3 (tracked);
  `docs/research/2026-10-01-formal-pass/types/verify.md` TY-06 (tracked);
  `docs/research/2026-09-16-core-goals-and-end-state.md` §8, §10 (tracked).
- **Literature.** Plotkin and Pretnar, *Handling Algebraic Effects*: read, §1 and §5
  (`docs/research/2026-09-07-lit-papers.md` Q11). Bauer and Pretnar, *Programming with Algebraic
  Effects and Handlers*: by name. Swierstra, *Data Types à la Carte*: read, §2 and §6 (the model
  probe's pedigree seat). Hyland, Plotkin and Power, *Combining effects: sum and tensor*: by name
  only, its content assumed. Goguen, Thatcher, Wagner and Wright (1977): by name. Ehrig and Mahr
  (1985): by name.
- **Status.** See system map §8, R1 and R2; witnesses re-read at `6b3f2c92` (the package at
  `a4ee7a14`).

### DB-02 — `Flow` was the sole reifiable program representation (superseded by `Eff`)

Superseded by `Eff` (`src/Effect4/Program/Eff.lean`) when the Flow route was archived off
main on 2026-09-04; the route is retained at `606918e` in main's history and on branch
`archive/flow-route`. The paragraphs below record the superseded design, not the current domain
model.

Canonical programs use a first-order graph with stable block, operation,
region, and decision identifiers. Admission has the shape:

```text
RawFlow --admit--> CheckedFlow
CheckedFlow --elaborates--> Program
CheckedFlow --denotes--> relational outcomes
CheckedFlow --lowers--> target program
```

`Flow` is not a second free monad. It exists because Lean continuations cannot
carry portable identity and because arbitrary effect flow needs cycles,
sharing, named blocks, and explicit decisions. The bridge to `Program` is an
elaboration relation or function with preservation theorems, not a type
synonym and not an assumed isomorphism.

Pure code is closed at this boundary. A pure fragment enters canonical flow
only through an admitted first-order term language. A host function, promise,
thunk, custom predicate, or raw closure must become a named and registered
foreign boundary or receive a profile refusal. This policy prevents an
uninspectable escape from being mislabeled as full reification.

- **Decision.** Superseded: the one program representation is `Eff`, a first-order tree with
  positional binders (`src/Effect4/Program/Eff.lean`). What survives of this row is its boundary
  rule: pure code is closed at the boundary, and a host function, promise or closure is a named,
  registered foreign row or a refusal. `AGENTS.md`'s representation rules own that rule today, and
  it is the pedigree of R7 (system map §8).
- **Witnesses** (re-read at `6b3f2c92`). `Eff` (`src/Effect4/Program/Eff.lean`); the Flow route
  at `606918e` and on `archive/flow-route` (history, not re-read).
- **Refusals.** `E4-ALG-CE-007` (archived: the higher-order carrier is not canonical program
  content); the Flow route's rows in the archive register.
- **Sources.** `docs/research/2026-09-30-model-probe/synthesis.md` §3.3, the DB-02 row (tracked).
- **Literature.** None.
- **Status.** Settled (superseded); witnesses re-read at `6b3f2c92`.

### DB-03 — open nondeterminism and divergence are relational; behaviour is a function of the tape

The denotation is a family of judgments over configurations, explicit
decision tapes, observable events, and terminal outcomes. With no tape fixed,
the meaning of a program is a relation. A complete compatible tape may make a
fragment deterministic; determinism is never inferred merely because one
runner selected one branch.

Scheduling, race winners, wake-up order, external replies, and other choices
have distinct decision kinds. A safety theorem does not assume fairness.
Divergence is witnessed by an infinite run or by compatible finite prefixes,
not by running out of fuel. The design is informed by the event/continuation
semantics and weak equivalence of
[Interaction Trees](https://arxiv.org/abs/1906.00046) and by Choice Trees'
separation of external events from internal nondeterministic branching in
[Choice Trees](https://arxiv.org/abs/2211.06863).

Effect4 does not currently adopt either tree library as its canonical carrier.
An optional comparison may later relate Effect4 runs to an interaction-tree or
choice-tree model. Such a relation needs explicit trace, divergence, and
equivalence judgments; shared monad structure is not enough.

**In today's names** (amended 2026-10-01; this replaces the paragraph that kept meaning "in
judgments over `Flow`"). The relation is over the machine and the decision tape. `replayEval`
runs a tape against a machine, stopping at the first stuck machine or exhausted budget; one
decision is one `stepDecisionState`, a function, so at the level of the model no choice is made
off the tape. With the tape fixed the machine is a deterministic transition system labelled by
decisions, and with its observation `obs` (every fiber's exit, and the stores) a Moore machine:
`Beh` is its behaviour at a sufficient budget, and `Beh_fuel_irrelevant` makes it independent of
which sufficient budget. `Beh` is a function of the machine and the tape, not a second datatype
that duplicates the relation; with no tape fixed, meaning stays a relation over tapes.

Every choice a run makes is a decision on the tape: scheduling, timing, interruption, and the
host's answers (row 95). How a host answer is admitted and applied is owned by
`docs/core/host-boundary.md`; this row owns only that a host answer is a decision like the
others. A run's journal is a word over commands, and replay is the action of that free monoid
(K5). The tape acts on machines the same way: replaying `a ++ b` is replaying `a`, then `b` from
the machine `a` reached, unless the prefix ran out of fuel, which absorbs the suffix
(`replayEval_append`). Compatible finite prefixes are the chain this gives: along a tape's prefixes
the results form a chain, fuel exhaustion absorbing. Telling divergence from "a frontier at every
budget" by those
prefixes is not yet a statement (no infinite tape is defined), and is R12's (system map §8).
The session runner's `behaviour` is unique by its unfolding (`behaviour_unique`): that is the
uniqueness half of finality for the runner's map. "Equal observations imply equal runs" is a
different fact, injectivity of the behaviour map; the tree neither claims nor needs it (decisions
row 146, recorded), and `behaviour_unique` does not discharge it.

Two invariants are proposed and not ruled: INV-TAPE-1, no off-tape choice, and INV-TAPE-2, a
frontier records what it awaits (`docs/research/2026-09-07-lit-papers.md` Q7 and §A item 1).
No decisions row rules them (the model probe's D7 is open); where they stand is R12's.

- **Decision.** Meaning is a relation over the machine and the decision tape; given a tape, the
  machine is deterministic and its behaviour is `Beh`; every choice, host answers included, is a
  tape decision; divergence is witnessed by an infinite run or compatible finite prefixes, never by
  fuel.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `stepDecisionState`
  (`src/Effect4/Machine/Fibers.lean`) and `replayEval`
  (`src/Effect4/Machine/Fibers.lean`), both functions; `obs`
  (`src/Effect4/Laws/Machine/Behaviour.lean`), `Beh`
  (`src/Effect4/Laws/Machine/Behaviour.lean`), `Beh_fuel_irrelevant`
  (`src/Effect4/Laws/Machine/Behaviour.lean`), `obs_mono_of_le_terminal`
  (`src/Effect4/Laws/Machine/Behaviour.lean`), `replayEval_trace_extends`
  (`src/Effect4/Laws/Machine/Approximation.lean`); the journal action `replay_append`
  (`src/Effect4/Laws/Api/Runner.lean`), `replay_unique` (`src/Effect4/Laws/Api/Runner.lean`),
  `behaviour_cons` (`src/Effect4/Laws/Api/Runner.lean`), `journal_replays`
  (`src/Effect4/Laws/Run.lean`); host answers at the empty table,
  `emptyTable_refuses_every_answer` (`src/Effect4/Laws/Program/Admit.lean`); the frontier law
  `awaitDecision_iff` (`src/Effect4/Laws/Api/Frontier.lean`); `FairTape`
  (`src/Effect4/Laws/Machine/Scheduling.lean`) is a definition on finite tapes. Proved in the
  tree since `a561d604` (landed by seat E): the tape action `replayEval_append`
  (`src/Effect4/Laws/Machine/Approximation.lean:904`) and the session runner's
  uniqueness `behaviour_unique` (`src/Effect4/Laws/Api/Runner.lean`; it concerns
  the session runner, the coherence principle's census row 27); tested,
  `Test/Machine/Runtime/TapeAction.lean` and
  `Test/Api/RunnerFinality.lean`.
- **Refusals.** `E4-SCHED-CE-015` (row 95's repair: the capstone counts only tapes with no host
  answer), `E4-BEH-CE-001`, `E4-BEH-CE-002`, `E4-LIVE-CE-001`, `E4-LIVE-CE-002`; DI-23, DI-57,
  DI-58, DI-68. Decisions row 95 (ruled, landed) and row 146 (recorded); status: those rows.
- **Sources.** `docs/research/2026-09-05-runtime-semantics-core-math.md` §2, §4, §9 (tracked);
  `docs/research/2026-09-07-lit-papers.md` Q7, Q10, §0, §A (tracked);
  `docs/research/2026-09-05-effects-papers-review.md` §1.4, §7 (tracked);
  `docs/research/2026-09-30-model-probe/synthesis.md` §2.2 R12, §3.1 "Behaviour is a function of the
  tape" (tracked); `docs/research/2026-10-01-formal-pass/synthesis.md` §1 item 5, §2, §4.4
  (tracked); `docs/research/2026-10-01-formal-pass/algebra/note.md` §1 row 5, §2.5, A7 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-07, ALG-13, ALG-19 (tracked).
- **Literature.** Xia et al., *Interaction Trees*: read, §3.2 and §7 with Def. 1–2 (lit-papers Q7,
  Q10). Chappe et al., *Choice Trees*: read, §2.2, §7.1, §7.2, §8 (lit-papers Q7, §0). Jacobs,
  *Introduction to Coalgebra*: read (papers review §1.4, §7): of ch. 2, only §2.5's opening (Prop.
  2.5.3, the cofree coalgebra on a colour set) is recorded as read, the basis on which the formal
  synthesis marks ch. 2 read; ch. 3, Thm 3.4.1 (bisimilarity is equality of behaviour). Rutten
  (2000): by name. Lee, Cho, Song, Hur et al., *Fair operational semantics*: by name (core math §9).
- **Status.** See system map §8, R12 (divergence, liveness, frontiers) and R6 (host answers);
  witnesses re-read at `6b3f2c92`.

### DB-04 — fixed fuel is an approximation; the meaning of a loop is the limit of a budget chain

A bounded runner may report completion, an observable terminal result, or a
live frontier. A live frontier is distinct from typed failure, defect,
interruption, and profile refusal. In particular, fuel exhaustion must not be
encoded as `Refusal.failed`.

There is no general fixed-fuel bind law. Giving the same fuel independently to
a program and both sides of a bind changes how the budget is distributed, so
the runner cannot be a monad morphism for all programs. Composition and
coherence are proved at the unbounded big-step or interpreter face. The
Foldlab compatibility proof therefore targets its `interpretRef` observation,
not a universal equation over `run fuel`.

Finite approximations must instead satisfy monotonicity, compatibility, and
coherence laws. A completing observation cannot later become an unrelated
failure. A live leaf may be refined by more execution without first being
reclassified as an error.

*The Flow route's receipt (at `c407ab7` and `606918e`, 2026-09-04, before the route was archived;
kept as a dated receipt).*
Those three laws are now theorems, not requirements, for both runners over
`StateT σ Id` (`git:c407ab7:Effect4/Semantics/Approximation.lean`; battery
`git:c407ab7:Effect4Test/Semantics/ApproximationContract.lean`). What a bounded run *observes*
is `observe result log`: a fuel frontier contributes `live` and the log it had
reached, without the trailing marker and without the resumption block, and
every other result is `terminal`. `Observation.le` orders those observations —
a live observation is below every one whose log extends it, a terminal one is
maximal — and is reflexive, transitive and antisymmetric. Monotonicity is
`loop_obs_mono` / `run_obs_mono` / `region_obs_mono` / `runRegions_obs_mono`;
compatibility is `Chain.stable` (with the raw form `loop_fuel_stable`);
coherence is `Chain.colimit` with `Chain.colimit_below`,
`Chain.colimit_bound_mono` and `Chain.colimit_eq_of_settled`. For an admitted
plain flow the colimit is total, `runColimitDefault`, because
`run_fuelFor_finishes` (DB-04's own fuel argument, `git:c407ab7:Effect4/Semantics/Fuel.lean`)
proves the allotted fuel suffices; the region runner has no such theorem yet, so
`runRegionsColimit` is searched below a bound and returns an `Option`. The block
identity inside `Frontier.fuel` is deliberately not observed: it is where to
resume, not what was seen, and a jump cycle observes the same empty log at two
different blocks (receipt in `git:606918eb73daefcc235a261fce879bf910f2471e:Effect4Test/Semantics/ApproximationContract.lean`).

**The budgeted meaning on `Eff`** (amended 2026-10-01; rows 30 and 41). The budget is a separate
denotation beside `denote`, joined to it by a connector, not a parameter changed in place: the
end-state note's "a parameter on the one `denote`, changed in place" (its §4.2 and §9 item 4) is
superseded by the build-in-parallel rule. `iter f k x` runs a step at most `k` times, `none`
meaning that the budget ended first; it is generic over the signature, and the loop arm of a
meaning is one application of it. `denoteB` uses it for `iterate` and, because its answer is read
through the store handler, keeps the stores written so far. On the straight fragment the budgeted
meaning is `denote` (`denoteB_straight`); a finished answer survives a larger budget
(`denoteB_mono`); two budgets that both finish agree on the exit and the stores
(`meaningB_unique`). The machine follows it on `Looped` (`loopAgreement`), and loops keep their
types (`soundB`, `meaningB_typed`).

What the construction is. The budgeted meaning is the Kleene chain of the least fixed point of a
loop's unfolding equation. `Program` is well founded, so it has no iteration operator and is not
an Elgot algebra; the limit lives outside it. For the limit, convergence (some budget finishes
with this answer and these stores), Elgot's fixpoint law holds (`conv_fixpoint`), convergence is
the least relation closed under the loop's two rules (`conv_least`), and it is single-valued,
stores included (`conv_unique`); no single budget solves the equation (`budget_not_fixpoint`).
These four are in the tree since `a561d604` (seat E).
`meaningB_unique` is that single-valuedness at the tree's level, Capretta's single-valued
termination relation, not a fixpoint law. Naturality, dinaturality and the codiagonal (nested
loops as one loop) are owed only when a form or a printer step declares a loop rewrite (R10).

At the machine, fuel is the same discipline: budget irrelevance and the terminal projection
(`Beh_fuel_irrelevant`, `obs_mono_of_le_terminal`) rest on `drive_add`, with
`drive_stable_of_done`, `replay_stable`, `replay_obs_mono` and `replay_colimit`. A budget with its
sufficiency receipt (`Suffices`) is not CompCert's stuttering measure: a measure preserves
divergence, and a budget claims nothing about it.

- **Decision.** Fixed fuel is never a denotation and admits no bind law; a frontier is live, never
  failure, defect, interruption or refusal. A loop's meaning is the limit of the budget chain
  (`denoteB` beside `denote`), single-valued by `meaningB_unique`; laws for the limit, not for one
  budget.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `iter`
  (`src/Effect4/Laws/Program/Iter.lean`), `iter_zero` (`src/Effect4/Laws/Program/Iter.lean`),
  `iter_succ` (`src/Effect4/Laws/Program/Iter.lean`), `iter_uniform`
  (`src/Effect4/Laws/Program/Iter.lean`), `Looped` (`src/Effect4/Laws/Program/DenoteB.lean`),
  `denoteB` (`src/Effect4/Laws/Program/DenoteB.lean`), `meaningB`
  (`src/Effect4/Laws/Program/DenoteB.lean`), `denoteB_straight`
  (`src/Effect4/Laws/Program/DenoteB.lean`), `iter_mono`
  (`src/Effect4/Laws/Program/DenoteB.lean`), `denoteB_mono`
  (`src/Effect4/Laws/Program/DenoteB.lean`), `meaningB_unique`
  (`src/Effect4/Laws/Program/DenoteB.lean`), `LoopAgreement`
  (`src/Effect4/Laws/Program/LoopAgreement.lean`), `loopAgreement`
  (`src/Effect4/Laws/Program/Agreement/Loop.lean`), `soundB`
  (`src/Effect4/Laws/Program/LoopSound.lean`), `meaningB_typed`
  (`src/Effect4/Laws/Program/LoopSound.lean`), `drive_add`
  (`src/Effect4/Laws/Machine/Approximation.lean`), `drive_stable_of_done`
  (`src/Effect4/Laws/Machine/Approximation.lean`), `replay_stable`
  (`src/Effect4/Laws/Machine/Approximation.lean`), `replay_obs_mono`
  (`src/Effect4/Laws/Machine/Approximation.lean`), `replay_colimit`
  (`src/Effect4/Laws/Machine/Approximation.lean`), `Suffices`
  (`src/Effect4/Laws/Machine/Approximation.lean`), `Beh_fuel_irrelevant`
  (`src/Effect4/Laws/Machine/Behaviour.lean`). The limit's laws, proved in the tree since
  `a561d604` (landed by seat E from the algebra seat's probe): `Conv`
  (`src/Effect4/Laws/Program/IterLimit.lean:42`), `conv_fixpoint`
  (`src/Effect4/Laws/Program/IterLimit.lean:48`), `conv_least`
  (`src/Effect4/Laws/Program/IterLimit.lean:79`), `conv_unique`
  (`src/Effect4/Laws/Program/IterLimit.lean:122`); tested, the red control `budget_not_fixpoint`
  (`Test/Program/IterLimit.lean:39`).
- **Refusals.** `E4-ALG-CE-006` (archived, moved to the `effects` package: a fixed-fuel evaluator
  admits a bind law), `E4-APPROX-CE-001`, `E4-APPROX-CE-002`, `E4-APPROX-CE-003`,
  `E4-APPROX-CE-004`, `E4-RTERM-CE-007`; DI-10 (no general bind law; the fixed-fuel counterexample
  stands).
- **Sources.** `docs/research/2026-09-05-runtime-semantics-core-math.md` §3, §4 (tracked);
  `docs/research/2026-09-16-core-goals-and-end-state.md` §2.2, §4.2, §8, §9 item 4 (tracked; §4.2
  and §9 item 4 superseded as above); `docs/research/2026-09-16-select-and-iterate-ready-packet.md`
  §2.2–§2.3 (tracked); `docs/research/2026-09-30-model-probe/synthesis.md` §3.1 "Partiality is a
  budget", §3.2 item 5 (tracked); `docs/research/2026-10-01-formal-pass/synthesis.md` §1 items 6 and
  12, §2, §4.4 (tracked); `docs/research/2026-10-01-formal-pass/algebra/note.md` §1 row 3, §2.3, A8
  (tracked); `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-08 (tracked).
- **Literature.** Capretta (2005): by name (core math §3). Chapman, Uustalu and Veltri (2015): by
  name (core math §3). Hasuo, Jacobs and Sokolova (2007): by name (core math §2). Jacobs,
  *Introduction to Coalgebra*, Prop. 5.3.3 and Thm. 5.3.4: read (papers review §1.4). Elgot (1975);
  Adámek, Milius and Velebil, *Elgot algebras* (2006): by name (the coherence principle; core math
  §3). Xia et al.'s `iter` laws: by name (core math §4). Leroy, CompCert (2009), for the measure: by
  name.
- **Status.** Settled; divergence adequacy is R12's (system map §8); witnesses re-read at
  `6b3f2c92`.

### DB-05 — first-order children do not require `HHandler`; the fiber layer is algebraic in representation and operational in meaning

[Higher-order effect frameworks](https://arxiv.org/abs/2302.01415) show why an
operation that accepts an actual computation needs more structure than an
ordinary algebraic operation. The scoped calculus of
[Bosman, van den Berg, Tang, and Schrijvers](https://arxiv.org/abs/2304.09697)
also makes the inner and outer continuations of a scope explicit.

Effect4 applies that distinction at the reification boundary. A scoped
construct of `Eff` (a catch, a finalizer, a mask, a scope, a fork, a race, a
layer's build) carries its body as a child subterm of the first-order tree,
addressed by a `Point` (its path from the root, its environment and its fuel),
not as a Lean computation. (On the archived Flow route the children were
`BlockId` values; the decision was first made in those terms.) A handler whose
target monad contains an environment and residual `Program` is already a value
of the existing `Handler` type, and `interpret_bind` plus `Handler.through`
supplies its composition law. Effect4 therefore introduces no `HHandler` carrier
for first-order children.

`Scope` remains a separate signature summand because acquisition,
registration, delimitation, exit-aware finalization, and closing order are
observable. A Layer may be modeled semantically as a program that constructs
a service handler, but that does not merge Layer, Scope, or service lookup into
one operation family.

The no-`HHandler` decision is conditional on the first-order contract. If a
future public operation stores an actual subcomputation rather than a stable
block reference, its breaker packet must either prove an adequate
defunctionalization or introduce a separately justified higher-order calculus.

**The honest boundary** (amended 2026-10-01). `denoteR` elaborates the scoped constructs into
programs over `RSig = StoreSig ⊕ FiberSig`, delimiting each scope with a `guard_` node and closing
it with `unguard` (`guardR`). This is the bracket encoding of scoped effects that Wu, Schrijvers
and Hinze describe and set aside because nothing forces brackets to pair; here they pair by
construction, since `guardR` is their only producer and the concrete judgment types the pair.
`denoteR` is an elaboration in the hefty-algebra sense, written by fuel recursion rather than as
a fold, because a layer reference hops to another path of the root. Control erasure is a handler,
so it is a monad morphism (`eraseControl_bind`); erasing a scope gives its body
(`eraseControl_guardR`); and on `Straight`, with budget for its depth, the erased elaboration is
the straight denotation injected on the left (`denoteR_straight`). Sequencing after a scope enters
the normal branch only after the closing marker (`guardR_bind`, in the tree before the formal
pass), moving the continuation inside a scope changes the program, so a scope is not an
algebraic operation (`guardR_not_algebraic`), and
on one fiber a scope erases to plain sequencing (`eraseControl_guardR_bind`), for continuations
that pass a skipped exit through, as `seqR` does.

The store half of the sum has a handler and a meaning. The fiber half has none, on purpose:
`fiberRefusal` is a total placeholder and not a semantics (`E4-SCHED-CE-001`). The fiber layer
is therefore algebraic in representation and operational in meaning: its meaning is the
reference machine, a deterministic transition system labelled by decisions (DB-03), and the
statements there are simulations on named fragments and observations: `run_eq_meaning` on
`Straight`, `loopAgreement` on `Looped`, and `run_eq_ref` between the frame machine and the
reference at the empty host table with no oracle. In formal terms: the store is a lawful comodel
of state on its live cells (DB-07 owns that fact), and the machine runs the free model against it
only on the straight and looped fragments; past the first fiber operation it is an abstract machine,
not a runner. This corrects the end-state note's "a handler for the control signature (the
scheduler)" (its own last sentence on the point, the honest boundary, is the one this row keeps)
and the model probe's level-3 row ("the machine as runner … holds as a reading"), which holds only
on those fragments (the algebra verifier's ALG-10).

- **Decision.** Scoped bodies are first-order children addressed by `Point`s, elaborated by
  `denoteR` into bracketed `RSig` programs; there is no `HHandler`. The fiber signature has no
  handler; the fiber layer's meaning is operational, related to the denotation and between the two
  machines only by simulations on named fragments.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `Point`
  (`src/Effect4/Program/Compile.lean`), `Straight` (`src/Effect4/Program/Fragment.lean`),
  `seqR` (`src/Effect4/Laws/Program/DenoteR.lean`), `guardR`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `controlErasure`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `eraseControl_bind`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `eraseControl_guardR`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `denoteR`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `denoteR_straight`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `RSig`
  (`src/Effect4/Laws/Program/Sched.lean`), `fiberRefusal`
  (`src/Effect4/Laws/Program/Sched.lean`) with the module's boundary paragraph
  (`src/Effect4/Laws/Program/Sched.lean:32-39`), `run_eq_meaning`
  (`src/Effect4/Laws/Program/Agreement/Machine.lean`), `loopAgreement`
  (`src/Effect4/Laws/Program/Agreement/Loop.lean`), `run_eq_ref`
  (`src/Effect4/Laws/Program/RuntimeR.lean`; its fragment, the empty table and the empty oracle,
  at `src/Effect4/Laws/Program/RuntimeR.lean`). Tested: the frozen scope-versus-bind control
  `cleanup_boundary_distinct` (`Test/Program/DenoteRContract.lean`). The scope law is proved in
  the tree: `guardR_bind` (`src/Effect4/Laws/Program/Intro/Prepare.lean`; it predates the formal
  pass, whose probe proved the same equation again, spelling out `unguardTail`). Proved in the tree
  since `a561d604` (landed by seat E): `eraseControl_guardR_bind`
  (`src/Effect4/Laws/Program/ScopeMarkers.lean:47`); tested, the red control
  `guardR_not_algebraic` (`Test/Program/ScopeMarkers.lean`).
- **Refusals.** `E4-SCHED-CE-001` (the summed handler is not a semantics of the fiber operations),
  the archive's `E4-SCHED-CE-004` (`Test/Counterexamples/Archive/REGISTER.md`: raw bind terms lose
  the cleanup boundary; the register's row with that id is another statement); DI-07, DI-12, DI-57.
- **Sources.** `docs/research/2026-09-16-core-goals-and-end-state.md` §8 (tracked);
  `docs/research/2026-09-05-runtime-semantics-core-math.md` §5–§7 (tracked);
  `docs/research/2026-09-07-lit-papers.md` Q2, §0 item 1 (tracked);
  `docs/research/2026-09-30-model-probe/synthesis.md` §3.1 "Control is scoped syntax" and level 3,
  §3.2 item 4 (tracked); `docs/research/2026-10-01-formal-pass/synthesis.md` §1 item 2, §2, §4.4
  (tracked); `docs/research/2026-10-01-formal-pass/algebra/note.md` §1 rows 2 and 4, §2.2, §2.4
  (tracked); `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-10, ALG-12 (tracked).
- **Literature.** van den Berg and Schrijvers, *A Framework for Higher-Order Effects & Handlers*:
  read, §3 and §4.1 (lit-papers §D). Bosman, van den Berg, Tang and Schrijvers, *A Calculus for
  Scoped Effects & Handlers*: read, its headings and §3's framing only (lit-papers §C, §D). Wu,
  Schrijvers and Hinze (2014): read, §9 and §10 (lit-papers Q2). Piróg, Schrijvers, Wu and
  Jaskelioff (2018): read, §1.2 and §1.3 (lit-papers Q2). Bach Poulsen and van der Rest, *Hefty
  Algebras*: read, §1.2–§1.4, §2.5–§2.6, §3.1, §3.4–§3.5, §5.2–§5.4 (lit-papers Q2, §D). van den
  Berg, Schrijvers, Bach Poulsen and Wu (latent effects, 2021): read, §2.1–§2.3 and §3's opening
  (lit-papers Q2, §D). Chappe et al., *Choice Trees* §7.2 (no congruence across the scheduler): read
  (lit-papers §0 item 1). Plotkin and Power (2002) on algebraicity: by name (core math §6).
- **Status.** Settled; witnesses re-read at `6b3f2c92`.

### DB-06 — EffHOL contributes the logic layer, not the carrier

Adopted as a design constraint; the proof receipts in the last paragraph belong to the archived
Flow route.

[EffHOL](https://arxiv.org/abs/2506.09458) parameterizes effectful realizability
by a monad and a program modality. That organization supports a logic over
Effect4 computations after the computational semantics is fixed. It does not
select `Program`, `Flow`, a scheduler, or Effect TypeScript as the meaning of
the monad.

Effect4 classifies EffHOL's angle modality
`<x <- p> phi` as a weakest liberal precondition, `wlp`, rather than a total
weakest precondition, `wp`. The paper explicitly permits
`<x <- p> false` to be derivable for some `p`; the modality therefore does not
itself require termination. Effect4's total-correctness layer must establish
the decomposition

```text
wp p post <-> wlp p post /\ total p
```

for the chosen semantics before calling a judgment `wp`. That theorem is discharged (2026-09-03) in `git:c407ab7:Effect4/Semantics/Logic.lean`,
over the semantics D1 fixed: `Effect4.Logic.wp_iff_wlp_and_total` for every
`Program` relative to an answer specification, and `Effect4.Flow.wp_iff` in the
flow reading, where the partiality `total` excludes is exactly the unanswered
frontier and the refusal (never fuel, per DB-04). `box_sound` ties the liberal
judgment to `interpret`, and `Flow.wlp_runDefault`/`wp_runDefault` to the runner
through T1/T2. The paper's constructive soundness theorem is evidence about
EffHOL, not a proof of Effect4's instance.

- **Decision.** A logic over Effect4 computations comes after the computational semantics and does
  not select it. EffHOL's modality is classified as a weakest liberal precondition (`wlp`); a
  judgment is called `wp` only with `wp ↔ wlp ∧ total` proved for the chosen semantics, where
  `total` never treats fuel as partiality (DB-04).
- **Witnesses** (re-read at `6b3f2c92`). None on `Eff`: the tree declares no weakest-precondition
  calculus over `Eff` at `6b3f2c92` (tested, `git grep`: no `wp` or `wlp` declaration under
  `src/Effect4`; the `wp` some proofs unfold is Lean core's `Std.Do`, over `Except` and `Option`).
  The archived route's receipt: `wp_iff_wlp_and_total`
  (`git:c407ab7:Effect4/Semantics/Logic.lean:89`).
- **Refusals.** DI-10 (no general bind law until a neutral-stack shape is chosen; the logic inherits
  it).
- **Sources.** `docs/research/2026-09-05-reification-effhol.md` (tracked; its "What the paper
  establishes").
- **Literature.** Cohen, Grunfeld, Kirst and Miquey, *Syntactic Effectful Realizability in
  Higher-Order Logic* (EffHOL): read, Sections IV–V, VII, IX and Appendix E
  (`docs/research/2026-09-05-reification-effhol.md`, tracked).
- **Status.** Settled (a constraint); witnesses re-read at `6b3f2c92`.

### DB-07 — runtime state remains observable on failure

The reference runtime floor keeps the exit as a value beside the state, so that a failure carries
the state it reached (amended 2026-10-01: the tree uses no `EStateM`). The meaning of a program is
an exit and the stores, `ExitV × Stores`, read through `StateT Stores Id`; a typed failure, a
defect and an interruption are values of `ExitV`, not exceptions of the monad, so the stores come
back with every exit. The scope machine's cleanup handler has the same shape, `StateT σ Id` over
exits. Lean's law
[`EStateM.run_throw`](https://lean-lang.org/doc/api/Init/Control/Lawful/Instances.html)
returns `Result.error error state`, the precedent this follows. This is required because scope
cleanup and supervision must observe registrations and state changes made before a typed
failure, defect, or interruption.

The project compiles this choice against
[`leanprover/lean4:v4.33.1`](https://github.com/leanprover/lean4/tree/v4.33.1).
The unversioned documentation links explain the API; the pinned toolchain is
the source and kernel authority for Effect4 receipts.

The order is semantic, not cosmetic. Lean's official discussion of
[transformer ordering](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/)
shows that `StateT` outside `ExceptT` can lose state on error, while `ExceptT`
outside `StateT` retains it. Effect4 freezes state-outside-failure for the
runtime and resource machine. Rollback, when desired, is a separate
transactional operation with its own laws.

Keeping state on failure supplies neither concurrency nor resource correctness by itself. The
runtime still needs proved transitions for finalizer registration and order, exactly-once close,
interruption masking, fiber ownership, scheduler decisions, and managed-runtime disposal. The
theorem this paragraph asks for is R11 (system map §8): release at most once per registration,
counted by identity, and exactly once in close order over closed scopes and structured regions
with a completed-cleanup receipt (the closed bit is set before cleanup runs), with state retained
at frontiers. At a frontier, open scopes are reported and closed only by an explicit `abandon`
(the owner's ruling of 2026-09-07, the grill agenda §3, call 9). What a finished run that leaves a
scope open owes is R11's (the model probe's D8 is not ruled; rc.112 also leaves such a scope
open).

**The store as a comodel** (amended 2026-10-01). The store handler gives each store operation one
co-operation `Stores → Val × Stores`: it is a comodel of the store signature, and `meaning` is the
run of the free model against it. The state laws hold on live cells and fail on dead ones: on a
cell the store holds, put-get, get-get and put-put hold (`put_get`, `get_get`, `put_put`, in the
tree since `a561d604`); on a cell
the store never allocated, writing 7 and reading back answers `unit` (`put_get_dead_fails`), which
is `E4-DEN-CE-002` in comodel terms (the handler's fallback breaks put-get). `Fits` admits only
declared cells (DB-16), the part where the laws hold. The laws are owed in full only when a form
or an optimization declares a state equation.

- **Decision.** The runtime's result keeps the state with every exit (an exit value beside the
  stores, under `StateT`); rollback is a separate transactional operation with its own laws. The
  store handler is a comodel of the store signature, lawful on live cells.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `ExitV`
  (`src/Effect4/Machine/Alphabets.lean`), `storeHandler`
  (`src/Effect4/Laws/Program/Denote.lean`), `meaning`
  (`src/Effect4/Laws/Program/Denote.lean`), `runState`
  (`src/Effect4/Laws/Machine/ScopeMachine.lean`), `runState_complete`
  (`src/Effect4/Laws/Machine/ScopeMachine.lean`), `runState_restore`
  (`src/Effect4/Laws/Machine/ScopeMachine.lean`), `runState_result`
  (`src/Effect4/Laws/Machine/ScopeMachine.lean`), the heap's read-over-write `refPeek_poke_self`
  (`src/Effect4/Machine/Stores.lean`) and `refStep_get_after_set`
  (`src/Effect4/Machine/Stores.lean`), the arena's `peek_poke_other`
  (`src/Effect4/Laws/Machine/Arena.lean:30`). The comodel's laws, proved in the tree since
  `a561d604` (landed by seat E from the algebra seat's probe): `put_get`
  (`src/Effect4/Laws/Program/StoreComodel.lean:51`), `get_get`
  (`src/Effect4/Laws/Program/StoreComodel.lean:67`), `put_put`
  (`src/Effect4/Laws/Program/StoreComodel.lean:88`); tested, the red control `put_get_dead_fails`
  (`Test/Program/StoreComodel.lean:33`).
- **Refusals.** `E4-DEN-CE-002` (the handler's fallback on an unminted key), `E4-STORES-CE-001`;
  DI-65 (terminal cleanup needs completed-cleanup and ownership premises, not correspondence alone).
- **Sources.** `docs/research/2026-09-30-model-probe/synthesis.md` §2.2 R11, §3.3 the DB-07 row
  (tracked); `docs/research/2026-09-30-codex-review-model-probe/audit.md` §5 (tracked);
  `docs/research/2026-09-07-grill-agenda.md` §3 call 9 (tracked);
  `docs/research/2026-09-05-runtime-semantics-core-math.md` §7 (tracked);
  `docs/research/2026-10-01-formal-pass/synthesis.md` §2 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/note.md` §1 row 4, §2.4, A9 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-09 (tracked).
- **Literature.** Lean `v4.33.1` sources and documentation (`EStateM.run_throw`, transformer
  ordering): read by the 2026-08-31 re-review (this file's Re-review ruling). Plotkin and Power
  (2008), comodels: by name (core math §7). Ahman and Bauer, *Runners in action* (2020): by name
  (core math §7). Sivaramakrishnan et al., *Retrofitting effect handlers onto OCaml*, §3.2 on what a
  stopped run leaves open: read (lit-papers Q3).
- **Status.** See system map §8, R11; witnesses re-read at `6b3f2c92`.

### DB-08 — `Expr` is a metaprogramming input only

Restated in `AGENTS.md`, Representation rules (canonical program content).

Lean's [`Expr`](https://lean-lang.org/doc/api/Lean/Expr.html) represents kernel
and elaborator expressions, including metadata and metavariables. Effect4 may
inspect an elaborated `Expr`, but it must emit a checked first-order
declaration row before the value enters program identity, semantics, or target
generation. Raw `Expr`, syntax trees, metavariables, tactic closures, and
elaborator state are not semantic data.

Declaration metadata that must survive imports uses
[persistent environment extensions](https://lean-lang.org/doc/api/Lean/Environment.html).
The exported entries are deterministic serializable rows; any cache built from
them is derived state. Stable ordering and digests are established before
emission so parallel elaboration cannot change generated bytes.

[`Lean.collectAxioms`](https://lean-lang.org/doc/api/Lean/Util/CollectAxioms.html)
is the audit primitive for the transitive axiom dependencies of exported
theorems. Its output is an axiom receipt, not a semantic correctness proof and
not evidence about generated TypeScript behavior.

- **Decision.** Raw `Expr`, syntax, metavariables, tactic closures and elaborator state never enter
  program identity, semantics or generated code; a checked first-order row does. Persistent metadata
  is deterministic serializable rows; `collectAxioms` is an axiom receipt, not a correctness proof.
- **Witnesses** (re-read at `6b3f2c92`). Tested: the trust gate `Test/Audit/AxiomGate.lean` (imports
  `Lean.Util.CollectAxioms`, `Test/Audit/AxiomGate.lean:2`, and audits declarations by module); the
  rule is written in `AGENTS.md` (Representation rules).
- **Refusals.** None registered; `AGENTS.md`'s trust rules refuse `unsafe`, `extern` and
  `implemented_by`.
- **Sources.** None beyond this row.
- **Literature.** Lean `v4.33.1` sources and documentation (`Expr`, `Environment`, `collectAxioms`):
  read by the 2026-08-31 re-review at the digests its ruling records.
- **Status.** Settled; witnesses re-read at `6b3f2c92`.

### DB-09 — Effect TypeScript is a versioned target profile

Restated in `AGENTS.md`, Representation rules (target profile).

The semantic authority for the first target profile is the Effect source tree
at commit
[`2600f62f4532026928454dcea8d1c48557b3f942`](https://github.com/Effect-TS/effect/tree/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src),
paired with `effect@4.0.0-rc.112`. The target profile records the distinctions
observed in that version: success, typed failure, defect, interruption,
service requirements, scope, fibers, causes, exits, and runtime boundaries.
It does not make Effect's internal runtime representation part of Effect4's
canonical syntax.

Source revision and installed package bytes are separate evidence. The
upstream commit and tree identify source history. Foldlab's lockfile identifies
the exercised package by integrity
`sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==`.
The installed `vendor/effect-4.0.0-rc.112/src/Schema.ts` has SHA-256
`9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784`,
while the file at the pinned upstream commit has SHA-256
`f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f`.
This mismatch is not classified as package corruption; it is evidence that a
repository revision cannot stand in for installed bytes.
(2026-10-01: the vendored `vendor/effect-4.0.0-rc.112/src/Schema.ts` hashes to the installed
digest above, tested with `shasum -a 256` at `dceae006` and again at `6b3f2c92`.)

The
[`effect-ts/language-service`](https://github.com/Effect-TS/language-service/tree/5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4)
pin is an auxiliary diagnostic source. Its Effect v4 harness targets
`4.0.0-beta.107`, so it cannot decide rc.112 surface membership or runtime
meaning. Acceptance requires direct rc.112 TypeScript typechecking, language-
service diagnostics, runtime vectors, negative fixtures, and mutation tests.

Generation must prove or test separate claims:

1. lowering preserves the admitted Effect4 typing judgment;
2. rendering and parsing preserve the target intermediate representation;
3. the TypeScript checker accepts positive vectors and rejects negative ones;
4. direct runtime observations match the reference semantics for the tested
   fragment; and
5. any unsupported or lossy operation receives a stable refusal rather than a
   fabricated implementation.

No one gate discharges the others.

Amended 2026-09-09 (S0; register rows DI-56, DI-57, DI-58). A target profile has **three
parts, and they are three kinds of content**, not three data files:

- **ProfileData** — serialisable policy and identity: the scalar domains and their refusal
  rule, the admitted operations and their invocation forms, the adapter identities and
  imports, and the error projection.
- **HostSpec** — a Lean specification: the value correspondence `Rep`, the state relation,
  the call protocol and the observation relation, as propositions and functions in checking
  code. Functions in checking and semantic code are allowed; functions in canonical programs
  are not (the exclusion list below), and no language for serialising every law is invented.
- **Binding** — the runtime adapter and its evidence: the tapes, the differentials, the
  finite host tests.

Amended 2026-09-09 (Wave 2, DI-65): general host transitions may have alternative
completions and resulting states. Determinism is an additional property after fixing the
determining decisions; at-most-once consumption belongs to the checked session. State
correspondence during execution can include open resources. The terminal cleanup observation
requires completed-cleanup and ownership premises, not correspondence alone. The resource
binding's second close completes with a defect; its closure diagnostic is a separate operation
from live-resource use. A refused late acquisition reply does not itself release the host
resource: the adapter/session retains cleanup ownership. The frozen amendment is
`Test/contracts/foundation-wave2.contract.md`.

rc.112 is the first profile. Which targets the model runs on, and in what order, is the system
map's (§1 and §3: the Lean machine compiled through LCNF into OCaml today, WASM next through the
generated OCaml, Effect TypeScript printed and read back); this row does not restate the route.
The 2026-09-09 sentence that called OCaml native a test bed and js_of_ocaml unclaimed (DI-56,
DI-19) is superseded by that route (amended 2026-10-01). This row keeps the profile's three
parts, the scalar-domain rule below and the evidence classes (§ Source and evidence rules).

A profile's scalar domain is **bounded with explicit refusal, intermediates included**:
naturals, framing lengths and every arithmetic result stay inside it or the host refuses —
no wrapping, no saturation — while the logical `Nat` stays unbounded and distinct from any
target's finite representation. A refusal must have an execution outcome: the adapter raises
a distinguished `ProfileRefusal`, the recorder records it as its own row class, and the
comparator classifies that run "outside the profile" — neither agreement nor disagreement,
with the retained state per the observation policy; the run is counted, not claimed. Until
that lands, the truth claim names the exercised safe fragment (DI-56).

- **Decision.** Effect TypeScript is one versioned target profile (rc.112 the first), not the
  semantic owner. A profile is three kinds of content: `ProfileData` (serialisable policy and
  identity), `HostSpec` (a Lean specification of correspondence, state, call protocol and
  observation, lawful by `LawfulHostSpec`) and a binding (the adapter and its evidence). Each
  profile's scalar domain is bounded with an explicit refusal, intermediates included. The route is
  the system map's.
- **Witnesses** (re-read at `6b3f2c92`). Defined: `ProfileData`
  (`src/Effect4/Program/Profile.lean`), `HostSpec` (`src/Effect4/Program/Profile.lean`),
  `LawfulHostSpec` (`src/Effect4/Program/Profile.lean`). Tested:
  `Test/Program/HostSpecContract.lean` (each general law earned by a fixture); the frozen amendment
  `Test/contracts/foundation-wave2.contract.md`.
- **Refusals.** DI-19, DI-56, DI-57, DI-58, DI-65; the number policy is row 108 (open).
- **Sources.** `docs/research/2026-09-30-model-probe/synthesis.md` §3.3, the DB-09 row (tracked);
  `docs/core/host-boundary.md` (the host lane's authority).
- **Literature.** None; the Effect source and the language service are sources, pinned above.
- **Status.** See system map §8, R6 (the host) and R8 (faces); witnesses re-read at `6b3f2c92`.

### DB-10 — PolyFun is pinned prior art, not a public dependency

Adopted as prior art, not an Effect4 proof receipt.

The isolated audit of
[`Verified-zkEVM/PolyFun` at `3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9`](https://github.com/Verified-zkEVM/PolyFun/tree/3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9)
used Lean `v4.33.1`, Mathlib `v4.33.1`, and cslib `v4.33.1`. Its build, tests,
validation script, and declared axiom sweep passed in the isolated checkout.
That evidence applies to the pinned checkout and its stated theorems; it does
not establish an Effect TypeScript bridge.

Effect4 has no public PolyFun dependency. Pulling it into the foundation would
add Mathlib and cslib, substantially enlarge a full validation checkout, and
couple the public API to a rapidly changing library. Effect4 instead keeps its
small algebra self-contained and may adapt independently proved API shapes:
signature maps and lenses, first-class monad morphisms, finite paths, and an
optional interaction-tree comparison. Borrowed code, if any, must retain its
license and exact source provenance.

PolyFun's `FreeM` is still a higher-order proof representation. It cannot
replace the first-order checked `Eff` (DB-02; the 2026-08-31 text said `Flow`), so adopting the
dependency would not remove the reification boundary.

- **Decision.** No public PolyFun dependency; independently proved API shapes may be adapted with
  their licence and provenance; PolyFun's `FreeM` cannot replace `Eff`.
- **Witnesses.** None in the tree: the evidence is the isolated audit of the pinned PolyFun checkout
  (`3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9`), which applies to that checkout only.
- **Refusals.** None.
- **Sources.** None tracked; the isolated audit is recorded here only.
- **Literature.** None (PolyFun is a code dependency, not a paper).
- **Status.** Settled; witnesses re-read at `6b3f2c92` (none in the tree).

### DB-11 — one value carrier, images over it, admission as a premise and as a check

Adopted 2026-09-07 (U0, U1a, U1b: `7cbd436`, `54c90a4`).

Every value the runtime carries is one tree, `Effect4.Store.Val`
(`src/Effect4/Store/Carrier/Val.lean`): the content store's frames plus `handle` (tag 12), a live
allocation index into a running machine's stores. `Machine.Val` and `Env.Val` are that type
by `abbrev` (`src/Effect4/Machine/Stores.lean`, `src/Effect4/Machine/ContextMap.lean`); the
runtime alphabets that were inductives of their own — exits, causes, the fiber context, the
service map — are images over it (`Effect4.Store.Image`, `src/Effect4/Store/Carrier/Image.lean`:
`toVal`/`ofVal` with `ofVal_toVal` and `ofVal_exact`), so a value is read back by a reader
(`Val.context?`, `Env.decode`, `Val.scope?`, `exitOfVal`) and never matched as a constructor. A
handle is not content: no store shape accepts it, and its kind table is the Machine's. (The two
module paths moved under `Store/Carrier/` since the row was written; corrected 2026-10-01.)

Well-formedness is a theorem premise, not a runtime check. `Val.WF` (frame sizes),
`Stores.WF` (every handle a live allocation, a closed scope's exit valid in the store, a memo
entry's Deferred and layer scope live) and `validIn` are the hypotheses the laws carry
(`syncOpStep_answer_valid`, `interpOf_keyBounded`), and `Stores.empty` satisfies every
family's conjunct so the store has a bottom.

**Admission exists** (amended 2026-10-01; the 2026-09-07 text said it was owed to a later step).
`admitProgram` (DI-61) decides a program against its row table and returns the certificate
`AdmittedProgram`, whose fields are proofs: typed at the table's signature, a lawful table, rows
the runner can register, no `int` in the table, the program or its type, and no internal handle
kind in a host row's answer or error columns (row 97's interim rule). A host answer is admitted
before it is applied: `admitAnswer` checks the answer against the row's columns and refuses a
handle that names no live allocation. A forged handle is a refusal row (`E4-HANDLE-CE-001`), never
a defect the model raises. Value typing is not this row's: the runtime keeps the one coarse check
`Val.hasTy`, and the proof side types values by the world (rows 44, 96 and 137: `Fits`, comparing
declarations in the checker's order since row 137 was ruled); DB-16 owns that decision.

- **Decision.** One value carrier, `Store.Val`; every runtime alphabet an exact image over it, read
  back by a reader; well-formedness a premise of the laws; admission a located decision before a
  program runs (`admitProgram`) and before a host answer is applied (`admitAnswer`).
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `Val`
  (`src/Effect4/Store/Carrier/Val.lean:150`), `Image` (`src/Effect4/Store/Carrier/Image.lean`)
  with its laws `ofVal_toVal` (`src/Effect4/Store/Carrier/Image.lean`) and `ofVal_exact`
  (`src/Effect4/Store/Carrier/Image.lean`), `AdmittedProgram`
  (`src/Effect4/Program/Admission.lean`), `admitProgram`
  (`src/Effect4/Program/Admission.lean`), `internalHandleScan`
  (`src/Effect4/Program/Admission.lean`), `admitAnswer` (`src/Effect4/Program/Admit.lean`),
  `mintedIn` (`src/Effect4/Program/Admit.lean`), `admitted_row`
  (`src/Effect4/Laws/Program/Admit.lean`), `external_answer_typed`
  (`src/Effect4/Laws/Program/Admit.lean`), `external_error_typed`
  (`src/Effect4/Laws/Program/Admit.lean`), `admitted_decision_minted`
  (`src/Effect4/Laws/Program/Admit.lean`), `replayCheckedFrom_eq_replay`
  (`src/Effect4/Laws/Program/Admit.lean`), `admitted_unique` (`src/Effect4/Laws/Run.lean`),
  `admitProgram_certificate` (`src/Effect4/Laws/Run.lean`).
- **Refusals.** `E4-HANDLE-CE-001`, `E4-HOST-CE-007` (row 97's interim rule, repaired);
  `E4-TYPED-CE-015` (DI-67's emptiness gap: `prod never nat` and `except never never` are admitted
  though empty; registered at `66aa97d7`); DI-61, DI-62, DI-67, DI-92.
  Decisions rows 97 (interim rule landed), 127 (ruled: register, then repair) and 149 (ruled: the
  frozen `uninhabited` stays for the `int` scan, the emptiness check is `emptyColumn`); status:
  those rows.
- **Sources.** `docs/research/2026-09-08-build-path.md` §3 (tracked; the 2026-09-07 plan);
  `docs/research/2026-09-30-model-probe/synthesis.md` §3.3, the DB-11 row (tracked);
  `docs/research/2026-10-01-data-probe/synthesis.md` §5 row 127 (tracked);
  `docs/research/2026-10-01-formal-pass/synthesis.md` §4.4 (tracked).
- **Literature.** Miller's thesis (2006) and Devriese, Birkedal and Piessens (2016) on capability
  safety, for the minted-handle invariant: by name (the types note §9).
- **Status.** See system map §8, R1 (admission) and R4 (state); witnesses re-read at `6b3f2c92`.

### DB-12 — one context, layers by path

Adopted 2026-09-07 (the join: `6305ce3`, `4aae12f`, `4d7c34e` and its records commit).

The fiber context is one structure (`Machine.Ctx`, `src/Effect4/Machine/Stores.lean`): the
service map (`Env.Ctx`, `src/Effect4/Machine/ContextMap.lean`) and the two budget caches
rc.112's `setContext` stores off it (`internal/effect.ts:726-727`). `Ctx.withServices` is
the one constructor, so the cache law (`Ctx.CacheAgrees`) holds by construction and is not a
field; the ambient `Scope` is a lookup on the map (`Ctx.ambientScope`), cached nowhere.
There is no second context: `Effect.service`, `provideService`, `Effect.provide` and `scoped`
read and write this one map through `updateContext`'s region (`src/Effect4/Program/Compile.lean`:
`updateContextAt`, `updateThenK`).

A layer is a program subterm. `LayerTerm` is a member of the `Eff` mutual family
(`src/Effect4/Program/Eff.lean`: `succeed`, `effect`, `effectDiscard`, `provide`,
`provideMerge`, `merge`, `fresh`, `orDie`, and since 2026-09-08 (the host rows slice) `ref`
and `mergeAll` — the n-ary merge is its own constructor over a `LayerTerms` spine, one
parallel parent scope and one sequential child per layer as `mergeAllEffect` builds it
(`Layer.ts:1587-1602`), because a fold of `merge` builds a different scope tree for three or
more layers; `merge` is its binary case, `:1905`), reached through `Eff.provideLayer` with
rc.112's `local` flag as a field, and
`Node.layer` addresses it. Its identity is its path: `LayerId := List Nat` is the memo world's
key (`Stores.memo`, `MemoWorld`), and `compileLayer` builds a layer at its point with the memo
map and the scope as `build`'s two arguments (`Layer.ts:230-232`) — the build protocol as
`EffName` continuations at Points (`fromBuildThen`, `withMemoMapThen`, `memoize`,
`provideThen`, `mergeChildren`, …) and `Region` as the first-order "what runs under a context
region". There is no layer table, no `Construction`, no `ProgName`-style program table and no
second `RunMachine` instantiation: the Layer machine
(`git:4aae12f:src/Effect4/Machine/Layer.lean`) retired with the join, its memo world and
operations joined into the one `Stores` verbatim.

What path identity refuses, and what a reference adds (amended 2026-09-08, the host rows
slice). rc.112 keys the memo map on the layer *object* (`Layer.ts:411`, `:438`); a path is
where a layer *is*, never what it says, so two inline sites of one printed term are two keys:
`harness/truth`'s `pProvideTwice` pins the two-site protocol (two builds) and keeps reading
`2`. One object at two sites — `const L = Layer.effect(…)` then `Layer.merge(L, L)` — is
`LayerTerm.ref`, the path of the defining occurrence, and the compile redirects a reference
to its target's path (`resolveLayer`), so both sites share one memo entry and a memo hit is
reachable from a printed program for the first time: `pDiamond` reads `1` beside
`pProvideTwice`'s `2`, and the pair is the receipt that path identity now tracks object
identity. A well-formed reference names a non-reference layer that precedes it in program
order and does not enclose it (`src/Effect4/Program/Refs.lean`, `layerRefsWF`); the printer hoists
every
target into a `const L_<path>` (`printModule`) so the host sees one object. Grill call 10
(keep the memo store) stays settled by build order-independence
(`docs/research/2026-09-08-build-path.md` §2 (working note)). Inserting under one
path leaves every other path's entry untouched (`MemoWorld.find?_append_other_key`,
`LAYER-FB-LAYER-IDENTITY`); a forged path is the refusal row.

**A layer is built where it was checked, and its value fits its key** (amended 2026-10-01; rows 104
and 105, landed at `d20f3292` and `57c93ba4`). Both machines build a layer at its checked lexical
point: the layer child with the empty environment (`Point.layerBuild`), which matches the checker's
closed layer bodies, the printed TypeScript and memo identity by path; a layer body never reads
the enclosing environment. The checker and `LayerHasTy` require a `succeed` or `effect` layer's
value to fit its key's declared service carrier, in the checker's normalized order, and refuse a
key with no service type (`valueNotSubtype`, `serviceUnknown`); TypeScript already refuses those
programs. The row-calculus rationale behind layer typing (rows, `provide`, satisfaction) is
DB-17's; the service table's place in the world and its lawful declarations are rows 112–114.

- **Decision.** One context per fiber (`Machine.Ctx`: the service map and the two budget caches,
  built by one constructor); a layer is a subterm of `Eff`, identified by its path, built at its
  checked closed point, its value fitting its key's declared carrier; a reference shares its
  target's memo entry.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `Ctx`
  (`src/Effect4/Machine/Stores.lean`), `withServices` (`src/Effect4/Machine/Stores.lean`),
  `ambientScope` (`src/Effect4/Machine/Stores.lean`), `CacheAgrees`
  (`src/Effect4/Machine/Stores.lean`), `LayerTerm` (`src/Effect4/Program/Eff.lean`),
  `compileLayer` (`src/Effect4/Program/Compile.lean`), `resolveLayer`
  (`src/Effect4/Program/Compile.lean`), `layerBuild` (`src/Effect4/Program/Compile.lean`),
  `layerBuild_env` (`src/Effect4/Program/Compile.lean`), `provideLayerWithK`
  (`src/Effect4/Program/Compile.lean`), `provideLayerR`
  (`src/Effect4/Laws/Program/DenoteR.lean`), `checkLayer`
  (`src/Effect4/Program/Checker.lean`), `LayerHasTy`
  (`src/Effect4/Laws/Program/Typing/HasTy.lean`), `layerRefsWF`
  (`src/Effect4/Program/Refs.lean`), `find?_append_other_key`
  (`src/Effect4/Machine/Stores.lean`). Tested:
  `Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean` and
  `Test/Counterexamples/Machine/Semantics/LayerValue.lean` (rows 104 and 105's retained falsifiers);
  the truth harness's `pProvideTwice` and `pDiamond` (`harness/truth/Truth.lean`).
- **Refusals.** `E4-PROV-CE-005` and `E4-PROV-CE-006` in `Test/Counterexamples/REGISTER.md`
  (repaired 2026-10-01; the archive's rows with those ids are other statements),
  `LAYER-FB-LAYER-IDENTITY`; DI-71. Decisions rows 104 and 105 (ruled, landed); status: those rows.
- **Sources.** `docs/research/2026-09-08-build-path.md` §2 (tracked);
  `docs/research/2026-09-08-host-rows-slice.md` (tracked);
  `docs/research/2026-09-30-pass/synthesis.md` §6 slices 1–2 (tracked).
- **Literature.** None.
- **Status.** See system map §8, R5; witnesses re-read at `6b3f2c92`.

### DB-13 — one wake protocol, the family's policy on top

Adopted 2026-09-08 (the scheduler surface: `5347294`, `4ed61a7` and the records commit).

Every waiting family parks its waiters on one list, `WakeList π` (`src/Effect4/Machine/Wake.lean`),
generic in the family's payload `π`: Deferred and the timer do so now, and a module that lands
later (Latch, Queue, Semaphore, Pool, PubSub) does so as a composed `Eff` program over `Ref`,
`Deferred` and this list, never as a new machine store (DI-11, which names Queue, Mailbox and
PubSub; Latch is decisions row 81's design). (Wording amended 2026-10-01: the 2026-09-08 text,
"Latch, Queue, Semaphore, Pool, PubSub and the timer as they land", read as one store per family
against DI-11.) The protocol fixes *when* a waiter is woken and how a
cancel is accounted; *which* waiters and *with what* is the family's policy (`WakePolicy`:
`broadcast`, `signal`, `sweep`), a function over the list, never a second list. A waiter is
`(fiber, token, phase, payload)`, captured at registration (the WHATWG capture rule: a later
list replacement cannot retarget it); the phase is the list's counter, advanced by every wake
(Eio's `In_transition` role). A wake owes resumes, `Owed κ` = `(waiter, token, code, mode)`,
and `WakeMode` says how an owed resume is delivered: `now` inline at the drain (Deferred,
`internal/effect.ts:5277`), or `scheduled owner priority` posted on the owner's dispatcher and
fired by the host's flush (the six `scheduleTask` sites, `Scheduler.ts:193-247`). A
`scheduled` wake coalesces: the first `schedule` captures the pending waiters into the batch
and posts one `Task.wake list phase`; a later one joins the batch and posts nothing
(`WakeList.schedule_coalesces`, `Latch.scheduleUnsafe`).

The cancelled-waiter clause is verbatim: a cancel on a waiter still pending removes it and
owes nothing; a cancel on a waiter no longer pending consumed a wake, and the cancelling step
owes one (`WakeList.cancel_owed_iff`; a `broadcast` list lost nothing,
`wakeAll_cancel_owed`). The machine side stays the token guard: a resume for a waiter no
longer parked is inert.

The dispatcher's address is its making fiber's id, and nothing else: the machine never
removes a fiber record (`spawn` appends, `RunMachine.update` maps in place), so a dispatcher
outlives its fiber's run exactly as rc.112's object does (`Queue.ts:455` stores it at make),
and a post to an exited fiber's dispatcher is delivered. There is no dispatcher table. A post
to an id the machine never minted is the frontier `Stuck.unknownFiber`
(`SCHED-FB-UNKNOWN-OWNER`).

The `Delay` reply (Riot's `Proc_state.step` third answer) is not a new machine answer: a row
that is not ready registers on the family's list with *the row itself* as the payload
(`WakeList.delay`) and parks on a fresh token; the wake re-presents the row and it is polled
again, consuming no frame (Queue's signal-then-repoll, `Queue.ts:1955-1975`, `:1432`). A
spurious wake is permitted by construction: the repoll may park again at the advanced phase.

What this basis refuses. A waiter list is FIFO in registration order and a family's non-FIFO
policy is a sweep over it, not a reordering (`sweep_keeps_order`, `SCHED-FB-NO-FIFO`);
`Task.wake` and `WakeList.delay` have no rc.112 producer in this tree until Latch and Queue
land, so their meaning is pinned by executed fixtures (`SchedulerCoreContract` §Wake), not by
the truth harness (`SCHED-FB-PRODUCER`); `TxRef` is its own subcalculus, not a policy on
this list.

- **Decision.** One waiter list, `WakeList π`, for every waiting family; the protocol fixes when a
  waiter is woken and how a cancel is accounted; the family's policy is a function over the list; a
  later module is a composed `Eff` program over `Ref`, `Deferred` and this list (DI-11).
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `WakeList`
  (`src/Effect4/Machine/Wake.lean`), `WakeMode` (`src/Effect4/Machine/Wake.lean`),
  `WakePolicy` (`src/Effect4/Machine/Wake.lean`), `Owed` (`src/Effect4/Machine/Wake.lean`),
  `delay` (`src/Effect4/Machine/Wake.lean`), `wakeBy` (`src/Effect4/Machine/Wake.lean`),
  `cancel_owed_iff` (`src/Effect4/Machine/Wake.lean`), `schedule_coalesces`
  (`src/Effect4/Machine/Wake.lean`), `wakeAll_cancel_owed`
  (`src/Effect4/Machine/Wake.lean`), `sweep_keeps_order` (`src/Effect4/Machine/Wake.lean`).
  Tested: the executed fixtures of `Test/Machine/Runtime/SchedulerCoreContract.lean` §Wake.
- **Refusals.** `SCHED-FB-NO-FIFO`, `SCHED-FB-PRODUCER`, `SCHED-FB-UNKNOWN-OWNER` (fallback ids, in
  the text above); DI-11. Decisions row 81 (open: Latch); status: that row.
- **Sources.** `docs/research/2026-09-30-model-probe/pedigree/verify.md` P10 (tracked).
- **Literature.** None; Eio's `In_transition` and Riot's `Proc_state.step` are cited above for their
  roles, from those runtimes' sources.
- **Status.** Settled; witnesses re-read at `6b3f2c92`.

### DB-14 — one logical clock, a duration decision, staged fires

Adopted 2026-09-08 (the timer, A4: the three commits of
`docs/research/2026-09-08-timer-dispatch.md` (working note)).

Physical time is not modelled and never will be (DB-04 forbids fuel as time; wall-clock, drift,
the browser's floor and `setTimeout`'s ceiling are host facts). Logical time is one store on
the wake protocol (`src/Effect4/Machine/Timer.lean`, DB-13): `TimerStore` is the clock, the
pending sleeps as waiters whose payload is the deadline, and the end of an advance in
progress. Its shape is rc.112's `TestClock` (`testing/TestClock.ts`: a timestamp that moves
only when the host says so, a table ordered by deadline then registration, an `adjust` that
fires every due sleep in that order staging the clock at each fired deadline and letting
fibers run between fires); its registration meaning is the live `ClockImpl`'s
(`internal/effect.ts:6052-6066`): a cancelled sleep is removed.

The host moves the clock by one decision, `RunDecision.advance (millis : ClockMillis)` — a duration,
never a timestamp — and the machine runs the staged loop (`advanceState`): fire the least due
sleep (`RunInterp.clockStep`, the one new interpreter field), resume it, flush the
dispatchers, repeat, then set the clock to the end. A sleep a woken fiber registers that is
due by the end fires in the same advance (finding 4 of
`docs/research/2026-09-04-timer-semantics-and-proofs.md` (working note)). A fired sleep resumes inline
(`WakeMode.now`, as a Deferred's completion does); the latch-posted spelling rc.112 uses there
is Latch's to land. Two rows reach the store: `sleep d` with `0 < d < ∞` registers
(`Name.registerSleep`, cancel `Name.cancelSleep` = `clearTimeout`), and `clockNow` reads
(`SyncOp.clockNow`); `sleep 0` is `yieldNow` and `sleep ∞` is `never`, decided at the row.
`TimerStore.WF` — every pending deadline at or after the clock — is a conjunct of
`Stores.WF`, kept by every store step and every clock step.

The owner amended the carrier on 2026-09-20: logical milliseconds, stored deadlines and
advance durations use exact arbitrary-precision arithmetic. `ClockMillis` keeps this
carrier distinct from ordinary program numbers; the OCaml target uses Zarith. Advances
and timer-frontier deadlines cross the wire as canonical nonnegative decimal strings.
The keyed host tape uses protocol version 3 (`effect4-host-session-v3`, `keyed-v3`):
version 2 used numeric clock durations and is not accepted by the current reader. Legacy
recordings stay unchanged; any future migration must be explicit. The current format never
accepts a number-or-string union for the clock field.
`clockNow` retains its number-valued result and explicitly refuses observations outside
the target's numeric profile. The stock rc.112 TestClock adapter likewise refuses an
out-of-profile advance or deadline before mutation. These are host profile refusals,
separate from program failures and from fuel frontiers; the ordinary scalar profile
remains DI-56's. The implementation receipt is
`docs/research/2026-09-20-skeleton-first-receipt.md`.

What this basis refuses. `setTime` (`TIMER-FB-SET-TIME`): the clock never moves backwards. A
kept cancelled sleep (`TIMER-FB-KEPT-CANCEL`): the store models `clearTimeout`, not the test
clock's table. An infinite deadline (`TIMER-FB-INFINITE`). A `Psq` carrier: the wake list is
the one carrier and the earliest deadline is a policy on it (`WakeList.wakeBy`), measured
elsewhere as not worth a second structure; a keyed carrier is a later, measured change.

- **Decision.** Physical time is not modelled; logical time is one store on the wake protocol, moved
  only by the host's `advance` decision (a duration in exact milliseconds), with staged fires; a
  cancelled sleep is removed; out-of-profile clock values are host profile refusals.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `TimerStore`
  (`src/Effect4/Machine/Timer.lean`), `advanceState` (`src/Effect4/Machine/Fibers.lean`),
  `clockStep` (`src/Effect4/Machine/Fibers.lean`), `wakeBy`
  (`src/Effect4/Machine/Wake.lean`); `ClockMillis` (`src/Effect4/Data/ClockMillis.lean`). The
  implementation receipt of the 2026-09-20 amendment:
  `docs/research/2026-09-20-skeleton-first-receipt.md`.
- **Refusals.** `TIMER-FB-SET-TIME`, `TIMER-FB-KEPT-CANCEL`, `TIMER-FB-INFINITE` (fallback ids, in
  the text above); DI-56. Decisions row 83 (open: custom clocks and the seeded random profile);
  status: that row.
- **Sources.** `docs/research/2026-09-08-timer-dispatch.md` (tracked);
  `docs/research/2026-09-04-timer-semantics-and-proofs.md` finding 4 (tracked);
  `docs/research/2026-09-20-skeleton-first-receipt.md` (tracked).
- **Literature.** None; rc.112's `TestClock` and `ClockImpl` are sources, cited above.
- **Status.** Settled; witnesses re-read at `6b3f2c92`.

### DB-15 — strings are machine values; host records and errors cross as strings; records are type-language growth

Adopted 2026-09-08 (the host rows slice, decision 3 of
`docs/research/2026-09-08-host-rows-slice.md` §7 (working note); step 1 of its
dispatch).

A `str` literal is a machine value on the native route: `Lit.toVal (.str s) = some (.str s)`
(`src/Effect4/Machine/Term.lean`), and the value typing inhabits `.string` with the carrier's `str`
frame and `.option t` with its `none` and `some` frames (`Val.hasTy`,
`src/Effect4/Program/Typed.lean`; both paths corrected 2026-10-01 to where the definitions are at
`dceae006`, unchanged at `6b3f2c92`). Every literal now evaluates, so `evalTerm_isSome` carries no
`noStr` premise and the register row `E4-TYPED-CE-001` is retired with its ID kept. The provision
route's `litVal` (`src/Effect4/Program/Typing.lean`) still refuses a string as a layer value
(`PROV-FB-STRING-VALUE`); that refusal is its own and is not moved here.

What crosses a host row, so that a canonical row table can be typed with neither a record
nor a dynamic type in `Ty` (`src/Effect4/Program/Eff.lean` has neither and gains no `json`
leaf): a SQL row is `list (prod string string)`, one `(column, cell)` pair per column in the
order the package answered them; a row set is `list (list (prod string string))`; bind
parameters are `list string`; and every cell and parameter is JSON text (`7` is `"7"`, `"a"`
is `"\"a\""`, `null` is `"null"`). A bind outside `Lit` (a `Date`, a `Uint8Array`, an object)
is `E-ARG-DYNAMIC` at ingest. An error crosses as `prod string string`, the `_tag` and the
message: `SqlError` is a tagged union of eleven reasons (`unstable/sql/SqlError.ts:31-329`)
and `Ty` has no sum. The machine's error alphabet carries it as `Err.tagged tag message`
(`src/Effect4/Machine/Stores.lean`, appended 2026-09-09 so every earlier golden keeps its
bytes), whose value image is `ctor 2 [str tag, str message]`; `errOf` reads a two-string pair
into it, `errAdmits` admits it exactly where the row's error type admits the pair, and the
truth wire spells it as the two-element array the host's `pair` builds. `orDie` on a tagged
error dies as `badName`, since the defect alphabet has no string payload
(`ORDIE-FB-TAGGED`). For a two-level error — a tagged record whose one field `reason` is
itself tagged, rc.112's `SqlError`, the shape its `Effect.catchReason` dispatches on — the pair
is the reason's tag and the driver's message under it, the outer `_tag` implied by the row
(ruling G1, 2026-09-09): `SqlError.message` is the constant `"Failed to execute statement"`
for a missing table, a syntax error, a constraint violation and a closed database alike, so
the literal `(_tag, message)` distinguished none of them (the error-paths receipt). A row
whose package effect is typed `never` — the sqlite client's `make` — has an empty error
channel: a file that cannot be opened is a defect rc.112 throws, which no tape can replay. A
handle a row answers stays a `Ty.handle` target spelling (DB-11); an
optional answer (`KeyValueStore.get`) is `.option string`, and the host adapts the package's
`string | undefined` with `Option.fromNullable`. Amended 2026-09-09 (host rows step 5): a
term spells a parameter list with the variadic atom `strings(s₁, …, sₙ) : list string`
(`nativeAtom`, `src/Effect4/Program/Native.lean`), the one list a term can build; and because the
wire is JSON
text, the *host* decodes each parameter with `JSON.parse` before binding it, so `"7"` binds a
number and `"\"x\""` a string, exactly as the foreign `${7}` and `${"x"}` did. The canonical
tables are `Program/Packages/SqliteBun.lean` and `KeyValueStoreMemory.lean`; what in them is
the package's and what is the harness's plumbing is said in their module headers.

Amended 2026-09-09 (S0; the foundation settlement, register rows DI-59, DI-35, DI-62), three
sentences.

*Where the pair is made* (DI-59): at the **row adapter** — `Effect.mapError(toPair)` in every
shim of `harness/truth/prelude.ts` — so the program's own handlers and the recorder observe the
same value. Corrected 2026-09-09 (Wave 2): the recorder retains a **bounded, versioned diagnostic
projection** beside the row, with its fields, ordering and losses explicit. It does not promise
lossless serialization of arbitrary raw host objects or causes. Unsupported mixed-cause
recording must be represented or explicitly refused, not silently reduced to the first failure.
The current historical tapes contain the projected pair/outer tag until their explicit migration.
The type oracle (DI-29) binds the adapter rather than the package member.

*The equality refusal set* (DI-35, ruling G9): `eq` widens **one `Ty` at a time, and only where
`===` compares faithfully** — `.string` today, with `or`/`and` at `.bool` beside it, since the
term language has `not` and no other connective. Past that the printed `eq` becomes
`Equal.equals`, which is its own slice; `Val.eqAt : Ty → Val → Val → Bool` is the destination
beside `Val.hasTy`; the `Effects` package gets no `Equal` class.

*The admissible error image* (DI-62): a program may introduce a failure payload only at `never`,
`nat`, `string`, `prod string string`, or a union of those (a literal type once `Ty.lit` lands),
and the restriction applies at **every** introduction — `fail`, `yieldError`, and each `fail`
leaf of a cause literal — while defect-only and interrupt-only causes stay admitted at `never`.
`Err.text s` is appended so a plain string round-trips instead of collapsing to `boom`; `errOf`
is total onto `tag`/`text`/`tagged` with `boom` retained for old tapes; and a declared error type
never permits discarded data (`errAdmits_errOf`). `Err.value (v : Val)` is **refused**: a handle
inside a cause would extend the minted-handle invariant into causes.

Ruled 2026-09-09 (Wave 2, DI-15/55/38): append string-literal `Ty.lit` and its subtype
relation after deep normalization, then change answer merging in a separate proved slice.
Keep literal tags through const-generic pair construction. A richer `prod (lit tag) X` error
still requires a supported image for X and its recovery laws; literals alone do not create
that image. No record constructor or arbitrary error-value carrier is added by this ruling.

What this basis refuses. A `json` leaf in `Ty`: the value language is the carrier's frames
and a codec is a row. A record type in `Ty`: columns are pairs. `.int` stays uninhabited
(`TYPED-FB-INT`): `Val.nat` is a `.nat`, and the printer's identification of the two as
`number` is not the typing's.

Recommended beside these refusals, not ruled (scout E, 2026-09-09). All three stand, with two
amendments: `Headers` and `File.Info` are codec-able as `list (prod string string)`, the shape
the SQL row already uses; and `.int` is the one refusal a package member's *declared* type
contradicts (`SocketCloseError.code: Schema.Int`), and the cheapest to lift, since the ordinal
and its `render` arm already exist. G1's implied outer tag is sound **exactly when a row's
package effect has a single outer tag**: `SqlClient.withTransaction` (whose channel is the
body's `E` union `SqlError`) and `SqliteMigrator.layer` (two outer tags, from the installed
driver) violate it, and four error class names are declared twice across packages
(`AuthenticationError`, `UnknownError`, `InternalError`, `PersistenceError`), so a row whose
`E` is a union must declare the outer tag too. Two sentences above are corrected by the same
reading: `SqlError`'s eleven reasons are **not uniform** — `UniqueViolation` carries a twelfth
field `constraint` the other ten do not, and "they differ only by tag" is what makes
`prod string string` look sufficient; and the JSON-text refusal covers the **bind** direction
only — the package's own parameter and cell domain is `Statement.PrimitiveKind`'s eight members,
`JSON.stringify` throws on a `bigint` and is lossy on a `Date` and a `Uint8Array`, and the
**answer** direction is unrefused (DI-56).

**Records** (amended 2026-10-01; decisions row 119, ruled: "ratify as accepted"). Row 119 lifts the
refusal of "a record type in `Ty`" above by a ruled design; until its slice lands, `Ty` has no
record and today's host-row columns stay pairs. Records are growth of the type language (Σ_core,
system map §1.1), not of Σ_app: `Ty.record (fields : List (String × Ty))`, appended as a core
constructor under DI-47's discipline; fields in a canonical order by name, a repeated name refused
at formation; values positional (`ctor 0` of the fields in that order, no new `Val` frame);
membership reads the fields in canonical order, so it stays a fold; subtyping exact (the same
names, each field below), width refused by name inside a program and projected by the row adapter
at the boundary (the S-3 codec contract's strict field set and DI-59's adapter already do this);
records not distributed over union-typed fields; the eliminator and the equality generated. Three
proved facts fix that shape, all in the data probe's models (not the tree): width with positional
values is unsound; reading fields in written order breaks `hasTy_normalize`; reading them in
canonical order keeps that law with no premise and stays a fold. The coercive alternative (width
as a projection at subsumption) holds on a small model and is not chosen. The slice (stage 1,
records only) lands after the M5–M7 milestone by default (row 119).

The other data rows of 2026-10-01, by number; each row's content and status are the register's
(`docs/core/decisions.md`), and none is restated here: row 120, error payloads (DI-62 amended):
proposed; row 121, `int` and numbers: proposed, with row 108; row 122, Decision 12 and the boundary
decode route: ruled, and written into `docs/core/host-boundary.md` §7 at `0eea3cd0`, which owns it
(this row links there and copies nothing); row 123, the in-program schema operation: proposed in
principle; row 124, recursive types: open; row 125, keyed collections: open; row 126, equality at
records: proposed; row 127, DI-67's admission gap: ruled (its counterexample is `E4-TYPED-CE-015`);
row 128, the two embeddings called exact: ruled (retractions until their exactness theorems land);
row 129, register and text repairs: open (coordinator); row 130, `catchTag`'s residual: proposed,
with variants; row 131, a number-to-text atom: proposed; row 132, `Ty` case analysis kept in
`Laws/Program/Typed/Membership.lean`: proposed for the M5–M7 brief. Row 149 (ruled) names the two
admission refusals; row 2's stage (b) is ruled by row 119.

- **Decision.** Strings are machine values; a host row's records and errors cross as strings and
  string pairs, with the pair made at the row adapter; a program's failure payload is restricted to
  `never`, `nat`, `string`, `prod string string` or their unions; `int` stays uninhabited. Records
  enter `Ty` by row 119's ruled design (canonical field order, positional values, exact subtyping,
  width projected at the boundary); until that slice lands, `Ty` has none.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved (string values and pairs): `Lit.toVal`
  (`src/Effect4/Machine/Term.lean`), `Val.hasTy` (`src/Effect4/Program/Typed.lean`), `errOf`
  (`src/Effect4/Machine/Term.lean`), `errAdmits_errOf`
  (`src/Effect4/Laws/Program/Admit.lean`), `evalTerm_isSome`
  (`src/Effect4/Laws/Program/Typed.lean`); tested: `Test/Program/TypedContract.lean` (the
  retired `E4-TYPED-CE-001`'s fixture). Records: witness missing at `6b3f2c92` (stage 1 not landed);
  the design's facts are proved in the data probe's models: `positional_width_unsound`
  (`git:f62c972d:docs/research/2026-10-01-data-probe/tree/RecordNested.lean:1087`), `fitsFields_exact_mono`
  (`git:f62c972d:docs/research/2026-10-01-data-probe/tree/RecordNested.lean:1259`) (the tree seat);
  `hasTyV_normalize_fails` (`git:f62c972d:docs/research/2026-10-01-data-probe/tree/verify-RecordRed.lean:1324`),
  `fits_coerce` (`git:f62c972d:docs/research/2026-10-01-data-probe/tree/verify-CoerciveWidth.lean:107`) (its
  verifier); in the synthesis's own model, `hasTy_normalize`
  (`docs/research/2026-10-01-data-probe/synthesis.md:1143`) and its red control
  `written_order_not_invariant` (`docs/research/2026-10-01-data-probe/synthesis.md:1174`).
- **Refusals.** `E4-TYPED-CE-001` (retired), `E4-TYPED-CE-002`; `E4-TYPED-CE-015` (registered at
  `66aa97d7`); `TYPED-FB-INT`, `ORDIE-FB-TAGGED`,
  `PROV-FB-STRING-VALUE` (fallback ids, in the text above); DI-15, DI-35, DI-56, DI-59, DI-62,
  DI-67.
- **Sources.** `docs/research/2026-09-08-host-rows-slice.md` §7 (tracked);
  `docs/research/2026-10-01-data-probe/synthesis.md` §1, §3.1–§3.2, §5 rows 119–132, §6.4 (tracked);
  `docs/research/2026-10-01-formal-pass/synthesis.md` §4.4 (tracked);
  `docs/research/2026-10-01-formal-pass/types/note.md` §2.6, §4.5 (tracked).
- **Literature.** Wand; Rémy (1994); Gaster and Jones (1996); Leijen, *Extensible records with
  scoped labels* (2005): by name (why closed records, not row polymorphism; the data probe §6.4).
  Morris and McKinna (2019): assumed. Pierce, *TAPL* §15.2 (record rules) and §15.6 (coercion
  semantics); Breazu-Tannen, Coquand, Gunter and Scedrov (1991); Luo (1999): by name (the types note
  §9). Frisch, Castagna and Benzaken, *Semantic subtyping* (2008): assumed. Lean 4.33.1's deriving
  and induction facts F1–F6: read and tested (the type-algebra note §0; the data probe).
- **Status.** See system map §8, R3; witnesses re-read at `6b3f2c92`.

### DB-16 — typing is a protocol per operation over a world

New 2026-10-01; re-read at `6b3f2c92` against decisions rows 134–137, 139 and 156 as recorded
there (row 154). Settled by decisions rows 44–45 (coarse values, a typed world; ruled 2026-09-19),
48 (existential middle types in the stack; ruled 2026-09-20), 96 (`Fits`; landed 2026-09-30),
106 and 107 (the queue facts and the exit clause), 134 and 137 (ruled 2026-10-01) and the slice-5
contract ruling of 2026-09-23. Rows 135, 136 and 156 have landed in the tree and row 139 in part;
what is ruled and what is open is each row's own status. The glossary of the formal notions (tree
name, literature name, law) is the dictionary's §3.9 (`docs/core/controlled-english.md`; moved
from system map §9 on 2026-10-03); this row links to it and does not copy it.

**The judgment.** A protocol says, for each operation, what it demands of the world it is
performed in (`pre`) and what its handler promises of the answer in the world it answers in
(`post`), through one ghost certificate per operation shared by both and by the continuation. A
program is typed at a world when every leaf satisfies the result predicate there, and every
operation's demand holds now and its continuation is typed at every later world in which the
handler answers within the protocol. The generic judgment `Typed` states this over any
signature. The concrete judgment `TypedProg` is its own inductive since the slice-5 ruling: it
reuses the generic protocol structure through `Ψ_S` (31 store rows) and `Ψ_F` (40 fiber rows),
and has four arms of its own for the control markers (`guard_`, `unguard`, `finishFinalizer`,
`scopeExit`); the scope-exit arm holds only at a world whose store holds the scope it exits
(`ScopeLive`, row 156). It shares the protocol shape of de Vilhena's judgment and is not an
instance of it, so `Typed.inl` and the generic inversions do not apply to it.

**The world and its order.** A world is `⟨ids, state, Γ, Π, Ρ, Θ⟩`: the machine's identifiers and
stores, and four ghost tables typing fibers, deferreds, cells and resume tokens. It is ordered by
table extension and cell compatibility (`World.le`), with external handle spellings stable
(`World.leHost`). Typing is upward closed along this order: `Typed.mono` for the generic
judgment, and for the concrete one `typedProg_mono` (proved; row 135), because every
continuation clause, the saved frames' arms and the hook protocols quantify over later worlds in
their own definitions. It is antitone in the order relation itself: a finer order keeps every
derivation (`typed_antitone`), a wider one can lose it (`order_widening_loses_typing`). Scope
presence persists along the order (`scopeLive_mono`: a scope entry is never removed). The typed
state as a whole is not upward closed: world validity has exact support
(`worldValid_not_upward_closed`), as a well-typed store in TAPL's sense is not; "Kripke" names
`Fits`, `TypedProg` and the saved stacks, not the typed state.

**Values are coarse; the world types them.** The runtime keeps one executable check, `Val.hasTy`,
which ignores the type arguments of handle sorts (Effect's own erasure); the proof side has one
judgment, `Fits`, constructor-complete over the actual encoding, whose handle leaves read the
world's declarations (rows 44, 96) and compare a declaration with a certificate in the checker's
order, `subN` (`sub (normalize a) (normalize b)`, row 137), and whose scope leaf reads the one
presence predicate (`ScopeLive` in `HandleFits`, row 156). Declared types come from creation
evidence and the checker, never from values (row 97). `Fits` is the world-indexed value
interpretation of a Kripke model for first-order references, a store typing in TAPL's sense
rather than a full logical relation (it has no arrow clause); `fits_hasTy` is type erasure to the
executable check. Membership is invariant under normalization and closed under the checker's
order and join (`fits_normalize`, `fits_subN`, `fits_join_left`, `fits_join_right`), and a term
the checker types evaluates to a member of its type (`evalTerm_fits`, TY-07). No step indexing
is needed, because worlds hold syntactic types that the handle arms read as declarations, so the
world is not defined through `Fits`. The exit judgment at every typed position is
`ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex` (row 107); part two, the
`missingService` clause, is row 117's presence (coeffect) contract.

**The typed state, split on `running`** (row 134). The machine-level statements read `J`,
`MachineTyped`: the generated typed state `TypedState` (world validity, every typed position, the
scheduler, observer and registration facts; it reads no queue and no current code), the world's
service table tied to the source's (row 112), `LiveCode` (the code of every fiber that has not
exited and is not running is typed with its stack at its declared type) and `MachineLive` (the
machine has not halted; a scheduled resume has its owner). The command loop reads `I`,
`ConfigTyped`: `J`, `ReadCode` (a running fiber whose code a queued `loop` or `deliver` reads is
typed) and `QueueOk` (every queued command's content, authority and keys, the observer and
enrollment correlations, and the scope of a queued `link` present). A budget cut drops the queue,
so `J` holds where the single invariant failed. `StepPreserves` over `I` is exactly the lift's
step premise (`guarded_stepKeeps_of_stepPreserves`), the loop-entry premise holds
(`evaluate_entry`), `J` is `I`'s projection (`machineTyped_of_configTyped`), all proved, and
`DecisionLift` is unchanged. `decision_preserves` and `typedState_reachable` are stated over `J`.

**What the formal pass refuted, and the repairs that landed** (2026-10-01). The clauses below,
as the tree declared them at `dceae006`, were refuted, and none of them is this basis's decision.
Each refutation is kept in the tree as a historical control over a local copy of the old clause,
beside the repair and its positive controls (tested, in the batteries named in the witnesses).
Each repair changed statements only, no runtime code.
- **Saved frames and hook protocols were typed at one world** (row 135, `E4-TYPED-CE-012`; it
  answers row 87 and strengthens row 48). World weakening failed for saved stacks
  (`stackAccepts_not_mono`) and the declared `M6Ledger.step_loop` was false at a concrete typed
  state (`step_loop_refuted`). The repair closes `FrameAccepts`'s arms, the three hook protocols
  and `HookLaws` over later worlds in their own definitions: saved stacks transport along the
  host order (`stackAccepts_mono`, `savedOk_mono`), the closed judgment refuses the bad frame at
  once (`bad_not_kripke_initial`) and gives the one-world judgment at the current world
  (`stackAccepts_now`), so nothing proved is lost, and the same `loop` keeps `I` once the frame
  is typed on every success (`step_loop_good`). Wrapping at the frame does not survive the walk
  (`output_not_kripke`, `hookLawsX_refused`).
- **`Fits` compared declared handle types in the raw order; the checker compares and joins in the
  normalized order** (row 137, `E4-TYPED-CE-009`; it re-reads row 96's D1). A checked, closed,
  admitted, host-free program loaded into no typed state, and the capstone failed with it
  (`m5_false`, `capstone_false`). The repair compares in `subN` at every handle arm and protocol
  entry that compares a declaration with a certificate; membership's closure laws hold, and the
  same program loads into `J`, where M5's and the capstone's propositions hold
  (`prog3_loads_typed`, `loadsTyped`, `capstone_at_load`).
- **Eight protocol rows' posts contradicted their handlers, and no obligation said a handler
  answers within its protocol** (row 136, `E4-TYPED-CE-010`, `E4-TYPED-CE-013`). The
  await-by-value post made M5 false for the typed corpus's own program (`typedState_load_false`).
  The repair puts the posts at the machine's answers (await-by-value at `exitOf ty.answer
  ty.error`, the cleanup rows at `unit`, `refModify`'s pre at the declared `nat`, the scope rows'
  pre carrying presence) and proves the handler rule once for the store rows and once per fiber
  frame (`storeStep_typed`, `answerFrame_typed`, `seqFrame_typed`), each row's fulfilment an
  instance in `M3bAdequacy`, proved or declared there; the corpus program now loads into `J`
  (`loadsTyped`). The close rows' handler side is rows 151 and 152: a lone finalizer may answer
  outside the close-scope post (`lone_release_outside_post`), and the close walk's protocol cannot
  carry shape-defect exclusion through reified exits (`closeSeq_protocol_refused`).
- **The machine-level statements read the typed state at a budget cut, where the command residue
  was dropped** (row 134, `E4-TYPED-CE-011`, at the cut only: the finished run is covered by row
  133's published-exit clause, `m9_root_inert`). The single invariant failed at the cut
  (`window_untyped`, `capstone_false_window`, `ledger_jointly_false_window`). The repair is the
  split above: `J` holds at the cut and at the finished run (`machineTyped_m6`,
  `machineTyped_m9`), the running-keyed clause being the reason (`running_exempt_at_m6`). It
  supersedes row 133's halt extension (plan O4).
- **The typed state did not exclude halting** (row 139, `E4-TYPED-CE-014`). Landed so far:
  `MachineLive`'s `stuck = none`, `QueueOk`'s live link scope, the scope-drop arms of the observer
  clauses, race-id liveness by `RegistrationState`, and the target and scope premises of the
  halting fiber rows; a close at an absent scope is refused (`close_code_refused_absent`);
  scope-handle validity is declared for M7 (`M7.exitHandles_valid`).
- **Scope presence was not one fact** (row 156, `E4-TYPED-CE-018`). The posts that answer a scope
  handle said only that the answer is some scope handle, and membership at `Ty.scope` read the
  target name only, so a checked program that makes a scope and forks into it had no typing at
  any world without that scope (Codex's second-eyes review, kept as history). The repair is one
  predicate, `ScopeLive` (the world's store holds the scope's entry), read by name by the scope
  arm of `HandleFits`, the five scope-handle posts, the scope arms of `storePre` and `fiberPre`,
  and `TypedProg`'s `scopeExit` constructor; it persists along the order, and a fiber's ambient
  scope is live from `J` (`ambientScope_live`). Positive controls: `makeThenClose_typed` and
  `forkAfterMake_typed` at every world, and `forkAfterMake_denotes` (M5's `DenotesTyped`
  proposition at its point). The machine stores' three spellings of presence are owed one shared
  definition (row 156).
- **`TypedProg` is not closed under bind**, because a scope marker's skipped exit bypasses the
  continuation (a non-local exit, not a handler frame in the context): `bind_not_typed`,
  `guard_bind_not_closed`. The sequencing tool M5 uses is the `seqR` compatibility lemma
  (`seq_typed`, resting on `close_typed`; landed by seat E), and M5's content is the denotation
  lemma `denoteR_typed` with term soundness: row 148. Term soundness is proved (`evalTerm_fits`;
  at any row table, `evalTerm_fits_native`); the ledger states it as its goal
  `M3bAssembly.evalTerm_fits`.

- **Decision.** Typing is a protocol per operation over a world: one certificate per operation
  shared by its pre, its post and its continuation; continuations typed at every later world, the
  saved frames and the hook protocols included (row 135); the generic `Typed` and the concrete
  `TypedProg` (its own inductive) share the protocol shape; worlds are ghost store typings ordered
  by extension, along which scope presence persists; values are coarse at run time and typed by
  the world through `Fits`, which compares declarations in the checker's order (row 137) and reads
  a scope's presence through the one predicate `ScopeLive` (row 156); the posts sit at the
  machine's answers, the handler rule a theorem (row 136); the exit judgment is `ExitOk`; the
  machine-level statements read the cut-tolerant `J`, and the command loop's configuration `I`
  adds the running fibers' code and the queue (row 134). Ruled: rows 134 and 137. Landed in the
  tree, each row holding its own ruling: rows 135, 136 and 156, and row 139 in part. Open: the
  close rows' handler side (rows 151 and 152). Owed: one definition of presence shared by the machine stores' three
  spellings of it (row 156).
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved, the generic judgment: `WorldOrder`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Protocol`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.mono`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.bind`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.widen`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Protocol.sum`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.inl`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.inr`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.inl_inv`
  (`src/Effect4/Laws/Effects/Protocol.lean`), `Typed.inr_inv`
  (`src/Effect4/Laws/Effects/Protocol.lean`) and protocol refinement `Typed.refine`
  (`src/Effect4/Laws/Effects/Protocol.lean:194`). The concrete judgment: `StoreCert`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `storePre`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `storePost`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `Ψ_S`
  (`src/Effect4/Laws/Program/Typed/Residual.lean:110`), `FiberCert`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `fiberPre`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `fiberPost`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `Ψ_F`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `TypedProg`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`) and its scope-exit arm `TypedProg.scopeExit`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `fiber_inv`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `IteratorProtocol`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `LoopProtocol`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `guard_frame`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), `typedProg_mono`
  (`src/Effect4/Laws/Program/Typed/Residual.lean`), the ledger's goal for it
  `M3bWorld.typedProg_mono` (`src/Effect4/Laws/Program/Typed/Residual.lean`, declared, its
  statement the theorem's). The world: `World` (`src/Effect4/Laws/Program/Typed/World.lean`),
  `World.le` (`src/Effect4/Laws/Program/Typed/World.lean`), `ScopeLive`
  (`src/Effect4/Laws/Program/Typed/World.lean`), `order_refl`
  (`src/Effect4/Laws/Program/Typed/World.lean`), `order_trans`
  (`src/Effect4/Laws/Program/Typed/World.lean`), `scopeLive_mono`
  (`src/Effect4/Laws/Program/Typed/World.lean`), `WorldValid`
  (`src/Effect4/Laws/Program/Typed/Validity.lean`), `World.leHost`
  (`src/Effect4/Laws/Program/Typed/Validity.lean`), `leHost_refl`
  (`src/Effect4/Laws/Program/Typed/Validity.lean`), `leHost_trans`
  (`src/Effect4/Laws/Program/Typed/Validity.lean`). Membership: `Val.hasTy`
  (`src/Effect4/Program/Typed.lean`), `HandleFits`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `Fits`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `FitsExit`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_hasTy`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_map`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_mono`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_sub`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_normalize`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_subN`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_join_left`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `fits_join_right`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`), `NoShapeDefect`
  (`src/Effect4/Laws/Program/Typed/Admission.lean`), `ExitOk`
  (`src/Effect4/Laws/Program/Typed/Admission.lean:31`), `evalTerm_fits`
  (`src/Effect4/Laws/Program/Typed/Admission.lean`), `evalTerm_fits_native`
  (`src/Effect4/Laws/Program/Typed/Admission.lean:88`). Frames: `FrameAccepts`
  (`src/Effect4/Laws/Program/Typed/Contracts.lean`), `StackAccepts`
  (`src/Effect4/Laws/Program/Typed/Contracts.lean`), `SavedOk`
  (`src/Effect4/Laws/Program/Typed/Contracts.lean`), `stackAccepts_mono`
  (`src/Effect4/Laws/Program/Typed/Contracts.lean`), `savedOk_mono`
  (`src/Effect4/Laws/Program/Typed/Contracts.lean`), `HookLaws`
  (`Test/Program/FramesNotKripke.lean`). The typed state: `TypedState`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `QueueOk`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `LiveCode`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `ReadCode`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `MachineLive`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `MachineTyped`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `ConfigTyped`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `machineTyped_of_configTyped`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean:277`), `ambientScope_live`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `evaluate_entry`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `StepPreserves`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `guarded_stepKeeps_of_stepPreserves`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`), `Guarded`
  (`src/Effect4/Laws/Machine/Lift.lean`), `DecisionLift`
  (`src/Effect4/Laws/Machine/Lift.lean`). The handler rule: `StoreTyped`
  (`src/Effect4/Laws/Program/Typed/Adequacy.lean`), `StoreImplements`
  (`src/Effect4/Laws/Program/Typed/Adequacy.lean`), `storeStep_typed`
  (`src/Effect4/Laws/Program/Typed/Adequacy.lean`), `answerFrame_typed`
  (`src/Effect4/Laws/Program/Typed/Adequacy.lean`), `seqFrame_typed`
  (`src/Effect4/Laws/Program/Typed/Adequacy.lean`). Sequencing (landed by seat E):
  `close_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean`), `seq_typed`
  (`src/Effect4/Laws/Program/Typed/Seq.lean:59`). Declared, not proved (each a
  `ProofGraph.Obligation`): `denoteR_typed`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean:1447`), `typedState_load`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean:1452`), `step_loop`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean:1478`), `decision_preserves`
  (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`), `typedState_reachable`
  (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`), `exitHandles_valid`
  (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`). Tested, the refutations kept as history
  over local copies of the old clauses: `stackAccepts_not_mono`
  (`Test/Program/FramesNotKripke.lean`), `step_loop_refuted`
  (`Test/Program/FramesNotKripke.lean`); `m5_false`
  (`Test/Counterexamples/Machine/Semantics/FitsOrder.lean`), `capstone_false`
  (`Test/Counterexamples/Machine/Semantics/FitsOrder.lean`); `typedState_load_false`
  (`Test/Program/ProtocolPosts.lean`); `window_untyped`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `capstone_false_window`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `ledger_jointly_false_window`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`). Tested, the positive and red
  controls of the current judgment: `step_loop_good` (`Test/Program/FramesNotKripke.lean`),
  `bad_not_kripke_initial` (`Test/Program/FramesNotKripke.lean`), `stackAccepts_now`
  (`Test/Program/FramesNotKripke.lean`), `hookLawsX_refused`
  (`Test/Program/FramesNotKripke.lean`), `output_not_kripke`
  (`Test/Program/FramesNotKripke.lean`); `prog3_loads_typed`
  (`Test/Counterexamples/Machine/Semantics/FitsOrder.lean`), `loadsTyped`
  (`Test/Counterexamples/Machine/Semantics/FitsOrder.lean`), `capstone_at_load`
  (`Test/Counterexamples/Machine/Semantics/FitsOrder.lean`); `loadsTyped`
  (`Test/Counterexamples/Machine/Semantics/AwaitLoad.lean`); `close_code_refused_absent`
  (`Test/Program/ProtocolPosts.lean`), `lone_release_outside_post`
  (`Test/Program/ProtocolPosts.lean`), `closeSeq_protocol_refused`
  (`Test/Program/ProtocolPosts.lean:548`); `m9_root_inert`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `running_exempt_at_m6`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `worldValid_not_upward_closed`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `machineTyped_m6`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `machineTyped_m9`
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean`); `makeThenClose_typed`
  (`Test/Counterexamples/Machine/Semantics/ScopePresence.lean`), `forkAfterMake_typed`
  (`Test/Counterexamples/Machine/Semantics/ScopePresence.lean`), `forkAfterMake_denotes`
  (`Test/Counterexamples/Machine/Semantics/ScopePresence.lean`); the red controls
  `typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean`), `bind_not_typed`
  (`Test/Program/TypedProgBindRed.lean:106`), `guard_bind_not_closed`
  (`Test/Program/TypedProgBindRed.lean:120`). Proved in a probe, by the model probe's pedigree
  seat: `typed_antitone` (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:198`)
  and `order_widening_loses_typing`
  (`docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean:215`). The formal pass's
  probes and their ports at `dceae006` (`docs/research/2026-10-01-landing/ports-at-dceae006/`) are
  the sources of the batteries above, which replace them as witnesses.
- **Refusals.** In the register (`Test/Counterexamples/REGISTER.md`) at `6b3f2c92`:
  `E4-TYPED-CE-003`, `E4-TYPED-CE-004`, `E4-TYPED-CE-005`, `E4-TYPED-CE-006`, `E4-TYPED-CE-007`,
  `E4-TYPED-CE-008`, `E4-TYPED-CE-009`, `E4-TYPED-CE-010`, `E4-TYPED-CE-011`, `E4-TYPED-CE-012`,
  `E4-TYPED-CE-013`, `E4-TYPED-CE-014`, `E4-TYPED-CE-016`, `E4-TYPED-CE-017`, `E4-TYPED-CE-018`,
  `E4-SCHED-CE-010`, `E4-SCHED-CE-011`, `E4-SCHED-CE-012`, `E4-SCHED-CE-013`, `E4-SCHED-CE-014`,
  `E4-SCHED-CE-016`, `E4-SCHED-CE-017`, `E4-SCHED-CE-018`, `E4-SCHED-CE-019`, `E4-SCHED-CE-020`.
  DI-10 (a bind law waits for its neutral-stack shape). Decisions rows: ruled 44, 45, 48, 96, 106,
  107, 134, 137, 138, 150 (a narrower lift for the six fold-level guard inductions, `FoldLift`
  (`src/Effect4/Laws/Machine/Lift.lean`), with `DecisionLift` unchanged); landed with their
  rulings their own: 135, 136, 156, and 139 in part; open: 87, 117, 140, 148, 151, 152, 153;
  status: those rows.
- **Sources.** `docs/research/2026-09-20-m1-kickoff-confidence-and-design-representations.md` §2–§4
  (tracked; its §3 mapping of `Typed.mono` is corrected below);
  `docs/research/2026-09-18-typed-state-composed-graph.md` §4 (tracked);
  `docs/research/2026-09-23-foundations-slice5-contract-ruling.md` (tracked);
  `docs/research/2026-09-21-foundations-review-and-theoretical-analysis.md` §4 (tracked; its §2.4,
  §4.3 and §7.2 item 5 are corrected by the model probe's synthesis §3.2 items 2–3);
  `docs/research/2026-09-05-effects-papers-review.md` §1.3, A2, A3, G8 (tracked);
  `docs/research/2026-09-30-pass/membership/note.md` §2 (tracked);
  `docs/research/2026-09-30-model-probe/synthesis.md` §3.1 levels 0–2, §3.2 items 1–3 (tracked);
  `docs/research/2026-10-01-formal-pass/synthesis.md` §1, §2, §3.1, §4.4, §5 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/note.md` §2.6 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-01, ALG-18 (tracked);
  `docs/research/2026-10-01-formal-pass/types/note.md` §4 (tracked);
  `docs/research/2026-10-01-formal-pass/types/verify.md` TY-01, TY-19 (tracked);
  `docs/research/2026-10-01-formal-pass/proofs/note.md` §1, G1, G2, G4, G6 (tracked);
  `docs/research/2026-10-01-landing/plan.md` §0, §2 (tracked);
  `docs/research/2026-10-01-landing/receipt-B.md` (tracked; rows 135, 136);
  `docs/research/2026-10-01-landing/receipt-C.md` (tracked; rows 134, 139);
  `docs/research/2026-10-01-landing/receipt-I.md` (tracked; the union of seats B, C, E and F);
  `docs/research/2026-10-01-landing/receipt-I2.md` (tracked; rows 137 and 156);
  `docs/research/2026-10-01-landing/codex-second-eyes/review.md` (tracked; row 156).
- **Literature.** Level 0, the free monad typed by a protocol per operation: Xia et al.,
  *Interaction Trees*, §3.2 and §7: read (lit-papers Q7, Q10); de Vilhena's thesis (2022), Def. 2.2,
  2.4–2.8 and the rules Bind and Monotonicity: read (papers review §1.3; Def. 2.4, 2.5, 2.8 and
  Monotonicity read again by the model probe's pedigree seat); the handler rule's premise, Def.
  2.2, as the papers review's *Implements* (A2), which the store rows' adequacy states. The
  correction (model-probe synthesis §3.2 item 1): Monotonicity is `Typed.widen` plus protocol
  refinement (`typed_along`); `Typed.mono` is world-order weakening, the upward closure of Kripke
  and Iris semantics (by name). Timany and Birkedal, "non-local control breaks the bind rule": by
  name, as de Vilhena §2.4 cites it (read via papers review G8). Level 1, the world and its order:
  de Vilhena §4.3; Cohen, Grunfeld, Kirst and Miquey (FSCD 2025) §4.1.1; Jacobs, Prop. 6.2.4:
  read (papers review A3); Ahmed (2004 thesis; 2006), Ahmed, Dreyer and Rossberg (2009), Appel and
  McAllester (2001), Iris: by name; Pierce, *TAPL* ch. 13 (§13.4–§13.5, store typings): by name;
  Reynolds (2000), extrinsic typing: by name. Level 2, the typed stack: Danvy and Nielsen,
  *Defunctionalization at work*, §1 and §3: read (lit-papers Q12); Harper, *PFPL* ch. 28;
  Reynolds; Van Horn and Might: by name. The typed state as an inductive invariant with a ghost
  world: Wright and Felleisen (1994); Manna and Pnueli; Owicki and Gries; Abadi and Lamport (1991);
  Jones (1983); O'Hearn, Reynolds and Yang (2001): by name.
- **Status.** See system map §8, R9 (and R1, R4); witnesses re-read at `6b3f2c92`.

### DB-17 — services and layers are one requirement row calculus

New 2026-10-01. Settled by the provision algebra (landed at `f182d2b3`, 2026-09-04), DI-20, DI-28
and decisions rows 51 (`ServiceOk` context-wide; ruled 2026-09-20), 90 (the context typed per
fiber; ruled 2026-09-24), 104 and 105 (ruled, landed). This row owns the calculus's rationale. One
context and layers by path are DB-12's; the service table's place in the world and the lawful
service declarations are rows 112–114 (ruled 2026-10-01) and 118 (structured carriers, open); the
glossary entry for provision is in the dictionary's §3.9 (`docs/core/controlled-english.md`).

**The rows.** A requirement row is a finite set of service keys with one canonical spelling
(`Row`), so its laws are equalities: union is associative, commutative and idempotent with the
empty row as unit, and difference has its laws. Rows are the free bounded join-semilattice on
service keys, with relative complement. Adding a requirement never invalidates a check, which is
why requirement checking is monotone.

**Provision is substitution.** A layer's signature is `⟨out, error, requires⟩` (`LayerTy`,
rc.112's `Layer<ROut, E, RIn>`), and `provide` is one equation on rows,
`requires (l ◁ d) = (requires l ∖ out d) ∪ requires d`: the free-variable law of substitution,
which is also the type rc.112 prints for `Layer.provide` (`Layer.ts:2008-2089`, the overload at
`:2089`) and for an HTTP
middleware's `ApplyServices`. The checker grades programs the same way: providing a layer removes
its outputs from the body's row and adds the layer's own (the checker's `provideLayer` arm), and
`scoped` discharges the scope key through `bodyRequires` (DI-63). Regrouping is free only through
`provideMerge`: `provide` is not associative on rows, because a nested `provide` hides the inner
dependency's outputs from the outer dependent (`provide_not_assoc`, a red control in the tree since
`a561d604`), while `provide` chains
regroup as one `provideMerge` (`provide_provide_rows` on rows; `provideMerge_assoc` and
`provide_provide` on the whole layer type, error column included, since `Ty.join` is associative).
`merge` is commutative on rows and right-biased on the built context: the type does not see
provider order, the run does.

**A requirement row is a grade.** A program's requirement row is the grade of a graded effect
system, removed at provision as a handler removes the operations it handles; read more closely it
is a flat coeffect: what the context must provide. A context satisfies a row exactly when the row
is included in the context's key row (`satisfies_iff_subset_keysRow`): satisfaction is inclusion
into `keysRow`, a representability fact with one monotone map. The law that makes a grade mean
something, effect
soundness (a program at row `r`, run under a context that satisfies `r`, never dies with
`missingService`), is row 117's: a presence clause per position, a requires-monotone side
condition on frames that discharge nothing, and the restored context at `scopeExit` and
`release` (proposed, amended 2026-10-01; `E4-TYPED-CE-008` is its red control).

**What was cut, and what is owed.** `build_total` (every well-typed layer builds under every
context that satisfies its row, for any leaf semantics honest about its own leaves) and
`buildAll_total` landed with the algebra at `f182d2b3` and were cut at `b08f3b58` (2026-09-18)
with no consumer; the module header's claim that it was proved was removed by row 105's landing
(`57c93ba4`, merged at `0c534f06`). R5 is the consumer: their restoration and the refinement
`lower_refines_build` are owed there (row 147, proposed). Requirement and
effect polymorphism in a stored program stay refused as a profile choice, not an impossibility
(DI-20, DI-28): builders in Lean and OCaml are polymorphic and instantiate closed `Eff` programs,
and subeffecting (`Row.Subset` as subsumption) is the shape on offer. Who may provide a key is a
capability question the calculus records and does not decide (`PROV-FB-KEY-FORGERY`).

- **Decision.** Requirement rows are the free bounded join-semilattice on service keys with relative
  complement; `provide` is substitution; regrouping is through `provideMerge`; a program's row is
  its grade, a flat coeffect; satisfaction is inclusion into the context's key row; grading
  soundness is row 117's theorem; `build_total`'s restoration is owed under R5.
- **Witnesses** (re-read at `6b3f2c92`). Defined or proved: `Row` (`src/Effect4/Data/Row.lean`),
  `union_assoc` (`src/Effect4/Data/Row.lean`), `union_comm` (`src/Effect4/Data/Row.lean`),
  `union_idem` (`src/Effect4/Data/Row.lean`), `union_empty_left`
  (`src/Effect4/Data/Row.lean`), `union_empty_right` (`src/Effect4/Data/Row.lean`),
  `mem_diff` (`src/Effect4/Data/Row.lean`), `diff_subset` (`src/Effect4/Data/Row.lean`),
  `diff_eq_empty_iff_subset` (`src/Effect4/Data/Row.lean`), `union_diff_distrib`
  (`src/Effect4/Data/Row.lean`); `Requirement` (`src/Effect4/Machine/Context.lean`),
  `keysRow` (`src/Effect4/Machine/Context.lean`), `Satisfies`
  (`src/Effect4/Machine/Context.lean`); `LayerTy` (`src/Effect4/Program/Typing/Rules.lean`),
  `provide` (`src/Effect4/Program/Typing/Rules.lean`), `provideMerge`
  (`src/Effect4/Program/Typing/Rules.lean`), `bodyRequires`
  (`src/Effect4/Program/Typing/Rules.lean`); the checker's arms `scoped`
  (`src/Effect4/Program/Checker.lean:198`) and `provideLayer`
  (`src/Effect4/Program/Checker.lean:211`); `provide_out` (`src/Effect4/Program/Provision.lean`),
  `provide_requires_subset` (`src/Effect4/Program/Provision.lean`), `provide_discharges`
  (`src/Effect4/Program/Provision.lean`), `provide_closed`
  (`src/Effect4/Program/Provision.lean`), `covers_of_provide_closed`
  (`src/Effect4/Program/Provision.lean`), `provide_provide_rows`
  (`src/Effect4/Program/Provision.lean`), `merge_rows_comm`
  (`src/Effect4/Program/Provision.lean`), `merge_requires`
  (`src/Effect4/Program/Provision.lean`), `provide_requires_antitone_out`
  (`src/Effect4/Program/Provision.lean`), `satisfies_iff_subset_keysRow`
  (`src/Effect4/Program/Provision.lean`), `appTy_closed_iff`
  (`src/Effect4/Program/Provision.lean`), `build` (`src/Effect4/Program/Provision.lean`),
  `join_assoc` (`src/Effect4/Laws/Program/TypeAlgebra.lean`); tested: `leftWins` and `rightWins`
  (`src/Effect4/Program/Provision.lean`, same signature, different built contexts) and
  `Test/Program/ProvisionContract.lean`. The cut theorem: `build_total` at
  `git:f182d2b3:src/Effect4/Program/Provision.lean:429` (absent at `6b3f2c92`). Proved in the tree
  since `a561d604` (landed by seat E from the algebra verifier's probe): `provideMerge_assoc_rows`
  (`src/Effect4/Program/Provision.lean`), `provideMerge_assoc`
  (`src/Effect4/Laws/Program/Provision.lean:32`), `provide_provide`
  (`src/Effect4/Laws/Program/Provision.lean:45`); tested, the red control
  `provide_not_assoc` (`Test/Program/ProvideRows.lean`).
- **Refusals.** In `Test/Counterexamples/REGISTER.md`: `E4-PROV-CE-001`, `E4-PROV-CE-002`,
  `E4-PROV-CE-003`, `E4-PROV-CE-004`, `E4-PROV-CE-005` and `E4-PROV-CE-006` (repaired; the archive's
  rows with those two ids are other statements), `E4-TYPED-CE-008` (row 117's red control); in
  `Test/Counterexamples/Archive/REGISTER.md`: `E4-PROV-CE-007` (a name table must skip the
  machine's four reserved keys);
  `PROV-FB-KEY-FORGERY`, `PROV-FB-STRING-VALUE` (fallback ids); DI-20, DI-24, DI-28, DI-63.
  Decisions rows: ruled 51, 90, 104, 105, 112, 113, 114; proposed 117, 118, 147; status: those rows.
- **Sources.** `docs/research/2026-09-04-provision-algebra.md` §§1–3, §6, §7, §10 (tracked);
  `docs/research/2026-09-05-effects-papers-review.md` A1 (tracked);
  `docs/research/2026-09-30-model-probe/synthesis.md` §2.2 R5, §3.1 "Services and layers are one row
  calculus", §3.2 item 7 (tracked); `docs/research/2026-09-30-codex-review-model-probe/audit.md` §6
  (tracked); `docs/research/2026-10-01-formal-pass/synthesis.md` §2, §4.4, §5 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/note.md` §1 row 8, §2.8, A11 (tracked);
  `docs/research/2026-10-01-formal-pass/algebra/verify.md` ALG-14, ALG-15, ALG-16 (tracked).
- **Literature.** Burckhardt et al., *Durable Functions* (OOPSLA 2021), Thm. 5.3 and 6.4; Lamport
  and Merz, *Prophecy Made Simple*, §3–§4.1 and §7; Kuessner, Mogk, Wickert and Mezini, *Algebraic
  Replicated Data Types* (ECOOP 2023), §4–§5: read (the provision algebra §7). de Vilhena's Tes,
  §7.3 (a row is a permission and a distinctness requirement): read (papers review §1.3). Leijen,
  *Type directed compilation of row-typed algebraic effects* (POPL 2017), §3 and §3.2: read
  (lit-papers Q4). Hillerström and Lindley, *Liberating effects with rows and handlers*: read, its
  kinds and handler types only (lit-papers §D). Katsumata (2014) and Orchard et al. (2014), graded
  monads: by name (the coherence principle §4b). Petricek, Orchard and Mycroft (2014), coeffects: by
  name (the algebra verifier, ALG-15). Bauer and Pretnar (2014), effect systems: by name. Wand;
  Rémy; Gaster and Jones: by name (the 2026-09-09 types scout, as the data probe §6.4 records it;
  the type-algebra note §8 lists them as assumed). Morris and McKinna: assumed (the type-algebra
  note §8).
- **Status.** See system map §8, R5; witnesses re-read at `6b3f2c92`.

## Source and evidence rules

The evidence classes answer different questions and are never substituted for
one another.

| Evidence | Answers | Does not answer |
| --- | --- | --- |
| Paper and mechanization | Which semantic construction and theorem shape is known in the cited system | Whether Effect4's definitions instantiate it correctly |
| Lean kernel proof | Whether a proposition follows from the imported declarations and recorded axioms | Whether the proposition specifies Effect TypeScript correctly |
| Upstream source commit | What repository state was reviewed | Which bytes a package manager installed |
| Package integrity and file digests | Which target bytes were exercised | Whether the upstream repository and package are semantically equivalent |
| Typechecker or language-service result | Whether a finite generated case satisfies that tool and version | Runtime behavior or surface exhaustiveness |
| Runtime vector | What happened for a finite execution | Denotational equivalence for all programs |
| Corpus census | Which public spellings appeared in a pinned sample | Completeness of the target API or semantic correctness |

The exact operational pins, source digests, and cutover dispositions are owned
by [`docs/GENERATED.md`](GENERATED.md): the generated inventory, the generation
order, the `cut-from:` stamps and the gates that compare them. (This paragraph
previously pointed at a `PORT-MANIFEST.md` above the repository root, which has
never existed here.) This document owns the architectural consequences of that
evidence.

## Designs excluded by this basis

The following choices require a new decision record and a breaker packet:

- a second free-program carrier beside `Program`;
- an `HHandler` whose only higher-order content is a first-order child address (a `Point` on
  `Eff`; a `BlockId` on the archived Flow route);
- a standalone executable `Behavior` datatype that duplicates relational
  semantics;
- a denotation defined by one fixed fuel value or a universal fixed-fuel bind
  law;
- treating a live frontier as failure, defect, interruption, or refusal;
- storing raw `Expr`, host closures, promises, or runtime objects as canonical
  program content;
- making PolyFun, Mathlib, Foldlab, Effect TypeScript, or the Effect language
  service the semantic owner of the core library;
- claiming full reification from compilation, a finite corpus sweep, or a
  finite runtime test alone;
- requirement polymorphism in a **stored program** (DI-20, refused 2026-09-09 as a
  profile choice): this profile has no runtime polymorphic syntax and adds none.
  Lean and OCaml builders are polymorphic and instantiate closed `Eff` programs;
  subeffecting (`Row.Subset` as subsumption) is the shape on offer. This is a
  bounded refusal, not a claim that polymorphism is impossible here; and
- effect polymorphism in a stored program (DI-28), refused on the same ground and
  with the same bound.

These exclusions keep the proof graph inspectable while leaving room for
explicit comparison models and target-specific implementations.

## Literature names, corrected (2026-10-01)

The literature's name for each object, where an earlier note used a looser one. One line each,
with its mark. This is pedigree only: what the tree calls these objects is the vocabulary's,
owned by the dictionary (`docs/core/controlled-english.md`), which this section does not
restate. Sources: the formal pass's synthesis §1 and §5 (tracked), the organization verifier's M7
and the types verifier's §3 (tracked).

- **Not an ornament.** `Ty → Representation` is a section with a partial left inverse: a partial
  isomorphism onto its image, and a retraction until its exactness lands (row 128). An ornament's
  forgetful map is total (McBride 2011; Dagand and McBride 2012: by name).
- **Adequacy, not "simulation", for the equations.** `run_eq_meaning`, `loopAgreement` and
  `run_eq_ref` are equal-observation statements on named fragments: computational adequacy (machine
  against meaning) or semantic preservation (machine against reference), each proved through a
  simulation relation; for `run_eq_ref` that relation is the book's lock-step one (`BookMeans` and
  `ReplayRel` in `src/Effect4/Laws/Machine/Book.lean`, instantiated as `BMeans` and lifted to tapes
  by `replay_rel`) (Lynch and Vaandrager 1995; Plotkin 1977: by name).
- **Injectivity, not "finality".** "Equal observations imply equal runs" is injectivity of the
  behaviour map, neither claimed nor needed (row 146); `behaviour_unique` is the uniqueness half of
  finality for the session runner (Jacobs: read, papers review §1.4; Rutten: by name).
- **Bisimulation is Jacobs ch. 3** (Thm 3.4.1: bisimilarity is equality of behaviour), read via the
  papers review §1.4; not ch. 2.
- **A bounded join-semilattice.** `CTy` has a least upper bound and a bottom; "not a lattice" is
  unsupported, and meets are not claimed (Pierce, *TAPL* §16.3: by name; the types verifier TY-17).
- **Its own inductive.** `TypedProg` shares the protocol shape of de Vilhena's judgment and is not
  an instance of it, since the slice-5 ruling (de Vilhena: read, papers review §1.3).
- **No step indexing, for this reason.** Worlds hold syntactic types that the handle arms of `Fits`
  read as declarations, so the world is not defined through `Fits`; "values carry no code" is the
  looser reason (Ahmed 2004; Appel and McAllester 2001: by name; the types verifier TY-19).
- **"Kripke" names `Fits`, `TypedProg` and the saved stacks (closed under later worlds since row
  135), not the typed state**, whose world validity has exact support and is not upward closed
  (TAPL ch. 13's well-typed store: by name).
- **A runner only on the fragments.** The machine runs the free model against the store comodel on
  the straight and looped fragments; past the first fiber operation it is an abstract machine
  related to the reference by a lock-step simulation, at the empty host table (Ahman and Bauer 2020:
  by name).
- **Elgot's law at the limit only.** The budgeted meaning is the Kleene chain of a least fixed
  point; Elgot's fixpoint law, leastness and single-valuedness hold at its limit, never at one
  budget (Elgot 1975; Adámek, Milius and Velebil 2006: by name).
- **Not bind-closed, for a non-local exit.** `TypedProg` is not closed under bind because a scope
  marker's skipped exit bypasses the continuation, not because of a handler frame in the context
  (Timany and Birkedal: by name, as de Vilhena §2.4 cites it, read via papers review G8).
- **Hierarchy-consistent, not persistent.** Growing Σ_core adds elements to an old sort, which is
  why a function with a catch-all arm can change (Ehrig and Mahr 1985: by name).
- **Not CompCert's measure.** A budget with its sufficiency receipt claims nothing about divergence;
  a stuttering measure preserves it (Leroy 2009: by name).
- **Analogies, not theorems.** The guard's tokens as "exclusive ghost tokens", and "Schema and
  program" as a graded Freyd category (system map §6 calls the second a proposed organization)
  (Power and Robinson 1997; Levy, Power and Thielecke 2003: by name).
- **A flat coeffect, and inclusion, not an adjunction.** A requirement row reads most closely as a
  flat coeffect, what the context must provide; satisfaction is inclusion into the context's key
  row, a representability fact with one monotone map (Petricek, Orchard and Mycroft 2014: by name).

## Bibliography

One list (2026-10-01; it replaces the former "Primary sources"). Built from the model probe's
literature column (`docs/research/2026-09-30-model-probe/synthesis.md` §3.1), the rows' citations
and the formal pass's marks (`docs/research/2026-10-01-formal-pass/synthesis.md` §2, §5). Each
entry carries the mark of the note that cites it: **read**, with the note that records the reading
and the sections read; **by name**, cited without a section read in the tree; **assumed**, a claim
about the paper's content that nobody in the tree has checked. No entry was promoted by this
refresh, and no paper was opened for it; titles and venues are given only where a cited note or
the former list gives them. "lit-papers" is `docs/research/2026-09-07-lit-papers.md`, whose corpus
numbers its papers 01–21; "the papers review" is `docs/research/2026-09-05-effects-papers-review.md`;
"core math" is `docs/research/2026-09-05-runtime-semantics-core-math.md`; "the coherence principle"
is the literature list of `docs/research/history/coherence-principle.md`.

*Algebraic effects, signatures and sums*

- Gordon D. Plotkin and Matija Pretnar,
  [*Handling Algebraic Effects*](https://arxiv.org/abs/1312.1399). **Read**, §1 and §5 (lit-papers
  Q11, corpus 05; §§2–4 and 6–7 not read). DB-01.
- Andrej Bauer and Matija Pretnar,
  [*Programming with Algebraic Effects and Handlers*](https://arxiv.org/abs/1203.1539) (2015). **By
  name.** DB-01. Not a source for "the coproduct of algebraic theories" (the model probe §3.2 item
  2).
- Bauer and Pretnar (2014), an effect system for algebraic effects. **By name** (the algebra seat).
  DB-17.
- Plotkin and Power, *Notions of computation determine monads* (FoSSaCS 2002), and their 2003 paper
  on algebraic operations. **By name** (core math §6); that state is presented by lookup and update
  with four equations is **assumed** (the algebra seat). DB-05.
- Plotkin and Power, *Tensors of comodels and models for operational semantics* (2008). **By name**
  (core math §7). DB-07.
- Ahman and Bauer, *Runners in action* (ESOP 2020). **By name** (core math §7). DB-07.
- Hyland, Plotkin and Power, *Combining Effects: Sum and Tensor* (TCS 357, 2006). **By name only**:
  never read in the tree (the 2026-09-02 algebra-package review lists it "primary not read"); every
  claim about its content is **assumed**. DB-01.
- Swierstra, *Data Types à la Carte* (JFP 2008). **Read**, §2 and §6 (the model probe's pedigree
  seat, `docs/research/2026-09-30-model-probe/pedigree/note.md`). DB-01.
- Goguen, Thatcher, Wagner and Wright (JACM 1977). **By name** (the coherence principle). DB-01.
- Fiore, Plotkin and Turi (LICS 1999), binding signatures. **By name** (the coherence principle).
  `Eff` as a binding signature's term algebra.
- Ehrig and Mahr (1985), persistency. **By name** (the types verifier, TY-06). DB-01.
- Benke, Dybjer and Jansson (2003); Chapman, Dagand, McBride and Morris (ICFP 2010), signatures as
  data. **By name** (the coherence principle §1). R1.

*Scoped and higher-order effects*

- Wu, Schrijvers and Hinze, *Effect handlers in scope* (2014). **Read**, §9–§10 (lit-papers Q2,
  corpus 10). DB-05.
- Piróg, Schrijvers, Wu and Jaskelioff, *Syntax and semantics for operations with scopes* (2018).
  **Read**, §1.2–§1.3 (lit-papers Q2, corpus 11). DB-05.
- van den Berg et al., *Latent effects for reusable language components* (2021). **Read**, §2.1–§2.3
  and §3's opening (lit-papers Q2, §D, corpus 13). DB-05, R7.
- Bach Poulsen and van der Rest, *Hefty algebras* (2023). **Read**, §1.2–§1.4, §2.5–§2.6, §3.1,
  §3.4–§3.5, §5.2–§5.4 (lit-papers Q2, §D, corpus 14). DB-05, R10.
- Birthe van den Berg and Tom Schrijvers,
  [*A Framework for Higher-Order Effects & Handlers*](https://arxiv.org/abs/2302.01415). **Read**,
  §3 and §4.1 (lit-papers §D, corpus 15). DB-05.
- Roger Bosman, Birthe van den Berg, Wenhao Tang, and Tom Schrijvers,
  [*A Calculus for Scoped Effects & Handlers*](https://arxiv.org/abs/2304.09697). **Read**, its
  headings and §3's framing only; §§4–9 not read (lit-papers §C, §D, corpus 12). DB-05.

*Behaviour, trees, iteration and coalgebra*

- Li-yao Xia et al.,
  [*Interaction Trees: Representing Recursive and Impure Programs in Coq*](https://arxiv.org/abs/1906.00046)
  (POPL 2020). **Read**, §3.2 and §7 with Def. 1–2 (lit-papers Q7, Q10, corpus 02); its `iter` laws
  **by name** (core math §4). DB-03, DB-04, DB-16.
- Nicolas Chappe et al.,
  [*Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq*](https://arxiv.org/abs/2211.06863).
  **Read**, §2.2, §7.1, §7.2, §8 (lit-papers Q7, §0, corpus 03). DB-03, DB-05.
- Jacobs, *Introduction to Coalgebra* (draft 2.00, 2012). **Read** (the papers review §1.4, §7):
  §2.5's opening (Prop. 2.5.3), §3.4 (Thm 3.4.1), §5.2, §5.3 (Prop. 5.3.3, Thm 5.3.4), §5.5, §6.2
  (Prop. 6.2.4), §6.8's opening, §6.9; chapters 1 and 4 not read. DB-03, DB-04, DB-16.
- Rutten (2000). **By name** (the formal synthesis §2). DB-03.
- Capretta, *General recursion via coinductive types* (LMCS 2005). **By name** (core math §3).
  DB-04.
- Chapman, Uustalu and Veltri, *Quotienting the delay monad by weak bisimilarity* (ICTAC 2015). **By
  name** (core math §3). DB-04.
- Hasuo, Jacobs and Sokolova, *Generic trace semantics via coinduction* (2007). **By name** (core
  math §2). DB-04.
- Elgot (1975). **By name** (the coherence principle). DB-04.
- Adámek, Milius and Velebil, *Elgot algebras* (2006). **By name** (the coherence principle; core
  math §3). DB-04.
- Lee, Cho, Song, Hur et al., *Fair operational semantics* (PLDI 2023). **By name** (core math §9).
  DB-03, R12.
- Lynch and Vaandrager (I&C 1995); Plotkin (1977), for adequacy; Leroy, CompCert (CACM 2009); Milner
  (1989). **By name** (the coherence principle; core math §11; the formal synthesis §2). DB-04, the
  literature names.

*Typing, worlds and protocols*

- de Vilhena, *Proof of Programs with Effect Handlers* (thesis, 2022). **Read**: chapters 1, 2 and
  4, §6.1–§6.2, and chapter 7 to §7.5 (the papers review §1.3, §7); Def. 2.4, 2.5, 2.8 and the rule
  Monotonicity read again from the text copy by the model probe's pedigree seat. DB-16, DB-17.
- Cohen, Grunfeld, Kirst and Miquey, *From Partial to Monadic* (FSCD 2025). **Read**, §1–§5,
  Appendices A–C, Appendix D to Theorem 18 (the papers review §7). DB-16.
- Timany and Birkedal, on non-local control and the bind rule. **By name**, as de Vilhena §2.4 cites
  it (read via the papers review G8). DB-16.
- Ahmed (2004 thesis; 2006); Ahmed, Dreyer and Rossberg (2009); Appel and McAllester (2001); Iris
  (Jung et al. 2018). **By name** (the foundations review §4.1; the types verifier TY-19). DB-16.
- Pierce, *Types and Programming Languages* (2002): ch. 13 (§13.4–§13.5), ch. 15 (§15.2, §15.6), ch.
  16 (§16.3). **By name** (the types note §9). DB-15, DB-16.
- Reynolds (2000), extrinsic typing; Wright and Felleisen (1994); Milner (1978). **By name** (the
  formal synthesis §2, §5). DB-16.
- Nanevski et al., Hoare Type Theory. **By name** (the foundations review §2.1, via the model probe
  §3.1). R4.
- Danvy and Nielsen, *Defunctionalization at Work* (2001). **Read**, §1 and §3 (lit-papers Q12,
  corpus 16). DB-16, R7.
- Harper, *Practical Foundations for Programming Languages* (2nd ed., 2016), ch. 28; Felleisen and
  Friedman's CK machine (1986); Reynolds; Van Horn and Might. **By name.** DB-16.
- Manna and Pnueli; Owicki and Gries; Abadi and Lamport (1991); Jones (1983); O'Hearn, Reynolds and
  Yang (2001); Hoare (1972). **By name** (the algebra note §2.7; the formal synthesis §2). DB-16.
- Modal p-morphisms (preservation and reflection of modal formulas). **Assumed** (the model probe
  §3.1). DB-01's C5.

*Rows, records and grading*

- Leijen, *Type directed compilation of row-typed algebraic effects* (POPL 2017). **Read**, §3 and
  §3.2 (lit-papers Q4, corpus 17). DB-17.
- Hillerström and Lindley, *Liberating effects with rows and handlers*. **Read**, its kinds and
  handler types only (lit-papers §D, corpus 18). DB-17.
- Katsumata (2014); Orchard et al. (2014), graded monads. **By name** (the coherence principle §4b).
  DB-17.
- Petricek, Orchard and Mycroft (2014), coeffects. **By name** (the algebra verifier, ALG-15).
  DB-17.
- Burckhardt et al., *Durable Functions: Semantics for Stateful Serverless* (OOPSLA 2021), Thm. 5.3
  and 6.4; Lamport and Merz, *Prophecy Made Simple*, §3–§4.1 and §7; Kuessner, Mogk, Wickert and
  Mezini, *Algebraic Replicated Data Types* (ECOOP 2023), §4–§5. **Read** (the provision algebra
  §7). DB-17.
- Wand; Rémy (1994); Gaster and Jones (1996); Leijen, *Extensible Records with Scoped Labels* (TFP
  2005). **By name** (the 2026-09-09 types scout, as the data probe §6.4 records it; the
  type-algebra note §8 lists the first three as assumed). DB-15, DB-17.
- Morris and McKinna (POPL 2019). **Assumed** (the type-algebra note §8). DB-15, DB-17.
- Breazu-Tannen, Coquand, Gunter and Scedrov, *Inheritance as implicit coercion* (I&C 1991); Luo,
  *Coercive subtyping* (JLC 1999). **By name** (the types note §9). DB-15.
- Frisch, Castagna and Benzaken, *Semantic subtyping* (JACM 2008). **Assumed** (the type-algebra
  note §5.3). DB-15.
- Comon et al., *Tree Automata Techniques and Applications*; Amadio and Cardelli, *Subtyping
  recursive types* (TOPLAS 1993). **By name** (the types note §9). Rows 124, 127.

*Embeddings and organization*

- Rendel and Ostermann (2010); Matsuda and Wang (2013); Foster et al. (2007); Pickering, Gibbons and
  Wu (2017). **By name** (the coherence principle). The K2 laws; row 128.
- McBride (2011); Dagand and McBride (2012), ornaments. **By name** (the coherence principle); the
  ornament reading of `Ty → Representation` is wrong (the literature names above).
- Power and Robinson (MSCS 1997); Levy, Power and Thielecke (I&C 2003), Freyd categories. **By
  name** (the coherence principle §4b); an analogy here. R8.

*Hosts and capabilities*

- Loring, Marron and Leijen, *Semantics of Asynchronous JavaScript*. **Read**, §2.3–§2.4 (lit-papers
  Q6, corpus 01). R6.
- Xie and Leijen, *Generalized Evidence Passing for Effect Handlers*. **Read**, §2.3–§2.6 and §2.12
  (lit-papers Q1, corpus 09). R7.
- Sivaramakrishnan et al., *Retrofitting Effect Handlers onto OCaml*. **Read**, §1, §3.1–§3.2, §4.1,
  §5.2–§5.4 (lit-papers Q3, §D, corpus 19). DB-07.
- Miller (2006 thesis); Devriese, Birkedal and Piessens (EuroS&P 2016). **By name** (the types note
  §9). DB-11.
- CompCert's external functions; CakeML's FFI oracle. **By name** (the model probe §3.1). The host
  boundary.

*Logic*

- Liron Cohen, Ariel Grunfeld, Dominik Kirst, and Étienne Miquey,
  [*Syntactic Effectful Realizability in Higher-Order Logic*](https://arxiv.org/abs/2506.09458)
  (EffHOL), arXiv v1, 2025-06-11. **Read**, Sections IV–V, VII, IX and Appendix E
  (`docs/research/2026-09-05-reification-effhol.md`, tracked). DB-06.

*The toolchain and the target, as sources*

- Lean, [source at `v4.33.1`](https://github.com/leanprover/lean4/tree/v4.33.1),
  [`EStateM` lawful instances](https://lean-lang.org/doc/api/Init/Control/Lawful/Instances.html),
  [transformer ordering](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/),
  [`Environment`](https://lean-lang.org/doc/api/Lean/Environment.html),
  [`Expr`](https://lean-lang.org/doc/api/Lean/Expr.html), and
  [`collectAxioms`](https://lean-lang.org/doc/api/Lean/Util/CollectAxioms.html). **Read** by the
  2026-08-31 re-review at the source digests its ruling records (recomputed 2026-10-01). Lean
  4.33.1's deriving and induction facts F1–F6: **read and tested** (the type-algebra note §0; the
  data probe). DB-07, DB-08, DB-15.
- Effect,
  [source at `2600f62f4532026928454dcea8d1c48557b3f942`](https://github.com/Effect-TS/effect/tree/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src),
  with `effect@4.0.0-rc.112` vendored at `vendor/effect-4.0.0-rc.112/src/`. A source, not
  literature. DB-09.

## History (retired 2026-10-01)

Three sections of this file are kept here as they were written, each under one line that says
what superseded it. Their text is not corrected: citations in it are as of their dates, and the
2026-10-01 citation check reports the ones that no longer hold as stale history
(`docs/research/2026-10-01-design-basis-refresh/receipt.md`). Nothing here is current.

### Semantic decomposition (written 2026-08-31)

*Superseded by DB-02 (the program data is `Eff`) and `docs/ARCHITECTURE.md` (the module
boundaries).*

The original Flow design separated the following four observations. This
historical table is superseded on the program-data side by DB-02; the current
module boundaries are in `docs/ARCHITECTURE.md`.

| Face | Purpose | Identity and evidence |
| --- | --- | --- |
| `Program` | Structural induction, algebraic laws, handler construction, and proof-local composition | Lean term identity only; no serialization or decidable content identity |
| checked `Flow` | Stable program identity, sharing, cycles, block references, admission, and generation | First-order canonical data with checked references and profile membership |
| relational semantics | Nondeterminism, divergence, interruption, scheduling, scope, and observable outcomes | Judgments over checked flow, configurations, decisions, and traces |
| bounded runner and host harness | Evaluation, counterexamples, generated TypeScript checks, and regression evidence | Fuel-indexed approximations and versioned host observations |

The faces are connected by explicit relations and preservation theorems. None
is silently identified with another. In particular, an executable runner is
not the denotation, and an Effect TypeScript value is not canonical Effect4
program data.

### Native library boundaries (written 2026-08-31; amended with DB-12)

*Superseded by DI-11 and DI-89 (`docs/DESIGN-ISSUES.md`), which own how a module enters `Eff`;
`docs/core/machine-state.md` §5 restates them.*

Effect4 does not place the whole Effect TypeScript API into one opcode family.
The following calculi have distinct indices and explicit embeddings:

- Schema separates representation, decoded value, encoded value, decoding
  services, and encoding services. A transformation composes its decoding
  direction forward and its encoding direction in reverse. Foldlab's CAS
  schema remains a checked downstream profile, not a duplicate generic
  carrier.
- Context and Service own stable typed keys, requirements, and environments.
  Layer owns construction, dependency order, memo identity, and cleanup —
  as program subterms addressed by path, on one context (DB-12).
- Scope and Resource own lifetime delimiters and exit-aware finalization.
  Their operations may be summed into a program without erasing the separate
  calculus.
- Runtime and ManagedRuntime own interpretation, lazy construction, cached
  context, scopes, fibers, and disposal. Runtime objects are target state, not
  program syntax.
- Fiber, scheduling, race, interruption, and supervision own concurrent
  transitions and decisions. Streams, channels, schedules, and transactions
  retain their own state machines rather than being reduced to lists,
  durations, or ordinary state updates.
- Cause and Exit are first-order result data outside `Program`. A richer cause
  tree may lower to an rc.112 ordered-reason representation only through a
  named, tested, and explicitly lossy quotient.

This organization keeps the generic algebra small while allowing the public
library to model the complete effectful interface through composition.

### Required proof graph (re-cut 2026-09-10)

*Superseded by the system map, which owns status (§2's layers, §8's requirements). When it was
retired three of its cells were stale (the model probe's synthesis §3.2 item 15): `run_eq_ref`'s
cell lacked "empty table only"; finite adequacy was called single-fiber straight-line only,
though `loopAgreement` covers `Looped`; scope elimination was called pending, though the
checker's `scoped` arm discharges the scope key (DI-63).*

Each public type closes its own graph before cutover. A later theorem cannot
silently stand in for an earlier edge.

Re-cut 2026-09-10 against `src/Effect4/Laws` and `Test/Audit/RuntimeCoverage.lean`. Two rows
were deleted with the subsystems they named: the `Program`/`Flow` bridge (the Flow route is at
`606918e` in main's history and on `archive/flow-route`) and the Foldlab adapter (the foldlab
vendor evidence is at `62c04d9` on `archive/char-stdlib`). "Pending" below means no theorem or
battery in this tree discharges the judgment — not that one is expected soon.

| Edge | Required judgment or evidence | Current state |
| --- | --- | --- |
| Algebra | monad equations; interpretation of `pure`, `bind`, and `perform`; sum laws; handler composition; freeness and initiality; axiom receipt | Implemented in the `effects` dependency and consumed by `src/Effect4/Laws/Program/Denote.lean`; independent assurance review remains separate |
| Admission | raw reference resolution, index well-formedness, type preservation, checked erasure, decidability, and stable refusal classification | Partly discharged by `src/Effect4/Laws/Program/Admit.lean`: which row a passed check identifies (`admitted_row`), that an accepted answer and its error image are typed in the allocation table (`external_answer_typed`, `external_error_typed`), that an accepted completion names only live handles (`admitted_decision_minted`), and that a checked replay walks the tape the unchecked one walks (`replayCheckedFrom_eq_replay`). The checker and the rules agree on the whole mutual syntax in `src/Effect4/Laws/Program/Typing/Sound.lean` (`effTy_sound`, `effTy_complete`, `hasTy_unique`), which is the decidability and type-preservation half. Stable refusal classification: **pending** |
| Operational semantics | step preservation, terminal exclusivity, tape compatibility, per-tape determinism where applicable, and explicit scheduler assumptions | Partly discharged: `run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean`) equates the frame machine's replay with the term reference's on every admitted program, compile budget, command budget, `Completion` tape and choice list — same classification, same observation, same sufficiency receipt. Budget irrelevance and the terminal projection are `Beh_fuel_irrelevant` and `obs_mono_of_le_terminal` (`src/Effect4/Laws/Machine/Behaviour.lean`) over `drive_add` (`src/Effect4/Laws/Machine/Approximation.lean`). The scheduler assumptions are the declared signature of `src/Effect4/Laws/Program/Sched.lean` and the census rows joined in `Test/Audit/RuntimeCoverage.lean`. No theorem relates either machine to rc.112 |
| Recursive meaning | approximation monotonicity, coherence, finite adequacy, divergence adequacy, and no completion-to-failure regression | Partly discharged: monotonicity and stability under a larger budget are `src/Effect4/Laws/Machine/Approximation.lean` (`drive_add`, `drive_stable_of_done`), packet `Test/contracts/machine-approximation.contract.md`. Finite adequacy holds on the single-fiber straight-line fragment only — `run_eq_meaning` (`src/Effect4/Laws/Program/Agreement/Machine.lean`) with `straight_ref` and `straight_sufficient` (`src/Effect4/Laws/Program/RuntimeR.lean`) — which excludes fork, `gen`, loops, layers and async (DI-07). Divergence adequacy: **pending**; the machine is fuel-indexed and a frontier is not divergence |
| Logic | `wlp` laws, totality, `wp <-> wlp /\ total`, consequence, bind at the semantic face, and classification transfer soundness | **Pending**, and empty: no weakest-precondition calculus exists in the tree. The `Std.Do` triples of `src/Effect4/Laws/Store/CanonicalSpec.lean` are decoder specifications, not this edge |
| Scope and runtime | state retention on failure, finalizer order and exactly-once execution, delimiter laws, interruption behavior, fiber ownership, and disposal | Partly discharged: `src/Effect4/Laws/Machine/ScopeMachine.lean` retains machine and service state, failure included, at every prefix and at the sequential fold's completion, for both strategy labels; `src/Effect4/Laws/Machine/ScopeRestoration.lean` gives the nine equations of the frame resumption; `src/Effect4/Laws/Machine/Handles.lean` states `MintedAt` — every collected handle names a live fiber, heap index, Deferred cell or scope entry; `src/Effect4/Laws/Machine/StoresLaws.lean` gives store growth, validity and heap well-formedness. The census's scope, fork and interrupt rows are joined to their witnesses in `Test/Audit/RuntimeCoverage.lean`. Parallel finalizer scheduling is not implemented and general region compilation is not claimed |
| Schema and services | representation well-formedness, directional codec laws, service-key identity, Layer dependency laws, provision observations, and scope elimination | Partly discharged, by mixed evidence. Service-key identity: `Test/contracts/environment-context-key.contract.md` with `Test/Machine/Environment/ContextKeyContract.lean`, and the context alphabet in `src/Effect4/Laws/Machine/ContextValue.lean`. One codec direction — a successful decode reconstructs its input — is `src/Effect4/Laws/Store/CanonicalSpec.lean` (`ofVal_spec`, `mapM_ofVal_spec`). The Layer rows are witnessed on the compile route by the `Program.Agreement.provideLayer*` declarations joined in `Test/Audit/RuntimeCoverage.lean`. Schema representation well-formedness is *tested* and *reproduced*, not proved: `Test/Schema/RepresentationContract.lean` and the `scripts/check-schema-*.sh` gates. Scope elimination: **pending** — `effTy`'s `.scoped` arm does not discharge `Scope` as rc.112 does (DI-63) |
| TypeScript target | typed lowering, deterministic rendering, decode round trips, direct rc.112 type/runtime vectors, diagnostic negatives, and simulation for each admitted fragment | Partly discharged: deterministic rendering and the decode round trip are `read_print` and `roundTrip_eq` in `src/Effect4/Codegen/Read.lean`, with `read_print_native` at the native alphabet. Direct rc.112 vectors are the truth harness's bounded differential over a frozen corpus at a pinned host, whose quantifiers and side conditions are stated in `Test/contracts/faces.contract.md`. Typed lowering: **pending** — the printed image is executed and parsed but never type-checked (DI-49), and a program with a non-empty requirement row prints untyped (DI-24). Simulation for each admitted fragment: **pending** |

Read the table as it stands. Every edge but `Logic` carries something now. `Admission`,
`Operational semantics`, `Recursive meaning` and `Scope and runtime` carry Lean theorems, each
with its fragment and its premises named beside it; `Schema and services` and `TypeScript
target` mix theorems with tested and reproduced evidence. No edge is closed: where a cell says
**pending** in bold, that is the named judgment of the edge which still has nothing, and for
`Logic` it is the whole row. No edge asserts agreement with the rc.112 runtime —
the only evidence for that is the truth harness's bounded differential, which is a differential
and not a bisimulation. `docs/research/history/DESIGN-MAP.md` grades the same material with the four evidence
words and `docs/RUNTIME-COVERAGE.md` owns the coverage number; a claim quoted from here should
agree with both.
