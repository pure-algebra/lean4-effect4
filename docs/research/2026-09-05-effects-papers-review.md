# The four papers of 5 September, read in full against the tree

Status: reading review, 2026-09-05, Mac seat, tree at `40f4537`. Sources: the text copies
under `docs/research/2026-09-05-effects-papers/text/` (the sections listed in §7), the digest
`docs/research/2026-09-05-effects-papers/README.md`, the proof-graph inventory
`docs/research/2026-09-05-proof-graphs-reading-store.md`, `docs/ARCHITECTURE.md`,
`docs/DESIGN-BASIS.md`, `AGENTS.md`, the open-work sheet of 4 September, the provision, streams
and algebra-denotation notes, the arbiter re-evaluation of 5 September, and the declaration
inventories of `src/Effect4/{Program,Machine,Data,Char,Store,Schema}` and
`.lake/packages/effects/Effects`. Nothing was built or edited; every count below is a `grep`
over `src/Effect4` at this commit.

## 0. The answer in one paragraph

The digest read the four documents from their abstracts and headings. Read in full, three of
them point at one hole, and it is not the Schema seam. The tree's proved algebra
(`Effects.Program`, `interpret`, freeness, initiality; 54 theorems in the nine algebra modules)
and its proved machine (`Machine/Frames.lean` 191 theorems, `Machine/Clauses.lean` 131,
`Machine/Witnesses.lean` 62) are joined by nothing: `src/Effect4/Program/Compile.lean` has
0 theorems, `Test/Program/CompileContract.lean` has 0 theorems and 114 `#guard`s, and no
function sends an `Eff` into an `Effects.Program`. Jacobs §5.5 names the missing object (a
distributive law under which the compile is a bialgebra map, after which trace equivalence of
programs is a congruence), Jacobs §5.3 names the missing theorems about fuel (the three laws
proved on the archived Flow route, absent over `replayEval`), and the MCA paper's Proposition 7
names the missing hypothesis under all of them (pure terms are central). de Vilhena adds three
statements the machine cannot make today: that the stores implement the rows' contracts (his
handler judgment), that a service key is fresh (Tes reads a row as a permission *and* a
distinctness requirement; the tree refuses freshness at `Machine/Scope.lean:318`), and that a
deadlocked machine is not a live frontier (his own Chapter 4 specification cannot see a
deadlock; `Machine/Fibers.lean:31-33` files it under tape exhaustion). Mattick gives the shape
of the one Schema theorem the proof-graphs note already ranks first. On the abstraction side the
papers agree on four unifications, each replacing a family of hand proofs with one theorem: rows
are free-variable sets and `Layer.provide` is the substitution lemma; a monotone store with
upper-closed predicates is one invariant theorem; a characterized component is a coalgebraic
class specification whose mutants can be proved *equivalent* rather than *not yet killed*; and
the specification layer, when it returns on the `Eff` route, should carry the MCA's three
modality laws instead of a weakest precondition written from scratch. Every item respects the
rulings of 4 and 5 September: no second program carrier, no closure in content, no `HHandler`,
and nothing against rc.112 is called a bisimulation.

## 1. What the documents establish

### 1.1 Cohen, Grunfeld, Kirst, Miquey, *From Partial to Monadic* (FSCD 2025)

A monadic applicative structure is a set of codes with an application `A × A → M A` into a Set
monad (Definition 3); evaluation is call-by-value through bind (Definition 4); a monadic
combinatory algebra adds abstraction codes with two laws, the partial application answering
`η` of the closure and the last application answering the evaluation (Definition 5).
Proposition 7 is the load-bearing detail the digest passed over: in the `s`/`k` presentation the
partial applications `eS · c₁`, `eS(c₁) · c₂`, `eK · c₁` must answer `η` of a code, that is,
they must be *pure*, not merely defined; "the axioms of s and k in the discourse are tailored to a
non-effectful behaviour" and the monadic version makes purity a hypothesis. Section 3.2 recovers
the known effectful algebras by choosing the monad (Figure 1): sub-singleton for partiality,
powerset for nondeterminism, powerset-state for state, continuation for control, sub-singleton
reader for oracles; §3.2.3 defunctionalises the continuation instance into an eval/apply machine
with an `Eval` state `e ▷ π`, an `Apply` state `c ◀ π` and a stack of tagged codes and terms.
Theorem 11 characterises an MCA as a combinatory object in the Kleisli Freyd category, and
Appendix C is where the categorical content sits: the value category is the *centre* of the
computation category, so "pure" means "commutes with every effect". Section 4 defines an
M-modality (Definition 13: a natural transformation `M X → (X → Ω) → Ω` with After-Return,
After-Bind and Internal Monotonicity), a separator (Definition 14: a combinatory-complete set
of codes whose applications *progress*, `⟨r ← cf · ca⟩ 0 ≤ 0`), shows that without a separator
a diverging code realises every entailment (the `c⟳` example, and Theorem 18: the frame is
consistent iff `1 ≤ 0` fails), and builds evidenced frames, triposes and assemblies from the
monadic core. Examples 20 to 22 fix the three modality readings the tree will need: angelic
(some result), demonic (every result, *with a termination conjunct* `m ⇓`), and stateful, which
is only well behaved over *future-stable* predicates, upper-closed in the state preorder.

### 1.2 Mattick, *Specifying Hyperdocuments with Algebraic Methods* (2014)

Not about effects. A document is a ground term of the constructor signature `Σ(G)` read off a
grammar; the set of ground terms is the initial algebra, so every view (markup, screen, document
tree, site map, screen reader) is the unique homomorphism into one more `Σ`-algebra (§2, Figure
2); a browser is a parser plus one algebra (§3, Figure 6). A schema is a tree grammar whose
occurrence bounds and required attributes are not context-free and live in a *constraint base*
beside the parser (§3); a stylesheet is a path-located tree transformation applied before
interpretation. The Haskell prototype encodes a signature as one record polymorphic in the
carrier sorts, an algebra as one record value, and a parser parameterised by the algebra so that
it compiles a source document directly into any target interpretation. Section 4's semi
documents are terms with variables, resolved by searching for an assignment that meets a profile.

### 1.3 de Vilhena, *Proof of Programs with Effect Handlers* (thesis, 2022)

Chapter 2 builds Hazel on Iris for a calculus with shallow handlers, mutable state and one-shot
continuations, the one-shot policy enforced by a location flag on the reified continuation
(Figure 2.2, `ResumeStep`). The device is the protocol, a relation between an effect payload and a
predicate on the resumption value (§2.2.2), with send-receive protocols
`! x⃗ (v) {P}. ? y⃗ (w) {Q}` (Definition 2.2), the bottom protocol (Definition 2.3), the sum, a
commutative monoid with `⊥` as unit (Definition 2.4), monotonic protocols and the upward closure
(Definitions 2.6, 2.7), and the protocol order (Definition 2.8). The weakest precondition
`ewp e ⟨Ψ⟩{Φ}` has three defining laws (Figure 2.3); the rules (Figure 2.4) include `Bind` for
*neutral* contexts only, `BindPure` for effect-free programs under any context, `TryWithShallow`
and `TryWithDeep` with the handler judgments of Figure 2.5, and `Monotonicity`, from which the
frame rule follows. The deep-handler judgment re-quantifies the protocol and postcondition of the
reinstalled handler because state may have changed. Theorem 2.1 (adequacy): `ewp e ⟨⊥⟩{Φ}`
implies `e` is safe. Chapter 4 verifies an async/await scheduler over a deep handler and a
queue: `Coop = Async + Await` (Figure 4.8), `isPromise` persistent because the promise map only
grows (§4.3), the `torch` token making "own promise already fulfilled" unreachable, and a queue
invariant `ready` that lets a queued fiber depend on the queue. The chapter states plainly
(§4.1, "Deadlock") that `run` terminates with unfulfilled promises under a wait cycle, and the
specification `ewp (run main) ⟨⊥⟩{_. True}` says nothing about it. Chapter 6 (Maze) shows what
multi-shot costs: the upward closure becomes persistent, non-persistent assertions vanish at every
effect, `Monotonicity` needs a persistently modality on the postcondition weakening because "a
program may terminate multiple times", and the frame rule survives only under `⊥`. Chapter 7 (Tes)
types dynamically allocated effect labels: a row is a list of signatures and row variables, an
arrow type carries a row and a purity attribute, and the novel reading is that a row is a
permission to perform *and* a requirement that its labels be pairwise distinct (§7.3.1). `effect
s in e` allocates a label from the store (Figure 7.2, `EffectStep`), `LetEffTyped` introduces
the absence signature `(s : abs)`, and erasing an absence signature needs a disjointness
context (Figure 7.6, `Erase`), because `σ · σ ≤ σ` would admit an unsafe program (§7.3.2). The
soundness proof is semantic: `wp` is `ValidDistinct E.1 -∗ ewp` (Figure 7.7), the fresh label
gives a persistent points-to that discharges distinctness (`TesLetEff`), and generalisation is
sound only for pure programs because "combining polymorphism with general references is akin to
commuting a universal quantifier with an update modality" (§7.4.1, §7.5).

### 1.4 Jacobs, *Introduction to Coalgebra*, draft 2.00 (2012)

Theorem 3.4.1: two states are bisimilar iff they have the same behaviour, and bisimilarity on
the final coalgebra is equality; Corollary 3.4.2 is the coinduction proof principle; Corollary
3.4.3 defines an observable (simple) coalgebra; Corollary 3.4.4: for deterministic automata,
language equivalence is bisimilarity. Definition 5.2.4 and Proposition 5.2.5: a distributive
law `FT ⇒ TF` is the same thing as a lifting of `F` to the Kleisli category. Theorem 5.3.1
(powerset) and Theorem 5.3.4 (any monad with a dcpo-enriched Kleisli category, a zero object,
least zero maps and a locally monotone lifting): the initial `F`-algebra is a final coalgebra of
the lifted functor, and the trace map is the join `⋁ₙ cₙ ; κₙ` of the chain `c₀ = ⊥`,
`cₙ₊₁ = c ; K(F)(cₙ)` (Proposition 5.3.3, the limit-colimit coincidence). Section 5.5: an
EM-law `TG ⇒ GT` makes bialgebras (Definition 5.5.2), Theorem 5.5.3 identifies them with
coalgebras of the lifted `G`, Theorem 5.5.5 says the initial-algebra map and the
final-coalgebra map out of the term algebra `T(0)` coincide and bisimilarity on `T(0)` is a
congruence, and Definition 5.5.6 with Lemma 5.5.7 and Theorem 5.5.8 give the GSOS format
`F(G × id) ⇒ G F*` under which the same holds. Definition 6.2.1: an invariant is a predicate
closed under transitions; Proposition 6.2.4: invariants are closed under unions,
intersections and direct and inverse images along homomorphisms; Theorem 6.2.5: invariants are
subcoalgebras; Theorem 6.2.6: unary induction. Proposition 2.5.3 and Proposition 6.8.1: the
cofree coalgebra on a colour set `C` is the final coalgebra of `C × F(−)`. Section 6.9: a
coalgebraic class specification is operations, assertions and creation; a model is a coalgebra
with an initial state satisfying them; the final coalgebra satisfying the assertions is the
greatest invariant as a subcoalgebra and is the minimal realisation; the bakery algorithm's
safety and liveness (Propositions 6.9.2, 6.9.3) are stated with the henceforth operator from
`new` and proved from invariants.

## 2. What the digest and the proof-graphs note already name

| item | where named | status at `40f4537` |
| --- | --- | --- |
| `s`/`k` purity axioms as the form of "combinators perform no effects" | digest, MCA relevance | no statement in the tree; §3 G3 makes it one |
| the eval/apply machine as the defunctionalised CPS interpreter | digest, MCA relevance | the frame machine is that machine with an error continuation; §3 G1 states the missing map |
| Schema as one signature, many algebras; the constraint base | digest, Mattick relevance | the design already; §4 A5 gives the seam theorem its shape |
| protocols as the spec side, the handler rule as the Scope and interruption boundary | digest, de Vilhena relevance | no judgment in the tree; §3 G4 and §4 A2 |
| Tes rows and the reserved-key trap | digest, de Vilhena relevance | `E4-PROV-CE-007`, `PROV-FB-KEY-FORGERY`, `Scope.key_freshness_refused`; §3 G5 |
| Jacobs Ch. 5 as the distributive-law picture behind the machine notes | digest, Jacobs relevance | no distributive law and no denotation exists; §3 G1, §4 A4 |
| Jacobs §5.3 as what the truth tapes record | digest, Jacobs relevance | the fuel chain of §5.3 has no laws on the `Eff` route; §3 G2 |
| Jacobs Ch. 6 invariants as runtime invariants; Ch. 3 bisimulation for the stress plan | digest, Jacobs relevance | `Char.Core` is Ch. 6; §4 A3 and A6, inside the arbiter ruling |
| `Document ⊢ Json` conformance, `document_fieldAdmissible`, `print_conforms` | proof-graphs §4.1 | 0 hits for `Conforms`, `print_conforms` |
| `canonical` as a function; `RoundTrip` widened; Wrangler and MCP rows | proof-graphs §4.2 | `Ingest.RoundTrip` still quantifies a `Domain` (`Ingest/Ingest.lean:46`) |
| SC-DOC-02/03/04 | proof-graphs §4.3 | open (`Schema/Document.lean` header) |
| `effective_perm`, `put_sound` | proof-graphs §4.4 | 0 hits for both |
| `Ty.join` laws (R7), `lower_refines_build` (R3), the `KeyKind` split (R8) | open-work sheet | 0 hits for `Ty.join` laws in `src/Effect4/Program`; 0 for `lower_refines_build` |

The rest of this note is what the full read adds.

## 3. Proof gaps the full read adds

### G1. No map from `Eff` to the algebra, and no theorem in the compile

**The paper.** Jacobs §5.5. The syntax is the term algebra `T(0)`; the machine is a coalgebra
`X → G X`; the two semantics of a program, by initiality (`interpret` of a handler) and by
finality (its behaviour), coincide exactly when the operational rules form a distributive law
(Theorem 5.5.5), and the GSOS format (Definition 5.5.6, Theorem 5.5.8) is the common sufficient
condition: the step of a compound term is determined by the steps and the syntax of its
immediate children. The MCA paper's §3.2.3 is the same picture one level down: the eval/apply
machine is what `interpret` into the continuation monad becomes after defunctionalisation.

**The tree.** `Effects.Program` and `interpret` carry the algebra's 54 theorems; the machine
carries 191 frame theorems and 131 clause theorems; `Program/Compile.lean` sends `Eff` to
`Prim` over `EffName`/`EffThunk` with `interpOf` giving names their meaning, and has 0 theorems;
`Test/Program/CompileContract.lean` has 0 theorems and 114 `#guard`s. The only use of
`Effects.Program` on the `Eff` route is `Machine/Context.lean:105` (`ServiceProgram`) and its
`UsesOnly` laws. `Compile.lean:24-27` folds "a yielded pure success inline"
(`Prim.iteratorFolded`) with no law that the fold preserves anything. The algebra-denotation
note of 3 September planned exactly this map (its T1, `run = interpret ∘ denote`) for the Flow
route, which was archived with the plan.

**The statement.** A denotation `denote : Eff NativeOp → Program (nativeSig ⊕ₛ decisionSig)
(ExitV)` over the sequential fragment (`succeed`, `fail`, `failCause`, `sync`, `suspend`,
`perform`, `bind`, `gen`, `catchCause`, `matchCause`, `onExit`, `exit`, `branch`, `whileLoop`),
a handler `machineHandler tape : Handler _ (StateT Stores (ReaderT Tape Option))`, and

```
theorem replay_eq_interpret (e : NativeEff) (tape) (fuel) (henough : fuelFor e tape ≤ fuel) :
    observe (replayEval interp fuel (compile e) tape) =
      observe (interpret (machineHandler tape) (denote e))
```

with `Prim.iteratorFolded`'s law as the first corollary, through the one missing algebra lemma
the denotation note named (`interpret_vis_of_pure`). The fiber actions enter as operations of
the signature whose handler is the dispatcher, the same way the Layer machine is already run
as a `ServiceProgram`. The obstacle is the tape: `Program` is inductive, so the denotation is
tape-indexed or it does not exist (`E4-ALG-CE-008`), which is DB-03 stated as a theorem
shape rather than a limitation.

**Estimate.** The denotation note priced the Flow version at about 250 lines with one
induction on fuel; `Eff`'s five mutual blocks and the generator program counter make the `Eff`
version larger. It is the first theorem `Compile.lean` would carry.

### G2. The approximation laws did not survive the cut-over

**The paper.** Jacobs Theorem 5.3.4 and Proposition 5.3.3. The trace of a coalgebra
`c : X → T F X` is the join of the fuel chain `c₀ = ⊥`, `cₙ₊₁ = c ; K(F)(cₙ)`, and the join
exists and is unique under three hypotheses: the Kleisli homsets are dcpos (an order on
observations with joins of chains), the zero maps are least (a frontier is below every
observation), and the lifting is locally monotone (more fuel, larger observation).

**The tree.** DB-04 records the three laws, monotonicity, compatibility and coherence, as
theorems "for both runners over `StateT σ Id`" at `git:c407ab7:Effect4/Semantics/Approximation.lean`
and the fuel-sufficiency theorem at `git:c407ab7:Effect4/Semantics/Fuel.lean`. Those paths are the
archived Flow route. Over `replayEval` and `drive` there is nothing: 0 hits for `Observation`,
`obs_mono`, `colimit` in `src/Effect4`. `Fibers.lean` is a definition module with 0 theorems;
its clause equations live in `Clauses.lean`.

**The statement.** The same three names over the live machine: `replay_obs_mono` (fuel is
monotone under `Observation.le`), `replay_stable` (a terminal observation never changes), and
`replay_colimit` (the chain's join is the relational meaning at that tape), plus the
fuel-sufficiency theorem `replay_fuelFor_finishes` restated for `Eff`, whose Flow proof went
through `CyclesWF`; on `Eff` the measure is the tape length together with the `whileLoop`
cursor and generator program counter. Jacobs 5.3.4 is also the reason the algebra cannot be the
behaviour carrier: `Program` is initial in Sets, the behaviour is final in the Kleisli category
of a monad with divergence, and the coincidence theorem is what lets a finite syntax carry
infinite runs. The `CLAIM-BOUNDARY` row "No finiteness" is that fact from the other side.

**Estimate.** The archived proofs are the template; the `Eff` machine adds the fiber
dispatcher, so monotonicity has to be stated per decision kind of `RunDecision`.

### G3. Pure terms are not proved central

**The paper.** MCA Proposition 7 and Appendix C. Purity of the combinators is a hypothesis
(`eK · c₁ = η eK(c₁)`), and in the Freyd category values are the central morphisms, the ones
that commute with every computation.

**The tree.** `Program/Eff.lean:196-201`: a `Lit` is `unit`, `nat`, `bool` or `str`; a `Term`
is a variable, a literal or an atom applied to terms; `Program/Native.lean` interprets the
atoms as a closed table. `Machine/Clauses.lean:351` (`evaluatePrim_sync_pure`) is the one-step
form: a `Prim.sync thunk` with `interp.syncState thunk m.state = none` answers `Prim.success
(interp.syncValue thunk)` and emits nothing. There is no run-level statement that a pure step
changes no store, and no commutation of a pure step with another fiber's step, which is what
`Prim.iteratorFolded` (`Compile.lean:24-27`), the printer's inlining of pure statements, and
any regrouping of `provide` chains at the run level all assume.

**The statement.**

```
theorem term_central (e₁ : pure step of fiber f) (e₂ : any step of fiber g ≠ f) :
    step e₂ (step e₁ m) = step e₁ (step e₂ m) ∧ events commute up to the two frame rows
```

stated over `drive` through `evaluatePrim_sync_pure`, and its corollary
`iteratorFolded_eq : replayEval … (folded) = replayEval … (unfolded)` under the same mask.

**Estimate.** Small; it is one clause lifted to an invariant of `RunMachine`.

### G4. The stores are not shown to implement the rows

**The paper.** de Vilhena Figure 2.5 (`shallow-handler`, `deep-handler`) and Figure 2.4
(`TryWithDeep`): a handler *implements a protocol*, and the proof of a program that performs
effects is separated from the proof of the handler that answers them by that judgment. Tes
Theorem 7.2 is the whole-program corollary: a well-typed closed program leaves no effect
unhandled.

**The tree.** `Program/Eff.lean` `Row` carries `request`, `answer`, `error`, `requires` and the
rc.112 line; `Program/Typing.lean` computes `typeOf` from the rows and names the receipt it
owes, "progress (a well-typed program's compile never reaches `PrimInterp.notImplemented`)",
assigned to lane A3, which is `Compile.lean` with 0 theorems. `Machine/Witnesses.lean:1283`
(`forbidden_no_notImplemented_defect`) is a witness on one program. On the key side the
judgment exists: `Machine/Context.lean:729` (`interpret_total`) says a program that uses only
its row never meets a missing lookup, and `Program/Provision.lean:429` (`build_total`) lifts it
to layers under `LeafSem.Typed`. On the value side nothing states that a store's answer to a row
inhabits `Row.answer`.

**The statement.** A typing of values `Val.hasTy : Val → Ty → Bool` (`Val.nat` at `.nat`, the
handle constructors at `.fiberOf`, `.handle`, and so on), then

```
theorem answer_typed (op : NativeOp) (req : Val) (hreq : req.hasTy (rowOf op).request) :
    ∀ m, (syncOpStep (SyncOp.ofRow op req) m).answer.hasTy (rowOf op).answer
theorem progress (e : NativeEff) (h : WellTyped nativeSignature e) (tape) (fuel) :
    replayEval interp fuel (compile e) tape never reaches PrimInterp.notImplemented
```

This is the A3 receipt the typing module promised, and the first-order form of the handler
judgment; §4 A2 is its general form.

**Estimate.** `answer_typed` is a case split over `SyncOp`; `progress` is an induction over
`compileEff` that needs G1's shape or a direct invariant on `Point`s.

### G5. Key freshness is refused where Tes proves it

**The paper.** Tes §7.3.1: a row is a permission and a distinctness requirement; §7.4.1: the
requirement is discharged by allocation, `effect s in e` takes a fresh location from the store
and `TesLetEff` turns its points-to into the persistent `ValidDistinct`. Hazel §4.3's `torch`
token is the same move for a handle: an exclusive resource forged with the promise makes
"already fulfilled by another fiber" contradictory.

**The tree.** `Machine/Key.lean`: a `ServiceKey` is a declared pair of naturals with no minting
operation. `Machine/Scope.lean:318` (`key_freshness_refused`) records that the model cannot
prove a minted scope key fresh. `Program/Provision.lean:257` (`LayerTerm.succeed (key :
ServiceKey) (value : Lit)`) lets any layer term spell any key, which is `PROV-FB-KEY-FORGERY`;
`E4-PROV-CE-007` is a name table landing on `maxOpsKey` (`Machine/Context.lean:915`), one of
the four reserved keys at `Context.lean:912-922`. Handles are different: `Term` has no literal
for a fiber, a promise or a scope (`Eff.lean:196-201`), so `Val.fiber`, `Val.promise` and
`Val.scopeHandle` can only enter a program through an answer variable. That unforgeability is
true by construction and stated nowhere.

**The statement.** Two theorems and one new operation.

```
theorem handles_minted (run) : every Val.fiber, Val.promise, Val.scopeHandle in a run's
    values was answered by the machine (an Inductive invariant of RunMachine)
```

is the tree's `torch` and costs one invariant. Then a minting operation for service keys, a
`RunDecision` or store step `allocKey` answering a key outside the reserved four and outside
the keys already minted, with the invariant `minted.Nodup ∧ ∀ k ∈ minted, k ∉ reserved`, and
`keyOf_ne_scopeKey` (`E4-PROV-CE-007`'s repair) as its corollary. A key a term can spell is a
table position; a key the machine minted is not spellable, which narrows the forgery refusal to
declared keys. This matches rc.112, where a tag is object identity created at module load
(`Context.ts:32-41`, cited in the provision note §5), and it is the missing half of R8: the
`KeyKind` split says which keys are soft, allocation says which are distinct.

**Estimate.** `handles_minted` is small. `allocKey` touches `Machine/Stores.lean` and
`Machine/Context.lean`, shared surfaces, so it is a coordinator seat.

### G6. A deadlock is filed as a live frontier

**The paper.** de Vilhena §4.1, "Deadlock": `run` returns when the queue is empty even though
fibers wait on unfulfilled promises, and the specification cannot see it. Jacobs 6.2.1 and
6.4 give the tool: a predicate closed under every transition is an invariant, and a state from
which no transition changes a predicate is where "eventually" fails.

**The tree.** `Machine/Fibers.lean:31-33`: tape exhaustion, fuel exhaustion and a `Stuck`
machine are the frontiers, and DB-04 makes them live. A machine whose every live fiber is parked
on a `Deferred` nobody will complete, with an idle dispatcher, is "tape exhausted", the same
class as "the host has not answered yet". The daemon grill of 4 September planned a frontier
taxonomy with three theorems; the arbiter note of 5 September records that it has not landed;
`deadlock`, `waitFor` and `Frontier` have 0 hits in `src/Effect4`.

**The statement.** A decidable predicate on `RunMachine`:

```
def Deadlocked (m) : Bool :=
  every fiber with exit = none is parked ∧ dispatcher idle ∧ no race pending ∧
  every parked fiber waits on a fiber or promise that is itself parked or incomplete
theorem deadlocked_fixed (m) (h : Deadlocked m) (d : RunDecision) (hd : ¬ d is interruptFrom) :
    stepDecision interp fuel d m = m
```

The exception is exact: `Clauses.lean:535` (`interruptRecord_parked_applies`) proves an
interrupt reaches a parked interruptible fiber, so a deadlock is dead modulo interruption, which
is rc.112's behaviour too. With it a run has four ends, `done`, `live`, `stuck`, `deadlocked`,
and the frontier taxonomy has its first theorem.

**Estimate.** One predicate, one theorem over the clause equations for `fire`, `flush`,
`evaluate`, `yieldVerdict`, `answerAsync` on a parked target, and `installMiddleware`.

### G7. Liveness has no vocabulary

**The paper.** Jacobs §6.9, Propositions 6.9.2 and 6.9.3: safety and liveness of the bakery
algorithm are both stated with the henceforth operator from the initial state and proved from
invariants; de Vilhena §4.3: the `ready` queue invariant is what makes "a queued fiber can
resume" provable.

**The tree.** `docs/RUNTIME-COVERAGE.md` lists the row kinds `op`, `frame-arm`, `checkpoint`,
`interrupt`, `fork`, `scope`, `scheduler`, `exit`, `cause`, `entry`, `rule`; every one is a
safety row. `Char.Core.Grade` (`Core.lean:483`) is `noLoss`, `noDup`, `order`, all safety. DB-03
rules that a safety theorem assumes no fairness, which is right and leaves liveness with no
place to be stated. `Witnesses.lean:476` (`w4_sibling_resumes`) is one tape.

**The statement.** `Fair (tape)` (every enabled decision is eventually taken), `Eventually P`
over the tape-indexed run as a definition over `Reach`, and one row:

```
theorem parked_on_completed_resumes (f) (p : DeferredKey) (hcomplete) (tape) (hfair : Fair tape) :
    Eventually (fun m => (m.fiber f).parked = Parked.notParked) …
```

through `Clauses.lean:308` (`drive_loop_parked`) and `Clauses.lean:1026`
(`fireObserver_resumeAwait`). The census gains a `liveness` kind whose rows name their fairness
hypothesis, which keeps DB-03 intact.

**Estimate.** Definitions only, then one theorem per row.

### G8. The bind law has a side condition the design basis does not record

**The paper.** de Vilhena Figure 2.4: `Bind` decomposes `N[e]` only for a *neutral* context
`N`, one with no handler frame; `BindPure` decomposes `K[e]` under any `K` only when `e`
performs no effects; §2.4 cites Timany and Birkedal, "non-local control flow breaks the bind
rule".

**The tree.** DB-04 records that there is no fixed-fuel bind law. The "Logic" row of the
required proof graph lists "bind at the semantic face" as pending with no shape. On the `Eff`
route `catchCause`, `matchCause` and `onExit` compile to handler frames (`contE`, `contAll`).

**The statement.** The first bind law is stated for neutral stacks:

```
theorem replay_bind_neutral (a b) (stack : no contE or contAll frame between the bind and its
    consumer) : replayEval … (bind a b) = replayEval … a >>= replayEval … b   (under a mask)
```

and the general law is refused by name, so that G1 and the logic layer (A4) do not attempt it.

**Estimate.** A shape fixed now, proved with G1.

## 4. Abstractions to derive

### A1. Rows are free-variable sets; `Layer.provide` is the substitution lemma

`Program/Provision.lean:71-75` defines `provide` by
`requires (l ◁ d) = (requires l ∖ out d) ∪ requires d`. That is the free-variable law of
substitution, `FV(t[σ]) = (FV t ∖ dom σ) ∪ FV(ran σ)`, read at the type level where the range is
counted whole. Mattick's semi documents (§4) are terms with variables closed by an assignment;
Tes rows (§7.3.1) are the same lists with row variables; `Program/Config.lean`'s `residual` is
the free-variable set of a `ConfigTerm` under a provider, with `orElse` and `nested` as the
substitution. One structure, `FreeVars` over a key type `K` with `fv`, a substitution with
`dom` and `ran`, and two lemmas, `fv_subst_subset` and `fv_subst_eq` when every binding is used,
instantiated at `ServiceKey` (layers), config paths (`Config`), and the positions of a
signature (`typeOf`'s `requires`). What it deletes: `provide_provide_rows` (`Provision.lean:151`)
becomes substitution composition, `merge_requires` (`:171`) and `provide_requires_antitone_out`
(`:177`) become weakening, `appTy_closed_iff` (`:350`) and `residual = ∅` become "the term is
closed", and Tes's row extension (`RowCons`) is `subset_union_left`. What it keeps: the nine
`Row.diff` lemmas at `Data/Row.lean:414-478`, which are the lemma's proof. The one care point is
the same as D2 on the open-work sheet: the TypeScript type is the coarse equality, substitution
gives `⊆`, and both are kept with their roles fixed.

### A2. A first-order protocol on a row, and `Implements` as the handler judgment

Hazel's send-receive protocol `! x⃗ (v) {P}. ? y⃗ (w) {Q}` (Definition 2.2) is a precondition
on the payload and a postcondition on the answer with shared binders. The tree's discipline
(DB-02, `AGENTS.md` representation rules) makes the first-order version `Protocol := ⟨pre :
Val → Bool, post : Val → Val → Bool⟩` per row, `Row.union` as the protocol sum (Definition 2.4,
a commutative monoid with the empty row as `⊥`), and

```
def Implements (interp : RunInterp …) (op) (Ψ : Protocol) : Prop :=
  ∀ req m, Ψ.pre req → Ψ.post req (answer of syncOpStep (SyncOp.ofRow op req) m)
```

G4's `answer_typed` is the instance `Ψ = ⟨hasTy request, fun _ a => hasTy answer a⟩`; the `w7_*`
witnesses of `Witnesses.lean:972-991` are instances on one store; `LeafSem.Typed`
(`Provision.lean:419`) is the layer-level instance. `TryWithDeep` becomes the law of `scoped`
and `onExit`: a body proved under `Ψ` and a finalizer proved under `Ψ'` compose to a program
under `Ψ'`. What is given up, and should be said on every page: Hazel's protocols are Iris
assertions with ownership; the first-order version has no separating conjunction, so
"who may provide a key" stays a refusal family (`PROV-FB-KEY-FORGERY`), exactly as the provision
note §5 already states.

### A3. Monotone stores with upper-closed predicates: one invariant theorem

Three papers state the same condition. MCA §4.1.1 and Example 21: the stateful modality is
well behaved only over future-stable predicates, upper sets in the state preorder; de Vilhena
§4.3: the promise map only grows, so membership is persistent; Jacobs Proposition 6.2.4:
invariants are closed under intersections, unions and images. The tree has six monotone
stores, each with its own invariant proofs: the content store (`Store.Closed`, `Store.Sound`
under `put`), `GSet` (`sub_join_left`), `Row` (`subset_union_left`), the Deferred store
(`w4_complete_twice_answers_false`, `Witnesses.lean:492`), the memo world of the Layer machine,
and the timer store's `now` (`advance_now` in `workshop/Timer/Timer.lean`). One structure,

```
structure Monotone (M : Machine S L) (le : S → S → Prop) : Prop where
  step : ∀ s l s', M.step s l = some s' → le s s'
def Stable (le) (P : S → Prop) : Prop := ∀ s s', le s s' → P s → P s'
theorem stable_inductive (hM : Monotone M le) (hP : Stable le P) : Machine.Inductive M P
```

on `Char.Core.Machine`, and each store's persistence facts become instances. The same `Stable`
is the hypothesis the MCA stateful modality needs, so A4 inherits it.

### A4. The logic layer carries the MCA's three laws, and the separator is the anti-vacuity kit

DB-06 fixes `wlp` against `wp` and its theorem `wp_iff_wlp_and_total` lives on the archived
route; the `Eff` route has no logic module (0 hits for `wlp`). When it returns, MCA Definition
13 is the smaller and sufficient axiomatisation: a transformer
`⟨x ← replay e tape⟩ φ` over `ExitV` with After-Return, After-Bind and Internal Monotonicity.
The demonic reading (Example 20, every tape, with the conjunct `m ⇓`) is `wp`, and `m ⇓` is the
tree's `total`, "no live frontier at `fuelFor`", which is DB-06's decomposition stated in the
paper's own terms; the angelic reading (some tape) is the existential half DB-03 asks the
model to keep visible. Definition 14's separator, the codes admitted as evidence because they
progress, and Theorem 18, consistency iff `1 ≤ 0` fails, are the estate's anti-vacuity kit
(`lossy_not_conserved` at `Core.lean:921`, `meet_is_not_join` at `:539`, the `Refute.*`
mutants) made into one criterion: a law is admitted only with a witness that the top grade is
refuted by some machine. Hazel's protocols stay on the effect side (A2); the modality is the
result side; both are first-order here. What this refuses: evidenced frames, triposes and
assemblies, which have no product need.

### A5. The Schema seam by initiality

Mattick §2 and §3: the accepted values are the ground terms of the signature, and every view is
the unique homomorphism out of them. `Store/Shape.lean` derives three algebras from one
`ShapeDoc`: `accepts` (`:175`), `document` (`:413`, through `render : Shape → Representation`
at `:370`, the print misnamed as a render, proof-graphs §5), and `print` (`:482`), with no
theorem between them (proof-graphs §3). The theorem the proof-graphs note ranks first,
`print_conforms : accepts doc v = true → Conforms (document doc) (print doc v)`, is Mattick's
"the JSON algebra factors through the language of the schema algebra", and its cheapest proof
defines the conformance judgment `Document ⊢ Json` as a fold over `Representation` that mirrors
`acceptsAt`'s fold over `Shape` (`:138`), so that the theorem is one structural induction with
`render` as the homomorphism. Renaming `render` at `:370` first, as the proof-graphs note asks,
is what lets the statement read as a print law. The constraint base of Mattick §3 is
`Schema/Check.lean` beside the representation; nothing to add there.

### A6. Characterized components are class specifications; mutants can be proved equivalent

`Char/Core.lean` is Jacobs §6.2 and §6.9 line for line: `Machine` (`:67`) a deterministic
partial transition system, `Inductive` (`:216`) an invariant, `reach_ind` (`:246`) the one
induction, `Guarded` and `Graded` (`:943`, `:967`) the operations-assertions-creation triple,
`Machine.Sound` (`:583`) "the model satisfies the assertions". Two things the chapter adds.
First, Corollary 3.4.4: on a deterministic machine, language equivalence is bisimilarity, so a
`Bisim M R` with the deterministic clause, `bisim_iff_traces`, and `Mutant.equivalent` as a
`Prop` with a bisimulation witness give the room a statement it cannot make today:
`Mutant.survivesSome` (`:685`) says the finite suite did not kill the mutant and cannot tell an
equivalent mutant from a weak suite; a bisimulation proves the mutant equivalent, and the
coinduction principle (Corollary 3.4.2) is the proof method. Second, §6.9: the final coalgebra
satisfying the assertions is the greatest invariant and the minimal realisation, so a component
can carry its canonical model as the thing mutants are compared against, and Proposition 6.2.4's
transport of invariants along homomorphisms is the theorem `Machine.prod` (`Conformance/Compose.lean:54`)
lacks: `run_prod_inl` (`:70`) and `injectL_sound` (`:175`) move words and vectors, not
invariants. Both are Lean against Lean, model against mutant, and stay inside the arbiter
ruling. The stress plan's S1 to S3 are the same case; S4, the host at volume, remains "agrees
under μ".

### A7. Masks are colourings of a cofree coalgebra

Vocabulary only. Proposition 2.5.3 and 6.8.1: the cofree coalgebra on a colour set `C` is the
final coalgebra of `C × F(−)`. `Effects.Trace.Event` is the colour set, `Mask.keeps` a
recolouring, "agrees under μ" equality after recolouring. The two laws worth having follow
without a proof about the machine: `project (m₁ ⊓ m₂) = project m₁ ∘ project m₂` and "a coarser
mask agrees on more runs". No landing row is needed for this; it names what the harness already
does.

## 5. Boundaries the papers do not move

- Nothing against rc.112 is a bisimulation (arbiter re-evaluation, 2026-09-05, vocabulary
  line). A6 and the congruence of G1 are between Lean programs and Lean machines and are said
  so.
- No separation logic. Hazel's ownership does not survive DB-02; A2 says what is lost.
- No realizability dependency. The M-modality laws are the borrowing; evidenced frames,
  triposes and assemblies are not.
- `Program` stays out of the behaviour seat (`E4-ALG-CE-008`); G2 is the reason in the
  paper's words.
- No `Skeleton` IR. The denotation note's T3/T4 served the archived lowering; on the `Eff`
  route the congruence of §3 G1 is what a printer normalisation (the total flattening of a
  `merge` chain into one `Layer.mergeAll`, `Codegen/Layer.lean`, provision note §10) needs.
- Effect polymorphism is not on the table. Tes §7.5 records that generalisation is unsound for
  programs that touch the store, which is every program here; D1 on the open-work sheet
  (`provide` and `service` in `Eff`) is unaffected, and the row stays monomorphic in `typeOf`.

## 6. Order, per algebra

The owner's ruling of 5 September is that each algebra's proof graph improves first and
integration happens only through the Schema seam, so the order is per track, not global.

| track | first | then | needs |
| --- | --- | --- | --- |
| Program and Machine | G3 `term_central`, G8's shape, G5 `handles_minted` (small, fix statements before proofs) | G1 `replay_eq_interpret` on the sequential fragment with `iteratorFolded_eq`; G2 the three laws over `replayEval`; G4 `answer_typed` then `progress` | nothing; one seat, `Program/Compile.lean` gains its first theorems |
| Machine frontiers | G6 `Deadlocked` and `deadlocked_fixed` | G7 `Fair`, `Eventually`, the first liveness row and a census kind | the census gate for the new kind |
| Provision and Context | A1 `FreeVars` over `Row` (coordinator: `Data/Row.lean`, `Provision`, `Config`) | G5 `allocKey` beside R8 | R7 `Ty.join` laws stay first on the sheet |
| Stores | A3 `Monotone`/`Stable`/`stable_inductive` on `Char.Core.Machine`, then the six instances | `effective_perm`, `put_sound` as instances where they fit | none |
| Char | A6 `Bisim`, `bisim_iff_traces`, `Mutant.equivalent`; invariant transport along `prod` | the minimal realisation as the canonical model | R-char-1/2 |
| Schema | A5 the fold-shaped `Conforms`, `print_conforms` after the `:370` rename | SC-DOC-02/03/04 | proof-graphs §4 order unchanged |
| Logic | A4 only after G1 and G2 exist, since the modality is stated over `replayEval` | | G1, G2 |

## 7. What was read, and what was not

Read in full: the MCA paper (§1 to §5, Appendices A to C, Appendix D through Theorem 18) and
Mattick (§1 to §5). Read: de Vilhena Chapters 1, 2, 4, §6.1 and §6.2, and Chapter 7 to §7.5;
Jacobs §2.5 (opening), §3.4, §5.2 (through Proposition 5.2.5), §5.3 (through Theorem 5.3.4),
§5.5 (through Theorem 5.5.8), §6.2, §6.8 (opening) and §6.9 (through Proposition 6.9.2).
Not read: de Vilhena Chapters 3 and 5 and §6.3; Jacobs Chapters 1 and 4, §5.1, §5.4, §6.1 and
§6.3 to §6.7; every figure and diagram, since the text copies flatten them (the digest says which
to read from the PDFs). No theorem of the Rocq or Coq developments was checked.
