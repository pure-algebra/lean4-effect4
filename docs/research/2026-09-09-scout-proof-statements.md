# Scouting review and Lean experiments: questions that decide the next phase

2026-09-09 · reviewed commit `66ee465730126048ad90d99d24ce4f12f5bb2982` · Lean 4.33.1.
Research only; no tracked changes, rulings, commits, full builds, or host-equivalence claims.
The owner's later instruction authorizes Lean experiments across the original B/C lane split.

## One page

**Finding.** The direction is a useful foundation for an algebraic-effect metalanguage, provided its next step separates what authors can express, what the checker establishes, what a target can execute, and what observations execution promises.

**Recommendation.** First close the small admission/error boundaries, build one state-aware host contract with adversarial examples, and prototype checked authoring and generated descriptors; defer a whole-machine typing theorem until its state and reachability premises are defined.

**Unverified.** This work does not establish arbitrary-host correctness, full reachable-machine typing, table-aware reference agreement, complete package coverage, or production performance.

The six briefs ask valuable questions, but some prescribe an answer or contain a false premise. The most consequential results of actually running Lean are:

| Question | Result | Consequence |
|---|---|---|
| Is operation-domain membership already implied by typing? | **No: a negation of the proposed universal statement is proved.** | DI-54 needs a repair and an independent negative fixture. |
| Would the domain repair change every corpus program containing an external call? | **No.** Of 400 generated programs and 42 goldens, zero verdicts change; the one external golden was already rejected. A separate counterexample does change. | Count changed verdicts, not syntactic occurrences. |
| Is cause typing a prerequisite for every useful typing result? | **No.** Both partial error-inverse laws and external failure membership are proved in scratch. | Start with these small boundaries. |
| Is adding a cause arm enough for environment typing? | **No.** Existing `Fits` rejects allocated external handles because it uses the default empty allocation table. | Parameterize the value relation by runtime state. |
| Does passing a table make the reference evaluator cover external calls? | **No.** A scalar callback finishes on the frame machine but stays at a frontier on the unchanged reference. | Extend registration, answer conversion, allocation and the evaluator's interpreter selection together. |
| Can a checked wrapper make the current API safe by construction? | It enforces the current checker, including its limitations: a table-valid `.perform` can type-check but remain a frontier while `.callback` completes. | Give typing and executable-profile admission distinct certificates. |
| Can Lean improve ergonomics without replacing `Eff`? | **Yes, in a bounded pilot:** named variables, lexical shadowing, early errors, a checked wrapper, and a real deriving handler all work. | Develop these as authoring/tooling layers; details in [scout C](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-descriptor.md). |

Completion criteria for this scouting pass: inspect every brief; replace consequential assumptions with checked statements or counterexamples; run the two B measurements; try real generation and authoring patterns; connect recommendations to existing literature and local implementations; save rerunnable sources, outputs, and a bounded follow-on work queue. Unproved candidate statements are definitions of propositions, never asserted theorems with holes.

## 1. Review of the briefs and the most pertinent questions

This is an assessment of the scouting plan, not authorization to land its proposed changes.

| Brief | Keep | Sharpen before the remaining work is assigned |
|---|---|---|
| A — host boundary | Observe errors **inside** handlers; compare real backend failures and tape projections. | Replace the required total `unknown → pair` policy with a comparison of explicit admission/projection policies. Unknown failures cannot acquire meaningful tags merely because a function must return a pair. Separate typed failure, defect, interruption, unsupported payload, and raw diagnostics. Check acquisition separately: `mapError` is not a defect handler. |
| B — proof statements | Exact statements against the current environment; small proofs and counterexamples. | Include allocation state and operation-form compatibility. Do not treat a proposition parameterized by an undefined reachability relation as a safety theorem. Correct M2's occurrence/verdict implication and the cause constructor spelling. |
| C — descriptor | Compare actual family domains; test generator output; retain a historical baseline. | Run the pilot, as now authorized. Stable tags and append-only positional tags **can both** be valid policies under a baseline. Neither generates semantic compatibility automatically. Distinguish tool imports from imports of generated library declarations. |
| D — census | Fresh pins, the rule that fired, and masked features. | A textual handler occurrence is not evidence that a handler rule would be reached after removing an earlier refusal. Report textual counts as a separate layer; use parsed, symbol-resolved occurrences and counterfactual engine probes for the stronger claim. |
| E — ecosystem | Stress the design beyond SQL and KV. | Define the finite domain first: exported services, service-producing constructors, combinators and implementations are different things. `rg` finds leads, not all inferred error types. Record overlapping error categories and unsupported extraction cases; distinguish installed, type-checkable and executable drivers. |

The key cross-brief question is **what an author may rely on when composing programs**. A/E should deliver the observations and admitted host behavior; B then states those guarantees precisely; C makes the descriptions consistent; D measures how much source material those choices actually admit. Running five broad inventories independently without this join would produce more descriptions to reconcile.

Source of the brief corrections: B M2 and P2(b), [B brief](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-brief-proof-statements.md:63); D Q2, [D brief](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-brief-census.md:38); A Q1, [A brief](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-brief-host-boundary.md:39); E Q1–Q2, [E brief](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-brief-ecosystem.md:31). These are references to the instructions being reviewed, not evidence about runtime behavior.

## 2. P1 — admission, operation addresses and recorded replies

### P1(a): the current statement is false

The scratch declaration is exactly:

```lean
def OperationAt {Op : Type} (e : Eff Op) (path : List Nat) (op : Op) : Prop :=
  ∃ request, Node.at_ (.eff e) path = some (.eff (.perform op request)) ∨
    Node.at_ (.eff e) path = some (.eff (.callback op request))

def DomainStatement : Prop :=
  ∀ (sig : Signature NativeOp) (e : NativeEff) (ty : EffTy),
    typeOfProgram sig e = some ty →
    ∀ path op, OperationAt e path op → sig.dom op = true
```

`domainStatement_false : ¬ DomainStatement` is proved. Its witness is
`bind (fail (lit (nat 1))) (perform (external 0) (var 0))`, accepted at the empty table.
The external operation is at path `[1]`; the signature rejects that index.
This is a statement about every syntactic site, so the failing prefix does not invalidate the witness.

Reuse `Node.at_`, rather than inventing another public tree representation:
[Refs.lean:57](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Refs.lean:57),
[Refs.lean:113](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Refs.lean:113).
Typing declares `dom` but does not consult it in the two relevant arms:
[Typing.lean:61](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing.lean:61),
[Typing.lean:185](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing.lean:185),
[Typing.lean:232](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing.lean:232).

**After the repair:** prove the local mutual typing result, then transport it through `typeOfProgram`'s layer-reference validation/expansion. Do not skip that last boundary. The mutual syntax has **65 constructors across seven families**: Eff 27, Stmt 6, Stmts 2, Effs 2, ActionTerm 16, LayerTerm 10, LayerTerms 2. Most cases merely transport a hypothesis; this is a moderate structural proof, not a two-line theorem. The constructor census is freshly reflected in C's receipt; the source block starts at [Eff.lean:264](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Eff.lean:264).

**Additional finding:** membership is not executable-profile admission. A valid table whose row is asynchronous admits a `.perform` by typing, while the compiler dispatches `.perform` using `NativeOp.row`; `.callback` has the table-aware external registration route. The C probe gives the same request/reply to both and gets frontier/finished respectively. This does not identify every frontier as an error. It refutes the expectation that `wellTyped` plus an available compatible answer guarantees completion of this particular call.
See [Compile.lean:540](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:540),
[Compile.lean:578](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:578).
The next contract should state which operation forms each row supports and reject or lower unsupported forms explicitly.

### P1(b): a concrete, decidable envelope

The scratch `RecordedReply` stores a full table, fiber, token, operation, request and completion. Full table equality deliberately avoids inventing a publication identity/hash policy.

```lean
def Envelope (table : RowTable) (m : NativeMachine) (r : RecordedReply) : Prop :=
  r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) ∧
    admit table m (.answerAsync r.fiber r.token r.completion) = none

def acceptReply (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Option NativeDecision :=
  if Envelope table m r then some (.answerAsync r.fiber r.token r.completion) else none
```

Proved: successful `acceptReply` establishes this envelope and the exact returned decision.
A real parked scalar callback supplies a positive premise witness; changing its operation, request, token, or table is rejected. These are finite probes of the proposed checker, **not a proof about today's Truth decoder**.

The existing surfaces already supply the difficult routing information:
[Admit.lean:30](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admit.lean:30),
[Admit.lean:66](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admit.lean:66).
The driver obligation is: decode a record, compare its projected request to the actual parked request under the same profile, check the envelope, then advance the machine and check the next record against that new state. Add duplicate/stale answer, reordered calls, wrong fiber, wrong completion category, and allocation-conversion fixtures before promoting it. Multi-fiber scheduling and partial tapes require a separately named policy. A valid prefix may end at a frontier.

**Size:** the local checker and implication are small; JSON decoding, request projection and sequential consumption are separate integration obligations. DI-58 cannot be closed by the local implication alone.

## 3. P2 — error inversion and cause membership

These definitions and all four associated laws elaborate; the laws are proved:

```lean
def valOfErr : Err → Option Val
  | .boom => none
  | .tag n => some (.nat n)
  | .tagged tag message => some (.list [.str tag, .str message])

theorem errOf_valOfErr (e : Err) (v : Val) (h : valOfErr e = some v) : errOf v = e := by
  cases e with
  | boom => cases h
  | tag n => cases Option.some.inj h; rfl
  | tagged t m => cases Option.some.inj h; rfl

theorem valOfErr_errOf (v : Val) (h : errOf v ≠ .boom) : valOfErr (errOf v) = some v := by
  unfold errOf at h ⊢
  split at h <;> simp_all [valOfErr]

def hasTyCause (v : Val) (e : Ty) : Bool :=
  match Val.cause? v with
  | some c => c.reasons.all (errAdmits e)
  | none => false

theorem hasTyCause_exitErr (c : CauseV) (e : Ty) :
    hasTyCause (Val.exitErr c) e = c.reasons.all (errAdmits e) := by
  simp [hasTyCause, Val.cause?_exitErr]
```

The partial inverse is intentional: arbitrary strings and other values collapse to `boom` through current `errOf`; there is no inverse for that collapse.
[Compile.lean:409](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:409).
The brief's `Val.exitErr (causeImage.toVal c)` has the wrong argument type: the machine-level constructor already receives `CauseV`. The lower `Value.exitErr` receives the encoded value.

The external failure theorem has this exact conclusion:

```lean
theorem external_error_typed (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (c : CauseV)
    (h : admit table m (.answerAsync fiber token (.ofExit (.failure c))) = none) :
    ∃ i request row,
      requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧
      hasTyCause (Val.exitErr c) row.error = true
```

It is proved from `admitted_row`, the failure branch of `admitAnswer`, and the cause reification law. A second theorem, `external_oracle_error_typed`, proves the analogous result from `externalAdmits table i (.ofExit (.failure c)) allocated = true`.
These proofs require no induction over programs or machine executions.
See [Laws/Program/Admit.lean:36](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Admit.lean:36),
[Compile.lean:1280](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:1280),
[Compile.lean:1322](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:1322).

Positive and negative guards establish that the theorem's premise is inhabited: a natural-number failure is admitted for the scalar row, a tagged string pair is rejected there, `boom` is rejected, and defects/interruption are admitted even when the typed-error column is `never`. The latter is intentional: `E = never` does not mean a computation cannot be interrupted or die.

**Not included:** typing a handler's appended environment, failed-exit checking in `Val.hasTy`, retention of failure state, or agreement with a JavaScript error object. Those remain distinct obligations. `Val.hasTy` currently ignores the error parameter of failed exits and both parameters of fiber handles, and has no accepting cause arm:
[Typed.lean:54](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typed.lean:54).

**Placement:** avoid making `Typed` import `Compile`. Move the shared error-value/cause-membership relation into a lower module that can be used by both, with the existing carrier and row type as dependencies. Keep decoding/reification lemmas beside that relation. The proof layer can then relate it to admission and handler binding. This is a module-boundary recommendation, not an approved file move.

**Proof trust finding:** one initial broad simplification pulled in `Classical.choice`; replacing it with direct case analysis kept the final failure theorem at `[propext]`. Generated results and proof-search success still need their dependencies inspected.

## 4. P3 — what a row protocol must say

The requested simple protocol is useful for a narrow synchronous interface:

```lean
structure Protocol where
  pre : Val → Bool
  post : Val → Val → Bool

def ImplementsSync (op : NativeOp) (p : Protocol) : Prop :=
  ∀ (v : Val) (o : SyncOp) (s s' : Stores) (a : Val),
    Stores.HeapNat s → p.pre v = true → NativeOp.syncOpOf op v = some o →
    syncOpStep o s = some (s', a) → p.post v a = true
```

`rowProtocol` uses `Val.hasTy` at the request and answer columns. `native_row_protocol` is a literal application of existing `answer_typed`, including **HeapNat and successful stepping**, not a proof of arbitrary primitive progress:
[Progress.lean:389](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Progress.lean:389).
The pure instance `native_atom_protocol` directly uses `nativeAtom_typed`, including its `Fits` premise:
[Laws/Program/Typed.lean:218](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed.lean:218).

External success needs a different shape:

```lean
def ExternalSuccess (row : Row) (allocated : List String) (raw : Val) : Prop :=
  ∃ allocated' value,
    externalValue row.answer allocated raw = some (allocated', value) ∧
    Val.hasTy value row.answer allocated' = true
```

The external theorem is proved directly from `external_answer_typed`. It checks the **converted value in the new allocation state**, not necessarily the raw reply in the old state:
[Laws/Program/Admit.lean:82](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Admit.lean:82),
[Compile.lean:1289](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:1289).
P2 supplies the failure instance. Forcing all three into `post : Val → Val → Bool` would hide the important distinctions.

### A useful host model to construct next

Start with a small **state-indexed transition relation**, rather than a model of all JavaScript. Its parameters should expose:

| Part | What to represent | What a first slice must test |
|---|---|---|
| Value correspondence | `Rep profile world ty modelValue hostValue`, including scalar bounds and an identity map for handles | Same handle reused; wrong target; missing allocation; out-of-range number |
| Operation contract | Row identity, supported call form, request relation, success/failure alternatives | Valid scalar call and allocator; unsupported request and operation form |
| State transition | Before/after host state, model state, allocation extension, scope ownership and lifetime where relevant | Failure after mutation; cleanup after failure; resource use after release |
| Error observation | Which distinctions in tag, payload and causes programs may inspect | Matching and nonmatching handler; re-raise; defect; interrupted and combined causes |
| Decision/replay contract | Parked call, token, fiber, request, admissible reply and state advance | Wrong/repeated/reordered reply, exhausted tape, independent pending calls |
| Observer | Result, selected errors, resource effects and agreed trace events | Two executions that agree in final JSON but differ at an admitted intermediate observation |

The semantic relation may quantify over host objects/functions. The **published program and descriptor must remain data**. The brief's `Protocol` function fields are a specification interface, not a serializable row descriptor.

Do not require equality of machine and host values; require that each permitted observation respects `Rep`. Do not assume all errors can be losslessly projected into two strings. The existing pair is one chosen profile encoding; E/A must establish its adequacy for the observations admitted by each row.

The C experiment makes the state/failure choice concrete using standard Lean transformers. `StateT Nat (Except Nat)` loses the state on failure; `ExceptT Nat (StateM Nat)` returns the failure together with the incremented state. Both exact results are proved by reduction. This is a small semantic counterexample explaining the design choice, not an implementation of Effect4 finalization.

**Size:** local row instances are small; a reusable host relation needs the preceding data and observation decisions. Prove one scalar and one allocating row before adding many packages. A single value-shape theorem is insufficient for lifecycle guarantees.

## 5. P4 — environments at control points

The scratch `nextTypes`/`typesAlong`/`tyEnvAt` definitions reconstruct a lexical environment along `Node.child` paths. They account for bind, success/cause arms, finalization, release, loops and generator bindings, resetting layer environments as the current checker does. The combined helper is under sixty source lines. `reqAt` currently handles effect and layer nodes. Positive bind-path and invalid-path guards pass.

These are a **path-query pilot**, not a complete operational invariant. They do not yet connect expanded layer references, every statement/loop context, suspended captures and finalizer records to the actual machine's reachable points.

The more immediate obstacle is the value relation. Existing `Fits` uses `Val.hasTy` without allocation state:
[Laws/Program/Typed.lean:135](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed.lean:135).
The scratch generalization is:

```lean
inductive FitsWith (holds : Val → Ty → Prop) : List Val → TyEnv → Prop
  | nil : FitsWith holds [] []
  | cons {v t vs ts} : holds v t → FitsWith holds vs ts →
      FitsWith holds (v :: vs) (t :: ts)

abbrev FitsIn (allocated : List String) :=
  FitsWith (fun v t => Val.hasTy v t allocated = true)
```

Proved: agreement with old `Fits` at empty allocation; an append lemma; a `Point.childWith` extension lemma; an external handle is **not** in old `Fits` but **is** in `FitsIn` with the matching allocation. The append theorem uses no axioms. This is a reusable proof abstraction with two constructors, not another program representation.

A candidate statement now elaborates as a proposition:

```lean
def FitsAtStatement
    (Reached : NativeEff → RowTable → Point → List String → Prop) : Prop :=
  ∀ root table ty p allocated,
    Api.typeOf root table = some ty → Reached root table p allocated →
    ∃ ts, tyEnvAt table root p = some ts ∧ FitsIn allocated p.env ts
```

`Reached` is deliberately an **unimplemented parameter**, not an assumption already known to imply `Fits`. This statement has not been proved, and is not true for arbitrary choices of `Reached`. The restricted no-cause-handler version still needs an allocation-aware relation or a genuinely closed fragment; exclusion of cause binders alone does not repair it.

For whole-machine typing, define the invariant over fibers, stored continuations, captures, environments, heaps, completed exits, pending replies and allocation state. A minted-handle theorem establishes existence/ownership facts of its stated kind; it does not determine the A/E type of every stored value. This is a substantial invariant over transitions in addition to the 65 syntax cases. The scout should not budget it as “add one `hasTy` arm.”

## 6. P5 — table-aware internal agreement

The exact candidate equality is:

```lean
def RunEqRefTableStatement
    (reference : NativeEff → Nat → List Api.Decision → List Bool →
      List (Completion Val Err Defect FiberId Ann) → RowTable → RReplay) : Prop :=
  ∀ e fuel tape choices answers table,
    (Api.replay e fuel tape choices answers table).outcome =
      classify (reference e fuel tape choices answers table) ∧
    obs (Api.replay e fuel tape choices answers table).machine =
      obsR (reference e fuel tape choices answers table).machine
```

This is a proposition awaiting a reference implementation. It makes exactly the current internal observer comparison, not host equivalence. Existing agreement has neither parameter:
[RuntimeR.lean:200](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean:200).

The scratch adapter supplies the oracle queue to `RState` and introduces
`TableReferenceInterp := NativeEff → RowTable → List (FiberId × ExitV) → RInterp`.
It also replaces the reference term evaluator's `evaluate` field. That matters: today's
`termEvaluatorFor` calls `interpRAt` internally instead of using an arbitrary interpreter supplied to replay:
[EvaluateR.lean:342](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/EvaluateR.lean:342).

The counterexample uses one asynchronous external row, request `7`, reply `9`, fuel `40`, and the usual evaluate/flush tape:

| Observer | Frame machine | Unchanged reference behind the new parameter |
|---|---|---|
| Outcome | finished | frontier |
| Unconsumed oracle replies | 0 | 1 |

The reference still lacks external-row registration, admission/conversion/allocation and the prepared-answer behavior:
[InterpR.lean:313](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/InterpR.lean:313),
[Compile.lean:1410](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:1410),
[Compile.lean:1439](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:1439).

The proof repair crosses at least these distinct seams: reference loading; interpreter construction; evaluator selection; external registration; answer preparation; the state relation; evaluation simulation; scheduler/replay hooks; final observation extraction. The existing foreign-registration proof explicitly uses empty-profile behavior, and the hook proof simplifies the empty table:
[Simulation/Evaluate.lean:398](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Simulation/Evaluate.lean:398),
[Simulation/Evaluate.lean:783](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Simulation/Evaluate.lean:783),
[Simulation/Drive.lean:227](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Simulation/Drive.lean:227).
There are two dedicated current external/foreign cases in `evaluate_rel`; neither count is an estimate of the entire repair. Cost this as a multi-module semantic extension, after the row/answer protocol is fixed. It need not wait for full P4 typing: equivalence of two machines and typing of their states are different obligations.

## 7. Measurements

The M2 scratch copy reproduces the current six mutually recursive typing functions and changes **only** the two operation arms by adding `guard (sig.dom op)`. The diff is saved in scratch. The site census reuses the existing complete mutual walker at [Test/Program/Gen.lean:432](/Users/pooks/Dev/lean4-effect4/Test/Program/Gen.lean:432).

| Domain | Programs | Accepted before | Accepted after | Contain external | Changed verdicts |
|---|---:|---:|---:|---:|---:|
| `Test.Program.Gen.sample` | 400 | 152 | 152 | 0 | 0 |
| `OCaml5.Eff.Corpus.corpus` | 42 | 31 | 31 | 1 (`pExternal`) | 0 |
| Separate domain counterexample | 1 | 1 | 0 | 1 | 1 |

M1 inspected answer/error types of **accepted whole programs**, plus request/answer/error columns of all eight package rows. Every included type was recursively checked through all compound Ty constructors; repeated occurrences are counted.

| Type population | Occurrences | Distinct | Noncanonical at top | Noncanonical anywhere |
|---|---:|---:|---:|---:|
| Accepted sample roots | 304 | 27 | 0 | 0 |
| Accepted golden roots | 62 | 9 | 0 | 0 |
| Eight rows × three columns | 24 | 12 | 0 | 0 |

There are no offenders in these populations. A synthetic nested noncanonical union is detected by the recursive check while the top-only check misses it. This confirms DI-53's eight-row observation, not a universal normalization invariant. Types of every internal subexpression and rejected partial typing derivation were **not** measured; that extension must be explicit if M1 is intended to cover them.

## 8. Work structure and proof priorities

| Work item | Depends on | Useful guarantee / next decision |
|---|---|---|
| P1 domain repair + operation-form admission | Exact source/target profile | Every admitted call refers to an allowed row in an executable form; destination DI-54 and a contract packet |
| P2 inverse and shared cause membership | Error representation decision | Error elimination/re-raise has a stated domain; destination DI-09/DI-26 and lower-module ownership |
| P1 envelope checker integrated into replay | Request projection and table/profile identity | Recorded replies belong to actual pending calls; destination DI-58 |
| P3 one scalar + one allocating host protocol | A/E observation policy, scalar/handle representation | Permitted operations respect the host relation, including failure state; destination DI-29/DI-56/DI-59 |
| Checked authoring and finite generation pilot | Stable checker claims and retained byte baseline | Early feedback, less repeated metadata, unchanged canonical program data; destination DI-18/DI-41/DI-47 |
| P4 local environment transitions, then invariant | Allocation-aware `Fits`, cause/exit interpretation, reachability | Bindings retain the claimed types; destination DI-26 and typed-machine contract |
| P5 reference extension and simulation | Frozen row/answer state protocol | Internal agreement under nonempty tables and replies; destination DI-57 |

The highest-value proofs are the ones at **construction and conversion boundaries**, where a small local obligation prevents many downstream checks: descriptor validity, checked erasure, exact decoding, call envelopes, value conversion, error membership and state retention. Keep progress, eventual response, fairness, termination and target agreement separate. A fuel frontier cannot discharge or refute all of them.

## 9. Literature, existing abstractions, and what “general” should mean

The owner's goal is broader than transcribing one runtime. A useful provisional description is:

> Effect4 is an inspectable language for composing effectful computations. Lean supplies its authoring and modeling tools, checks explicit contracts, and generates consistent representations. Programs are stored as first-order data; named target profiles realize their operations and observations on host systems.

This is proposed wording for a future README/design ruling, not a claim that every part exists. Before adding features, evaluate “general” on independent axes: open operation signatures; reusable parameterized program builders; scoped and delayed computations; choice/resumption policies; recursion; data expressiveness; and multiple target profiles. More package rows mainly exercise the first and last axes. They do not by themselves provide arbitrary user-defined control handlers.

Relevant resources were read with a specific design question in view:

| Resource | Reusable idea | Application and limit |
|---|---|---|
| Matija Pretnar, *An Introduction to Algebraic Effects and Handlers*, 2015, [tutorial](https://www.eff-lang.org/handlers-tutorial.pdf) | Operations describe interactions; handlers assign interpretations; resumption behavior is part of the design. | Start the language description with interfaces, control behavior and observations. General handlers are a broader promise than a table of host calls. |
| Wouter Swierstra, *Data Types à la Carte*, 2008, local corpus paper 06; [author copy](https://webspace.science.uu.nl/~swier004/publications/2008-jfp.pdf) | Compose signatures and their interpretations. | Use modular authoring/interfaces while retaining a validated closed descriptor at publication. An open sum alone does not solve stable IDs or serialization. |
| Olivier Danvy and Lasse Nielsen, *Defunctionalization at Work*, 2001, local paper 16 §1/§3; [BRICS copy](https://tidsskrift.dk/brics/article/download/21684/19120/49299) | Relate higher-order construction/semantics to explicit first-order code and environments. | Rich Lean builders need not imply stored Lean closures. The C syntax pilot demonstrates only a small supported elaboration, not arbitrary-function reification. |
| Casper Bach Poulsen and Cas van der Rest, *Hefty Algebras*, 2023, local paper 14 §1.2/§3/§5.2; [author copy](https://casperbp.net/store/hefty-algebras.pdf) | Give higher-order operations named, composable elaboration interfaces. | Try reusable scoped combinators with explicit lowering contracts. Do not flatten catch, finalization and delayed release into undifferentiated request/answer rows. Handler interaction remains a semantic choice. |
| Birthe van den Berg et al., *Latent Effects for Reusable Language Components*, 2021, local paper 13 §1/§2; [paper](https://arxiv.org/abs/2108.11155) | Delaying a body beyond the operation's return differs from an ordinary scoped body. | Record when bodies run, what they capture and who may resume them. This motivates distinctions, not a proof that a particular IR constructor arrangement is mandatory. |
| Irene Yoon, Yannick Zakowski and Steve Zdancewic, *Formal Reasoning about Layered Monadic Interpreters*, 2022, local paper 04; [author copy](https://www.ireneyoon.com/paper/fralmi.pdf) | Reuse relational interpretation/lifting laws rather than repeating each layer's glue. | The installed `Effects` library already supplies handler composition; C proves an instance by using it. Transfer to the scheduler requires its own relation. |
| Ningning Xie and Daan Leijen, *Generalized Evidence Passing for Effect Handlers*, 2021, local paper 09 §2.3–2.6; [paper](https://xnning.github.io/papers/multip.pdf) | Separate handler lookup, continuation capture and representation costs. | Benchmark dispatch/environment layout and staging costs separately. Canonical indexed lookup trades setup work for cheaper calls; escaping resumptions can invalidate a static-context assumption. No performance result for Effect4 was established here. |
| Daan Leijen, *Koka: Programming with Row-Polymorphic Effect Types*, 2014, local paper 08; [paper](https://arxiv.org/abs/1406.2061); [Effekt contextual effect polymorphism](https://effekt-lang.org/docs/concepts/effect-polymorphism) | Effect-polymorphic higher-order libraries need not have unwieldy user-facing annotations. | Distinguish polymorphic **builders/source interfaces** from the monomorphic closed program you publish. The lack of function-valued Eff nodes alone does not settle the authoring-language question. |
| Xia et al., *Interaction Trees*, 2020, local paper 02; Chappe et al., *Choice Trees*, local paper 03 (2022 preprint/POPL 2023) | Name the equivalence and distinguish environment answers from internal choice. | Reuse their relational vocabulary when needed; do not replace this project's explicit-decision machine merely because a coinductive carrier exists. |

The local paper directory is [the 21-paper collection](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/README.md). Thirteen relevant PDF hashes were checked against its manifest; five were freshly text-extracted successfully. Relevant sections of the existing text and new extracts were read. This is not a claim to have reread all 21 papers end to end.

Foldlab's [reference catalog](/Users/pooks/Dev/foldlab/.reference/catalog/REFERENCES.md) and [ITrees/CTrees survey](/Users/pooks/Dev/foldlab/docs/entity-store/research/itrees-ctrees-literature-notes.md) provide useful navigation. Several effect-related PDFs listed in its paper lock are absent on this Mac; catalog entries are not treated as locally read papers. Its actual [Defun.lean:362](/Users/pooks/Dev/foldlab/library/cas/Cas/Lang/Defun.lean:362), [Defun.lean:998](/Users/pooks/Dev/foldlab/library/cas/Cas/Lang/Defun.lean:998), and [Defun.lean:2101](/Users/pooks/Dev/foldlab/library/cas/Cas/Lang/Defun.lean:2101) supply nearby patterns for direct/embedded execution agreement, storage round trips and rejecting dangling references. Those source statements were inspected, not rebuilt in this task. Their guarantees are not inherited by Effect4.

A further local dependency already contains the general algebraic interfaces:
[Effects/Algebra/Signature.lean:33](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Signature.lean:33),
[Program.lean:40](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Program.lean:40),
[Handler/Composition.lean:32](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Handler/Composition.lean:32).
Its programs contain Lean continuations and are a semantic carrier, not a replacement for durable `Eff` content. The pilot reuses `interpret_through` instead of rebuilding a composition theorem.

## 10. Corrections to the record

| Claim | Correction supported by this run |
|---|---|
| Synthesis §0: nothing in the type layer is statable before the cause arm | Partial inversion, external cause membership, local environment-extension and primitive/row results are already provable. |
| B P2(b): `Val.exitErr (causeImage.toVal c)` | Use `Val.exitErr c`, or `Value.exitErr (causeImage.toVal c)` at the lower carrier. |
| B M2: external-containing programs equal changed verdicts | 1 external golden, 0 changed golden verdicts; the separate regression does change. |
| B M1 suggested golden namespace | The actual corpus is `OCaml5.Eff.Corpus.corpus`, declared in Goldens. |
| Restricted no-cause environment typing needs no other change | Old `Fits` rejects external allocated handles; the relevant state parameter is also required. |
| P5 is an extra parameter on replay | Reference evaluator selection and operational hooks must change too; the scalar counterexample distinguishes them. |
| A certificate around `typeOf` implies the full intended execution guarantee | It certifies exactly `typeOf`; the valid-table perform/callback probe demonstrates the remaining admission distinction. |

Earlier DI-55 and host pair corrections remain as recorded in [the previous review](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-tie-together-codex-review.md); this pass did not repeat those TypeScript probes.

## 11. Probe log and reproducibility

Run from the repository root:

```text
python3 docs/research/2026-09-09-scout-proof-statements-probes.py
python3 docs/research/2026-09-09-scout-descriptor-probes.py
```

Each script stores its complete Lean sources, checks the reviewed commit and relevant source hashes, takes the lane for each Lean invocation, captures exact arguments/output/exit code/timing, and rejects errors, panics and unacceptable proof dependencies. `--extract-only` restores the readable scratch sources without running Lean.

B's [script](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-proof-statements-probes.py) and [JSON receipt](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-09-scout-proof-statements-probes.json) are the durable evidence. They run `Reference.lean` (which contains the foundations, statements and reference probes) and `Measurements.lean`. Scratch lives under `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/87ecec62-218c-44f7-8b37-aa7a52f76968/scratchpad/scouts/B/`.

Final verification uses the saved reproducer, not a remembered intermediate success. All printed B proof dependencies are within `[propext, Quot.sound]`; exact per-declaration output is in the receipt. The receipt also includes the measured populations and verdict changes. Candidate P4/P5 propositions are not counted as proved laws.

Development failures were retained in scratch logs: the first inversion proof attempt, namespace/measurement elaboration errors, and the initial reference fixture's use of `.perform` instead of `.callback`. The latter prompted the additional operation-form experiment rather than being discarded as irrelevant. Failed development outputs are not successful evidence. C records its own metaprogramming-specific failures and corrections.

## 12. Remaining work suitable for Opus 5

These are bounded follow-on assignments, after this Lean-focused pass; they do not need the Lean lane. No Opus agent has been launched by this report.

1. **A/E joint contract pilot:** read both briefs and these results; enumerate the pinned service/error inventory with explicit extraction boundaries; fully trace one scalar row, one allocator, and one structured/union error from a third package. Deliver an observation matrix, candidate projection/refusal policies, real failure fixtures and TypeScript evidence. Do not assume every error must become a pair or that one package's tags identify another's errors.
2. **D census:** rerun into scratch with current provenance; distinguish source occurrences, resolved handler calls, first refusal and counterfactual admission. Deliver both raw counts and denominators. Treat unrecognized syntax and missing checkout pins as data, never agreement.
3. **C remaining integration/history:** use the completed finite pilot and domain census; independently reconcile every historical ordinal-copy claim and full engine declaration mirror, exercise retained-baseline mutations and all four compatibility directions, and specify the producer/import changes. Do not regenerate production outputs or change the root gate.

Before committing a design, compare the proposed slices on: how few files a new operation touches; whether malformed descriptions fail early; whether a reader can find an operation's meaning and host obligations; whether old content remains readable; and measured authoring/generation/dispatch costs. A successful small abstraction should reduce repeated obligations, not merely rename them.

## What I could not verify

No full library/root/axiom gate was run: the brief forbids full builds, and these are isolated probes against existing oleans. No production code changed. Full host conformance, package and corpus census, complete internal-subexpression normalization counts, unrestricted reachability typing, table-aware reference simulation, recursive deriving and multi-target performance remain open. The experiments establish useful construction patterns and concrete limits at the stated pin; they do not establish a definitive language design.
