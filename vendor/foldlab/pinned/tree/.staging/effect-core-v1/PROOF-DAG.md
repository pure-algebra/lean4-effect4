# Effect Core v1 — proposed declaration and proof DAG

Status: **PRE-GRADE / PROPOSED SIGNATURE SNAPSHOT**, 2026-08-31

Claim gate: none

Depends on: `PLAN.md`, `CONTRACT-PACKET.md`, `ALGEBRA.md`,
`CLASSIFICATION.md`

This is Pass A architecture. It contains no Lean declarations or proofs. Every
declaration node is a **PROPOSED TERM**. Every theorem signature is a **PENDING
THEOREM**. Every external gate is a **PENDING HARNESS**. After grilling, a Pass
B snapshot may freeze public Lean names; an implementer may not weaken a
quantifier, premise, observation, or conclusion without reopening the packet.

Signatures below are schematic Lean-shaped notation, not compilable code.

`EXHIBITS-REVIEW.md` fixes which scratch results may be reused and prohibits
globalizing their deterministic CAS/block conclusions. `TYPE-CLOSURE.md` owns
the per-type proof edges and cutover predicate. No scratch carrier is promoted
by appearing in this DAG.

`.staging/agent-reports/2026-08-31-effect-core-local-anchors.md` supplies the
local counterexamples and theorem anchors used to shape the row premises below.
Its report does not discharge any PENDING row.

The evidence-backed §17 rulings freeze conditions 10, 11, 15, 16, 18, 19,
20, and only the classifier half of condition 17 as constraints on a later
Pass B signature. Condition 14 and renderer injectivity remain open. A ruled
condition fixes packet shape; it does not discharge any PENDING node below.

## 1. Declaration DAG

```text
D0  ValueTy / rows / values / identifiers / diagnostics
 |\
 | D1  frozen PublicSurface rows / seven dispositions / smaller Alphabet /
 |     OpDesc / pure and foreign registries
 |  \
 |   D2  RawProgram / blocks / regions / ProgramWF
 |    |\
 |    | D3  checker / normalizer / CheckedProgram / erasure
 |    |  \
 |    |   D4  Flow constructors and graph composition
 |    |    |\
|    |    | D5  DirectHandler / CauseTree / Exit / reference state
 |    |    |  \
 |    |    |   D6  Step / execStep / execN
 |    |    |    |\
 |    |    |    | D7  Runs / Denotes / derived FinApprox / observation masks
 |    |    |    |  \
 |    |    |    |   D8  abstract domains / classifier / reductions
 |    |    |    |
 |    |    |    +---- D9  scope / resource / fiber / cancellation laws
 |    |    |
 |    |    +--------- D10 CAS injection / projection / canonical seam
 |    |
 |    +-------------- D11 TsCore / lowering / target semantics / renderer
 |                         |
 +-------------------------D12 AcceptedTs relation / tooling evidence plane
                           |
                           D13 compiler and host bridge obligations
```

No node imports TypeScript diagnostics into `ProgramWF`, `Step`, `Runs`, or
`Denotes`. D12 consumes D11 output and records evidence; it is not an
ancestor of the Semantic Model.

## 2. Proposed public declaration shapes

### D0–D1: types and closed operations

```text
PROPOSED TERM EC1-D001  ValueTy : Type; toAst? : ValueTy -> Option Cas.Schema.Ast
PROPOSED TERM EC1-D002  Value : ValueTy -> Type; ElBridge on supported codes
PROPOSED TERM EC1-D003  ErrorRow : Type
PROPOSED TERM EC1-D004  RequirementRow : Type
PROPOSED TERM EC1-D005  AER : Type
PROPOSED TERM EC1-D006  PublicSurface : Type
PROPOSED TERM EC1-D007  SurfaceRowKey : Type
PROPOSED TERM EC1-D008  SurfaceDisposition : Type
PROPOSED TERM EC1-D009  PublicSurfaceWF : PublicSurface -> Prop
PROPOSED TERM EC1-D010  Alphabet : Type
PROPOSED TERM EC1-D011  OpDesc : (a : Alphabet) -> a.toSig.Op -> Type
PROPOSED TERM EC1-D012  PureExpr : Context -> ValueTy -> Type
PROPOSED TERM EC1-D013  PureAtom : Context -> ValueTy -> Type
PROPOSED TERM EC1-D014  ForeignEffect : Alphabet -> OpId -> Type
```

The source hoover owns completeness of `PublicSurface`;
Lean consumes generated rows and decides disposition/mapping totality. The
authored `Alphabet` is a mapped subset, never the source universe.

`EC1-D011` is only the proposed Lean-modeled specialization. Freeze condition
14 remains open until a neutral protocol operation identity and its explicit
admission bridge to existing `Sig.Op`/`Sig.Ans` are declared; host-obligation
identities may not be forced through that bridge or mistaken for Lean-modeled
operations.

Required instance/declaration obligations: decidable equality for codes and
IDs; canonical ordering/normalization for rows and tables; typed lookup; finite
enumeration of operation IDs; no function-valued serialization field.

### D2–D4: graph boundary and composition

```text
PROPOSED TERM EC1-D020  RawProgram : Type
PROPOSED TERM EC1-D021  ProgramWF : RawProgram -> Prop
PROPOSED TERM EC1-D022  Diagnostic : Type
PROPOSED TERM EC1-D023  CheckedProgram : AER -> Type
PROPOSED TERM EC1-D024  check : RawProgram -> Except Diagnostic
                                      (Sigma CheckedProgram)
PROPOSED TERM EC1-D025  erase : CheckedProgram aer -> RawProgram
PROPOSED TERM EC1-D026  normalizeRaw : RawProgram -> RawProgram
PROPOSED TERM EC1-D027  Flow : AER -> Type
PROPOSED TERM EC1-D028  close / seq / choose / catch / scope / ensure /
                        provide / par / race / feedback / await / join /
                        requestInterrupt / interruptAwait
```

Each proposed `Block` contains the existing `PProg` as its sequential body and
adds parameters, region, and terminator. No second sequential line/table type
is a declaration node.

### D5–D7: reference semantics

```text
PROPOSED TERM EC1-D040  CauseTree : ErrorRow -> Type
PROPOSED TERM EC1-D041  CauseReasons : ErrorRow -> Type
PROPOSED TERM EC1-D042  quotientCause : CauseTree e -> CauseReasons e
PROPOSED TERM EC1-D043  Exit : ErrorRow -> ValueTy -> Type
PROPOSED TERM EC1-D044  DirectHandler : Alphabet -> HandlerRoute -> Type
PROPOSED TERM EC1-D045  HandlerEnv : Alphabet -> Type
PROPOSED TERM EC1-D046  Configuration : CheckedProgram aer -> Type
PROPOSED TERM EC1-D047  Label : Type
PROPOSED TERM EC1-D048  Step : Configuration p -> Label -> Configuration p -> Prop
PROPOSED TERM EC1-D049  Decision : Configuration p -> Type; DecisionSelects
PROPOSED TERM EC1-D050  execStep : (c : Configuration p) -> Decision c -> ExecResult p
PROPOSED TERM EC1-D051  execN : Nat -> DecisionTape p -> Configuration p -> RunPrefix p
                             with TapeCompatible c tape
PROPOSED TERM EC1-D052  FinApprox : Nat -> Configuration p -> Type; approx
PROPOSED TERM EC1-D053  truncate : m <= n -> FinApprox n c -> FinApprox m c
PROPOSED TERM EC1-D054  Runs : Configuration p -> List Label -> Configuration p -> Prop
                             Denotes : CheckedProgram aer -> Initial p
                                     -> List Label -> Configuration p -> Prop
PROPOSED TERM EC1-D055  ObservationMask : Type; Observed O p i x : Prop
PROPOSED TERM EC1-D056  SemEq O p q := forall i x,
                                      Observed O p i x <-> Observed O q i x
```

### D8–D9: classification and structured runtime state

```text
PROPOSED TERM EC1-D060  AbsDomain : Type
PROPOSED TERM EC1-D061  Bounds : AbsDomain -> Type
PROPOSED TERM EC1-D062  ClassProduct : Type
PROPOSED TERM EC1-D063  classify : CheckedProgram aer -> ClassProduct
PROPOSED TERM EC1-D064  concreteClass : List Label -> Configuration p -> ConcreteProduct
PROPOSED TERM EC1-D065  gammaProduct : ClassProduct -> Set ConcreteProduct
PROPOSED TERM EC1-D066  reduceProduct : ClassProduct -> ClassProduct
PROPOSED TERM EC1-D070  ScopeFrame / ResourceEntry / FiberState / Scheduler
```

### D10–D13: CAS and generated TypeScript

```text
PROPOSED TERM EC1-D080  CasAdmissible : PProg -> Prop
PROPOSED TERM EC1-D081  CheckedPProg := { p : PProg // CasAdmissible p }
PROPOSED TERM EC1-D082  admitCas : PProg -> Option CheckedPProg
PROPOSED TERM EC1-D083  injectCas : CheckedPProg -> CheckedProgram casAER
PROPOSED TERM EC1-D084  CasImage : CheckedProgram casAER -> Prop
PROPOSED TERM EC1-D085  toPProg : CheckedProgram casAER -> Option PProg
PROPOSED TERM EC1-D086  projectCas : CasImage p -> PProg
PROPOSED TERM EC1-D087  canonCore / canonCas
PROPOSED TERM EC1-D090  TsCore : AER -> Type
PROPOSED TERM EC1-D091  lower : CheckedProgram aer -> TsCore aer
PROPOSED TERM EC1-D092  TargetRuns : TsCore aer -> InitialTarget
                                   -> TargetTrace -> TargetState -> Prop
PROPOSED TERM EC1-D093  render : TsCore aer -> Bytes
PROPOSED TERM EC1-D094  structuralDecode : Bytes -> Except Diagnostics (Sigma TsCore)
PROPOSED TERM EC1-D095  AcceptedTs : ToolPins -> Bytes -> TsCore aer -> Prop
PROPOSED TERM EC1-D096  EvidencePlane : Type
```

## 3. Foundation theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T001` | PENDING THEOREM | `normalizeRow_idempotent : norm (norm r) = norm r` | D0 |
| `EC1-T002` | PENDING THEOREM | `normalizeRow_canonical : NodupKeys r -> NodupKeys s -> (rowEq r s <-> norm r = norm s)` | `T001`; existing `canonServices_perm_of_nodup_keys`/`canonServices_perm` shape |
| `EC1-T003` | PENDING THEOREM | `pure_eval_adequate : EnvWF env -> (evalPure e env = v <-> PureDenotes env e v)` | D0–D1; structural decrease; relational pure semantics |
| `EC1-T003E` | PENDING THEOREM | `value_el_bridge : toAst? τ = some ast -> Value τ ≃ Cas.Schema.El ast` | supported overlap only; empty/unsupported `El` arms excluded explicitly |
| `EC1-T004` | PENDING THEOREM | `alphabet_lookup_total : op in a -> exists! d, lookup a op = some d` | D1 |
| `EC1-T004S` | PENDING THEOREM | `alphabet_answer_bridge : (op : a.toSig.Op) -> Value (lookup a op).answerTy ≃ a.toSig.Ans op` | `T004`; existing `Sig` answer indexing |
| `EC1-T004X` | PENDING THEOREM | `alphabet_sum_preserves_arms : extend a b |>.toSig = a.toSig ⊕ₛ b.toSig` with left/right metadata and handler projections | existing `Sig.sum`, `Handler.sum`, `Prog.inl/inr` laws |
| `EC1-T004RW` | PENDING THEOREM | existing `RootSig`/`StoreSig` and `WordSig`/`WordedSig` CAS-agreement and WF-preservation laws remain imported under alphabet selection | `stepRooted_cas_agrees`, `since_cas_agrees`, corresponding preservation theorems |
| `EC1-T005` | PENDING THEOREM | `serialized_fields_first_order : SerializableField raw field -> not FunctionVal field` | D2 |
| `EC1-T006` | PENDING THEOREM | `normalizeRaw_idempotent : normalizeRaw (normalizeRaw r) = normalizeRaw r` | D2 |
| `EC1-T007` | PENDING THEOREM | `normalizeRaw_alpha : alphaEq r s -> normalizeRaw r = normalizeRaw s` | D2, `T006` |
| `EC1-T008` | PENDING THEOREM | `surface_disposition_total : PublicSurfaceWF s -> forall row in s, exists! d, disposition row = d` | generated surface rows; seven-value enum |
| `EC1-T009` | PENDING THEOREM | `surface_mapping_closed : PublicSurfaceWF s -> every effect-bearing row has a constructive mapping/direct-handler-or-boundary witness` | `T008`; generated mapping rows |

The deleted `exists! v, evalPure e env = v` and same-input function-equality
forms are tautologies for any Lean function. `EC1-T003` instead owes a
two-sided semantic adequacy result. `EC1-T002` deliberately carries the premise
shown necessary by `Cas/Backend/Canon.lean`'s duplicate-key counterexample.

## 4. Admission theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T010` | PENDING THEOREM | `check_sound : check r = ok <a,p> -> ProgramWF r` | D0–D3 |
| `EC1-T011` | PENDING THEOREM | `check_complete : ProgramWF r -> exists p, check r = ok <a,p>` | D0–D3; decidability of every WF clause |
| `EC1-T012` | PENDING THEOREM | `check_error_iff : (exists d, check r = error d) <-> not ProgramWF r` | `T010,T011`; decidable WF |
| `EC1-T013` | PENDING THEOREM | `check_erase : check (erase p) = ok <a, normalizeChecked p>` | `T006,T010` |
| `EC1-T014` | PENDING THEOREM | `erase_wf : ProgramWF (erase p)` | `T010,T013` |
| `EC1-T015` | PENDING THEOREM | `first_diagnostic_complete : FirstReject r path code -> check r = error (diagnostic path code)` | canonical checker order; existing `checkRefs_error_condemns`/`checkRefs_complete` shape |
| `EC1-T016` | PENDING THEOREM | `aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer` | D0–D3 |
| `EC1-T017` | PENDING THEOREM | `checked_aer_exact : p : CheckedProgram aer -> SynthAER (erase p) aer` | `T010,T016` |

`EC1-T011/T012` are prohibited if any `ProgramWF` clause is silently changed to
an undecidable semantic property. Such a change requires a new checked-boundary
design and a weaker, explicitly regraded contract.

`EC1-T015` is first-error completeness, not an accumulating-diagnostic theorem.
The local two-defect counterexample proves that a fail-fast checker cannot
promise every condemning clause. Changing this row back requires explicitly
constructing and separately proving an accumulating checker.

## 5. Flow algebra theorem bundle

All equivalences below quantify over initial worlds, admitted direct handlers,
decision interfaces, and the stated observation mask.

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T020` | PENDING THEOREM | `wf_close / wf_seq / wf_choose / wf_scope / wf_par / wf_race` | `T010,T016`; graph builders |
| `EC1-T021` | PENDING THEOREM | `seq_left_id : SemEq O (seq (close x) k) (instantiate k x)` | relational `SemEq`; graph simulation |
| `EC1-T022` | PENDING THEOREM | `seq_right_id : SemEq O (seq p closeRef) p` | relational `SemEq`; graph simulation |
| `EC1-T023` | PENDING THEOREM | `seq_assoc : SemEq O (seq (seq p k) h) (seq p (composeCont k h))` | relational `SemEq`; graph simulation |
| `EC1-T024` | PENDING THEOREM | `map_identity / map_compose` | `T003`; relational `SemEq` |
| `EC1-T025` | PENDING THEOREM | `catch_close / catch_raise` | cause and handler semantics |
| `EC1-T026` | PENDING THEOREM | `feedback_unfold : SemEq O (feedback body) (guardedUnfold body)` | approximation coherence |
| `EC1-T027` | PENDING THEOREM | `alpha_semantics : alphaEq p q -> SemEq O p q` | `T007`; Step simulation |
| `EC1-T028` | PENDING THEOREM | `par_commute_independent : Independent p q -> SemEq (quotientIndependent O) (par p q) (swap (par q p))` | classifier frame proof, concurrency semantics |

There is deliberately no `race_commute` or unconditional `par_commute`
signature.

## 6. Machine safety and semantic triangle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T030` | PENDING THEOREM | `initial_wf : InitialWF p i -> ConfigWF (initialConfig p i)` | admission; handler completeness |
| `EC1-T031` | PENDING THEOREM | `step_preservation : ConfigWF c -> Step c l c' -> ConfigWF c'` | every Step rule |
| `EC1-T032` | PENDING THEOREM | `step_progress : ConfigWF c -> HandlerComplete c -> terminal c or suspended c or exists l c', Step c l c'` | `T004,T031` |
| `EC1-T033` | PENDING THEOREM | `execStep_sound : execStep c d = advanced l c' -> Step c l c'` | D6 |
| `EC1-T034` | PENDING THEOREM | `execStep_complete : Step c l c' -> exists d, execStep c d = advanced l c'` | D6; decision adequacy |
| `EC1-T035` | PENDING THEOREM | `decision_resolves_relation : DecisionSelects c d l c' -> Step c l c' and forall l' c'', DecisionSelects c d l' c'' -> l'=l and c''=c'` | D6; every nondeterministic Step premise represented in `Decision` |
| `EC1-T036` | PENDING THEOREM | `execN_rel : execN n tape c = prefix -> RelPrefix n tape c prefix` | `T033`, induction on `n` |
| `EC1-T037` | PENDING THEOREM | `rel_execN : RelPrefix n tape c prefix -> execN n tape c = prefix` | `T034,T035` |
| `EC1-T038` | PENDING THEOREM | `finApprox_finite_support : exists k, treeSize (approx n c) = k and every scheduler node has finite children` | finite graph/fibers; symbolic request frontier |
| `EC1-T039` | PENDING THEOREM | `approx_coherent : (h : m<=n) -> truncate h (approx n c) = approx m c` | induction on `m`; Step rules |
| `EC1-T040` | PENDING THEOREM | `exec_approx_member : execN n tape c = r -> observe r in approx n c` | `T033,T039` |
| `EC1-T041` | PENDING THEOREM | `approx_runs_adequate : leaf in approx n c <-> exists tr c', Runs c tr c' and depth tr <= n and leaf observes (tr,c')` | `T034,T038,T039`; both directions |
| `EC1-T042` | PENDING THEOREM | `semEq_approx_iff : SemEq O p q <-> forall i n, mask O (approx n (initialConfig p i)) = mask O (approx n (initialConfig q i))` | relational definition of `SemEq`; `T039,T041`; no family extensionality |
| `EC1-T043` | PENDING THEOREM | `semEq_equivalence : Equivalence (SemEq O)` | `T042` |
| `EC1-T044` | PENDING THEOREM | `diverges_iff_live_prefixes : Diverges c decisions <-> forall n, Live (execN n decisions c)` | compatible infinite decision stream; live is neither Refusal nor Cause |
| `EC1-T045` | PENDING THEOREM | `fixed_tape_relational_unique : TapeCompatible c tape -> RelPrefix n tape c r1 -> RelPrefix n tape c r2 -> normalizePrefix r1 = normalizePrefix r2` | `T035–T037`; proved from relation/executor adequacy, not function determinism; scheduler policy/state is in `c`; no separate schedule argument |
| `EC1-T045A` | PENDING THEOREM | `ask_free_decision_irrelevant : AskFree c -> (forall c', Reachable c c' -> Subsingleton (Decision c')) -> TapeCompatible c tape1 -> TapeCompatible c tape2 -> RelPrefix n tape1 c r1 -> RelPrefix n tape2 c r2 -> normalizePrefix r1 = normalizePrefix r2` | `T035–T037`; the workshop `denotes_unique_on_the_askFree_fragment` is evidence only for the subfragment whose sole choices are asks; full-core ask-freedom alone does not exclude scheduler, race, foreign, or replay choices |
| `EC1-T046` | PENDING THEOREM | `cas_block_stable_outcome_unique : two completed non-frontier CAS/block outcomes selected beyond sufficient unfolding fuel agree with the exhibited big-step result` | CAS injection; big-step handler interpretation; excludes exhaustion/frontier labels |

`EC1-T035` is not the tautology that a Lean function has one output. It states
that the explicit decision interface is exhaustive and exclusive for the
relation's nondeterminism; together with `T033–T034` it makes a fixed decision
tape the only executable choice source.

`EC1-T045` is relational: two derivations from the same initial configuration
and compatible tape must agree after normalization. It is not discharged by
the fact that `execN` is a function. `EC1-T045A` records the narrower
ask-free result supported by the workshop exhibit. In the full core,
`AskFree` must be paired with a proved absence of every other decision source;
ask-freedom by itself says nothing about scheduler ties, races, foreign
responses, or replay selection.

`EC1-T038` states that each produced approximation has finite structure. It
does not assert that the type of all approximations has finitely many
inhabitants; values, requests, and world projections may range over infinite
types. The deterministic `Denotes`/coherence exhibit applies only to stable
non-frontier outcomes in its CAS/block subfragment. It does not equate
incidental exhaustion/refusal labels at smaller fuels. Full-core `Denotes` is
a proposition relating traces and reached configurations over answers,
scheduler-enabled choices, and symbolic frontiers. Only a fixed initial
configuration and compatible complete decision tape induce one deterministic
executable path; scheduler policy/state is already in that configuration.
There is no public behavior or disguised coherent-family carrier and no
full-core `denotes_unique` node.
Big-step coherence for a selected deterministic unfolding factors through
`interpret_bind`; fixed-fuel `run` is related by step/fuel adequacy and is never
given a nonexistent general bind law.

## 7. Direct-handler theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T050` | PENDING THEOREM | `direct_lookup_unique : HandlerEnvWF h -> reachable op -> exists! clause, directLookup h op = clause` | D1,D5; checker |
| `EC1-T051` | PENDING THEOREM | `handler_types : HandlerWF h -> handles h op req = exit -> ExitHasType exit op.errors op.answerTy` | D5 |
| `EC1-T052` | PENDING THEOREM | `handler_frame : HandlerWF h -> handles h op req w = (x,w') -> EqualOutside h.frame w w'` | handler clauses |
| `EC1-T053` | PENDING THEOREM | `provide_lookup / provide_restore` | region Step rules; `T031` |
| `EC1-T054` | PENDING THEOREM | `resume_at_most_once : ConfigWF c -> reachable c' -> consumedCount token c' <= 1` | `ResumeWF,T031` |
| `EC1-T055` | PENDING THEOREM | `interpret_seq : denoteHandler h (seq p k) = semanticBind (denoteHandler h p) (denoteHandler h k)` | `T023,T041` |
| `EC1-T056` | PENDING THEOREM | `direct_handler_elaborates : DirectHandlerWF d -> exists h : Handler, DirectHandlerDenotes d h` | existing `Handler`; direct-route checker; target exposes child `Exit`/machine state |
| `EC1-T057` | PENDING THEOREM | `handler_sum_composes : DirectHandlerDenotes dS hS -> DirectHandlerDenotes dT hT -> DirectHandlerDenotes (sum dS dT) (Handler.sum hS hT)` | existing `Handler.sum`; both handlers share the same target monad |
| `EC1-T057T` | PENDING THEOREM | `handler_through_composes : DirectHandlerDenotes dUpper (hUpper : Handler S (Prog T)) -> DirectHandlerDenotes dLower (hLower : Handler T M) -> DirectHandlerDenotes (through dUpper dLower) (Handler.through hUpper hLower)` | existing `Handler.through`; applies only through the intermediate `Prog T` |
| `EC1-T058` | PENDING THEOREM | `handler_target_recovers : catch child handler in the selected state/error/machine target observes child failure and can return handler success` | rejects `ReaderT Env (Prog CasSig)` by `no_handler_into_ScopeM_catches`; ensuring also requires state to survive failure; minimum CAS witness `ReaderT Env (ExceptT Refusal (StateT Word Id))` |
| `EC1-T059` | PENDING THEOREM | `ensure_runs_after_failure : registered ensure body finalizer and body exits by typed failure/refusal -> finalizer begins before scope exit` | state-surviving failure target, minimally for CAS `ReaderT Env (ExceptT Refusal (StateT Word Id))`; machine unwind rules; existing `ensuring_never_finalises_a_refusal` excludes `Prog.bind` implementation |

Scoped children are `BlockId`s interpreted by the same existing `Handler`
carrier into an adequate state/error/machine target that observes child
outcomes. That scoped interpretation is direct; it is not an application of
`Handler.through`. `Handler.sum` handles same-target signature composition,
while `Handler.through` discharges only the separately typed `Prog T` tower
case in `EC1-T057T`. There is no `HHandler` declaration or proof node. The scratch
`scopeHandler` clauses are not a semantic premise for catch, scope,
interruption, or finalization. `scopeHandlerR` is a catch-only witness and loses
the state needed by ensuring; it, `scopeHandlerW`, and all scratch helper
carriers remain unpromoted. The adopted information contract is only that the
selected target observes child outcome and preserves state on failure.

## 8. Scope, resource, and cause theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T060` | PENDING THEOREM | `region_non_escape : ConfigWF c -> ResourceOrScopedFiber v region -> visibleOutside region c -> False` | `RegionsWF,T031` |
| `EC1-T061` | PENDING THEOREM | `register_atomic : registrationCommitted trace r <-> exactly one resourceRegistered event for r before any delivery` | registration Step rules |
| `EC1-T062` | PENDING THEOREM | `release_exactly_once : registered r trace -> scopeHalted owner trace -> countRelease r trace = 1` | `T031,T061`; finalizer progress-to-halt premise |
| `EC1-T063` | PENDING THEOREM | `release_zero_unregistered : not registered r trace -> countRelease r trace = 0` | scope rules |
| `EC1-T064` | PENDING THEOREM | `release_lifo : registeredBefore r1 r2 -> bothReleased -> releaseBefore r2 r1` | finalizer stack invariant |
| `EC1-T065` | PENDING THEOREM | `scope_waits_cleanup : parentResumed scope trace -> allOwnedHalted scope trace and allRegisteredReleased scope trace` | scope exit rules |
| `EC1-T066` | PENDING THEOREM | `cause_finalizer_then : bodyFails b -> finalizerFails f -> scopeExit = failure (CauseTree.then b f)` | CauseTree rules |
| `EC1-T067` | PENDING THEOREM | `typed_catch_only_fail : catchTyped h cause = handled -> selected fail leaves are covered and every unhandled branch is retained` | CauseTree eliminator |
| `EC1-T068` | PENDING THEOREM | `quotientCause_then_both : quotientCause (CauseTree.then x y) = quotientCause (CauseTree.both x y)` | rc.112 stable de-duplicating reason quotient |
| `EC1-T069` | PENDING THEOREM | `stock_cause_bridge : stockCauseObservation runtime = quotientCause modelTree` | conditional G4 observation; never full topology |

`EC1-T062` requires the premise that the scope reaches a halted exit. If a
finalizer diverges, the correct conclusion is “release began once and the
scope remains finalizing,” not a fabricated completion theorem.

## 9. Fiber, scheduling, and cancellation theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T070` | PENDING THEOREM | `fiber_owner_unique : ConfigWF c -> live fiber -> exists! owner, Owns owner fiber c` | `FibersWF,T031` |
| `EC1-T071` | PENDING THEOREM | `scoped_children_closed : scopeHalted s -> forall child ownedBy s, halted child` | `T065,T070` |
| `EC1-T072` | PENDING THEOREM | `await_exit : awaitReturned parent child x -> childExit child = x` | await rules |
| `EC1-T072J` | PENDING THEOREM | `join_success_or_propagates : joinReturned parent child a -> childExit child = success a; joinFailed parent child c -> childExit child = failure c` | join rules |
| `EC1-T072I` | PENDING THEOREM | `interrupt_awaits_cleanup : interruptAwaitReturned parent child -> halted child and childFinalizersComplete child` | interrupt-and-await rules |
| `EC1-T073` | PENDING THEOREM | `mask_retains_pending : interruptPending f -> masked f -> stepsWithinMask -> interruptPending f'` | mask rules; `T031` |
| `EC1-T074` | PENDING THEOREM | `unmask_delivers : interruptPending f -> reachesInterruptibleBoundary -> nextSemanticAction is delivery` | delivery priority rule |
| `EC1-T075` | PENDING THEOREM | `race_losers_interrupted : raceParentResumed r -> forall loser, interruptRequested loser and halted loser` | race + cleanup rules |
| `EC1-T076` | PENDING THEOREM | `race_cleanup_before_resume : loserFinalizers r precede parentResume r` | `T065,T075` |
| `EC1-T077` | PENDING THEOREM | `fixed_decision_replay : same initial Configuration and same compatible DecisionTape -> same normalized execN` | `T035`, induction on fuel; scheduler policy/state is part of `Configuration` |
| `EC1-T078` | PENDING THEOREM | `safety_no_fairness : SafetyInvariant inv -> all finite Step prefixes preserve inv` | `T031`; no fairness premise |
| `EC1-T079` | PENDING THEOREM | `fair_liveness : FairSelections c decisions -> HandlerProgress -> FinalizerProgress -> RankedInternalCycles -> eventually terminal or externalSuspended` | compatible infinite decision stream; fairness concerns ready-fiber selections enabled by the scheduler stored in evolving configurations |

## 10. Classifier theorem bundle

For each domain `D`, define `concreteD` from one `Denotes` witness and `gammaD`
from the abstract result.

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T080` | PENDING THEOREM | `transfer_monotone_D : Monotone transferD` for every constructor/operator | domain definitions |
| `EC1-T081` | PENDING THEOREM | `transfer_sound_D : child facts in gamma -> composed fact in gamma (transfer child summaries)` | semantics of matching constructor |
| `EC1-T082` | PENDING THEOREM | `loop_solver_sound_D : solution = loopD cfg -> every finite unfolding fact in gamma solution` | `T080`; SCC fixed point |
| `EC1-T083` | PENDING THEOREM | `classify_sound_D : classifyD p = a -> Denotes p i tr c' -> concreteD tr c' in gammaD a` | `T081,T082`; graph induction/SCC |
| `EC1-T084` | PENDING THEOREM | `reduce_sound : concrete in gammaProduct c -> concrete in gammaProduct (reduceProduct c)` | one lemma per reduction |
| `EC1-T085` | PENDING THEOREM | `classify_sound : classify p = c -> Denotes p i tr c' -> concreteClass tr c' in gammaProduct c` | every `T083`, `T084` |
| `EC1-T086` | PENDING THEOREM | `exact_field_complete : precision field = exact -> lower field = concrete field and upper field = concrete field` | domain-specific completeness certificate |
| `EC1-T087` | PENDING THEOREM | `aer_classifier_exact : (classify p).aer = staticAER p` | `T017`; transfer equations |
| `EC1-T088` | PENDING THEOREM | `classifier_semEq_overlap : SemEq O p q -> Observed O p i x -> x in gammaProjection O (classify p) and x in gammaProjection O (classify q)` | `T042,T085`; `SemEq` supplies the corresponding `q` run; mask-selected facts only |

No theorem requires complete classifier equality under `SemEq`. In particular,
the local CAS witness has equal runs but different `PProg.envelope` answer-
dataflow graphs. D4 and other structural/provenance fields may therefore differ;
only explicitly mask-selected concrete projections participate in `EC1-T088`.

## 11. Foreign theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T090` | PENDING THEOREM | `foreign_registry_total : ForeignWF p -> reachable foreignOp -> exists! entry, registryLookup = entry` | checker |
| `EC1-T091` | PENDING THEOREM | `foreign_model_frame : modelStep entry req w = x,w' -> EqualOutside entry.frame w w'` | registry model definition |
| `EC1-T092` | PENDING THEOREM | `receipt_roundtrip : decodeReceipt (encodeReceipt r) = ok r` | receipt codec |
| `EC1-T093` | PENDING THEOREM | `receipt_replay : receiptMatches entry initial req r -> replay r initial req = recordedModelObservation r` | `T092`; declared frame |
| `EC1-T094` | PENDING THEOREM | `host_foreign_conformance` | **conditional** on exact host pin and G4/G6 evidence; not derivable from model |

## 12. CAS sublanguage theorem bundle

These obligations are early (`EC1-S3`) so later power cannot obscure a CAS
regression. Injection rows quantify over `p : CheckedPProg`; `p.val` is the
existing canonical `PProg`. Refusal-map rows quantify over their existing
closed model/host universes.

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T100` | PENDING THEOREM | `admitCas_iff : (admitCas raw).isSome = true <-> CasAdmissible raw` and successful admission yields `ProgramWF (erase (injectCas p))` | Core checker; `PLine.WF`; dataflow/entry checks; empty and dangling negatives |
| `EC1-T101` | PENDING THEOREM | `recognize_injectCas : toPProg (injectCas p) = some p.val` | D10; literal canonical-image recognition |
| `EC1-T101S` | PENDING THEOREM | `toPProg_sound : toPProg g = some q -> CasAdmissible q and g is the canonical normalized injected image of q and its CAS-mask relational observations agree with q` | structural recognizer proof; never completeness under `SemEq` |
| `EC1-T101P` | PENDING THEOREM | `project_injectCas : projectCas (casImage_inject p) = p.val` | `T101`; total restriction to `CasImage` |
| `EC1-T102` | PENDING THEOREM | `run_injectCas : runCore H (p.val.length + 1) (injectCas p) w = runP H p.val w` | existing `runP_embed_agree`; tight fuel witness |
| `EC1-T103` | PENDING THEOREM | `denotes_injectCas : Observed casMask (injectCas p) i x <-> CasObserved p.val i x` | `T102,T041`; existing `ObsEq_embed_of_runP` direction |
| `EC1-T104` | PENDING THEOREM | `canon_injectCas : canonCore (injectCas p) = canonCas p.val` | canonical serializer; `T101`; any address recovery separately carries WF/separation premises |
| `EC1-T105` | PENDING THEOREM | `classify_injectCas_sound : existingEnvelopeFacts p.val refine (classify (injectCas p))` | existing envelope upper/lower theorems; `T085` |
| `EC1-T106` | PENDING THEOREM | `cas_no_new_observation : runMask observes status and partial word; obsEqMask observes refusal but hides its partial word` | injection shape; existing `ObsEq.run_refused` boundary |
| `EC1-T107` | PENDING THEOREM | `cas_refusal_map_reused : casRefusalClass (injectCas p) = existing RefusalMap classification` | existing `Refusal.Clause`/`RefusalMap`; no new enum |
| `EC1-T108` | PENDING THEOREM | `cas_error_row_from_ops : staticAER (injectCas p).E = synthesized injected OpDesc error rows` | checker; never `PProg.envelope` |
| `EC1-T109` | PENDING THEOREM | `cas_world_observation_scoped : exact writes quantify over H and refusal-word equality is required only when the selected mask exposes it` | existing H-dependent run and `ObsEq` boundaries |
| `EC1-T123` | PENDING THEOREM | `cas_partial_correctness_bridge : ModelsPartial (injectCas p) Q <-> wlp H p.val Q` | existing `wlp`; `T103` under the CAS observation mask |
| `EC1-T124` | PENDING THEOREM | `cas_total_correctness_bridge : wp H p.val Q w <-> (wlp H p.val Q w and wp H p.val WPost.top w)` | existing `wp_iff_wlp_and_total`; the second conjunct is totality; no new modality |
| `EC1-T125` | PENDING THEOREM | `auth_security_injectCas` transports `whole_run_security` through injection with no premise on `H` and the same explicit collision branch | `Cas/Lang/Auth.lean`; `T102`; hash-lattice Level 0 |
| `EC1-T126` | PENDING THEOREM | `auth_correctness_injectCas` transports `whole_run_correctness` through injection | `Cas/Lang/Auth.lean`; `T102` |
| `EC1-T127` | PENDING THEOREM | every existing `Refusal.Clause` has a nonempty host image and every host tag is mapped or in the declared host-only row | existing `hosts_ne_nil`, `mapped_or_hostOnly`, `clause?_none_iff_hostOnly` |
| `EC1-T128` | PENDING THEOREM | model-to-host and host-to-model table agreement is exactly existing `RefusalMap.table`/`hostOnlyTable` | existing table agreement/completeness family |
| `EC1-T129` | PENDING THEOREM | refusal host images are disjoint and model/host wires are duplicate-free | existing `hosts_disjoint`, `wire_nodup` theorems |
| `EC1-T130` | PENDING THEOREM | `modE_wlp_append : pre != [] -> wlp H (pre ++ post) Q w <-> wlp H pre (fun _ w' => wpAux H True (PProg.answersFrom H [] pre) post Q w') w` | new obligation derived by specializing shipped `wpAux_append`; suffix receives prefix answer history; no restarted table-only rule; scratch `wlp_append` is not promoted |

`EC1-T100` is the admission stop: raw empty and dangling `PProg` values remain
representable but cannot be silently coerced into `CheckedProgram`.
`EC1-T101S` is a sound recognizer theorem, not a semantic projection theorem:
unreachable-tail and relocated-entry counterexamples may be `SemEq` to an
injected graph while `toPProg` returns `none`. `EC1-T104` is the identity stop
theorem: without it, the new carrier may reason about CAS but may not become an
alternative canonical CAS serializer.

`EC1-T123–T124` specialize the general semantic judgments to the existing CAS
logic. They do not introduce another `WPre`, `WPost`, EffHOL modality, `wlp`,
or `wp` carrier. `EC1-T130` is the only proposed Mod-E theorem and retains both
the nonempty-prefix and threaded-history premises forced by the counterexamples.
It is new work whose shipped derivation anchor is `wpAux_append`; no estate
`wlp_append` theorem is inherited.

## 13. TypeScript target theorem bundle

| ID | Status | Schematic signature | Depends on |
| --- | --- | --- | --- |
| `EC1-T110` | PENDING THEOREM | `lower_wf : TsCoreWF (lower p)` | D11; per-constructor typing |
| `EC1-T111` | PENDING THEOREM | `lower_aer : targetAER (lower p) = sourceAER p` with every source transform justified by its canonical public overload row | `T009,T017,T087` |
| `EC1-T112` | PENDING THEOREM | `lower_step_sim : source Step c l c' -> exists t t', targetSteps t (mask l) t' and Relate c t and Relate c' t'` | per-constructor simulations |
| `EC1-T113` | PENDING THEOREM | `lower_step_reflect : target public step -> corresponding source weak step` | target administrative-step quotient |
| `EC1-T114` | PENDING THEOREM | `lower_denotes : Observed O p i x <-> TargetObserved O (lower p) (lowerInitial i) x`, where stock rc.112 requires `O <= effectReasonQuotient` | `T068,T112,T113,T039,T042`; relational preservation |
| `EC1-T115` | PENDING THEOREM | `render_injective_normal : TsCoreWF t1 -> TsCoreWF t2 -> normalizeTarget t1=t1 -> normalizeTarget t2=t2 -> render cfg t1 = render cfg t2 -> t1=t2` | canonical constructor/escaping uniqueness; normalized admitted subset only |
| `EC1-T116` | PENDING THEOREM | `decode_render : structuralDecode (render t) = ok (normalizeTarget t)` | parser/validator and renderer |
| `EC1-T117` | PENDING THEOREM | `render_decode_canonical : structuralDecode b = ok t -> render (normalizeTarget t) = canonicalize b` | admitted source subset only |
| `EC1-T118` | PENDING THEOREM | `accepted_source_checked : AcceptedTs pins b t -> exists p, CheckedSourceGraph b p and lower p = normalizeTarget t`, including canonical public symbol/overload selection | `AcceptedTs` includes structural relation; `T009` |
| `EC1-T119` | PENDING THEOREM | `accepted_diagnostics_no_semantic_power : AcceptedTs pins b t -> ProgramWF p` only through `CheckedSourceGraph`, never diagnostic output alone | trust-boundary factorization |
| `EC1-T120` | PENDING THEOREM | `code_action_semantics : AdmittedAction pins a b b' -> decode b=t -> decode b'=t' -> SemEq O (sourceOf t) (sourceOf t')` | action-specific validator/simulation |

Compilation and hosted execution are not consequences of `EC1-T114–T120`:

| ID | Status | Obligation |
| --- | --- | --- |
| `EC1-T121` | PENDING THEOREM OR VALIDATION CERTIFICATE | Pinned TypeScript compilation preserves the declared source/target observations (G5). |
| `EC1-T122` | PENDING THEOREM OR HOST EVIDENCE | Named engine and host preserve declared observations under stated assumptions (G6). |

Neither `EC1-T121` nor `EC1-T122` may select the full ordered-cause topology
for the unmodified rc.112 runtime. That observation is available only through
a separately classified topology-preserving project-owned adapter.

The omitted same-input `render_deterministic` equation is true of every Lean
function and carries no design content. `EC1-T115` is the stronger,
falsifiable no-collision obligation; the existing non-injective plain renderer
is a warning, not an inherited proof. Freeze condition 17 is closed only for
classifier overlap; `EC1-T115` and the renderer half remain open.

## 14. Required source/tooling harnesses

These are not Lean theorems and contribute no denotational trust.

| ID | Status | Required harness result |
| --- | --- | --- |
| `EC1-H01` | PENDING HARNESS | Resolve exact Effect-TS/tsgo source/provenance plus npm package/version/integrity/lockfile row/resolved path/CLI `--version`/hash; matching platform package (locally `@effect/tsgo-darwin-arm64@0.38.0`)/integrity/binary hash/complete `upstream.json`; TypeScript package/version/head/integrity; Effect peer/dependency range and resolved version; Node/Bun/OS/architecture; and tool/config/catalog/input digests. |
| `EC1-H02` | PENDING HARNESS | Assert exact `typescript@7.0.2` and git head `2bd066d87f5bafd315be9f40889d0a60b9e58e0b`, `@effect/tsgo@0.38.0`, matching platform `0.38.0`, upstream-head equality, successful `--typescript --oxlint` patch receipt, plugin name `@effect/language-service`, complete config/rules/overrides/severities, and diagnostic/action/refactor catalog digests before running. |
| `EC1-H03` | PENDING HARNESS | Run `bun run --cwd experiments/effect-core-surface typecheck` from repo root; require the script to equal `effect-tsgo diagnostics --project tsconfig.json --format json --strict --list-files`, valid normalized diagnostic JSON with exact `diagnostics`, `files`, and `summary`, zero stderr except declared Bun progress, zero unapproved errors/warnings/messages/suggestions, canonical sort by file/span/rule/action/edit, and byte-identical fresh runs. The experiment working directory is required so the pinned local TypeScript installation is discovered. |
| `EC1-H04` | PENDING HARNESS | Independently resolve the dedicated tsconfig's expected sources and require exact equality with canonicalized reported files plus `filesChecked = totalFiles`; fail on missing or extra files even with empty diagnostics. |
| `EC1-H05` | PENDING HARNESS | Require every file to report detected/supported Effect v4. The current library's 43/43, zero-message run is only a live-route witness until a reproducible receipt exists. |
| `EC1-H06` | PENDING HARNESS | Enable diagnostics, refactors, quick information, completions, and actions; join every diagnostic/action symbol and every fix-inserted import to the independent public census/`U_package`; reject nonexistent, null-masked, internal, or uncensused imports without letting the language service catalog add/remove universe rows or define symbol identity. |
| `EC1-H07` | PENDING HARNESS | Capture normalized diagnostics/suggestions/quick fixes/refactors/edit hashes; select each admitted action by stable rule/action/span/description identity; validate ordered non-overlapping edits; parse, typecheck, resolve imports, decode/compare declared IR or semantic change, rerender, rerun diagnostics, then require zero second-pass edits and byte identity. |
| `EC1-H08` | PENDING HARNESS | Mutate floating/nested Effects, promises/async, generator yield/return/try-catch, missing or leaking services, assertions, map/flatMap/Effect.fn, Layer dependencies, console/date/fetch/random/timers/process.env/abort/Node globals, duplicate/mismatched Effect packages, outdated APIs, service-key/class/Schema patterns, `A/E/R`, cleanup, race, foreign calls, and host escapes; require the intended Effect-aware or structural refusal. |
| `EC1-H09` | PENDING HARNESS | Mutate missing/extra coverage, Effect-version detection, invalid imports, overlapping edits, non-parsing fixes, target-changing style fixes, non-idempotence, and tool/config/rule/action catalog drift; require the named leg to fail. |
| `EC1-H10` | PENDING HARNESS | Render, decode, and rerender every target fixture byte-for-byte; differentially compare normalized model/target/runtime observations only at the gate actually supported, retain sample counts, and restrict stock cause observations to the quotient. |
| `EC1-H11` | PENDING HARNESS | Recursively resolve the complete pinned public module/export/member/overload universe, including both deep MultipartParser controls; require seven-disposition and mapping zero counters and cross-check, but never derive closure from, the runtime-value bank. |

## 15. Dependency ledger by slice

| Slice | Declarations | Required theorem/falsifier exit |
| --- | --- | --- |
| `EC1-S0` | packet only | grilling verdict; all statuses remain proposed/pending until ratified |
| `EC1-S1` | D0–D1 plus frozen type annotations | `T001–T009` including `T003E,T004S,T004X,T004RW`; `H11`; `F01–F03,F08,F20,F59,F60,F80,F82,F86,F87`; every required type row closes its constructor/checker/semantics/classifier/lowering/red-control edges before cutover |
| `EC1-S2` | D2–D3 | `T006–T017`; `F01–F10,F81` |
| `EC1-S3` | D10 CAS seam | `T100–T109` including `T101S,T101P`, plus `T123–T130`; `F41–F46,F74,F75,F79,F88,F91,F92` |
| `EC1-S4` | D4–D6 sequential/direct | `T020,T030–T037,T050–T059,T057T`; sequential/handler falsifiers including `F78,F89,F90` |
| `EC1-S5` | branch/cycle/call + D7 | `T026,T038–T046,T045A`; stable non-frontier CAS/block determinism boundary; `F13–F19,F31–F35,F38,F40,F69–F73,F77,F93` |
| `EC1-S6` | AER and nonconcurrent D8 | `T080–T087` for D0–D6 classifier dimensions |
| `EC1-S7` | handler/scoped bodies | `T050–T059,T057T`; handler provision/recovery/ensuring negatives including `F78,F89,F90` |
| `EC1-S8` | D9 scope/resource/cause | `T060–T069`; `F21–F25,F30,F36,F61` |
| `EC1-S9` | fibers/scheduler | `T070,T071,T072,T072J,T072I,T077,T078`; `F62,F63`; ownership/await/join/replay falsifiers |
| `EC1-S10` | interruption/race/liveness | `T073–T079`; `F26–F29` |
| `EC1-S11` | foreign atoms | `T090–T094`; frame, receipt, purity negatives |
| `EC1-S12` | complete product/triangle | all `T080–T088`; every classification falsifier including `F83` |
| `EC1-S13` | D11 target | `T110–T117`; `F47–F48,F58,F85` |
| `EC1-S14` | D12–D13 tooling/compiler/host | `T118–T122`, `H01–H11`, `F49–F57,F64–F68`; claims stamped individually; stock cause claims quotient-bounded |

## 16. Proof routes

| Obligation family | Proposed primary route | Prohibited shortcut |
| --- | --- | --- |
| Checker | structural recursion plus decidable per-clause reflection | using successful examples as completeness |
| Values | restrict/bridge the overlapping structural fragment to `Cas.Schema.El`; name empty/unsupported arms and new handle codes | duplicating an inhabited `El` meaning or silently treating an empty arm as inhabited |
| Operation families | pending condition 14: neutral protocol identity plus explicit admission bridge for Lean-modeled operations to existing `Sig.Op`; preserve `Sig.sum` with left/right laws | pretending every protocol identity already has a `Sig.Op`, or modifying/replacing `Sig` to carry classification grades or flattening Root/Word extensions |
| Graph safety | induction on `Step`; one case per terminator/administrative rule | trusting checked constructors without preservation |
| Runner relation | decision-indexed one-step iff, then induction on fuel | comparing only final return values |
| Approximation | induction on depth; symbolic request frontiers; coherent truncation | enumerating infinite answer types or calling a sweep universal |
| Algebra | graph simulation/bisimulation under explicit observation mask | syntactic rewriting across ordered resource/concurrency traces |
| Direct handlers | elaborate scoped clauses to existing `Handler` directly in a state/error/machine target that observes child outcomes and preserves state on failure; use `Handler.sum` for same-target signature families; use `Handler.through` only for an upper `Handler S (Prog T)` followed by a lower `Handler T M` | minting `HHandler`, treating `Handler.through` as generic retargeting, using inadequate `ReaderT Env (Prog CasSig)`, promoting scratch `scopeHandlerR`/`scopeHandlerW`, adopting scratch `scopeHandler`, or encoding ensuring-on-refusal with `Prog.bind` |
| Scope/resources | frame/ownership invariant plus trace-count lemmas | assuming finalizers terminate |
| Concurrency | labeled transition simulation; scheduler state/policy in `Configuration`; typed tape selection; explicit fairness only for compatible infinite decision streams in liveness | a separate schedule input, global determinism, or implicit fairness |
| Classifier | abstract interpretation soundness per transfer; SCC fixed point; certificate checks for lower facts; reindexed D4 sequence; separate D1/D2/D10 carriers; mask-selected concretization overlap under `SemEq` | conflating may and must, operation occurrence/world delta/order, demanding whole-product invariance, or narrowing unknown foreign frames |
| CAS | admit only `CheckedPProg`; recognize only `CasImage`; reuse existing `runP`, envelope, frame, canonical representation, complete `RefusalMap`, and `Auth.lean` theorem families through one simulation | total raw-`PProg` injection, treating `toPProg` as semantic projection, restating CAS semantics, weakening Level-0 security to receipt replay, or minting another serializer |
| CAS program logic | specialize semantic partial correctness to existing `wlp`; reuse `wp_iff_wlp_and_total`; prove new `EC1-T130` from shipped `wpAux_append` with nonempty-prefix and threaded-history premises | citing a shipped `wlp_append`, adding a duplicate EffHOL modality, table-only suffix rule, `WPre`, `WPost`, `wlp`, or `wp` |
| Lowering | per-constructor forward simulation, weak reflection for administrative target steps, coherent-prefix lifting; canonical renderer round trip and injectivity on normalized admitted targets | source text snapshots or tautological function determinism as semantic proof |
| Tooling | exact pins, machine-readable diagnostics, idempotence, mutation, structural decode | granting TypeScript/LSP diagnostics semantic authority |

## 17. Freeze conditions

A Pass B signature freeze remains blocked by every **OPEN** item below. The
grilling pass has frozen the evidence-backed items marked **RULED** as packet
constraints; that status does not discharge their PENDING proof rows.

1. **OPEN** — the precise `ValueTy` universe and row representation;
2. **OPEN** — whether daemon fibers are admitted in v1 or remain a checked refusal;
3. **OPEN** — the full closed alphabet/version and direct-handler table;
4. **OPEN** — the default observation mask and independent-event quotient;
5. **OPEN** — the external-request frontier representation in `FinApprox`;
6. **OPEN** — the TypeScript target constructor list;
7. **OPEN** — the selected `@effect/tsgo` source/provenance pin and code-action set;
8. **OPEN** — CAS canonical normalization behavior;
9. **OPEN** — which classifier fields must be exact in v1 versus conservative bounds;
10. **RULED** — the CAS/block-only boundary of deterministic `Denotes`/coherence and the
    absence of a full-core uniqueness theorem;
11. **RULED** — reuse of existing `Refusal.Clause`/`RefusalMap`, H-dependent write facts,
    and the refusal-word observation masks; and
12. **OPEN** — the O0 per-type proof-closure schema from `EXISTING-TYPES.md` and
    `ORGANIZATION.md`;
13. **OPEN** — the exact supported overlap and explicit insufficiency boundary between
    `ValueTy` and `Cas.Schema.El`;
14. **OPEN** — the neutral protocol operation identity and its admission bridge
    to existing `Sig.Op`/`Sig.Ans`, while retaining `Sig.sum` and Root/Word
    extension-law reuse for admitted Lean-modeled operations;
15. **RULED** — `CasAdmissible` and the rejection boundary for empty/dangling raw `PProg`;
16. **RULED** — first-error checker semantics and duplicate-free row-normalization
    premises; and
17. **PARTIALLY RULED** — classifier meaning is mask-selected concretization
    overlap rather than whole-product `SemEq` invariance; **OPEN** — renderer
    injectivity on normalized admitted targets;
18. **RULED** — the scoped-handler information contract requires child-outcome
    observation and state survival on failure, minimally witnessed for CAS by
    `ReaderT Env (ExceptT Refusal (StateT Word Id))`; `ReaderT Env (Prog CasSig)`,
    scratch `scopeHandler`/`scopeHandlerR`/`scopeHandlerW`, and `Prog.bind` stay at
    their proved boundaries and no scratch carrier is promoted;
19. **RULED** — `toPProg` as a sound `CasImage` normal-form recognizer rather than a
    semantic projection; and
20. **RULED** — Mod-E's nonempty-prefix/threaded-history premises and the stable
    non-frontier boundary of CAS/block uniqueness. The carrying theorem is the
    new PENDING `EC1-T130`, derived from shipped `wpAux_append`, not an inherited
    `wlp_append`.

Every type required by a slice has one cutover row whose edges are
`constructor`, `checker`, `semantics`, `classifier`, `lowering`, and
`redControl`. A row may cut over only when every required edge is discharged by
its named evidence. A full Effect Core cutover is blocked while any required
row has an open edge; closing a neighboring type or running a finite probe
cannot satisfy it.

Until every **OPEN** portion is ruled, the identifiers above are organizational
targets only. The ruled constraints bind subsequent packet work, but every
proof remains PENDING.
