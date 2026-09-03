# The algebraic denotation of a checked flow

Research note, 2026-09-03. Read-only survey of `/Users/pooks/Dev/lean4-effects`
(Effects v0.5.0) and `/Users/pooks/Dev/lean4-effect4` at `codex/effect4-cutover`.
Question: what does a `CheckedFlow` denote in the algebra, and which of today's
executable checks become theorems once that is written down.

Nothing in either repo currently defines a flow denotation. `grep -rn denote`
finds only `Alphabet.toFamily`'s type-code argument (`Effects/Family.lean:72`).
`docs/TRACE-DAG.md:40` records the `semantics` edge as `required-open` with "no
simulation theorem in this phase". So everything below is new work.

---

## 0. Three corrections to the premise

**(a) The traced service emits three of nine row kinds.** `Family.Service.traced`
(`Effects/Trace.lean:171-182`) appends exactly `op` and `answer`;
`Service.tracedExcept` (`Effects/Trace.lean:264-270`) adds `failed`. Every other
constructor of `Trace.Event` — `decide`, `enter`, `leave`, `finalizer`, `done`,
`frontier` — has no producer in the algebra at all. In Effect4 they are emitted
by the runners: `decide` at `Effect4/Semantics/Runs.lean:139` and
`Effect4/Flow/Region.lean:127`; `enter`/`leave`/`finalizer` at
`Effect4/Flow/Region.lean:68,69,133`; `done` at `Runs.lean:125`; `frontier` at
`Runs.lean:135,147`. So "the runner's log is literally
`interpret (service.traced …) (denote …)` up to `done`/`frontier`" is false: the
`decide` rows fail too, and they are exactly the rows that separate `m1` from
`m2` (`Effects/Trace.lean:112-119`). The oracle at `harness/trace/Generate.lean:403`
compares under `m2`. The denotation must therefore land in a **signature sum**,
and the interpreting handler must be a `Handler.sum` whose second summand logs
`decide`.

**(b) The denotation cannot be tape-free.** `Program` is inductive, so every
root-to-leaf path is finite — `docs/CLAIM-BOUNDARY.md` states this as "No
finiteness: `Program` is well-founded on every selected branch" (`E4-ALG-CE-008`).
An admitted flow may cycle indefinitely (`chosenLoop`,
`Effect4Test/Flow/RunnerContract.lean:140`), so no total function
`CheckedFlow → Program` exists. The tape is not a convenience, it is the
termination measure. "Tape or a Decisions family" are the same object curried:
`fun tape => denote flow tape input` **is** the relational denotation DB-03 asks
for (`docs/DESIGN-BASIS.md:127-152`); a fixed tape picks one member.

**(c) The runner and the reified rc.112 Scope already disagree.** See §2.3. This
is the concrete cost of checking emitters against each other instead of against
the algebra: the divergence is real, is invisible to the corpus, and no golden
can see it.

---

## 1. The denotation and `run = interpret ∘ denote`

### 1.1 The signature

`FlowService` (`Runs.lean:52`) is untyped: `handle : alphabet.Op → Val → M Val`.
That is precisely a `Family.Service` for the constant denotation, so the
embedding the algebra already owns applies:

```lean
def FlowAlphabet.toAlphabet (a : FlowAlphabet Ty) : Alphabet Ty :=      -- missing, trivial
  ⟨a.Op, a.requestTy, a.answerTy⟩

abbrev Flow.Fam (a : FlowAlphabet Ty) : Family.{uOp,0,0} :=
  a.toAlphabet.toFamily (fun _ => Effects.Trace.Val)                     -- Effects/Family.lean:71
abbrev Flow.Sig (a : FlowAlphabet Ty) : Signature := (Flow.Fam a).toSignature

def FlowService.toService (s : FlowService a M) : (Flow.Fam a).Service M := s.handle   -- rfl
```

`Family.toSignature` (`Effects/Family.lean:30`) gives `Op = Σ op, Val` and
`Answer _ = Val`; `Service.toHandler` (`Effects/Family.lean:42`) turns the
service into the handler. The `pure` flag of `FlowService` is a *tracing*
policy, not semantics, and stays out of the signature.

The decision summand announces a decision that the tape has already made:

```lean
def Flow.DecSig : Signature.{0,0} := ⟨DecisionId × Bool, fun _ => Unit⟩
abbrev Flow.FullSig (a : FlowAlphabet Ty) : Signature := Flow.Sig a ⊕ₛ Flow.DecSig
```

Answer `Unit`, not `Bool`. The branch is already fixed by the tape; the
operation carries the observation. The alternative — making the denotation
return `(RunResult × Log)` and appending `decide` rows as data — fails, because
the traced service writes its rows into a `StateT` log and a separately-returned
list cannot be interleaved with it. Using `Unit` as the answer keeps both
summands writing the same `StateT Effect4.Trace.Log`, which is what makes
interleaving definitional.

### 1.2 The denotation

```lean
def Flow.denote {a : FlowAlphabet Ty} (flow : CheckedFlow a) (tape : Tape) (input : Val) :
    Program (Flow.FullSig a) (RunResult × Tape)
```

with an inner recursion `go : BlockId → Env → Tape → Program …` that mirrors
`plan` (`Runs.lean:88`) case for case: `ret` → `.pure (.done v, tape)`;
`jump` → `go target env' tape`; `perform op req target env'` →
`.vis (.inl ⟨op, req⟩) (fun answer => go target (env' ++ [answer]) tape)`;
`choose` with `Tape.read` (`Effect4/Flow/Decision.lean:36`) answering
`.answered b rest` → `.vis (.inr (site, b)) (fun _ => go (if b then l else r) env' rest)`;
`.exhausted`/`.mismatch`/`.stuck` → `.pure` of the matching `RunResult`.

**Termination without fuel.** The measure is lexicographic
`(tape.length, (raw.reachSet block).length)`.

* At a `choose`, `Tape.read_answered_length` (`Decision.lean:60`) gives
  `rest.length + 1 = tape.length`.
* At a `jump` or a `perform`, the edge is an `EdgeNoChoose`
  (`Effects/Flow/Raw.lean:170`, since `isChoose` is false for both). Then
  `reachSet target ⊆ reachSet block` by `mem_reachSet` (`Raw.lean:497`) and
  transitivity of `ReachableNoChoose`, while `block ∈ reachSet block` and
  `block ∉ reachSet target` — the latter is exactly `wf.cycles`
  (`CyclesWF`, `Raw.lean:183`) applied to the edge. Both lists are `Nodup`
  (`nodup_saturate`, `Raw.lean:420`), so `length_le_of_nodup_subset` (`Raw.lean:477`)
  gives the strict decrease.

The missing lemma is one statement:

```lean
theorem reachSet_length_lt_of_edge {raw : RawFlow Ty} (cycles : CyclesWF raw)
    {source target : BlockId} (edge : EdgeNoChoose raw source target) :
    (raw.reachSet target).length < (raw.reachSet source).length
```

So `denote` needs **no fuel at all**, and it needs `CheckedFlow` rather than
`RawFlow` for exactly one reason: `wf.cycles`. That is the sharpest answer to
"what does admission buy" available in this lane.

### 1.3 The interpreting handler

```lean
def Flow.decisionHandler [Monad M] : Handler Flow.DecSig (RunM M) :=
  ⟨fun (site, branch) => emit (.decide site.value branch)⟩          -- Runs.lean:63

def Flow.traceHandler [Monad M] (service : FlowService a M) (nameOf : a.Op → String) :
    Handler (Flow.FullSig a) (RunM M) :=
  (tracedFlowService service nameOf).toHandler.sum Flow.decisionHandler
```

`tracedFlowService` cannot be `Service.traced` verbatim: the runner suppresses
`op`/`answer` rows when `service.pure op` (`Runs.lean:130`), and
`Service.traced` logs unconditionally. Either generalise `Service.traced` with a
`keep : F.Name → Bool` guard in lean4-effects, or write the guarded service in
Effect4 and reuse the *general* projection lemma `interpret_projects_fst`
(`Effects/Trace.lean:196`) rather than the `traced_projects` instance
(`Trace.lean:217`). The general form takes an arbitrary
`traced : Handler S (StateT σ M)` with a `Handler.Projects` side condition
(`Trace.lean:188`), so it covers the guarded service, the decision handler and
the sum. This is the single most reusable existing lemma for the whole
programme, and it is currently used only once.

### 1.4 The theorem, split in two

Answering the question directly: **no, not one induction.** `loop`
(`Runs.lean:143`) recurses on fuel; `denote` recurses on the measure. Relating
them in one step means WF induction with a fuel case split. Split instead:

```lean
-- T1: one induction on fuel. Define `denoteFuel : Nat → BlockId → Env → Tape → Program …`
-- structurally, with `0 ↦ .vis (.inr frontier) …` mirroring `loop 0`.
theorem Flow.runTape_eq_interpret [Monad M] [LawfulMonad M]
    (fuel : Nat) (flow : CheckedFlow a) (service : FlowService a M)
    (nameOf : a.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (Flow.runTape fuel flow service nameOf tape input).run log =
      (interpret (Flow.traceHandler service nameOf)
        (Flow.denoteFuel fuel flow.erase flow.erase.entry [input] tape)).run log

-- T2: the measure theorem. Needs `reachSet_length_lt_of_edge` and `wf.cycles`.
theorem Flow.denoteFuel_eq_denote (flow : CheckedFlow a) (tape : Tape) (input : Val)
    {fuel : Nat} (enough : Flow.fuelFor flow.erase tape ≤ fuel) :
    Flow.denoteFuel fuel flow.erase flow.erase.entry [input] tape =
      Flow.denote flow tape input
```

T1 is a plain induction on `fuel`, generalised over `block`, `env`, `tape`,
`log`; the `perform` case is `interpret_vis` (`Effects/Algebra/Laws.lean:44`) plus
`Handler.sum_handle_inl` (`Effects/Algebra/Sum.lean:9`). It needs one auxiliary
lemma that does not exist and that both emitters need:

```lean
theorem interpret_log_append …:                       -- "the log is a writer"
    (interpret h program).run log = (fun r => (r.1, log ++ r.2)) <$> (interpret h program).run []
```

Without it, `emit`'s `log ++ [event]` (`Runs.lean:64`) and `traced`'s
`log ++ [op, answer]` (`Trace.lean:181`) generate `List.append_assoc` noise on
every case.

T2 is the payoff nobody has claimed yet: **`fuelFor` (`Runs.lean:160`) is asserted,
not proved.** Its justification lives in a doc comment (`Runs.lean:157-159`) and
is checked by one `rfl` example on one program (`RunnerContract.lean:175`). There
is no theorem that `runDefault` never returns `.frontier (.fuel _)`.
`run_checked_not_stuck` (`Runs.lean:365`) rules out `stuck`; `loop_fuel_mono`
(`Runs.lean:384`) is conditional on *not* having exhausted. T2 supplies the
missing half and discharges DB-04's demand (`docs/DESIGN-BASIS.md:154`) that fuel
be an approximation with a coherence law rather than a denotation.

Corollary once both land:

```lean
theorem Flow.runDefault_no_fuel_frontier … :
    (((Flow.runDefault flow service nameOf tape input).run log).1).exhausted = false
```

### 1.5 Is the internal oracle then a corollary?

Almost, and the residue is instructive. Three gaps sit between T1 and
`flowLog = goldenLog`:

1. **`Script.toFlow` inserts operations the script does not have.** Literals
   (`ScriptFlow.lean:132-135`) and atoms (`ScriptFlow.lean:148-153`) become
   `perform`s over table rows of kind `.lit`/`.atom`, which `tableService.pure`
   marks pure (`ScriptFlow.lean:80-83`). So the flow's program is strictly larger
   than the script's. The bridging lemma is not `interpret_map`
   (`Effects/Morphism.lean:47`) — nothing is renamed, operations are *erased* —
   but a one-line missing lemma:

   ```lean
   theorem interpret_vis_of_pure [Monad M] [LawfulMonad M] (h : Handler S M)
       (op : S.Op) (v : S.Answer op) (eq : h.handle op = pure v) (next : _) :
       interpret h (.vis op next) = interpret h (next v) := by
     rw [interpret_vis, eq, pure_bind]
   ```

2. **A `Script → Program` denotation and its embedding theorem.**
   `denoteScript : ServiceRow → Script → Val → Program (Flow.Sig …) Val`, then
   `Script.toFlow_denote : Flow.denote (admit (toFlow rows atoms script)) [] input`
   equals `denoteScript` after erasing the pure operations. Induction on
   `script.steps` carrying the `Build` invariant (`ScriptFlow.lean:92-99`:
   `params = scope.map (·.2)`, `next = blocks.length`, table monotone). This is
   the fiddly part, ~250 lines.

3. **`effect_program` emits the program and the script independently**
   (`Effect4/Meta/Derive.lean:227-266`). Nothing relates `incr` to `incr.script`;
   the elaborator builds both from the same syntax and no theorem records it.
   This is a metaprogram-correctness claim and is not provable in Lean. The fix
   is cheap and should be done regardless: have `effect_program` also emit
   `example : denoteScript rows name.script = name := by rfl`. Then the oracle is
   a corollary *per program*, with an elaborator-emitted receipt, rather than a
   universally quantified theorem.

Plus one per-family side condition, dischargeable by `cases name`:
`cellFamily (spelling n) (encodeParam n p) = encodeAnswer n <$> cellLive n p`
(`Generate.lean:89,142`).

---

## 2. Regions

### 2.1 Is the region runner an interpretation of a scope signature?

Partly. Three obstructions, in increasing severity.

**(i) `enter`/`acquire`/`leave` are terminators, not alphabet operations**
(`Effects/Flow/Region.lean:30-41`). They become a third summand:

```lean
inductive ScopeName | enter | acquire | leave
def Flow.ScopeFam (a : FlowAlphabet Ty) : Family :=
  { Name := ScopeName
    Param := fun | .enter => RegionId
                 | .acquire => a.Op × Val × a.Op          -- acquire, request, release
                 | .leave => RegionId × Val
    Answer := fun | .enter => Unit
                  | .acquire => Except Val Val
                  | .leave => Except Val Val }
```

**(ii) `leave` performs alphabet operations.** Closing a frame runs the
registered releases, which are alphabet operations. So the scope handler cannot
be a `Handler ScopeSig M` for arbitrary `M`; it is an *upper* handler over
`Program (Flow.Sig a)`, carrying the frame stack as state:

```lean
abbrev Flow.Stack (a : FlowAlphabet Ty) := List (Frame a)

def Flow.scopeHandler {a : FlowAlphabet Ty} (nameOf : a.Op → String) :
    Handler (Flow.ScopeFam a).toSignature
      (StateT (Flow.Stack a) (Program (Flow.Sig a ⊕ₛ Flow.DecSig)))
```

and the collapse to the run monad is *not* `Handler.through`
(`Effects/Algebra/Handler/Composition.lean:10`), whose upper handler must land in
`Program T` with no state. It is `Handler.mapHom` along `MonadHom.stateT`:

```lean
Flow.scopeHandler nameOf
  |>.mapHom (MonadHom.stateT (interpretHom (Flow.traceHandler service nameOf)) (Flow.Stack a))
```

with `interpret_mapHom` (`Effects/Transport.lean:27`) as the law and
`MonadHom.stateT` (`Effects/Transport.lean:52`) supplying the lift. Its docstring
advertises it as "what `Layer.provide` with a `Ref` needs"; the region runner is
its second, and better, customer. `through_eq_mapHom` (`Transport.lean:46`)
records that `through` is the stateless special case.

**(iii) Failure is an abort, and `interpret` is a fold.** `fail`
(`Region.lean:87-92`) unwinds the whole stack and ends the run. `interpret`
cannot catch. So the aborting reading is unavailable and the denotation must be
`Program … (Except Val Val)`-shaped, with the case split performed by the
denotation function, not by a handler. `Service.tracedExcept` and
`interpret_tracedExcept_fst` (`Trace.lean:324`) do not help here: they forget the
log, they do not let a handler observe a failure.

### 2.2 The two lemmas

With `Frame.toScope (frame) : Scope Nat (a.Op × Val) β ε δ ι α` built as
`⟨.sequential, .openMap (frame.releases.reverse.zipIdx)⟩` — `releases` is stored
latest-first (`Region.lean:145` conses) while `Scope.finalizers` is registration
order (`Scope.lean:250`):

```lean
/-- L1 (order). A frame closes in the reified scope's close order, latest-first,
each release preceded by one `finalizer` row carrying the closing exit. -/
theorem Flow.closeFrame_log [Monad M] [LawfulMonad M]
    (service : RegionService a M) (nameOf : a.Op → String)
    (frame : Frame a) (exit : Outcome Val) (log : Effect4.Trace.Log) :
    ((Flow.closeFrame service nameOf frame exit).run log).snd =
      log ++ [.leave frame.region.value exit] ++
        (Scope.closeOrder frame.toScope).flatMap fun (op, v) =>
          .finalizer frame.region.value exit :: opRows service nameOf op v

/-- L2 (first failure wins). The error reported is the first error in close order. -/
theorem Flow.closeFrame_first_failure … :
    ((Flow.closeFrame service nameOf frame exit).run log).fst =
      (Scope.closeOrder frame.toScope).findSome? fun (op, v) => (resultOf service op v).error?
```

L1 reduces to `closeOrder_eq` (`Scope.lean:908`) and `closeExits_reverse`
(`Scope.lean:928`) after `List.reverse_reverse`; `closeOrder_last_first`
(`Scope.lean:912`) is the shape lemma for the head. Both are ~80 lines of fold
induction over `frame.releases`.

### 2.3 A divergence the corpus cannot see

`closeFrame` keeps the **first** release failure (`Region.lean:76`:
`if failure.isNone then failure := some error`). `Scope.closeResult`
(`Scope.lean:796-805`) **merges every** failing finalizer: two or more exits go to
`Exit.asVoidAll`, and `closeResult_reasons` (`Scope.lean:994`) together with
`asVoidAll_reasons` (`Effect4/Semantics/Exit.lean:188`) and
`asVoidAll_keeps_duplicates` (`Exit.lean:234`) says every reason of every
finalizer reaches the closing cause, in order. So for a frame with two failing
releases the region runner reports one error and the reified rc.112 scope reports
a merged cause. That error reaches the trace as `done (.failure e)`
(`Region.lean:91`), which is an `m1` row.

It is unexercised: the only fixture with a failing release,
`regionReleaseFails` (`Generate.lean:308`), has a single failing release and is
excluded from host goldens because `Effect.acquireRelease` types a release
`Effect<unknown, never, R>` (`Generate.lean:304-307`, E4-TARGET-CE-012). A
two-failing-release fixture cannot be lowered, so no golden and no host receipt
can ever catch this. Only L2 stated against `Scope.closeResult` can.

`Scope.closeExits` also takes a *pure* `run : φ → Exit → Exit Unit`
(`Scope.lean:790`), while the runner's releases run in `M`. Exact agreement holds
only at `M = Id`, or after a monadic generalisation `closeExitsM`. That is a
missing definition in `Effect4/Runtime/Scope.lean`, which carries census tags and
so needs a coverage row.

---

## 3. The lowerings

**Nothing statable today.** `lowerDispatch` (`Effect4/Target/TypeScript/FlowLower.lean:198`)
and `lowerStructured` (`StructuredLower.lean:84`) produce `TypeScript.Stmt`, a
syntax type with no evaluator in either repo. "Denotes the same `Program`" has no
subject.

**Do not transform the denotation.** `Program` is a tree with no loop
constructor. Structuring is a graph operation; on the tree it is vacuous, because
`⟦dispatch⟧ = ⟦structured⟧` would have to be proved by first denoting both, which
is the thing being asked for. The recommendation is neither of the operator's two
options as stated, but a third:

1. Introduce a **`Skeleton` IR** in Effect4: labelled blocks, `while(true)`,
   `switch`, `break`/`continue` to a label, assignment, `perform`, `return`. This
   is the abstract syntax the two lowerings already share; today `lowerBlockWith`
   (`FlowLower.lean:147`) emits `Stmt` directly and `Structure.Shapes`
   (`StructuredLower.lean:49`) is instantiated at `Stmt`.
2. Give `Skeleton` a denotation into the same `Program (Flow.FullSig a)` — same
   measure argument, since the loops are the flow's loops.
3. Factor both lowerings as `render ∘ skeleton…`, where `render : Skeleton → List Stmt`
   is a pure printer with no semantics.

Then:

* **Provable, Lean-side.** `T3 : ⟦skeletonDispatch flow⟧ = Flow.denote flow tape input`
  and `T4 : ⟦skeletonStructured flow⟧ = ⟦skeletonDispatch flow⟧` for reducible
  graphs. T4 closes `structured-agreement`, currently `required-open`
  (`docs/TRACE-DAG.md:46`: "the Lean theorem that they agree on every flow is
  owed"). Note T4 needs **no** TypeScript fidelity whatsoever: it is a relative
  claim between two compilations of one IR.
* **Evidence, permanently.** `render`'s faithfulness to Effect v4 generator
  semantics — `yield*`, generator resumption, `Effect.scoped` finalizer order.
  A Lean-side TypeScript interpreter would only relocate this: it would be a
  *second* trusted artifact whose agreement with the host is exactly today's
  receipt. Its only real use is T4, and T4 does not need it to be faithful.

The straight-line `Script.lower` (`EffectV4.lean:285`) is the same story one
level down and gets its Lean-side half for free from §1.5.

---

## 4. Ranking, sizes, reuse

| # | Work | Lines | Reuses | Missing | Buys |
| --- | --- | --- | --- | --- | --- |
| 1 | **T1** `runTape = interpret ∘ denoteFuel` | ~250 | `interpret_vis`, `interpret_bind`, `Handler.sum_handle_inl/inr`, `Service.toHandler`, `Alphabet.toFamily`, `interpret_projects_fst` | `FlowAlphabet.toAlphabet`, `interpret_log_append`, guarded `Service.traced` | the `m2` oracle becomes a theorem schema; half of `semantics` |
| 2 | **T2** fuel-free `denote`, `fuelFor` sufficiency | ~250 | `mem_reachSet`, `nodup_saturate`, `length_le_of_nodup_subset`, `cyclesChoose_iff`, `Tape.read_answered_length`, `plan_checked` | `reachSet_length_lt_of_edge` | `runDefault` never hits a fuel frontier; discharges DB-04 |
| 3 | **L1/L2** region close order and first failure | ~200 | `closeOrder_eq`, `closeOrder_last_first`, `closeExits_reverse`, `closeResult_single/many/reasons`, `asVoidAll_reasons` | `Frame.toScope`, `Scope.closeExitsM` | pins two host-only facts; the §2.3 divergence is already found |
| 4 | **T5** `denoteScript` + `Script.toFlow` embedding | ~250 | `interpret_bind`, `Program.bind_assoc` | `interpret_vis_of_pure`, `Build` invariant, elaborator-emitted `rfl` receipt | oracle as a per-program corollary (straight-line only) |
| 5 | **Region denotation** via `mapHom`/`stateT` | ~350 | `interpret_mapHom`, `MonadHom.stateT`, `interpretHom`, `through_eq_mapHom` | scope signature, `Except`-shaped denotation | region runner = interpretation |
| 6 | **T3/T4** `Skeleton` IR, dispatch ≡ structured | ~700+ | T1, T2 | `Skeleton`, `render`, reducibility transfer across repos | closes `structured-agreement` |

Rows 1–3 are where value per line is highest. Row 3 has already paid for itself
before being written. Row 6 is the only item that touches lean4-typescript and
should be scheduled last, but its *statement* is cheap to fix now: factoring the
two lowerings through a `Skeleton` costs little while the code is fresh and is
what makes the theorem sayable at all.

**Not provable, ever, in Lean:** that `effect_program` emits a matching
program/script pair (metaprogram correctness — replace with an emitted `rfl`);
that `render` is faithful to Effect v4 (host receipt); anything about frames,
scheduling or primitives (`docs/TRACE-DAG.md:79-86`).
