# A proof-safe Lean 4 API for characterized components of the Effect runtime

Research report, 2026-09-04. Read-only survey plus a type design. No library code, contract,
pin, ruling or generated fact was changed by this work; the only file written is this one.

Every claim about existing code carries a `file:line` citation that was opened at the line.
Line numbers are as of the working tree at the time of reading (lean4-effect4 `main` @ `e1cad67`
plus an untracked `workshop/OCaml5/server/`; effect-nats-verified as checked out at
`/Users/pooks/Dev/effect-nats-verified`).

The question is not "can this be modeled in Lean". It plainly can; there are already two
kernel-checked models of Effect's `Queue` fragment on this machine. The question is which
*types* make the second, fifth and twentieth component cheap, and the answer is decided almost
entirely by four choices: where `Bool` stops and `Prop` starts, whether proofs are ever fields
of a runtime record, whether the transition function is total-or-disabled, and whether the
registry is monomorphic data joined to theorem *names* rather than a dependent container of
theorem *values*.

---

## 1. Lessons from the existing code

### 1.1 The transition function should be total-or-disabled, and the label should carry the answer

Both existing state machines are `S → L → Option S`, never a relation and never a partial
function:

```lean
def rtStep (s : RtState) : RtLabel → Option RtState
  | .op o e => rtOp s o e
  ...
```
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/Runtime.lean:296-305`).

The reason is stated in that module's own header: "`rtStep` is total-or-disabled, like stage A's
`apply`, so runtime traces are kernel-checkable by `decide`"
(`Runtime.lean:21-22`). The relation is then *derived* from the function, not the other way
round:

```lean
def RtNext (s : RtState) (l : RtLabel) (s' : RtState) : Prop := rtStep s l = some s'
```
(`Runtime.lean:307`).

The scheduler in this repository does exactly the same thing in the other direction, and says so:

```lean
/-- The one-step relation is exactly the graph of `stepEval`. -/
def Step (boundary : InterruptBoundary τ) (before : Machine τ)
    (decision : SchedulerDecision τ) (result : StepResult τ) : Prop :=
  result = stepEval boundary before decision
```
(`/Users/pooks/Dev/lean4-effect4/Effect4/Concurrency/Scheduler.lean:612-615`), with
`step_iff : … ↔ result = stepEval …` proved by `Iff.rfl` (`Scheduler.lean:617-620`).

The second half of the idiom is the one the starting sketch misses. The *answer* an operation
produces is carried **in the label**, not returned as a second component of the step's result:

```lean
inductive RtLabel where
  | op (o : Op) (expect : Expect)
  ...
```
(`Runtime.lean:105-125`), and the step refuses when the actual answer differs from the label's
expectation:

```lean
match step s.core o, e with
| .error err, .error err' => if err = err' then some s else none
| .ok (core', r), .ok r' => if r ≠ r' then none else …
```
(`Runtime.lean:140-144`). The sequential trace runner does the same
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/Traces.lean:71-77`).

That single decision is why the whole layer above works. Because the label fixes the answer, the
run function stays `Option S`, every trace is self-describing first-order data, and the entire
test surface is a `Bool`. A `step : S → L → Option (S × O)` shape, as in the starting sketch,
forces every downstream lemma to carry a pair and forces the enumerator to compare outputs
structurally; the tree already found the cheaper encoding.

Where an observation genuinely depends on state, it is computed as a *delta between the before
and after states*, not returned:

```lean
def appended (before after : SubState) (id : SubId) : List Observed :=
  (observedOf after id).drop (observedOf before id).length
```
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/SubPlacements.lean:42-43`), used by
`afterLabel` (`SubPlacements.lean:59-62`) to build the per-consumer chunk history. The only place
a step's output is materialized at all is `chunkOf`
(`Runtime.lean:245-249`), and it is folded straight back into the state field `chunks`
(`Runtime.lean:263-266`).

### 1.2 Invariants are extrinsic, and the ruling says why

```
Invariants are extrinsic — plain data plus propositions, proven over reachable states —
because publish/prune/rollup create no invalid intermediate states worth typing away,
and intrinsic sortedness would tax every operation.
```
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/Invariants.lean:6-9`).

The carrier is a plain `structure … deriving DecidableEq, Repr`
(`Runtime.lean:55-76`), and the invariant is a *separate* `structure … : Prop` with **named**
clauses:

```lean
structure QueueInv (cap : Nat) (q : EffectQueue) : Prop where
  takerLive : q.taker = true → q.status ≠ .shutDown
  doneEmpty : ∀ e, q.status = .done e → q.buffer = []
  closingNonempty : ∀ e, q.status = .closing e → q.buffer ≠ []
  shutDownClear : q.status = .shutDown → q.buffer = [] ∧ q.taker = false
  capacity : q.buffer.length ≤ cap
```
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/RtInvariants.lean:25-36`), and the
eleven-clause stage-A form at
`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/SubInvariants.lean:30-43`.

The counter-case is in this repository and was written up as a defect. Finding 24 of the
Lean-core survey observes that `Representation.FieldAdmissible`
(`Effect4/Schema/Check.lean:710`) is "a 60-line `match` whose arms are anonymous conjunctions,
21 `∧` in the definition", that nothing names which clause failed, and that the fix is "named
`structure … : Prop` records (one per shape)", citing `Effects.FlowWF` as the good pattern
already in the tree
(`/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-03-survey-lean-core.md:832-855`).

A named-clause invariant is not cosmetic. It is what makes clause reuse work: `SubCore.lean:279`
rebuilds one invariant from another by projecting five clauses by name
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/SubCore.lean:279`), and every
preservation proof cites `hqi.closingNonempty` rather than `.2.2.1`
(`RtReachable.lean:613`, `SimProof.lean:1458`).

### 1.3 Reachability needs one strengthened induction principle, exported once

The naive shape is a two-constructor inductive:

```lean
inductive ReachableRt : RtState → Prop
  | init : ReachableRt initialRt
  | step {s s' l} : ReachableRt s → RtNext s l s' → ReachableRt s'
```
(`Runtime.lean:309-311`), matching `Reachable` for the sequential core
(`Invariants.lean:31-34`).

Its bare recursor is not usable, because in the step case it hands you `P s` and nothing else,
so every downstream fact re-proves the invariant. The fix is a hand-written strengthened
principle that bundles reachability and the invariant into the step hypothesis:

```lean
theorem reachableSub_all {P : SubState → Prop} (hinit : P initialSub)
    (hstep : ∀ {s s' : SubState} {l : Label}, ReachableSub s → StateInv s → P s →
      apply s l = some s' → P s')
    {s : SubState} (h : ReachableSub s) : P s
```
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/SubReachable.lean:220-226`), whose
docstring says it is "the one induction principle every further reachable-state fact goes
through", and the package rule makes that binding: "Per-stream invariants go through
`reachable_all`. … do not write a second induction over `Reachable`"
(`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:51`).

That single rule is the difference between one bootstrap induction plus N cheap corollaries and
N expensive inductions. `stateInv_reachable` (`SubReachable.lean:207-210`) is the bootstrap;
`pending_le_capacity` (`SubReachable.lean:213-215`) is a three-line corollary of it.

### 1.4 Tests are `Bool` data, theorems are `= true`, and the runner is parametric in the model

The trace layer is data with a `Bool` runner:

```lean
structure SubTrace where
  name : String
  mirrors : List String
  steps : List SubTraceStep
  finalObserved : List (SubId × List Observed)
  deriving Repr

def runSubTraceWith (applyFn : SubState → Label → Option SubState) (t : SubTrace) : Bool
def runSubTrace : SubTrace → Bool := runSubTraceWith apply
```
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/SubTraces.lean:33-39`, `:74-79`),
and every trace theorem is `runSubTrace t = true := by decide`
(`SubTraces.lean:170`, `:202`, `:221`, `:240`, `:263`, `:288`, `:303`, `:324`, `:354`, and the
aggregate `all_sub_traces` at `:360`).

This is the reason the runner takes `applyFn` as a parameter rather than closing over the model:
the *same* trace data can be executed against a mutant. That is what makes the mutant layer free.

The package rule is "Traces are data. A new trace is a `Trace` value, its `runTrace … = true`
theorem, and an entry in `allTraces`"
(`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:58`).

### 1.5 Mutants must be killed by traces, and must also survive some traces

```lean
def pullStepW1 (sub : Subscriber) : Option Subscriber := …   -- one-element pull
def deliverOneW2 (stream) (m) (sub) : Subscriber := …        -- lastEnqueued advanced on overflow
```
(`SubTraces.lean:83-96`, `:99-116`), executed as
`runSubTraceW1 := runSubTraceWith (applyWith deliverOne pullStepW1)` (`:97`) and
`runSubTraceW2 := runSubTraceWith (applyWith deliverOneW2 pullStep)` (`:118`).

The kill theorems and, crucially, the *anti-vacuity* companions:

```lean
theorem w1_fails_drain : runSubTraceW1 saDrain = false := by decide      -- :365
theorem w2_fails_lag   : runSubTraceW2 saLag   = false := by decide      -- :368
theorem w1_passes_replay : runSubTraceW1 saReplay = true := by decide    -- :372
theorem w2_passes_drain  : runSubTraceW2 saDrain  = true := by decide    -- :373
```

Without the last two, a suite that refuses everything would "kill" every mutant. The same
discipline is recorded as an explicit packet obligation: "Every frozen theorem with hypotheses
gets a kernel-checked instance where the hypotheses hold and the conclusion is not trivial, and
every `decide`d trace theorem gets a guard against an empty list"
(`/Users/pooks/Dev/effect-nats-verified/docs/stage-b1-proof-map.md:262-263`).

The older Foldlab model gives the mutant a *type*, and parameterizes it by the hole rather than
by the whole machine:

```lean
structure Mutant (F : Type) where
  id : String
  attacks : String
  represents : String
  mutant : F
```
(`/Users/pooks/Dev/lean4-effect4/vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/Effects/Conformance/Mutant.lean:14-18`),
with the quarantine rule in the same header: "Mutants are never proof-bearing and never imported
by the model" (`Mutant.lean:4-7`), and thirty instance files under `Effects/Mutants/`, for
example `MRK002_EmitUnverified.lean:25-29`.

### 1.6 The finding that decides the whole shape: frame laws do not discriminate mutants

`ApplyLaws.lean` names what the stage-A model actually assumes of the two parametric holes
(`DeliverLaws` at
`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/ApplyLaws.lean:41-51`, `PullLaws` at
`:55-63`), proves the real steps satisfy them (`:68`, `:99`), and then proves the two
deliberately wrong models satisfy them too:

```lean
theorem w1_law_abiding_but_trace_excluded :
    PullLaws pullStepW1 ∧
      (historiesWith (applyWith deliverOne pullStepW1) saDrain 0).any
        (fun h => !(historiesWith apply saDrain 0).contains h) = true
```
(`ApplyLaws.lean:171-175`, and `w2_law_abiding_but_trace_excluded` at `:179-183`).

The module says what this means in as many words: "The frame laws do *not* discriminate the
slice document's two deliberately wrong models … Frame laws alone do not certify a replacement"
(`ApplyLaws.lean:20-26`), and: "The one law-shaped fact that *would* exclude W1 is queue fact
Q1's drain equation, which pins `pull` down to its definition … and so is not a law but the
definition; certifying a replacement `pull` is a simulation obligation (L7b), not a law
obligation" (`ApplyLaws.lean:23-25`).

Consequences for the API, which are large:

* A component's *laws* are necessary conditions, not a certificate. The certificate is the
  trace acceptance set, or a simulation.
* The `Law` slot in the sketch must therefore never be presented as the thing that establishes a
  grade. Its job is to make an *alternative implementation* inherit theorems, which
  `op_visible_frame_of_laws` demonstrates (`ApplyLaws.lean:247-253`).
* The idiom for checking a re-derived theorem is literally the frozen one is worth stealing:
  `theorem op_visible_frame_is_instance : @op_visible_frame = @op_visible_frame_of_laws := rfl`
  (`ApplyLaws.lean:257`), with the comment "'verbatim' is checked, not asserted" (`:255-256`).

### 1.7 Frozen statements are `#check` ascriptions cross-checked by a script

```lean
/-! The exact proposition each witness proves, frozen by ascription. A drift in
any statement is a `type mismatch` at the offending line. -/

#check (@Effect4.masked_interrupt_defers :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before after : Machine τ} … )
```
(`/Users/pooks/Dev/lean4-effect4/Effect4Test/Audit/RuntimeCoverage.lean:47-61`; the section runs
to `:2541`). The header records the guard that makes it non-deletable:
"`scripts/check-effect-runtime-census.sh` cross-checks that the snapshot names and the emitted
witness rows are the same list, in the same order, so the ascriptions cannot be deleted without
failing the gate" (`RuntimeCoverage.lean:25-30`).

The other half of the freeze is prose plus a revision log with the *refutations kept*:
`docs/signature-snapshot.md:57-82` records r4.1 and r4.2, each a post-freeze correction, each
with a kernel-checked refutation of the earlier form under `scripts/`
(`/Users/pooks/Dev/effect-nats-verified/scripts/A4CompleteR4Refutation.lean:22-29` restates the
old statement verbatim as `A4CompleteR4` and then refutes it). That pattern, restating the dead
statement so its falsity is a theorem, is the only durable way to keep a freeze honest.

### 1.8 The census-row to witness join is a flat data row plus a metaprogram, not a dependent list

```lean
private structure Row where
  id : String
  kind : String
  disposition : String
  coverage : String
  witnesses : List (Name × String)
```
(`RuntimeCoverage.lean:2547-2557`), with `censusRows : List Row` at `:2575` and vocabulary lists
at `:2562-2573`. The older Foldlab model does the same with a better-typed disposition:

```lean
inductive Disposition where
  | schema (family : String) (milestone : String)
  | carrier (milestone : String)
  | tsSide (milestone : String)
  | bridge (milestone : String)
  | review
  | deferred (target : String)
  deriving Repr

structure Obligation where
  id : String
  statement : String
  disposition : Disposition
  deriving Repr
```
(`vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/Effects/Conformance/Obligations.lean:14-40`,
`inventory : List Obligation` at `:42`).

Note what is *not* in either: a theorem value. The row holds a `Lean.Name` and an expected axiom
receipt string; the join is done by a `CommandElabM` checker that looks the name up in the
environment. This is the answer to the sketch's `List (Σ I, Invariant M I)`, and section 2.5
below spells out why the dependent version cannot work.

### 1.9 The link layer already exists, and is the model for a registry

```lean
inductive ModelRef where
  | row (family op : String)
  | prim (constructor : String)
  | action (name : String)
  | syncOp (name : String)
deriving DecidableEq, Repr

structure Link where
  path : Path
  refs : List ModelRef
deriving DecidableEq, Repr
```
(`/Users/pooks/Dev/lean4-effect4/Effect4/StdLib/Links.lean:31-46`), sixty-eight rows at
`:74-142`, one uniform checker

```lean
def Link.checked (link : Link) : Bool :=
  (rc112.resolve link.path).isSome && link.refs.all ModelRef.declared
```
(`Links.lean:158-159`), and `ModelRef.declared` decided against three literal name lists and a
family table (`:144-152`, `:49-71`).

Adding a link touches one list. Nothing else recompiles. That is the extensibility property the
component registry needs, and it is achieved without a single dependent type.

### 1.10 Content addressing is monomorphic in `Type`, and the injectivity law is a separate class

```lean
class Canonical (α : Type) where
  encode : α → Bytes

class LawfulCanonical (α : Type) [Canonical α] : Prop where
  encode_injective : Function.Injective (Canonical.encode (α := α))
```
(`/Users/pooks/Dev/lean4-effect4/Effect4/Store/Canonical.lean:70-79`), with the reason for the
split at `:75-77`: "kept separate so a carrier can be stored before its law is proved and the law
can never be assumed silently".

`Digest` is a `List UInt8` with `DecidableEq` derived, "so it has decidable equality and can key a
store" (`/Users/pooks/Dev/lean4-effect4/Effect4/Store/Digest.lean:26-29`, `:12-14`), and the store
laws are stated with digest freshness as a hypothesis rather than assuming SHA-256 is injective
(`/Users/pooks/Dev/lean4-effect4/Effect4/Store/Store.lean:22-26`, `get_put_new` at `:97-99`,
`put_held` at `:107-109`).

Two design constraints fall out. First, anything that goes into the store must be in `Type 0`
with `DecidableEq`, which excludes every proof-carrying record. Second, the framing discipline is
already solved: `framed (tag) (payload) = tag :: be64 payload.length ++ payload`
(`Canonical.lean:52-54`), with the reason "Framing is what makes concatenation injective"
(`:15-17`).

The existing pin carrier is already the right shape, but file-granular:

```lean
structure FilePin where
  module : String
  file : String
  sha256 : String
deriving DecidableEq, Repr, Inhabited
```
(`/Users/pooks/Dev/lean4-effect4/Effect4/StdLib/Entry.lean:52-56`), beside
`structure Entry` with `module/name/kind/line` (`Entry.lean:44-49`) and its path
`[entry.module, entry.name]` (`:61`).

### 1.11 Line numbers are the wrong pin granularity, and the tree already knows it

"When a pin moves, re-diff the transliterated sources *and re-open every `:line` citation* before
touching any proof; line numbers never survive a pin move unverified"
(`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:26`).

I tested that empirically. `EffectQueue.lean:6-35` cites `effect/src/Queue.ts` at rc.111 by line:
`:1789` (`sizeUnsafe`), `:645-648` and `:649`, `:659` (`offer` and the suspend strategy),
`:500`, `:458` (`bounded`, `make`), `:1000-1015` (`failCauseUnsafe`), `:1297-1298` (`takeAll`),
`:1994-1998` (`takeBetween`'s drain), `:2040-2047` (`releaseCapacity`), `:1607-1608`
(`takeUnsafe`'s `Done` arm), `:1955-1967` (`releaseTakers`), `:1191-1210` (`shutdown`). I opened
all twelve against the rc.112 bytes at
`/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/Queue.ts`
(SHA-256 `dc355d1a09662ae7b023c98ad47b7fe71051becaf9d461f244c37ad0a4d3dc35`, 2114 lines) and every
one still lands on the cited construct. That is luck, not a property: `releaseCapacity` now
*begins* at `:2037`, so the cited `:2040-2047` is its body rather than its head, and one more
edit above it moves everything.

Note also that `vendor/effect-4.0.0-rc.112/src/` in this repository holds only nine files and
does **not** contain `Queue.ts`; the only pinned `Queue.ts` on this machine is the Foldlab
`node_modules` copy, which matches the memory note about where the rc.112 runtime source lives.
A `Queue` component therefore has to pin bytes it can name, not a vendored path it does not have.

### 1.12 What got expensive, measured

* **Simulation.** `SimProof.lean` is 3648 lines, the largest module in the package by a factor of
  two (`wc -l EffectNatsSubstrate/*.lean`), and it proves one refinement between two hand-written
  machines. `Sim.lean:14-25` explains why a library simulation combinator was set aside: "one
  runtime step (`endFanOut`) must be matched by the abstract publish *followed by the owed pulls*
  … several abstract steps for one runtime step. The proof is therefore a direct induction on the
  runtime execution carrying the owed abstract suffix". Any API that promises cheap composition
  is promising something this package paid 3648 lines for once.
* **Enumeration under fuel.** `pullsAtGap` and `outcomesFrom`
  (`SubPlacements.lean:47-55`, `:67-77`) enumerate every placement of one consumer's pulls with
  fuel 2 per gap, and the header states the requirement: "Everything here is computed by
  structural recursion so the kernel can evaluate it (`decide`)" (`SubPlacements.lean:32-33`).
  The package gate makes it a rule: "`decide`-checked traces stay kernel-reducible: structural
  recursion only in anything `step` evaluates (no `String.splitOn`-style well-founded helpers)"
  (`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:89`).
* **Kernel `decide` over large terms.** Survey finding 22 measures the cost in this repository:
  four separation theorems closed by `decide` over fuel-20 region runs, with the note that
  "`by decide` forces the *kernel* to whnf the whole run … this cost lands in type-checking and
  in every downstream `collectAxioms`", and that these modules are "the ones most likely to hit
  `maxRecDepth`/heartbeat limits" (`docs/research/2026-09-03-survey-lean-core.md:762-792`).
* **Hand-maintained parallel lists.** Survey finding 15: fourteen frozen `private def` lists,
  roughly 2400 entries, in one 2512-line file, where "a single new theorem requires editing up to
  six of these lists *plus* regenerating the 237 KB `generated/fiber-assurance.tsv` *plus*
  possibly a row and a `#check` ascription" in a 4005-line module, and it is "the friction most
  likely to produce a wrong-but-green edit"
  (`docs/research/2026-09-03-survey-lean-core.md:549-596`). This is the single failure mode a
  component registry must be designed against.
* **`example` is invisible to the axiom gate.** Survey finding 1: 637 `example` declarations, one
  already carrying `native_decide`, none reachable by a gate that enumerates
  `environment.constants` (`docs/research/2026-09-03-survey-lean-core.md:27-71`). Every receipt in
  the new API must be a named `theorem`.
* **`autoImplicit` on in 107 of 115 library modules**, with the exact failure named: "a mistyped
  identifier in a theorem statement becomes a fresh universe-polymorphic implicit binder rather
  than an error, which is precisely how a vacuous or over-general theorem gets written and stays
  green" (`docs/research/2026-09-03-survey-lean-core.md:652-674`).
* **Half-applied universe polymorphism.** Survey finding 19: `Effects.RawFlow` and
  `FlowAlphabet` are universe-polymorphic, but `Effect4/Semantics/Equivalence.lean:29` and
  `Effect4/Semantics/Logic.lean:285` fix `Ty : Type`, so "the top-level composition story … does
  not compose with a flow over a `Type 1` type vocabulary"
  (`docs/research/2026-09-03-survey-lean-core.md:678-696`). The dependency itself needs
  `set_option linter.checkUnivs false in` to declare its two carriers
  (`.lake/packages/effects/Effects/Family.lean:19-25`).
* **32 `@[simp]` lemmas in 45 000 lines, all in one area**, so "every proof in those areas spells
  its unfolding list by hand (554 `simp only [...]` occurrences)"
  (`docs/research/2026-09-03-survey-lean-core.md:625-648`).
* **Per-module elaboration is not the problem; breadth is.** The two largest modules cost 14.2 s
  and 8.6 s, and "no single module is pathological … The build cost is *breadth*: `Effect4Test.lean`
  transitively imports 242 modules" (`docs/research/2026-09-03-survey-lean-core.md:933-963`).

### 1.13 Rulings this design must obey

* **DB-02**: canonical program content is first-order data; "A host function, promise, thunk,
  custom predicate, or raw closure must become a named and registered foreign boundary or receive
  a profile refusal" (`docs/DESIGN-BASIS.md:103-125`). The applied form is in `RefFamily`, where a
  read-modify-write function became a *name*: "DB-02 … forbids a Lean function in canonical
  content, so the function is a **name**: `Handle "RefFn"`"
  (`Effect4/Stateful/RefFamily.lean:52-58`).
* **DB-03**: "With no tape fixed, the meaning of a program is a relation … determinism is never
  inferred merely because one runner selected one branch" (`docs/DESIGN-BASIS.md:127-152`). So the
  component's `step` is deterministic given a label, and all nondeterminism lives in which label
  sequences are admitted.
* **DB-04**: "Fuel exhaustion and unanswered choices are live frontiers, never typed errors,
  causes, or refusals" (`AGENTS.md:63-64`; the full ruling at `docs/DESIGN-BASIS.md:154-191`).
  Fuel may appear in enumerators, never in the LTS.
* **Coverage vocabulary**: a witness is "a Lean `theorem` (never a `def`, never a Prop-typed
  def)" (`docs/RUNTIME-COVERAGE.md:52`), the green criterion is clause-by-clause and "A finite
  probe … does not turn a clause green" (`:47-50`), and "a host trace never turns a census row
  green" (`docs/LOWERING-COVERAGE.md:10-11`). The rungs of evidence in the sketch are already this
  repository's vocabulary; reuse the words rather than minting new ones.
* **No theorem transfer between handlers**: two handlers for one signature are two models, and
  "'Both are handlers for the same signature' is not such a hypothesis"
  (`/Users/pooks/Dev/lean4-effects/docs/CLAIM-BOUNDARY.md:32-38`). A grade proved of one model
  never transfers to another by shape alone.

### 1.14 The prior graded design, and why it is not the shape to copy

The effect-nats notes carry a grade ladder that was actually implemented:

```
| Guarantee | Delivery rung: `atMostOnce < atLeastOnce < dedupWindow` | 3-constructor enum, rank into `Nat` |
| meet | Weakest of two rungs; grade of sequential composition | `Guarantee → Guarantee → Guarantee` |
| Prog γ α | Reified NATS program of grade γ producing α | grade-indexed inductive |
```
(`/Users/pooks/Dev/effect-nats/packages/agents/notes/0002-lean-pass-a-contract.md:18-20`),
with `pure` later adjoined as top and the interpretation fixed as "a LOWER BOUND on the guarantee
of every delivery step a run executes"
(`/Users/pooks/Dev/effect-nats/packages/agents/notes/0003-graded-algebra-model.md:10-14`), the
laws proved as "comm, assoc, idem, neutral, lower-bound both sides, `atMostOnce` absorbing, order
total" (`0003:26-28`), and the two soundness theorems
`usesCore_grade` and `sim_guarantee_sound : m ∈ (sim p s).2.log → m ∈ s.log ∨ γ ≤ m.guarantee`
(`0003:43-44`).

Three rulings there are worth importing wholesale:

* Mathlib's `Order.Lattice` was classed adapt-later: "for a 3-element enum, from-scratch `meet` +
  `decide`-style case proofs is the smaller trusted base now" (`0002:53`).
* The overclaim guard is written down as a refutable sentence: "'`meet` is a join' - it is a
  MEET" (`0002:33-34`).
* Ordering guarantees are a **separate axis**: "when `race`/`all` arrive, sequential meet is
  expected to remain correct for delivery grade, but ordering guarantees compose differently;
  keep them a separate grade axis (do not force one monoid)" (`0003:29-31`).

But the *carrier* choice there, `Prog γ α` as a grade-indexed inductive, is the one to decline
for this API, and the notes say why in their own cost line: "**Any change to `meet` re-opens
`Prog`**" (`0002:84-86`), and grade-indexed programs "have no canonical serialization and
branch-folds are relational, not computable" (`0003:16-19`). A type-level index buys one thing,
elaboration-time refusal of an over-claiming program (`0003:47`), and costs the whole data face:
no `DecidableEq`, no `Canonical`, no store, no registry row. For a *component registry* the data
face is the product. Keep the grade as a value on a manifest, and recover the elaboration-time
refusal as a `decide`d theorem instead.

Finally, the algebra package this repository depends on has **no** order and no meet at all:
`Signature`, `Program`, `Handler`, `Family`, `Alphabet`, `Mask` and the experimental `Hom`
carry idempotent projections and a commutative idempotent monoid up to morphism, but nothing
lattice-shaped. The grade lattice is new construction, not inheritance.

The general ruling against a scalar grade is written down in the research bed:

```lean
structure Budget where
  work : Nat
  bytes : Nat
  apiCalls : Nat
  entropy : Nat
  deadline : Option Duration
  authority : CapabilitySet
```
under the heading "Use a resource product, not a fictitious universal scalar", with the closing
sentence "Move a grade into an indexed program type only when static rejection of over-budget
composition is worth the proof and ergonomics cost"
(`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-20-lean4-engineering-assurance-modeling.md:615-627`).
A record of independent axes is the recommended shape, and the indexed `Prog γ α` is explicitly
the expensive option, to be taken only for the elaboration-time refusal it buys.

### 1.15 The ack and redelivery bed: the failure model belongs in the label alphabet

`/Users/pooks/Dev/jetstream-workflow-model/formal/jetstream_workflows` is a second Lean model on
this machine, and its subject is exactly delivery grading under failure. Four things in it are
directly load-bearing here.

**The failure model is constructors of the label type, not a side condition:**

```lean
inductive Action where
  | publish (message : Message)
  ...
  | ack (id : MessageId)
  | loseAck (id : MessageId)
  | redeliver (id : MessageId) (worker : WorkerId)
  | tick
  | failReplica
  | recoverReplica
  | failConsumerReplica
  | recoverConsumerReplica
  deriving Repr, DecidableEq
```
(`…/JetstreamWorkflows/Semantics/System.lean:97-115`). The step is a function into `Except` with a
thirty-constructor error type (`:117-146`, `:213`), and the relation is derived
(`:404-405`: `def Step (cfg) (before after) : Prop := ∃ action, step cfg before action = .ok after`).

Because the failure events are labels, a delivery guarantee is a property of *words over an
alphabet that includes the failures*, which is precisely what the sketch's "grade relative to a
failure model `F ⊆ L`" wants, and it costs nothing extra.

**The state must be shaped so the counterexample survives.** Two fields are deliberately kept
apart:

```lean
  activityReceipts : ActivityKey → Bool
  externalEffects : ActivityKey → Nat
```
(`…/System.lean:31-32`), and the reason is a recorded representation decision: "External effects
and their durable receipts are separate fields. This preserves the exactly-once counterexample
rather than assuming it away"
(`/Users/pooks/Dev/jetstream-workflow-model/formal/jetstream_workflows/docs/domain-contract.md:138-139`).
A model that stored only a Boolean receipt would make duplicate execution unrepresentable and
would then "prove" exactly-once by construction. This is the most instructive single sentence in
either bed for grade design: **the carrier must be able to express the grade's failure.**

**The `Bool` / `Prop` / `Decidable` triad, applied at scale:**

```lean
def Setup.isValid (cfg : Setup) : Bool :=
  decide (1 ≤ cfg.streamReplicas ∧ cfg.streamReplicas ≤ 5) &&
    decide (1 ≤ cfg.consumerReplicas ∧ cfg.consumerReplicas ≤ cfg.streamReplicas) && …

def Setup.WF (cfg : Setup) : Prop := cfg.isValid = true

instance (cfg : Setup) : Decidable cfg.WF := by
  unfold Setup.WF
  infer_instance
```
(`…/JetstreamWorkflows/Model/Config.lean:119-167`), over a configuration with dozens of fields and
twenty-eight `decide (…)` chunks. This is strictly better than either pure `Bool` or pure `Prop`:
the `Bool` is what a test evaluates, the `Prop` is what a theorem takes as a hypothesis, and the
`Decidable` instance is recovered mechanically rather than written. Note the chunking: many small
`decide (… ∧ …)` conjuncts joined by `&&`, not one giant `decide` of a hundred-clause
conjunction.

**And the outcome, which is the cautionary half.** That package's independent review is
"pass for internal compilation and proof-term hygiene; fail for Pass-B promotion or any
end-to-end durability claim"
(`/Users/pooks/Dev/jetstream-workflow-model/formal/jetstream_workflows/docs/reviews/lean-assurance-review.md:5-6`).
One reason is `native_decide`, which had to be carved out into its own trust class:
"closed scenario propositions use `native_decide`; they are classified as finite checked results
with compiler/native evaluation in the trusted base, not as unbounded kernel-only proofs …
each `native_decide` scenario proof depends on Lean's generated native-decision axiom and is
therefore classified as a finite native check, not a kernel-only theorem"
(`…/docs/signature-snapshot.md:223-229`). The substrate package banned it outright, and its state
carrier is an association list rather than the function-valued `SystemState` above, precisely so
that whole states have `DecidableEq` and traces close by `decide`.

**The guarantee ladder itself is stated as trace properties with explicit escape clauses**:

> **G1 (at-least-once under `explicit`).** *If `D(s, k)` and never `A(s)` and never a `+TERM` for
> `s`, then either `D(s, k+1)` eventually occurs, or `rdc[s] ≥ maxdc` with `maxdc > 0`, or
> `¬Live`, or `s` left the stream.*

(`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-23-nats-consumer-acks-and-failure.md:739-741`),
followed by "Note the escape clauses are not decorative: the `MaxDeliver` clause, the `¬Live`
clause … and the 'left the stream' clause … are each reachable" (`:751-753`).

That is a design requirement, not a stylistic note. A grade whose escape clauses are unreachable
is a stronger grade misdescribed; a grade whose escape clauses are unnamed is an overclaim. The
API must therefore carry, per grade row, both the escape condition and a witness that it is
reachable.

**The evidence vocabulary that replaces `verified : Bool`:**

```lean
inductive EvidenceKind
  | proved                 -- kernel-checked theorem, with audited axioms
  | modelChecked           -- complete for a named finite abstraction/cutoff
  | exhaustivelyDecided    -- complete for a named finite domain/encoding
  | tested                 -- sampled executions and their generator provenance
  | measured               -- benchmark or calibrated observation
  | monitored              -- checked over an observed trace/window
  | assumed                -- explicit premise not established here
  | unknown                -- required link with no current evidence
```
(`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-20-lean4-engineering-assurance-modeling.md:648-662`),
with "Their outputs are not interchangeable endorsements; they populate different fields of the
same evidence bundle" (`:666`). The sketch's three rungs are a coarsening of this; the eight-way
version is better and costs one inductive.

### 1.16 The Foldlab conformance bed: laws and their anti-vacuity kit in one structure

This is the strongest transferable idea found anywhere in the survey, and it changes the
proposed API materially.

> each ratified schema family is a structure whose fields are the template's holes, whose laws
> are proof fields, and whose anti-vacuity kit is also fields. An obligation instance is a term of
> the family structure, a term without its law or kit does not elaborate, so proved-with-kit is
> the only representable state for Lean-side artifacts.

(`/Users/pooks/Dev/lean4-effect4/vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/Effects/Conformance.lean:18-22`).
Concretely, the trace-property family:

```lean
structure TraceExcludes (State Input Decision Mode : Type) where
  id : String
  sentence : String
  modeOf : State → Mode
  guarded : Mode
  decisions : State → Input → List Decision
  bad : Decision
  law : ∀ s i, modeOf s = guarded → bad ∉ decisions s i
  posState : State
  posInput : Input
  pos_mode : modeOf posState = guarded
  negState : State
  negInput : Input
  neg_mode : modeOf negState ≠ guarded
  neg_bad : bad ∈ decisions negState negInput

def TraceExcludes.entry (b : TraceExcludes State Input Decision Mode) : LedgerEntry :=
  { id := b.id, family := "TRACE-EXCLUDES", sentence := b.sentence }
```
(`…/Effects/Conformance/Schema/TraceExcludes.lean:9-27`), and the step-measure family
`ExactStep` with `law`, `posState`/`pos_wf`/`pos_hyp`, and `negState`/`neg_hyp`
(`…/Effects/Conformance/Schema/ExactStep.lean:9-27`).

Three properties of this shape matter here:

* It is **not** a `Σ` over a predicate. The structure's parameters are *carriers* (`State`,
  `Input`, `Decision`, `Mode`), all in `Type`, and instances are ordinary terms. So it does not
  hit the objection of checklist 2.5.
* The anti-vacuity kit is **unforgeable**: a theorem with an unreachable hypothesis cannot be
  packaged, because `pos_mode` demands a witness that the guard is satisfiable and `neg_bad`
  demands a witness that it is not vacuous. This is strictly better than a separate `by decide`
  receipt, which can be forgotten.
* The projection `entry` produces a three-field `LedgerEntry { id, family, sentence }`
  (`…/Effects/Conformance/Ledger.lean:14-18`), which is the flat data row that goes into the
  registry. The proof-carrying bundle and the manifest row are the same artefact seen from two
  sides.

The mutation gate that goes with it is `IO`-side and its kill condition is that the *rendered
vectors move*:

```lean
def report {F : Type} (m : Mutant F) (moved : Bool) : IO Nat := do
  if moved then IO.println s!"killed {m.id} ({m.attacks})"; return 0
  IO.eprintln s!"SURVIVOR {m.id} ({m.attacks}): vectors did not move"
  return 1
```
(`…/MutationMain.lean:147-163`), with an unknown attacked family counted as a survivor "so it
cannot pass silently" (`:165-179`). The governing metric is stated once:
"Row counts do not measure coverage; kill rates do"
(`…/CONFORMANCE-WORKFLOW.md:206`), and the naming rule that makes it navigable:
"One name binds all surfaces: ledger ID = Lean theorem name = manifest family = TypeScript test
name" (`:201-202`).

**The vocabulary this bed uses is five words, not one.** From
`/Users/pooks/Dev/foldlab/.staging/effect-core-v1/COUNTEREXAMPLES.md:21-36`:

* a **counterexample** is data plus a derivation showing a quantified statement is false, and it
  names the exact quantifier or missing premise it defeats;
* a **falsifier** is an executable challenge attached to a proposed law, and "A falsifier that
  currently passes does not establish completeness";
* a **negative fixture** is an input the checker must reject, and "is not a counterexample unless
  some claim says the input must be accepted";
* a **mutant** is a deliberately damaged implementation used to show a gate can fail; "It attacks
  the gate, not normally the semantic statement";
* a **boundary witness** separates two concepts without refuting a claim.

with six evidence states (`VERIFIED-KERNEL`, `VERIFIED-TOOL`, `REPORTED`, `RED`, `OWED`,
`SUPERSEDED`) and the rule "No prose review upgrades `REPORTED`, `RED`, or `OWED` to a verified
state" (`:44-53`). The sketch's `Test`/`Mutant` pair collapses at least three of these; the
report's proposal keeps them apart.

**The hash-hypothesis lattice, which the pin design must obey.** From the same estate:

```lean
theorem addr_eq_or_collision {n m : AdmittedNode} (h : addr H n = addr H m) :
    n = m ∨ (encodeAdmitted n ≠ encodeAdmitted m ∧
             H (encodeAdmitted n) = H (encodeAdmitted m))
```
with the comment "The disjunction needs no premise on `H`; discharging its right branch is exactly
what would require one"
(`/Users/pooks/Dev/lean4-effect4/vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/Effects/Cas/Address.lean:52-63`),
and injectivity appearing only as a named premise at `:69-70`. The three-level policy is: Level 0
takes no premise on the hash; Level 1 names `Injective H` as an explicit hypothesis; Level 2,
collision resistance, is never stated at all
(`/Users/pooks/Dev/foldlab/library/machine/MACHINE-ALGEBRA.md:76-84`). This repository already
follows it: `Effect4/Store/Store.lean:22-26` states each law with digest freshness as a
hypothesis, "never by assuming SHA-256 has no collision".

**And the gap that lands on this design directly:** span-level pins do not exist anywhere in the
estate. Everything is file-level, `gitBlob` plus SHA-256 plus byte length
(`/Users/pooks/Dev/foldlab/docs/provenance/README.md:10-21`; the realized lock at
`/Users/pooks/Dev/foldlab/.reference/provenance/sources.lock.json`). The span-shaped requirement
appears three times as owed work and never as an artefact. A verb-to-span pin is therefore new
construction, and it is the piece of this API with the least prior art behind it.

---

## 2. Kernel and elaborator ergonomics checklist for this domain

Each item names the reason and the failure it avoids.

**2.1 `set_option autoImplicit false` at the top of every module of the API.**
Reason: a mistyped binder in a theorem statement silently becomes a universe-polymorphic
implicit. Failure avoided: a vacuous or over-general frozen statement that stays green
(`docs/research/2026-09-03-survey-lean-core.md:652-674`).

**2.2 Everything in `Type 0`. No universe variables anywhere in the component core.**
Reason: `Canonical` is `class Canonical (α : Type)` (`Effect4/Store/Canonical.lean:70`), so
nothing polymorphic can be stored; and half-applied polymorphism is a recorded defect
(`survey-lean-core.md:678-696`). Component state and labels are always concrete first-order
data, so this costs nothing. Failure avoided: the `Effects.Family` situation, where the carrier
needs `set_option linter.checkUnivs false in` to declare
(`.lake/packages/effects/Effects/Family.lean:19-25`).

**2.3 `step : S → L → Option S`, total-or-disabled; the relation is `def R … : Prop := step … = some …`.**
Reason: `decide` on traces requires kernel reduction of the step; a relation has no reduction
behaviour. Failure avoided: a `Decidable` instance per step arm, and inductive relations whose
`cases` produce twelve goals per label (`Runtime.lean:296-307`, `Scheduler.lean:612-620`).

**2.4 Answers live in the label, not in a step output.**
Reason: keeps `run : S → List L → Option S`, keeps traces first-order and self-describing, keeps
the reading label-local. Failure avoided: pair-carrying lemmas and output comparison in every
enumerator (`Runtime.lean:105-125`, `Traces.lean:44-51`).

**2.5 No proof is ever a field of a runtime record, and no `Σ` over a predicate ever enters a list.**
Reason and failure avoided, spelled out because this is the sketch's biggest risk. Take
`invariants : List (Σ I : S → Prop, Inductive M I)`. It elaborates: for `S : Type`, `S → Prop`
is in `Type`, so the sigma is in `Type`. But:
  * it has no `DecidableEq`, no `Repr`, no `BEq`, so it cannot be compared, printed, or
    `decide`d;
  * it has no `Canonical` instance and never can, so it cannot enter the store
    (`Effect4/Store/Canonical.lean:70`) and cannot be a manifest field;
  * `List.get`/pattern matching on it yields a `Prop`-valued function whose only use is
    `Exists.elim`, so nothing downstream can *name* the third invariant;
  * two entries with the same statement are not provably equal (proof irrelevance gives you
    `HEq` at best across different `I`), so deduplication is undecidable;
  * every module that adds an invariant re-elaborates the list and every theorem quantifying
    over it.
Do instead what the two working registries do: the *statement* is a named `structure … : Prop`
frozen by `#check` ascription (`RuntimeCoverage.lean:47-61`), the *name* is a `Lean.Name` in a
flat data row (`RuntimeCoverage.lean:2547-2557`), and the join is a `CommandElabM` checker that
looks the name up, checks it is a theorem, and checks its axiom receipt
(`Effect4Test/Concurrency/FiberAssurance.lean:61-79`).

**2.6 Invariants are `structure … : Prop` with named clauses, one clause per proof site.**
Reason: clause reuse by projection, and a refusal that can name the failing clause. Failure
avoided: 21-way anonymous conjunctions and 5-`∧` characterization lemmas
(`survey-lean-core.md:832-855`; the good pattern at `RtInvariants.lean:25-70`).

**2.7 Exactly one strengthened reachability induction principle per machine, and a rule that
forbids a second.**
Reason: the bare recursor loses the invariant in the step case. Failure avoided: N inductions
instead of one (`SubReachable.lean:220-226`, `AGENTS.md:51` in effect-nats-verified).

**2.8 The `Bool` / `Prop` / `Decidable` triad, in that order.** Write the executable check as a
`Bool` function; define the proposition as `… = true`; recover decidability by `unfold` then
`infer_instance`:
```lean
def X.isValid (x : X) : Bool := decide (…) && decide (…) && …
def X.WF (x : X) : Prop := x.isValid = true
instance (x : X) : Decidable x.WF := by unfold X.WF; infer_instance
```
Reason: `decide` on a `Bool` equation needs no instance synthesis at all, the `Prop` is what a
theorem takes as a hypothesis, and the instance is generated rather than written. Precedent at
scale: this exact triad appears five times over a several-dozen-field configuration
(`/Users/pooks/Dev/jetstream-workflow-model/formal/jetstream_workflows/JetstreamWorkflows/Model/Config.lean:119-167`,
and again in `Model/Topology.lean`, `Model/Engine.lean`, `Model/Architecture.lean`,
`Semantics/Pipeline.lean`). Note the chunking: many small `decide (… ∧ …)` conjuncts joined by
`&&`, never one `decide` of a hundred-clause conjunction. Failure avoided: a `[DecidablePred φ]`
argument threading through the entire API, elaboration time in TC inference (1.62 s of the
largest module's 14.2 s, `survey-lean-core.md:941`), and two drifting statements of one property.

**2.9 `List` equality, never a permutation or multiset relation.**
Reason: order is the FIFO guarantee, and `List` equality is `DecidableEq` for free while
`Multiset` needs `Quot` and Mathlib. Failure avoided: a Mathlib dependency and a
`Quot.sound`-heavy axiom receipt. The existing invariants already use `List.Pairwise` and
`List.Nodup` from core (`SubInvariants.lean:40`, `RtInvariants.lean:55`).

**2.10 `Set`-free: a "set of labels" is a `List L` with `[DecidableEq L]`, membership by
`List.contains`.**
Reason: `Set L = L → Prop` has no decidable membership, no `Repr`, and cannot be manifest data.
Failure avoided: a failure model that cannot be printed, hashed, or `decide`d.

**2.11 Structural recursion only in anything the kernel must evaluate. No `termination_by`, no
`decreasing_by`, no `partial`, in any function `run`, a test, or an enumerator reaches.**
Reason: well-founded recursion unfolds through `WellFounded.fix`, which the kernel will not
reduce, so `decide` fails or diverges. Failure avoided: exactly the trap the gate names
(`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:89`). The whole 13 981-line
`EffectNatsSubstrate` tree contains zero `termination_by`, zero `decreasing_by`, zero
`set_option`, zero `partial` (verified by grep). Where a bound is needed, pass the value as its
own fuel, as `natBytes` does: "The number is its own fuel, so the recursion is structural"
(`Effect4/Store/Canonical.lean:42-50`).

**2.12 `deriving DecidableEq, Repr, Inhabited` on every data carrier, and nothing else.**
Reason: `DecidableEq` gives `==`, `decide`, and store keys; `Repr` gives diagnostics and
exporters; `Inhabited` gives `getD` and `Array` defaults. `BEq` derived separately from
`DecidableEq` creates a second equality that `simp` will not connect. Failure avoided: `OpRow`
derives `Repr, BEq, Inhabited` (`Effect4/Target/TypeScript/EffectV4.lean:183`) and consequently
cannot be a store key, while `Entry` derives `DecidableEq, Repr, Inhabited`
(`Effect4/StdLib/Entry.lean:49`) and can.

**2.13 Every receipt is a named `theorem`, never an `example`, never a `def` returning a Prop.**
Reason: the axiom gate enumerates `environment.constants` and `example` never enters it
(`survey-lean-core.md:27-71`); `docs/RUNTIME-COVERAGE.md:52` says a witness is "a Lean `theorem`
(never a `def`, never a Prop-typed def)". Failure avoided: a `sorry` or `native_decide` inside a
green build.

**2.14 Budget `decide`. State the size of every `decide`d term in the docstring, and cap it.**
Reason: kernel `decide` cost lands in type-checking and in every downstream `collectAxioms`
(`survey-lean-core.md:779-782`). Rule of thumb from the working tree: a trace of under thirty
labels over a structure-only state is comfortable (nine such traces plus their enumerations
elaborate inside one module at `SubPlacements.lean:124-141`); a fuel-20 interpreter run is
already flagged as a risk (`survey-lean-core.md:762-792`).

**2.15 One scoped `simp` set per component, tagging its own step and reading equations.**
Reason: 554 hand-written `simp only [...]` lists is the measured alternative
(`survey-lean-core.md:625-648`). Use `scoped simp` so a downstream component opts in and cannot
be broken by another component's rewrite set.

**2.16 Never a typeclass where a structure argument will do.**
Reason: the dependency has exactly one `class` in the whole library (`ToVal`,
`.lake/packages/effects/Effects/Trace.lean:53`) and passes `Signature`, `Handler`, `Family`,
`FlowAlphabet` explicitly. A typeclass makes "which model is this theorem about" invisible at the
use site, which is precisely the claim boundary the tree refuses to blur
(`/Users/pooks/Dev/lean4-effects/docs/CLAIM-BOUNDARY.md:32-38`). Failure avoided: an accidental
theorem transfer between two components with the same alphabet.

**2.17 Pin by byte span, and carry both the file digest and the span digest.**
Reason: line numbers do not survive a pin move
(`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:26`), and I confirmed the drift is live
(`releaseCapacity` moved head from the cited `:2040` to `:2037` between rc.111 and rc.112).
Failure avoided: a pin that silently starts naming the wrong code.

**2.18 The manifest is monomorphic over spellings; the machine is polymorphic over `L`; the
bridge is a `spell : L → String` with a `decide`d injectivity receipt on the finite label list.**
Reason: this is how a heterogeneous registry avoids `Σ`. Precedent: `ExportKind.spelling`
(`Effect4/StdLib/Entry.lean:32-38`), `OpRow.name : String` (`EffectV4.lean:166`), and `ModelRef`
naming constructors by string with a `declared : Bool` check
(`Effect4/StdLib/Links.lean:144-152`).

**2.19 One list per component, and one derived artefact. Never two hand-maintained lists that
must agree.**
Reason: the measured cost of the alternative is fourteen lists and six edits per new theorem
(`survey-lean-code`, `survey-lean-core.md:549-596`). Failure avoided: the wrong-but-green edit.

**2.20 Keep the checker invocation in the component's own module, not in a central one.**
Reason: a central checker imports every component, so adding one re-elaborates all of them; the
measured build cost of this tree is breadth, not depth
(`survey-lean-core.md:933-963`). Failure avoided: an O(N) rebuild per component added.

**2.21 The carrier must be able to express the grade's failure.**
Reason: a state that cannot represent duplicate delivery makes "no duplicates" true by
construction rather than by proof. The applied form is two fields kept apart,
`activityReceipts : Key → Bool` beside `externalEffects : Key → Nat`, with the recorded reason
"This preserves the exactly-once counterexample rather than assuming it away"
(`/Users/pooks/Dev/jetstream-workflow-model/formal/jetstream_workflows/docs/domain-contract.md:138-139`).
Failure avoided: a vacuous grade. Test for it: for every axis a grade claims, exhibit a mutant
whose state *does* violate it and check the tests kill that mutant.

**2.22 Every grade carries its escape clauses, and each escape clause carries a reachability
witness.**
Reason: "the escape clauses are not decorative"
(`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-23-nats-consumer-acks-and-failure.md:751-753`);
a guarantee with unnamed escapes is an overclaim, and one with unreachable escapes is a weaker
statement than the one that was available. Failure avoided: an at-least-once claim that quietly
depends on a `MaxDeliver` bound nobody stated.

**2.23 Laws travel with their anti-vacuity kit in the same structure.**
Reason: "a term without its law or kit does not elaborate, so proved-with-kit is the only
representable state"
(`vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/Effects/Conformance.lean:18-22`),
with `pos_*` and `neg_*` witness fields beside `law`
(`…/Effects/Conformance/Schema/TraceExcludes.lean:9-23`). Failure avoided: a frozen theorem whose
hypothesis is unsatisfiable, which the tree has already paid for twice as post-freeze corrections
(`/Users/pooks/Dev/effect-nats-verified/docs/signature-snapshot.md:57-82`).

**2.24 Use five words, not one: counterexample, falsifier, negative fixture, mutant, boundary
witness.**
Reason: they are different artefacts with different obligations; in particular "A falsifier that
currently passes does not establish completeness" and a mutant "attacks the gate, not normally the
semantic statement" (`/Users/pooks/Dev/foldlab/.staging/effect-core-v1/COUNTEREXAMPLES.md:21-36`).
Failure avoided: a negative test being reported as a refutation.

**2.25 Do not assume `deriving DecidableEq` will fire on a nested recursive carrier.**
Reason: a recorded probe at the toolchain in use found that both inline `deriving DecidableEq` and
a later `deriving instance DecidableEq` fail for the shape `List (String × Self)` at `v4.33.0`
because no deriving handler applies
(`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-22-session-types-pilot-vp1.md:181-185`),
and the hand-written `BEq` replacement then needs `beq a b = true ↔ a = b` and `LawfulBEq` for
every carrier. Failure avoided: a state carrier that cannot be `decide`d, discovered after the
trace layer is written. Design the state so every field is a `Nat`, a `String`, a finite
inductive, a product, or a `List` of those.

**2.26 Two named tactic traps, from a list written while proving.**
`omega` does not see through an `abbrev` to `Nat`, so a bound stated over `abbrev SubId := Nat`
needs `Nat.lt_succ_of_lt` and friends by hand
(`/Users/pooks/Dev/effect-nats-verified/docs/stage-a-proof-map.md:212-214`); and `rw`'s closing
`rfl` runs at reducible transparency, so `List.map f [a]` and `Option.map f (some a)` do not
reduce there (`:205-207`). The whole list at `:195-220` is worth reading once before writing the
first component. Related: unused-hypothesis and unused-simp-argument linters count as warnings
under a no-warnings gate (`:219-220`).

**2.27 `rfl` over large reduced data is a trap, and `decide` is the stable boundary.**
Reason: a recorded case raised `maxHeartbeats` to 4 000 000 and `maxRecDepth` to 10 000 to prove
two full-text facts by `rfl` over character lists, at roughly 58 seconds for one module, and the
review's recommendation was `List String` with derived `DecidableEq` closed by `decide`
(`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-22-session-types-pilot-vp1.md:150-164`).
Failure avoided: a component whose test module is the slowest thing in the build.

---

## 3. The proposed API

Namespace `Effect4.Char` (characterized components). One module per concept, all of them
`set_option autoImplicit false`, Lean core plus `Effect4.Store` only.

### 3.1 The machine

```lean
set_option autoImplicit false

namespace Effect4.Char

/-- A labelled transition system over first-order state and labels.
Functions only; this record is never `deriving`-ed and never stored. -/
structure Machine (S L : Type) where
  init : S
  step : S → L → Option S

namespace Machine

variable {S L : Type}

/-- Run a word. Structural recursion on the list, so the kernel reduces it. -/
def run (M : Machine S L) : S → List L → Option S
  | s, []      => some s
  | s, l :: ls =>
    match M.step s l with
    | some s' => M.run s' ls
    | none    => none

def enabled (M : Machine S L) (s : S) (l : L) : Bool := (M.step s l).isSome

/-- The accepted words, as a `Bool`: no `Decidable` instance is ever synthesized. -/
def accepts (M : Machine S L) (w : List L) : Bool := (M.run M.init w).isSome

/-- The reachable states. The relation is the graph of `step`, as in
`Effect4/Concurrency/Scheduler.lean:612-615`. -/
def Next (M : Machine S L) (s : S) (l : L) (s' : S) : Prop := M.step s l = some s'

inductive Reach (M : Machine S L) : S → Prop
  | init : Reach M M.init
  | step {s s' : S} {l : L} : Reach M s → M.step s l = some s' → Reach M s'

end Machine
```

`Reach` is an inductive `Prop` over `S : Type`, so it lives in `Prop` and gets a free recursor.
No `Decidable` instance is needed or wanted; reachability is a proof-side notion and the
executable face is `accepts`.

Prefix closure is a theorem, not a definition:

```lean
theorem Machine.accepts_prefix (M : Machine S L) (u v : List L) :
    M.accepts (u ++ v) = true → M.accepts u = true
```
by induction on `u`.

### 3.2 Invariants

```lean
/-- An inductive invariant: two obligations, no more. The predicate itself is a
named `structure … : Prop` declared by the component, as in
`EffectNatsSubstrate/RtInvariants.lean:25-36`. -/
structure Inductive {S L : Type} (M : Machine S L) (I : S → Prop) : Prop where
  init : I M.init
  step : ∀ {s s' : S} {l : L}, I s → M.step s l = some s' → I s'

theorem Inductive.reach {S L : Type} {M : Machine S L} {I : S → Prop}
    (h : Inductive M I) {s : S} (hr : Machine.Reach M s) : I s := by
  induction hr with
  | init => exact h.init
  | step _ hstep ih => exact h.step ih hstep

/-- The one strengthened induction principle. Every further reachable-state fact
of a component goes through this, and a component module may not write a second
induction over `Reach`. This is `SubReachable.lean:220-226` generalized. -/
theorem Machine.reach_ind {S L : Type} {M : Machine S L} {I P : S → Prop}
    (hI : Inductive M I)
    (hinit : P M.init)
    (hstep : ∀ {s s' : S} {l : L},
      Machine.Reach M s → I s → P s → M.step s l = some s' → P s')
    {s : S} (h : Machine.Reach M s) : P s
```

Adding an invariant to an existing component is: one new `structure X : Prop`, one
`theorem x_inductive : Inductive queue X`, one `#check` ascription, one manifest string. No
existing proof is touched, because `Inductive` never mentions the other invariants.

### 3.3 The reading: how a word and a state are read as deliveries

This is the piece the starting sketch left implicit, and it is where the grade denotation
becomes well-typed.

```lean
/-- Item identities are `Nat`, never Lean values: DB-02 (`docs/DESIGN-BASIS.md:103-125`)
forbids a closure or an opaque host value in canonical content, and the applied
precedent is `RefFn` as a `Handle` name (`Effect4/Stateful/RefFamily.lean:52-58`).
A component that needs richer items assigns them store ids. -/
abbrev Item := Nat

/-- What a component's alphabet means for delivery. `accepts` and `emits` read the
label alone, which is sound because answers live in the label (section 2.4);
`residue` reads the state, which is what makes conservation statable. -/
structure Reading (S L : Type) where
  accepts : L → Option Item
  emits : L → List Item
  residue : S → List Item

namespace Reading

variable {S L : Type}

/-- The items the client handed in, in order. -/
def acc (R : Reading S L) (w : List L) : List Item := w.filterMap R.accepts

/-- The items the component handed out, in order. -/
def del (R : Reading S L) (w : List L) : List Item := w.flatMap R.emits

end Reading
```

`acc` and `del` are `filterMap` and `flatMap` over a list, both structurally recursive in core
Lean, both with a rich existing lemma set (`List.filterMap_append`, `List.flatMap_append`),
which is exactly what the conservation induction needs.

### 3.4 Failure model and grade

```lean
/-- A failure model names the boundary labels the grade is stated relative to,
and the escape clauses it admits. `Set`-free by construction (checklist 2.10);
the escapes are named because "the escape clauses are not decorative"
(`…/2026-08-23-nats-consumer-acks-and-failure.md:751-753`). -/
structure Failure (L : Type) where
  name : String
  /-- The labels whose occurrence weakens the grade. -/
  boundary : List L
  /-- One plain sentence per escape clause, each of which must have a
  reachability witness in the component's kit (checklist 2.22). -/
  escapes : List String
deriving DecidableEq, Repr

def Failure.hit {L : Type} [DecidableEq L] (F : Failure L) (w : List L) : Bool :=
  w.any (fun l => F.boundary.contains l)

/-- The delivery grade. A fixed record of `Bool` axes, not a rung enum: the axes
are independent, and `0003:29-31` of the effect-nats notes rules that ordering
guarantees must not be forced into one monoid with delivery guarantees.
Adding an axis is a freeze revision, recorded like any other. -/
structure Grade where
  noLoss : Bool
  noDup : Bool
  order : Bool
deriving DecidableEq, Repr, Inhabited

namespace Grade

def top : Grade := ⟨true, true, true⟩
def bot : Grade := ⟨false, false, false⟩

def meet (a b : Grade) : Grade :=
  ⟨a.noLoss && b.noLoss, a.noDup && b.noDup, a.order && b.order⟩

/-- `a ≤ b` means every axis `a` claims is claimed by `b`. `Bool`, so `decide`
needs no instance. -/
def le (a b : Grade) : Bool :=
  (!a.noLoss || b.noLoss) && (!a.noDup || b.noDup) && (!a.order || b.order)

theorem meet_comm (a b : Grade) : meet a b = meet b a
theorem meet_assoc (a b c : Grade) : meet (meet a b) c = meet a (meet b c)
theorem meet_idem (a : Grade) : meet a a = a
theorem meet_top (a : Grade) : meet a top = a
theorem meet_le_left (a b : Grade) : le (meet a b) a = true
theorem meet_le_right (a b : Grade) : le (meet a b) b = true

end Grade
```

Every one of those six proofs is `by cases a with | mk x y z => cases b with | mk p q r =>
cases x <;> cases y <;> … <;> rfl`, at most 64 leaves, no Mathlib, no `Fintype`, no `Decidable`
instance. This is the note's own ruling: "for a 3-element enum, from-scratch `meet` +
`decide`-style case proofs is the smaller trusted base"
(`/Users/pooks/Dev/effect-nats/packages/agents/notes/0002-lean-pass-a-contract.md:53`). Do not
reach for `Order.Lattice`; there is no Mathlib in this dependency graph and the algebra package
has no order at all.

The overclaim guard from `0002:33-34` becomes a theorem here, so that "meet is a join" stays
refutable:

```lean
theorem meet_is_not_join :
    ∃ a b : Grade, Grade.le a (Grade.meet a b) = false := by decide
```

### 3.5 The grade denotation and soundness

```lean
/-- A `Bool` version of `List.Nodup` over items, structurally recursive. -/
def nodupB : List Item → Bool
  | [] => true
  | a :: r => !(r.contains a) && nodupB r

/-- What a grade promises of one *run*: a word and the state it reached.
`noLoss` is not a word property; the residue is what makes it statable, which is
why the queue's characterizing equation mentions the buffer
(`EffectQueueLaws`/`SubHistory` shape). -/
def Grade.holds {S L : Type} [DecidableEq L]
    (R : Reading S L) (F : Failure L) (g : Grade) (w : List L) (s : S) : Bool :=
  (!g.noLoss || F.hit w || (R.acc w == R.del w ++ R.residue s)) &&
  (!g.noDup  || nodupB (R.del w)) &&
  (!g.order  || (R.del w ++ R.residue s).isPrefixOf (R.acc w))

/-- Soundness: a `Prop` quantifying over every run, whose body is the `Bool`
above. The Prop/Bool seam is exactly here and nowhere else. -/
def Machine.Sound {S L : Type} [DecidableEq L]
    (M : Machine S L) (R : Reading S L) (F : Failure L) (g : Grade) : Prop :=
  ∀ (w : List L) (s : S), M.run M.init w = some s → Grade.holds R F g w s = true
```

Three theorems, all cheap, all general:

```lean
/-- Antitone in the grade: a weaker grade is sound whenever a stronger one is.
Proof: `cases` on the six Bools, `simp`. -/
theorem Machine.sound_mono {S L : Type} [DecidableEq L] {M : Machine S L}
    {R : Reading S L} {F : Failure L} {g g' : Grade}
    (hle : Grade.le g' g = true) (h : M.Sound R F g) : M.Sound R F g'

/-- Meet-soundness at one machine: a corollary of `sound_mono` and `meet_le_left`. -/
theorem Machine.meet_sound_self {S L : Type} [DecidableEq L] {M : Machine S L}
    {R : Reading S L} {F : Failure L} {g₁ g₂ : Grade}
    (h : M.Sound R F g₁) : M.Sound R F (Grade.meet g₁ g₂)

/-- The grade is monotone in the failure model: a larger boundary set is a weaker
claim. -/
theorem Machine.sound_of_boundary_subset {S L : Type} [DecidableEq L] {M : Machine S L}
    {R : Reading S L} {F F' : Failure L} {g : Grade}
    (hsub : ∀ l, F.boundary.contains l = true → F'.boundary.contains l = true)
    (h : M.Sound R F g) : M.Sound R F' g
```

The boolean shape is chosen so that `sound_mono` is trivial: `!g'.x || X` is implied by
`!g.x || X` whenever `g'.x → g.x`, per axis, and `Grade.le` is exactly that implication.

### 3.6 Bundling a property with its anti-vacuity kit

A frozen theorem whose hypothesis is unsatisfiable is the failure mode this tree has already paid
for twice (`/Users/pooks/Dev/effect-nats-verified/docs/signature-snapshot.md:57-82`). The fix is
the Foldlab schema-family shape: put the law and its witnesses in one structure, so a property
without its kit does not elaborate
(`vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/Effects/Conformance.lean:18-22`).

Two families cover what a component needs. Both are parameterized by *carriers* in `Type`, never
by a predicate, so checklist 2.5 is not violated.

```lean
/-- A trace property with its kit: the property holds on every run under the
guard, there is a run that satisfies the guard, and there is a run that does not
and on which the property fails. The third field is what makes the guard
non-vacuous. -/
structure Guarded (S L : Type) where
  id : String
  sentence : String
  guard : List L → S → Bool
  claim : List L → S → Bool
  law : ∀ (w : List L) (s : S), guard w s = true → claim w s = true
  posWord : List L
  posState : S
  pos_guard : guard posWord posState = true
  negWord : List L
  negState : S
  neg_guard : guard negWord negState = false
  neg_claim : claim negWord negState = false

/-- A grade row with its kit: soundness at the declared grade, plus, per escape
clause, a run on which the escape actually fires. -/
structure Graded (S L : Type) [DecidableEq L] where
  id : String
  sentence : String
  machine : Machine S L
  reading : Reading S L
  failure : Failure L
  grade : Grade
  law : machine.Sound reading failure grade
  /-- One reachable witness per entry of `failure.escapes`, in order. -/
  escapeWitnesses : List (List L × S)
  escapes_reachable : ∀ p ∈ escapeWitnesses, machine.run machine.init p.1 = some p.2
  escapes_covered : escapeWitnesses.length = failure.escapes.length
  /-- The grade is not vacuous: some run reaches the boundary, and some does not. -/
  quietWord : List L
  quiet_clean : failure.hit quietWord = false

/-- The flat row both families project to, which is what the manifest holds.
Follows `…/Effects/Conformance/Ledger.lean:14-18`. -/
structure Entry where
  id : String
  family : String
  sentence : String
deriving DecidableEq, Repr, Inhabited

def Guarded.entry {S L : Type} (g : Guarded S L) : Entry :=
  ⟨g.id, "GUARDED", g.sentence⟩

def Graded.entry {S L : Type} [DecidableEq L] (g : Graded S L) : Entry :=
  ⟨g.id, "GRADED", g.sentence⟩
```

The `law` fields are `Prop`, the surrounding structure is `Type`, and `entry` is the erasure to
manifest data. That is the same proof-carrying-bundle-with-a-data-projection shape as
`CheckedFlow`/`erase` in the algebra package, and it is why the registry never needs a `Σ`.

The naming discipline that makes this navigable is worth adopting verbatim: "One name binds all
surfaces: ledger ID = Lean theorem name = manifest family = TypeScript test name"
(`vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/CONFORMANCE-WORKFLOW.md:201-202`).

### 3.7 Tests, suites, and mutants

```lean
/-- A test is data. `accept = false` is a negative test: the word must be refused. -/
structure Test (S L : Type) where
  name : String
  labels : List L
  accept : Bool := true
  /-- Expected residue at the reached state; unread when `accept = false`. -/
  residue : List Item := []
deriving Repr

def Test.run {S L : Type} (M : Machine S L) (R : Reading S L) (t : Test S L) : Bool :=
  match M.run M.init t.labels with
  | some s => t.accept && (R.residue s == t.residue)
  | none   => !t.accept

def Suite (S L : Type) := List (Test S L)

def Suite.run {S L : Type} (M : Machine S L) (R : Reading S L) (ts : Suite S L) : Bool :=
  ts.all (Test.run M R)

/-- A mutant is a replacement for one *hole* of the parametric skeleton, not for the
whole machine: this is `lean-model-0.3`'s `Mutant (F : Type)`
(`…/Effects/Conformance/Mutant.lean:14-18`) crossed with `applyWith deliver pull`
(`EffectNatsSubstrate/ApplyLaws.lean:7-8`). `represents` and `attacks` are the plain
sentences the register needs. -/
structure Mutant (S L : Type) where
  id : String
  attacks : String
  represents : String
  machine : Machine S L

/-- The suite kills the mutant. -/
def Mutant.killed {S L : Type} (R : Reading S L) (ts : Suite S L) (m : Mutant S L) : Bool :=
  !(Suite.run m.machine R ts)

/-- The suite is not vacuously discriminating: the mutant passes at least one test.
Without this, a suite that refuses everything kills every mutant
(`SubTraces.lean:372-373`). -/
def Mutant.survivesSome {S L : Type} (R : Reading S L) (ts : Suite S L) (m : Mutant S L) : Bool :=
  ts.any (Test.run m.machine R)
```

A component's mutant receipt is then two named theorems, both `by decide`:

```lean
theorem queue_mutants_killed :
    queueMutants.all (Mutant.killed queueReading queueTests) = true := by decide

theorem queue_mutants_not_vacuous :
    queueMutants.all (Mutant.survivesSome queueReading queueTests) = true := by decide
```

Mutant modules are quarantined by layout and never imported by the model, per
`…/Effects/Conformance/Mutant.lean:4-7`; only the receipt module imports both.

The mutant register gets the same treatment: `Mutant` below already carries `attacks` and
`represents`, and `#characterize` requires every `Guarded.id` and `Graded.id` in the manifest to
be some mutant's `attacks`. That turns "kill rates, not row counts"
(`…/CONFORMANCE-WORKFLOW.md:206`) into a compile-time obligation.

### 3.8 Pins

```lean
/-- A literal span of pinned source, addressed by bytes. Line numbers are recorded
as a convenience for a human reader and are never load-bearing: they do not survive
a pin move (`/Users/pooks/Dev/effect-nats-verified/AGENTS.md:26`), and the drift is
live (`releaseCapacity` moved head from `:2040` at rc.111 to `:2037` at rc.112). -/
structure Pin where
  /-- Path relative to the pinned package root, e.g. `"src/Queue.ts"`. -/
  file : String
  /-- SHA-256 of the whole file, lowercase hex. -/
  fileSha256 : String
  /-- Byte offset of the span, inclusive. -/
  start : Nat
  /-- Byte offset one past the span, exclusive. -/
  stop : Nat
  /-- SHA-256 of the span's bytes, lowercase hex. -/
  spanSha256 : String
  /-- Advisory: the line the span begins on at the pin. -/
  lineHint : Nat
deriving DecidableEq, Repr, Inhabited

instance : Effect4.Store.Canonical Pin :=
  ⟨fun p => Effect4.Store.encode
      (p.file, p.fileSha256, p.start, p.stop, p.spanSha256, p.lineHint)⟩

/-- The pins for one verb of a component, keyed by the verb's spelling. -/
structure Verb where
  label : String
  pins : List Pin
deriving DecidableEq, Repr
```

The digest itself is not computed in Lean: the tree's `Digest`/`sha256` is available
(`Effect4/Store/Digest.lean:32-37`), but running SHA-256 over a 60 KB source file inside the
kernel is exactly the `decide` budget violation of checklist 2.14. The pin's hex strings are
produced by a script and checked by a script; the Lean side checks only that the pin is
well-formed (64 hex chars, `start < stop`) and that the manifest's verb list matches the label
alphabet, both `by decide` over a small list.

The **hash level** of every pin theorem is Level 0 or Level 1, never Level 2, per the estate's
policy (`/Users/pooks/Dev/foldlab/library/machine/MACHINE-ALGEBRA.md:76-84`). Concretely, the
pin's meaning theorem is the collision *characterization*, which needs no premise at all:

```lean
/-- Two pins with one span digest either name the same bytes, or exhibit a
SHA-256 collision. The disjunction takes no hypothesis on the hash; discharging
its right branch is exactly what would require one. This is
`…/Effects/Cas/Address.lean:52-63` restated for spans. -/
theorem Pin.eq_or_collision {p q : Pin} (h : p.spanSha256 = q.spanSha256) :
    spanBytes p = spanBytes q ∨
      (spanBytes p ≠ spanBytes q ∧ hexOfSha256 (spanBytes p) = hexOfSha256 (spanBytes q))
```

Injectivity of SHA-256 appears only as a named premise on the few statements that want the
converse, exactly as `Effect4/Store/Store.lean:22-26` already does with digest freshness.

### 3.9 The manifest and the registry

```lean
/-- Where a component's evidence for one obligation comes from. This is
`…/2026-08-20-lean4-engineering-assurance-modeling.md:648-662`'s `EvidenceKind`
restricted to the kinds this API can produce, crossed with the vocabulary of
`docs/RUNTIME-COVERAGE.md:52` and `docs/LOWERING-COVERAGE.md:10-11`. The three
rungs of the sketch are the coarsening `pinned < replayed < proved`; the finer
enumeration is kept because a replay and an exhaustive decision are not the same
evidence and must not be reported as one. -/
inductive Evidence where
  /-- The bytes decide: a pin, and nothing more. -/
  | pinned
  /-- A kernel-checked theorem, with its expected axiom receipt. Green. -/
  | proved (witness : String) (axioms : String)
  /-- Complete over a named finite domain, by kernel `decide`. Green when the
      domain is the whole claim; otherwise partial. -/
  | exhaustivelyDecided (witness : String) (domain : String)
  /-- A finite fixture agreed with the real implementation. Never green: a host
      trace never turns a census row green (`docs/LOWERING-COVERAGE.md:10-11`). -/
  | replayed (harness : String)
  /-- An explicit premise this component does not establish. -/
  | assumed (premise : String)
  /-- A required link with no current evidence. -/
  | unknown
deriving DecidableEq, Repr

structure GradeRow where
  failure : String
  /-- One sentence per escape clause, mirroring `Failure.escapes`. -/
  escapes : List String
  grade : Grade
  evidence : Evidence
deriving DecidableEq, Repr

/-- One component, as store content. Everything is a `String`, a `Nat`, a `Bool`
or a list of those, so it derives `DecidableEq`, has a `Canonical` instance, and
can be named in the store by `[component]` (`Effect4/Store/Store.lean:72-83`). -/
structure Manifest where
  component : String
  /-- The label spellings, in constructor order. -/
  labels : List String
  verbs : List Verb
  /-- Names of the frozen `structure … : Prop` invariants. -/
  invariants : List String
  /-- Names of the frozen law theorems. -/
  laws : List String
  /-- The `Entry` projections of this component's `Guarded` and `Graded`
  bundles, in declaration order. Because an `Entry` can only be obtained from a
  bundle, and a bundle does not elaborate without its kit, a row here is
  evidence that the kit exists. -/
  entries : List Entry
  grades : List GradeRow
  /-- Names of the two suite receipts and the two mutant receipts. -/
  receipts : List String
  mutants : List String
deriving DecidableEq, Repr, Inhabited

instance : Effect4.Store.Canonical Manifest := …
```

The bridge from the typed machine to the monomorphic manifest:

```lean
/-- The spelling of a component's labels. Required to be injective on the
component's own finite label list, which is a `decide`d receipt in the
component's module, never an assumption. -/
structure Spelling (L : Type) where
  spell : L → String
  all : List L

def Spelling.injectiveB {L : Type} (S : Spelling L) : Bool :=
  (S.all.map S.spell).eraseDups.length == S.all.length
```

and each component proves `theorem queue_spelling_injective : queueSpelling.injectiveB = true :=
by decide`.

The registry is then a list of *names*, not of manifests, so that adding a component does not
re-elaborate the others:

```lean
/-- The registry names the components; each component's own module holds its
manifest, its receipts, and its `#characterize` invocation. This is deliberately
*not* a central list of manifests: a central list imports every component and makes
each addition an O(N) rebuild (checklist 2.20), which is the measured cost of
`Effect4Test/Concurrency/FiberAssurance.lean`
(`docs/research/2026-09-03-survey-lean-core.md:549-596`). -/
def registry : List String :=
  ["Queue", "PubSub", "Scope", "Fiber", "Ref", "Deferred", "Layer"]
```

and one metaprogram command, declared once, invoked in each component module:

```lean
/-- `#characterize queueManifest` checks, at elaboration time, that:
  * every name in `invariants` is a `structure … : Prop` in the environment;
  * every name in `laws` and `receipts` is a `theorem` (never a `def`, never a
    Prop-typed def: `docs/RUNTIME-COVERAGE.md:52`);
  * each one's `collectAxioms` output equals its declared receipt;
  * every `Entry.id` in `entries` is produced by a `Guarded`/`Graded` bundle
    declared in this module, so its kit exists;
  * every `Entry.id` and every `GradeRow.failure` appears as some mutant's
    `attacks` field: kill rates, not row counts
    (`…/CONFORMANCE-WORKFLOW.md:206`);
  * every `GradeRow.escapes` has the same length as its `Failure.escapes` and its
    bundle's `escapeWitnesses`;
  * `labels` is duplicate-free and equals the component's `Spelling.all` spellings;
  * every `Verb.label` is in `labels`;
  * every `Pin` is well-formed;
  * the `#check` ascription block in this module names exactly
    `invariants ++ laws ++ entries.map (·.id) ++ receipts`, in order.
This is `Effect4Test/Concurrency/FiberAssurance.lean:61-79` plus the ordered
snapshot cross-check of `Effect4Test/Audit/RuntimeCoverage.lean:25-30`, applied to
one component instead of to a whole lane. -/
syntax (name := characterizeCmd) "#characterize " term : command
```

### 3.10 How a second component is added

Exactly seven artefacts, in one new module plus one line elsewhere:

1. `PubSub/Machine.lean`: `PubSubState`, `PubSubLabel` (`deriving DecidableEq, Repr`), and
   `def pubsub (cap : Nat) : Machine PubSubState PubSubLabel`, each verb docstring citing its
   `Pin`.
2. `PubSub/Inv.lean`: one or more `structure … : Prop` with named clauses, and one
   `Inductive (pubsub cap) X` per invariant.
3. `PubSub/Reading.lean`: `pubsubReading : Reading …`, and the conservation theorem, if the
   component has one.
4. `PubSub/Grade.lean`: a `Graded PubSubState PubSubLabel` bundle, whose `law` field is
   `(pubsub cap).Sound pubsubReading shutdownFailure ⟨true, false, true⟩` and whose
   `escapeWitnesses` field carries one reachable run per escape clause. The bundle does not
   elaborate without them.
5. `PubSub/Tests.lean`: `pubsubTests : Suite …`, `pubsubMutants : List (Mutant …)`, and the four
   `by decide` receipts.
6. `PubSub/Manifest.lean`: the `#check` ascription block, `pubsubManifest : Manifest` (whose
   `entries` field is the `Entry` projections of the bundles), and `#characterize pubsubManifest`.
7. One string appended to `registry`.

Nothing in `Queue` is imported, mentioned, or re-elaborated. The only shared modules are
`Machine`, `Reading`, `Grade`, `Test`, `Pin`, `Manifest`, all of which are closed. This is the
property that fails today in the concurrency lane, where a single new theorem touches up to six
hand-maintained lists (`docs/research/2026-09-03-survey-lean-core.md:572-577`).

---

## 4. The Queue instance

Transliterated from `effect/src/Queue.ts` at rc.112, SHA-256
`dc355d1a09662ae7b023c98ad47b7fe71051becaf9d461f244c37ad0a4d3dc35`, 2114 lines, at
`/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/Queue.ts`. The construct spans
were opened at the lines cited. The starting point is
`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/EffectQueue.lean:45-131`, restated
against this API and against the rc.112 bytes.

### 4.1 Carriers

```lean
/-- The queue's four states. `closing e` is rc.112's `"Closing"` with the stored exit
(`Queue.ts:1013`); `done e` and `shutdown` are two readings of `"Done"`, kept apart
because `shutdown` finalizes with `exitInterrupt` (`Queue.ts:1198`). -/
inductive QStatus where
  | opened
  | closing (err : Nat)
  | done (err : Nat)
  | shutdown
deriving DecidableEq, Repr, Inhabited

structure QState where
  buffer : List Item
  status : QStatus
  /-- A `takeAll` parked on an open empty buffer: rc.112 parks the taker and
  `scheduleReleaseTaker` (`Queue.ts:667`, `:1969-1975`) resumes it later, so the
  release is scheduled, not inline. -/
  taker : Bool
deriving DecidableEq, Repr, Inhabited

/-- The verbs. Every answer is in the label (checklist 2.4): `takeAll` carries the
chunk it returns, `takeExit` the exit it returns. -/
inductive QLabel where
  /-- `Queue.ts:645-668`. -/
  | offer (item : Item)
  /-- `Queue.ts:1297-1298` through `takeBetween`'s drain at `:1994-1998`. -/
  | takeAll (chunk : List Item)
  /-- `takeUnsafe`'s `Done` arm, `Queue.ts:1606-1609`. -/
  | takeExit (err : Nat)
  /-- The taker parks: `takeAll` on an open empty buffer. -/
  | takePark
  /-- `releaseTakers`, `Queue.ts:1955-1967`; resumes on `Closing` too. -/
  | wake (chunk : List Item)
  /-- `failCauseUnsafe`, `Queue.ts:1000-1015`. -/
  | fail (err : Nat)
  /-- `Queue.ts:1191-1210`. -/
  | shutdown
deriving DecidableEq, Repr
```

### 4.2 The step

```lean
/-- The bounded queue at capacity `cap`. `Queue.bounded n = make { capacity: n }`
(`Queue.ts:500`) with the default `"suspend"` strategy (`Queue.ts:458`), so an offer
at capacity parks the publisher (`Queue.ts:649`, `:659`); this model *disables* that
step rather than typing it, so the boundary is explicit and a later slice gives it a
transition. -/
def queue (cap : Nat) : Machine QState QLabel where
  init := { buffer := [], status := .opened, taker := false }
  step := fun s l =>
    match l, s.status with
    -- offer: `Queue.ts:645-668`
    | .offer m, .opened =>
        if s.buffer.length < cap then some { s with buffer := s.buffer ++ [m] } else none
    | .offer _, _ => some s                                    -- `:647-648`, refused, no change
    -- takeAll: `:1297-1298`, `:1994-1998`, and `releaseCapacity` `:2037-2047`
    | .takeAll c, .opened =>
        if s.buffer ≠ [] ∧ c = s.buffer then some { s with buffer := [] } else none
    | .takeAll c, .closing e =>
        if s.buffer ≠ [] ∧ c = s.buffer then
          some { s with buffer := [], status := .done e } else none
    | .takeAll _, _ => none
    | .takeExit e, .done e' => if e = e' then some { s with status := .shutdown } else none
    | .takeExit _, _ => none
    | .takePark, .opened => if s.buffer = [] ∧ !s.taker then some { s with taker := true } else none
    | .takePark, _ => none
    -- wake: `releaseTakers` `:1955-1967`, which returns early only on `Done`
    | .wake c, .opened =>
        if s.taker ∧ s.buffer ≠ [] ∧ c = s.buffer then
          some { s with buffer := [], taker := false } else none
    | .wake c, .closing e =>
        if s.taker ∧ s.buffer ≠ [] ∧ c = s.buffer then
          some { s with buffer := [], status := .done e, taker := false } else none
    | .wake _, _ => none
    -- fail: `failCauseUnsafe` `:1000-1015`
    | .fail e, .opened =>
        some (if s.buffer.isEmpty then { s with status := .done e }
              else { s with status := .closing e })
    | .fail _, _ => some s                                     -- `:1001-1003`, no-op
    -- shutdown: `:1191-1210`
    | .shutdown, _ => some { buffer := [], status := .shutdown, taker := false }
```

Every arm is a `match` on a pair of finite inductives with `if` guards over `DecidableEq` on
`List Item` and `Nat`. There is no recursion, so `decide` on any trace reduces in time linear in
the trace length.

### 4.3 The invariant

```lean
/-- The queue's representation invariant, five named clauses, transliterated from
`EffectNatsSubstrate/RtInvariants.lean:25-36` with its recorded corrections: a parked
taker can coexist with a non-empty buffer, because `offer` appends and only
*schedules* the release (`Queue.ts:666-667`, `:1969-1975`). -/
structure QInv (cap : Nat) (s : QState) : Prop where
  takerLive : s.taker = true → s.status ≠ .shutdown
  doneEmpty : ∀ e, s.status = .done e → s.buffer = []
  closingNonempty : ∀ e, s.status = .closing e → s.buffer ≠ []
  shutdownClear : s.status = .shutdown → s.buffer = [] ∧ s.taker = false
  capacity : s.buffer.length ≤ cap

theorem qInv_inductive (cap : Nat) : Inductive (queue cap) (QInv cap)
```

The proof is a `cases l <;> cases s.status <;> split <;> constructor <;> simp`-shaped
case analysis, seven labels by four statuses, with the `closing`/`done` arms discharged by the
previous state's `closingNonempty`/`doneEmpty`. No induction over `Reach` appears; that is
`Inductive.reach`'s job, once.

### 4.4 The reading

```lean
def queueReading : Reading QState QLabel :=
  { accepts := fun l => match l with | .offer m => some m | _ => none
    emits := fun l => match l with
      | .takeAll c => c
      | .wake c => c
      | _ => []
    residue := fun s => s.buffer }
```

### 4.5 Equation (C), stated

```lean
/-- **Conservation.** On a run with no `fail` and no `shutdown`, everything offered
is exactly everything taken followed by what the buffer still holds, *in order*.

This is the queue's characterizing equation. `noLoss`, `noDup` and FIFO are all
corollaries of it: FIFO because the two sides are `List`s and equality of lists is
order-sensitive (checklist 2.9); `noLoss` at quiescence because `s.buffer = []`
collapses the right-hand side; `noDup` because `List.Nodup (acc w)` transfers to a
prefix of it.

The interior form, and the actual induction, is the *generalized* statement below:
the theorem as stated is its instance at `s₀ = (queue cap).init`, whose buffer is
`[]`. -/
theorem queue_conservation (cap : Nat) (w : List QLabel) (s : QState)
    (hclean : w.all (fun l =>
        match l with | .fail _ => false | .shutdown => false | _ => true) = true)
    (hrun : (queue cap).run (queue cap).init w = some s) :
    queueReading.acc w = queueReading.del w ++ s.buffer

/-- The generalized form the induction actually proves. -/
theorem queue_conservation_gen (cap : Nat) (w : List QLabel) (s₀ s : QState)
    (hinv : QInv cap s₀)
    (hclean : w.all (fun l =>
        match l with | .fail _ => false | .shutdown => false | _ => true) = true)
    (hrun : (queue cap).run s₀ w = some s) :
    queueReading.acc w ++ s₀.buffer = queueReading.del w ++ s.buffer
```

**What the induction is.** Structural induction on `w`, with `s₀` generalized and `QInv cap s₀`
carried. It is *not* an induction over `Reach`: the invariant enters as a hypothesis, discharged
once at the call site by `Inductive.reach qInv_inductive`. The seven step cases:

* `offer m`, enabled only on `.opened` with room: `acc` gains `m` at the front of its tail,
  `del` gains nothing, and the new buffer is `s₀.buffer ++ [m]`. The goal closes by
  `List.append_assoc` after rewriting `acc (offer m :: w') = m :: acc w'`.
* `takeAll c`, enabled only when `c = s₀.buffer ≠ []`: `del` gains `s₀.buffer`, the new buffer is
  `[]`. Both sides move by `s₀.buffer`, and `List.append_nil` closes it.
* `wake c`: identical to `takeAll` on the buffer, differing only in the `taker` field, which the
  reading does not observe.
* `takeExit e`: enabled only on `.done e`, where `QInv.doneEmpty` gives `s₀.buffer = []`, and the
  label emits nothing. Both sides are unchanged.
* `takePark`: enabled only on `.opened` with `s₀.buffer = []`, no reading changes.
* `fail _` and `shutdown`: excluded by `hclean`, so those arms are closed by `simp` on the
  hypothesis. This is where the failure model earns its place: the equation is stated *relative*
  to a boundary-free run, and the graded form of section 3.5 weakens it exactly when
  `Failure.hit w = true`.

The only clause of `QInv` the induction consumes is `doneEmpty`, in the `takeExit` case. That is
worth noticing: the conservation equation is nearly invariant-free, which is what makes it a
good characterizing statement rather than a derived one.

**The corollaries, stated.**

```lean
theorem queue_noLoss_at_quiescence (cap : Nat) (w : List QLabel) (s : QState)
    (hclean : …) (hrun : …) (hq : s.buffer = []) :
    queueReading.acc w = queueReading.del w

theorem queue_fifo (cap : Nat) (w : List QLabel) (s : QState) (hclean : …) (hrun : …) :
    (queueReading.del w ++ s.buffer).isPrefixOf (queueReading.acc w) = true

theorem queue_noDup (cap : Nat) (w : List QLabel) (s : QState) (hclean : …) (hrun : …)
    (hfresh : nodupB (queueReading.acc w) = true) :
    nodupB (queueReading.del w) = true
```

`hfresh` is a hypothesis on the *word*, not a theorem: a client that offers the same item twice
gets it delivered twice, and that is correct behaviour. The honest reading of `noDup` for a queue
is "the queue introduces no duplicates", which is what `queue_noDup` says.

**The graded statement, which is what the manifest carries.**

```lean
/-- The `crash` failure model: the two labels that end the queue. -/
def queueCrash : Failure QLabel :=
  { name := "shutdown-or-fail"
    boundary := [.shutdown] }   -- plus each `.fail e` the component's alphabet admits

theorem queue_graded (cap : Nat) :
    (queue cap).Sound queueReading queueCrash ⟨true, true, true⟩
```

with the proof: `intro w s hrun`, split on `Failure.hit w`; the `true` branch closes the
`noLoss` conjunct vacuously and the other two follow from the version of conservation that
survives a boundary label (the `closing`/`done` arms preserve the buffer, so the equation becomes
an inequality that `isPrefixOf` records); the `false` branch is `queue_conservation` verbatim.

**The tests and the mutants.**

```lean
def queueTests : Suite QState QLabel :=
  [ { name := "drain", labels := [.offer 1, .offer 2, .takeAll [1,2]], residue := [] }
  , { name := "fifo", labels := [.offer 1, .offer 2, .takeAll [1,2], .offer 3], residue := [3] }
  , { name := "park-then-wake", labels := [.takePark, .offer 1, .wake [1]], residue := [] }
  , { name := "closing-keeps-buffer", labels := [.offer 1, .fail 7, .takeAll [1]], residue := [] }
  , { name := "shutdown-discards", labels := [.offer 1, .shutdown], residue := [] }
  , { name := "over-capacity-refused", labels := [.offer 1, .offer 2], accept := false }
  , { name := "one-at-a-time-refused", labels := [.offer 1, .offer 2, .takeAll [1]]
    , accept := false } ]

def queueMutants : List (Mutant QState QLabel) :=
  [ { id := "Q-W1", attacks := "queue_conservation"
    , represents := "Killing this mutant shows the tests notice a take that drains one element instead of the whole buffer."
    , machine := queueW1 }
  , { id := "Q-W2", attacks := "queue_graded"
    , represents := "Killing this mutant shows the tests notice a fail that discards a non-empty buffer instead of keeping it (Queue.ts:1006-1014)."
    , machine := queueW2 }
  , { id := "Q-W3", attacks := "queue_noLoss_at_quiescence"
    , represents := "Killing this mutant shows the tests notice a shutdown that delivers the buffer instead of discarding it (Queue.ts:1196)."
    , machine := queueW3 } ]
```

Note that `Q-W1` is the same mutant that the *frame laws* failed to exclude
(`ApplyLaws.lean:171-175`), and that here it is killed by the `drain` and `one-at-a-time-refused`
tests. That is the whole argument for tests being part of the component and not an afterthought.

---

## 5. Composition

### 5.1 What composition is, in this design

Two components in one system do not compose by product. They compose by both being *refined* by
a composite machine, and the grade of the composite is the meet of the grades that survive the
refinement.

```lean
/-- `N` refines `M` along a label projection `π` and a state abstraction `σ`.
A composite label that `π` forgets must leave `M`'s abstraction unchanged, which is
the standard stuttering condition. -/
structure Refines {S L S' L' : Type} (N : Machine S' L') (M : Machine S L)
    (π : L' → Option L) (σ : S' → S) : Prop where
  init : σ N.init = M.init
  step : ∀ {s s' : S'} {l' : L'}, N.step s l' = some s' →
    match π l' with
    | some l => M.step (σ s) l = some (σ s')
    | none   => σ s' = σ s

/-- Refinement lifts from steps to runs, by induction on the word. -/
theorem Refines.run {S L S' L' : Type} {N : Machine S' L'} {M : Machine S L}
    {π : L' → Option L} {σ : S' → S} (h : Refines N M π σ)
    {w' : List L'} {s' : S'} (hr : N.run N.init w' = some s') :
    M.run M.init (w'.filterMap π) = some (σ s')
```

`Refines.run` is a genuine, cheap, core-Lean theorem: induction on `w'`, `cases π l'`, one
`List.filterMap_cons` rewrite per case. Perhaps thirty lines.

### 5.2 Transporting a grade along a refinement

```lean
/-- Read the composite's word through `π` and its state through `σ`. -/
def Reading.comap {S L S' L' : Type} (R : Reading S L) (π : L' → Option L) (σ : S' → S) :
    Reading S' L' :=
  { accepts := fun l' => (π l').bind R.accepts
    emits := fun l' => ((π l').map R.emits).getD []
    residue := fun s' => R.residue (σ s') }

def Failure.comap {L L' : Type} (F : Failure L) (π : L' → Option L) (all' : List L') :
    Failure L' :=
  { name := F.name
    boundary := all'.filter (fun l' => match π l' with
      | some l => F.boundary.contains l | none => false) }

/-- The transport theorem. Needs two `filterMap` commutation lemmas:
`acc (R.comap π σ) w' = R.acc (w'.filterMap π)` and the same for `del`. -/
theorem Machine.sound_of_refines {S L S' L' : Type} [DecidableEq L] [DecidableEq L']
    {N : Machine S' L'} {M : Machine S L} {π : L' → Option L} {σ : S' → S}
    {R : Reading S L} {F : Failure L} {g : Grade} {all' : List L'}
    (hcover : ∀ l' : L', l' ∈ all')
    (h : Refines N M π σ) (hs : M.Sound R F g) :
    N.Sound (R.comap π σ) (F.comap π all') g
```

`hcover` is the finiteness obligation: `Failure.comap` needs the composite's label list, which is
per-component data, not a `Fintype`. In practice `all'` is the composite's `Spelling.all` and
`hcover` is a `decide`d receipt.

### 5.3 `meet_sound` for two components

```lean
/-- Two components refined by one composite, read through the *same* composite
reading. The grade of the composite is the meet. -/
theorem Machine.meet_sound {S₁ L₁ S₂ L₂ S' L' : Type} [DecidableEq L'] [DecidableEq L₁]
    [DecidableEq L₂]
    {M₁ : Machine S₁ L₁} {M₂ : Machine S₂ L₂} {N : Machine S' L'}
    {π₁ : L' → Option L₁} {σ₁ : S' → S₁} {π₂ : L' → Option L₂} {σ₂ : S' → S₂}
    {R₁ : Reading S₁ L₁} {R₂ : Reading S₂ L₂} {R : Reading S' L'}
    {F : Failure L'} {g₁ g₂ : Grade}
    (h₁ : Refines N M₁ π₁ σ₁) (h₂ : Refines N M₂ π₂ σ₂)
    (hs₁ : M₁.Sound R₁ F₁ g₁) (hs₂ : M₂.Sound R₂ F₂ g₂)
    -- the reading-agreement obligation, per pair:
    (hagree₁ : ∀ w' s', N.run N.init w' = some s' →
        Grade.holds (R₁.comap π₁ σ₁) (F₁.comap π₁ all') g₁ w' s' = true →
        Grade.holds R F g₁ w' s' = true)
    (hagree₂ : ∀ w' s', N.run N.init w' = some s' →
        Grade.holds (R₂.comap π₂ σ₂) (F₂.comap π₂ all') g₂ w' s' = true →
        Grade.holds R F g₂ w' s' = true) :
    N.Sound R F (Grade.meet g₁ g₂)
```

The proof body is short: transport each grade by `sound_of_refines`, move each through its
`hagree`, then use `sound_mono` with `meet_le_left`/`meet_le_right` and conclude by conjunction
of axes. Maybe fifteen lines.

### 5.4 What is honestly provable in core-only Lean, and what is not

**Provable, once, generically, and cheaply:**

* `Refines.run`, by list induction.
* `sound_of_refines`, by two `filterMap` commutation lemmas.
* `sound_mono`, `meet_sound_self`, `sound_of_boundary_subset`, by `cases` on Bools.
* The `Grade` lattice laws, by `cases` on Bools.
* `accepts_prefix`, `Inductive.reach`, `reach_ind`, by list and `Reach` induction.

**Per pair of components, and expensive:** the `hagree` hypotheses. They say that the composite's
own reading of a delivery agrees with what each component's reading sees through its projection.
That is the entire content of a composition claim, and it is not a corollary of anything. The
evidence for the price is `SimProof.lean`, 3648 lines for one such relation, with the design note
explaining why an off-the-shelf simulation combinator did not fit
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/Sim.lean:14-25`).

**Not provable and not attempted here:** that a composite of two grade-sound components is
automatically grade-sound at the meet with *no* agreement hypothesis. It is false in general: a
composite can lose an item in the seam between two components each of which loses nothing. The
`hagree` hypothesis is where that would be caught, and the API's job is to make it impossible to
state the composition theorem without it. That is why `hagree` is an explicit argument rather
than an instance or a field.

**A second thing not attempted:** a general parallel composition of two components' *label
alphabets*. The effect-nats ruling applies: "ordering guarantees compose differently; keep them a
separate grade axis (do not force one monoid)"
(`/Users/pooks/Dev/effect-nats/packages/agents/notes/0003-graded-algebra-model.md:29-31`). The
`order` axis of `Grade` must be understood as per-component FIFO, and a system-level ordering
claim is a different statement about the composite, not a meet of component claims.

---

## 6. Risks and open questions, ranked

**R1. The `hagree` obligation is the whole product and it is not cheap.** The generic composition
theorems in section 5 are correct and cheap, and they push all the difficulty into two
hypotheses that no library can discharge. If the goal is "a registry of components that compose",
the registry composes *statements*, not proofs. Mitigation: make each `hagree` a named theorem
with a `#check` ascription and a `Rung`, so an uncomposed pair is *visibly* uncomposed rather
than silently assumed. Do not ship a `Composed` typeclass.

**R2. `decide` budget on trace suites and enumerations.** The queue's seven tests reduce in
linear time, but an acceptance-set enumeration in the style of `SubPlacements.outcomesFrom`
(`SubPlacements.lean:67-77`) grows with placements per gap and is the thing that will eventually
blow the heartbeat. Survey finding 22 is the recorded precedent
(`docs/research/2026-09-03-survey-lean-core.md:762-792`). Mitigation: state the term size in each
`decide`d theorem's docstring; keep enumerations in a separate module so a limit failure is
localized; prefer many small `decide`s to one aggregate.

**R3. Manifest drift.** A manifest that is a hand-authored list of strings drifts from the
environment. The `#characterize` command must fail loudly on every mismatch, and the ascription
block must be *ordered*, matching the RuntimeCoverage cross-check
(`Effect4Test/Audit/RuntimeCoverage.lean:25-30`). Open question: whether the manifest's
`invariants`/`laws`/`properties` lists should be *derived* from the environment (all theorems
declared in the component's namespace) rather than authored. Derived is more robust but loses the
ability to declare something deliberately out of the frozen surface. The measured cost of the
authored direction is survey finding 15; the measured benefit is that the surface is exact.
Recommendation: authored for the frozen surface, derived for the *completeness* check (every
theorem in the namespace is either in the manifest or explicitly listed as private).

**R4. The `Grade` record is a freeze surface.** Adding a fourth axis changes `Grade`'s
`DecidableEq`, `Canonical` encoding, and every stored manifest's digest. That is by design, but it
means the axis set must be decided before the store is populated. Open question: which axes.
`noLoss`, `noDup`, `order` cover the queue; `PubSub` will want a per-subscriber axis; `Scope` will
want an ordering axis over finalizers that is not the same `order`. Recommendation: enumerate the
axes for all seven planned components *before* writing `Grade`, and accept a wider record with
mostly-`false` fields rather than a later revision.

**R5. Item identity as `Nat` is a two-faced number.** The tree already recorded this exact
hazard: "the handle index is per-family here and global on the host", so `op set [0, 9]` answers
`1` on the host and `0` in the model, and `E4-SEM-CE-014` refuses to compare the numbers until
the tail reconciles the counters (`Effect4/Stateful/RefFamily.lean:85-100`). A `replayed` rung for
a component will hit this the first time a fixture compares item ids. Mitigation: the reading's
`Item` is a *model-local* id, and a replay harness must supply an explicit renaming, recorded as
part of the `replayed` rung's harness name.

**R6. Pin staleness.** Byte offsets survive an edit no better than lines; what survives is the
span digest. A pin move must therefore recompute `fileSha256`, `start`, `stop` and `spanSha256`
together, and any mismatch must fail the gate rather than warn. Open question: whether to store
the span *bytes* as store content so the pin is self-verifying without the source tree present.
That would make a component's pins re-checkable offline, at a cost of a few kilobytes per
component. My recommendation is yes, because the only pinned `Queue.ts` on this machine is in a
`node_modules` directory outside the repository, which is not a durable location.

**R7. The Prop/Bool seam can drift.** `Grade.holds` and `Machine.Sound` are two statements of one
idea. They are tied by `Sound`'s definition, which is the right construction, but a future
"optimization" of `holds` silently changes what every `Sound` theorem means. Mitigation: freeze
`holds` by `#check` ascription like any theorem, and add a `decide`d receipt pinning `holds` on a
handful of literal runs, so a change to it fails a test rather than quietly re-interpreting a
theorem.

**R8. Mutant adequacy.** Three mutants per component is a number chosen by intuition. The design
above makes the coverage obligation mechanical (`#characterize` requires every `Entry.id` and
every `GradeRow.failure` to be some mutant's `attacks`), which is the cheapest real quality gate
here and matches the ratified floor "one hand-declared mutant per obligation-ledger falsification
case … named by the obligation it attacks"
(`vendor/foldlab/pinned/tree/library/effects/archive/lean-model-0.3/CONFORMANCE-WORKFLOW.md:206-210`).
What it does not give is a *kill rate*: the estate's own metric is that "Row counts do not measure
coverage; kill rates do" (`:206`) and that kill rate "is quoted as evidence, never as proof"
(`:140`). Open question: whether to report a per-component kill rate at all, given that here the
kills are `decide`d theorems rather than an `IO` run, so a survivor is a build failure rather than
a number. My view is that a survivor should be a build failure and no rate should be published.

**R9. The `order` axis conflates two things.** `isPrefixOf (del ++ residue) (acc)` is FIFO for a
single-producer single-consumer queue. For a `PubSub` with several subscribers it is false as
stated, and the right statement is per-subscriber. Open question: whether `Reading` should be
indexed by a *client* (`Reading S L Client` with `emits : Client → L → List Item`), which is what
`rtHistory s id` does in the working model (`Runtime.lean:100-103`). My recommendation is to add
the client index now rather than later, because retrofitting it changes every grade statement.

**R10. A vacuous grade is the failure this design must be judged against.** Checklist 2.21 says the
carrier must be able to express the grade's failure, and the recorded precedent is that keeping
`externalEffects : Key → Nat` beside `activityReceipts : Key → Bool` is what "preserves the
exactly-once counterexample rather than assuming it away"
(`/Users/pooks/Dev/jetstream-workflow-model/formal/jetstream_workflows/docs/domain-contract.md:138-139`).
The queue design above passes this test for `noDup` only because `Item = Nat` and the reading
counts occurrences in a `List`; a design that had used a set would have made `noDup` true by
construction. Every new component needs this check made explicitly and recorded, and the
`Graded` bundle's `quietWord` field is only half of it. Open question: whether to add a
`vacuityMutant` field to `Graded` naming the mutant that violates this grade, so the check is a
field rather than a review step.

**R11. The schema-family bundles are `Type`-level records with `Prop` fields, and they will be
the slowest thing to elaborate in a component module.** Each `Graded` instance carries a
`Machine`, a `Reading`, a `Failure`, a proof of `Sound`, and a list of witnesses with two proofs
about it. The tree has no measurement of this shape at scale; the nearest number is that the
largest existing modules cost 8 to 14 seconds dominated by `simp` and type checking
(`docs/research/2026-09-03-survey-lean-core.md:933-943`). Mitigation: keep each bundle in its own
module so the cost is per-component and parallel, and never put two components' bundles in one
file.

**R12. Nothing here has been elaborated.** This report contains signatures, not a compiled
module. The three specific things I expect to bite on first contact: the `match l, s.status`
pattern in `queue` may need the arms reordered for the equation compiler to produce usable
`step_*` equations; `Reading.comap`'s `emits` uses `Option.map … |>.getD []` which will not
`simp` through `filterMap` without a helper lemma; and `Failure.comap`'s dependence on `all'`
makes `sound_of_refines` carry a finiteness argument that may be more pleasant as a
`Spelling L'` field. None of these is structural, but a Pass B freeze should follow a compiled
Pass A skeleton, exactly as
`/Users/pooks/Dev/effect-nats/packages/agents/notes/0002-lean-pass-a-contract.md:3-5` prescribes:
"approved for exploratory modeling (first slice; representations may still move; **Pass B freezes
signatures before serious proof work**)".
