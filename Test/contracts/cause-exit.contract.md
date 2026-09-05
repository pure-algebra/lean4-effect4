# Cause and Exit first-order data contract

Status: FROZEN / RED, breaker-authored 2026-09-01

Implementation fence:
`Effect4/Semantics/{Cause,Exit}.lean`

Lean battery:
`Test/Machine/Semantics/CauseExitContract.lean`

Axiom report:
`Test/Machine/Semantics/CauseExitAxiomReport.lean`

Counterexamples: `E4-SEM-CE-001` through `E4-SEM-CE-007` in
`Test/Counterexamples/REGISTER.md`; witnesses in
`Test/Counterexamples/Machine/Semantics/CauseExit.lean`; attack shapes in
`git:c407ab7:test/counterexamples/semantics/ATTACKS.md`

Proof graph: `CAUSE-PG-FLAT` in `docs/research/CAUSE-DAG.md`

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` section 8.

## Claim boundary

This packet freezes one bounded model: Effect v4's `Cause` and `Exit` as
first-order data over four externally admitted alphabets — the typed error `ε`,
the defect `δ`, the interruptor identity `ι`, and the annotation value `α`.

It does not implement the model. It does not model effect syntax, primitives,
continuation frames, the run loop, fibers, scopes, schedulers, host `Error`
objects, stack traces, spans, hashing, JSON rendering, or pretty printing. It
makes no Effect TypeScript compatibility claim and no code-generation claim.

It does **not** claim that `Effect4.Cause` is equivalent to rc.112's `Cause`.
It claims that each named clause of each named census row below has an exact
theorem over the Effect4 model, and it names, in three `CAUSE-FB-*` rows of
`docs/research/CAUSE-DAG.md`, exactly what was dropped: the `WeakMap` host-identity
annotation memory, reference equality on annotation maps and on the combine
short circuit, and the host `Error` message bytes of the last two squash arms.

## CATEGORIES

- `inductive-data` — annotations, reason tags, reasons, causes, squash
  observations, and exits are first-order data parameterized by externally
  owned alphabets;
- `total-functions` — every operation is a total, kernel-reducible function
  over finite data; there is no relation, no fuel, and therefore no determinism
  theorem to state;
- `algebraic-laws` — combine identity, union order, deduplication, squash arm
  selection, annotation merge, finalizer merge, and the void join;
- `counterexamples` — seven finite proved witnesses force the representation;
- `claim-scope` — the pinned host boundary is named, not silently modelled, and
  `exit.success-failure` is declared partial rather than green.

## REQUIRES

1. Lean core and Std at the repository's pinned toolchain. No Mathlib.
2. `src/Effect4/Machine/Cause.lean` and `src/Effect4/Machine/Exit.lean` import
   nothing from `Effect4/Concurrency/`, `Effect4/Runtime/`, `Effect4/Layer/`,
   `Effect4/Channel/`, or any other area above Semantics in
   `docs/ARCHITECTURE.md` "Dependency direction". `Exit.lean` may import
   `Cause.lean`; `Cause.lean` may import `Std`.
3. `ε`, `δ`, `ι`, and `α` are opaque parameters. No constructor, decidable
   equality, order, or default value of any of them is assumed beyond the
   instance binders written in the frozen signatures.
4. `DecidableEq` is derived, never classical. `Classical.choice`,
   `native_decide`, `sorry`, `admit`, `partial`, `unsafe`, and new axioms are
   not allowed in the packet or the implementation. The axiom ceiling for every
   public theorem is `propext` and `Quot.sound`.
5. Universe policy: one explicit `universe u`; every alphabet is `Type u`. See
   the open question at the end of this file.
6. `Effect4.Annotations` is already owned by `src/Effect4/Schema/Payload.lean`.
   This packet's annotation carrier is therefore `Effect4.ReasonAnnotations`,
   and no conversion between the two is declared.

## Public declarations

Binder names may differ. Public names, constructor order and fields, argument
roles, result types, and theorem propositions are frozen by the Lean battery's
`#check (@name : proposition)` ascriptions. The battery is the authority; the
Lean shown here is a reading aid.

### Existing-type and duplicate-prevention rows

The six rows, their owners, relationships, pins, and assurance routes are in
`docs/research/CAUSE-DAG.md` "Existing-type rows". They are not restated here.

### D0 — annotations

```lean
structure ReasonAnnotations (α : Type u) where
  entries : List (String × α)
  keysNodup : (entries.map Prod.fst).Nodup
deriving DecidableEq

ReasonAnnotations.empty    : ReasonAnnotations α
ReasonAnnotations.keys     : ReasonAnnotations α -> List String
ReasonAnnotations.lookup   : ReasonAnnotations α -> String -> Option α
ReasonAnnotations.annotate :
  ReasonAnnotations α -> ReasonAnnotations α -> Bool -> ReasonAnnotations α
```

The stored list is insertion-ordered with unique keys, exactly like the
rc.112 `ReadonlyMap<string, unknown>`. It is proof-carrying: a duplicate-key
spelling is unconstructible, and `keysNodup` is the only admission boundary.
`Repr` is deliberately **not** derived, because the proof field has none.

`Effect4.Data.Row` is not reused: it is the canonical finite *set*, stores no
values, needs a lawful order on its element type, and erases both order and
duplicates. See `docs/research/CAUSE-DAG.md` separation 3.

### D1 — the reason alphabet

```lean
inductive ReasonTag
  | fail
  | die
  | interrupt
deriving DecidableEq, Repr

ReasonTag.all : List ReasonTag

inductive Reason (ε δ ι α : Type u)
  | fail (error : ε) (annotations : ReasonAnnotations α)
  | die (defect : δ) (annotations : ReasonAnnotations α)
  | interrupt (interruptor : Option ι) (annotations : ReasonAnnotations α)
deriving DecidableEq

Reason.tag         : Reason ε δ ι α -> ReasonTag
Reason.annotations : Reason ε δ ι α -> ReasonAnnotations α
Reason.error?      : Reason ε δ ι α -> Option ε
Reason.defect?     : Reason ε δ ι α -> Option δ
Reason.annotate    :
  Reason ε δ ι α -> ReasonAnnotations α -> Bool -> Reason ε δ ι α
```

`Option ι` is rc.112's `fiberId: number | undefined`. `undefined` is a real
inhabitant produced by `runFork`'s `AbortSignal` and by `Exit.interrupt()`, so
it is `none`, not an error.

There is no fourth constructor and no nesting. `Reason` is where the
concurrency representative's terminal alphabet `τ` may later be instantiated;
it is not a copy of it, and this packet imports nothing from Concurrency.

### D2 — the flat cause

```lean
structure Cause (ε δ ι α : Type u) where
  reasons : List (Reason ε δ ι α)
deriving DecidableEq

Cause.empty     : Cause ε δ ι α
Cause.fail      : ε -> Cause ε δ ι α
Cause.die       : δ -> Cause ε δ ι α
Cause.interrupt : Option ι -> Cause ε δ ι α
Cause.annotate  : Cause ε δ ι α -> ReasonAnnotations α -> Bool -> Cause ε δ ι α
Cause.dedup     : List (Reason ε δ ι α) -> List (Reason ε δ ι α)
Cause.combine   : Cause ε δ ι α -> Cause ε δ ι α -> Cause ε δ ι α
Cause.squash    : Cause ε δ ι α -> Squashed ε δ
```

One field. No sequential node, no parallel node, no depth, no empty
constructor distinct from an empty list. `dedup`, `combine`, and every theorem
mentioning them carry `[DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
[DecidableEq α]`.

`Cause.dedup` is first-occurrence deduplication and is structurally recursive:

```lean
Cause.dedup [] = []
Cause.dedup (reason :: rest) =
  reason :: (Cause.dedup rest).filter (fun other => decide (other ≠ reason))
```

Both equations are frozen, so `dedup` may not be replaced by an
order-destroying or last-occurrence variant. No `termination_by` or
`decreasing_by` is needed.

### D3 — squash and exit

```lean
inductive Squashed (ε δ : Type u)
  | error (error : ε)
  | defect (defect : δ)
  | interruptedWithoutError
  | emptyCause
deriving DecidableEq

inductive Exit (β ε δ ι α : Type u)
  | success (value : β)
  | failure (cause : Cause ε δ ι α)
deriving DecidableEq

Exit.void                   : Exit Unit ε δ ι α
Exit.isSuccess              : Exit β ε δ ι α -> Bool
Exit.cause?                 : Exit β ε δ ι α -> Option (Cause ε δ ι α)
Exit.causeReasons           : Exit β ε δ ι α -> List (Reason ε δ ι α)
Exit.mergeFinalizer         :
  Exit β ε δ ι α -> Exit Unit ε δ ι α -> Exit Unit ε δ ι α
Exit.restoreAfterFinalizer  :
  Exit β ε δ ι α -> Exit Unit ε δ ι α -> Exit β ε δ ι α
Exit.asVoidAll              : List (Exit β ε δ ι α) -> Exit Unit ε δ ι α
```

`Squashed` has **four** constructors. `causeSquash` at
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:298-309` ends with
`return new globalThis.Error("Empty cause")` after the three partition tests.
The `cause.squash` census summary names only the first three; both are
recorded in `docs/research/CAUSE-DAG.md` under "Census-summary note", and every clause
of the current summary still has a theorem.

`Squashed` carries no annotations and has no inverse. It is a lossy projection
used by rc.112's throwing entry points, not a second cause carrier.

## ENSURES — public theorem spine

Every proposition below is frozen in the Lean battery by exact ascription. A
weaker statement does not satisfy this contract.

### Annotation laws (census: cause.annotations)

```lean
ReasonAnnotations.keys_eq   : self.keys = self.entries.map Prod.fst
ReasonAnnotations.keys_nodup : self.keys.Nodup
ReasonAnnotations.lookup_eq :
  self.lookup key =
    (self.entries.find? (fun entry => decide (entry.fst = key))).map Prod.snd
ReasonAnnotations.ext : left.entries = right.entries -> left = right
ReasonAnnotations.empty_entries : ReasonAnnotations.empty.entries = []
ReasonAnnotations.lookup_empty : ReasonAnnotations.empty.lookup key = none
```

The merge shape is frozen exactly, because the position of an overwritten key
is observable:

```lean
ReasonAnnotations.annotate_entries :
  (self.annotate extra overwrite).entries =
    self.entries.map (fun entry =>
      if overwrite = true then
        match extra.lookup entry.fst with
        | some value => (entry.fst, value)
        | none => entry
      else entry) ++
    extra.entries.filter (fun entry => decide (entry.fst ∉ self.keys))
```

Existing keys keep their slot; a new key is appended in `extra`'s order. The
four observational laws and the identity follow:

```lean
ReasonAnnotations.annotate_empty :
  self.annotate ReasonAnnotations.empty overwrite = self
ReasonAnnotations.annotate_keys :
  (self.annotate extra overwrite).keys =
    self.keys ++ extra.keys.filter (fun key => decide (key ∉ self.keys))
ReasonAnnotations.lookup_annotate_kept :
  self.lookup key = some value ->
    (self.annotate extra false).lookup key = some value
ReasonAnnotations.lookup_annotate_new :
  self.lookup key = none -> extra.lookup key = some value ->
    (self.annotate extra overwrite).lookup key = some value
ReasonAnnotations.lookup_annotate_overwrite :
  extra.lookup key = some value ->
    (self.annotate extra true).lookup key = some value
ReasonAnnotations.lookup_annotate_absent :
  self.lookup key = none -> extra.lookup key = none ->
    (self.annotate extra overwrite).lookup key = none
```

`annotate_empty` is the modelled half of rc.112's `if (annotations.mapUnsafe
.size === 0) return this` guard at `internal/core.ts:207`.

Two facts about equality are frozen rather than assumed:

```lean
ReasonAnnotations.order_retained :
  exists left right : ReasonAnnotations Nat,
    (forall key : String, left.lookup key = right.lookup key) /\ left ≠ right

Reason.host_memory_refused :
  forall (recall : ε -> ReasonAnnotations α) (left right : ε),
    left = right -> recall left = recall right
```

The first proves this model's annotation equality is *not* extensional: it is
strictly finer than key-to-value content equality, which is the direction that
keeps it a sound over-approximation of rc.112's reference equality. The second
is the theorem-shaped refusal of `CAUSE-FB-WEAKMAP`: any Effect4 recall of the
`annotationsMap` (`internal/core.ts:178`, read at `:197`) is a function of the
*value*, so the host object-identity distinction is not representable here.

### Reason laws (census: cause.reason-fail, cause.reason-die,
cause.reason-interrupt, exit.reason-alphabet)

```lean
ReasonTag.all_nodup     : ReasonTag.all.Nodup
ReasonTag.mem_all       : forall tag, tag ∈ ReasonTag.all
ReasonTag.cases_receipt :
  forall tag, tag = .fail \/ tag = .die \/ tag = .interrupt

Reason.tag_fail / tag_die / tag_interrupt
Reason.annotations_fail / annotations_die / annotations_interrupt
Reason.error_fail / error_die / error_interrupt
Reason.defect_fail / defect_die / defect_interrupt

Reason.fail_inj :
  Reason.fail leftError leftAnnotations = Reason.fail rightError rightAnnotations
    <-> leftError = rightError /\ leftAnnotations = rightAnnotations
Reason.die_inj      : (same shape for the defect)
Reason.interrupt_inj : (same shape for the optional interruptor)

Reason.cases_receipt :
  (exists error annotations, reason = Reason.fail error annotations) \/
  (exists defect annotations, reason = Reason.die defect annotations) \/
  (exists interruptor annotations,
    reason = Reason.interrupt interruptor annotations)
Reason.tag_mem_all : reason.tag ∈ ReasonTag.all

Reason.annotate_tag :
  (reason.annotate extra overwrite).tag = reason.tag
Reason.annotate_annotations :
  (reason.annotate extra overwrite).annotations =
    reason.annotations.annotate extra overwrite
```

`interrupt_inj` is the `cause.reason-interrupt` equality clause: the optional
interruptor and the annotations are compared together. `cases_receipt` plus
`ReasonTag.cases_receipt` and `mem_all` are the whole of
`exit.reason-alphabet`: three cases, no fourth.

### Cause laws (census: cause.flat-reasons, rule.cause-has-no-structure)

```lean
Cause.ext     : left.reasons = right.reasons -> left = right
Cause.eq_iff  : left = right <-> left.reasons = right.reasons
Cause.eq_iff_pointwise :
  left = right <->
    (left.reasons.length = right.reasons.length /\
      forall index : Nat, left.reasons[index]? = right.reasons[index]?)

Cause.empty_reasons     : Cause.empty.reasons = []
Cause.fail_reasons      :
  (Cause.fail error).reasons = [Reason.fail error ReasonAnnotations.empty]
Cause.die_reasons       :
  (Cause.die defect).reasons = [Reason.die defect ReasonAnnotations.empty]
Cause.interrupt_reasons :
  (Cause.interrupt interruptor).reasons =
    [Reason.interrupt interruptor ReasonAnnotations.empty]
Cause.annotate_reasons  :
  (self.annotate extra overwrite).reasons =
    self.reasons.map (fun reason => reason.annotate extra overwrite)
```

`eq_iff_pointwise` is the rc.112 `CauseImpl[Equal.symbol]` shape at
`internal/core.ts:166-172`: equal length and pairwise-equal ordered reasons.
`ext` plus one field is `rule.cause-has-no-structure`'s first half: a cause is
determined by its reason list, so there is nowhere to hide a sequential or
parallel node.

### Deduplication and combine (census: cause.combine-union,
rule.cause-has-no-structure)

```lean
Cause.dedup_nil       : Cause.dedup [] = []
Cause.dedup_cons      :
  Cause.dedup (reason :: rest) =
    reason :: (Cause.dedup rest).filter (fun other => decide (other ≠ reason))
Cause.mem_dedup       : reason ∈ Cause.dedup list <-> reason ∈ list
Cause.dedup_nodup     : (Cause.dedup list).Nodup
Cause.dedup_of_nodup  : list.Nodup -> Cause.dedup list = list

Cause.combine_empty_left  : Cause.combine Cause.empty that = that
Cause.combine_empty_right : Cause.combine self Cause.empty = self
Cause.combine_reasons     :
  self.reasons ≠ [] -> that.reasons ≠ [] ->
    (Cause.combine self that).reasons =
      Cause.dedup (self.reasons ++ that.reasons)
Cause.mem_combine :
  reason ∈ (Cause.combine self that).reasons <->
    reason ∈ self.reasons \/ reason ∈ that.reasons
Cause.combine_no_new_reason :
  reason ∈ (Cause.combine self that).reasons ->
    reason ∈ self.reasons \/ reason ∈ that.reasons
Cause.combine_order :
  self.reasons.Nodup -> that.reasons.Nodup ->
    (Cause.combine self that).reasons =
      self.reasons ++
        that.reasons.filter (fun reason => decide (reason ∉ self.reasons))
Cause.combine_nodup :
  self.reasons.Nodup -> that.reasons.Nodup ->
    (Cause.combine self that).reasons.Nodup
Cause.combine_self : self.reasons.Nodup -> Cause.combine self self = self
```

`combine_empty_left` and `combine_empty_right` are rc.112's two
length-zero short circuits at `internal/effect.ts:248-252`, which return the
*other* operand untouched — so an operand carrying duplicates keeps them, and
`combine_nodup` therefore needs both hypotheses.

`combine_reasons` is the definition-level law for the remaining branch, and
`combine_order` is the exact `Arr.union` reading: `self`, then the elements of
`that` that are not already present, first occurrences kept. The two agree
because `dedup` fixes a duplicate-free prefix and removes only later repeats;
`combine_order` carries its `Nodup` hypotheses because
`dedup (a ++ b) = a ++ b.filter (∉ a)` is false when `a` or `b` repeats.

`combine_self` is the structural-equality short circuit
(`Equal.equals(self, newCause) ? self : newCause`, `internal/effect.ts:256`).
In this model that test is a no-op because equality is structural and a `Cause`
has exactly one field; the rc.112 *reference* preservation is refused under
`CAUSE-FB-REFERENCE-EQ`. The `Nodup` hypothesis is required: `combine a a = a`
fails when `a` already repeats a reason.

`combine_no_new_reason` is `rule.cause-has-no-structure`'s second half.

**Assumption, stated because the bytes are not vendored.** `Arr.union` is
imported from `../Array.ts` at `internal/effect.ts:1`, and that file is *not*
inside `vendor/effect-4.0.0-rc.112/src/`. The union semantics used here —
first occurrences kept, `self` before the new elements of `that`, structural
equality — is taken from the census summary for `cause.combine-union` and from
`docs/effect-rc112-fiber-runtime.html` section 8 ("set-union of reasons by
Equal, order a then new from b"). It is an authored assumption, not a byte
observation, and it is the one place in this packet where that is true. A later
packet that vendors `Array.ts` must re-check `combine_order` against it.

### Squash (census: cause.squash)

```lean
Squashed.cases_receipt :
  (exists error, squashed = .error error) \/
  (exists defect, squashed = .defect defect) \/
  squashed = .interruptedWithoutError \/ squashed = .emptyCause

Cause.squash_error :
  self.reasons.filterMap Reason.error? = error :: rest ->
    self.squash = Squashed.error error
Cause.squash_defect :
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = defect :: rest ->
    self.squash = Squashed.defect defect
Cause.squash_interrupted :
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = [] ->
  self.reasons ≠ [] -> self.squash = Squashed.interruptedWithoutError
Cause.squash_empty : Cause.empty.squash = Squashed.emptyCause
Cause.squash_emptyCause_iff :
  self.squash = Squashed.emptyCause <-> self.reasons = []

Cause.squash_fail      : (Cause.fail error).squash = Squashed.error error
Cause.squash_die       : (Cause.die defect).squash = Squashed.defect defect
Cause.squash_interrupt :
  (Cause.interrupt interruptor).squash = Squashed.interruptedWithoutError
Cause.squash_fail_over_die :
  (Cause.mk [Reason.die defect dieAnnotations,
      Reason.fail error failAnnotations]).squash = Squashed.error error
```

The four arms are stated as partition tests, not as positional tests: a `Fail`
anywhere in the list beats a `Die` anywhere in the list, and the *first* `Fail`
in reason order wins among the fails. `squash_fail_over_die` is the ground
receipt that fixes the direction, and `E4-SEM-CE-003` is the attack it rejects.
`squash_emptyCause_iff` is where the closed three-tag alphabet is used: with no
fourth reason constructor, "no fail and no die and no interrupt" is exactly
"no reasons".

### Exit (census: exit.success-failure, cause.finalizer-merge; adjacent:
scope.exit-as-void-all)

```lean
Exit.cases_receipt :
  (exists value, self = Exit.success value) \/
  (exists cause, self = Exit.failure cause)
Exit.success_ne_failure : Exit.success value ≠ Exit.failure cause
Exit.success_inj : Exit.success left = Exit.success right <-> left = right
Exit.failure_inj : Exit.failure left = Exit.failure right <-> left = right
Exit.void_eq : Exit.void = Exit.success ()

Exit.isSuccess_success / isSuccess_failure
Exit.cause_success / cause_failure
Exit.causeReasons_success / causeReasons_failure
```

`combineFinalizerCause` at `internal/effect.ts:3800-3804` is frozen by four
exact arms, one per branch of `exitIsSuccess(exit_) ? finalizer :
catchCause(finalizer, cause => failCause(causeCombine(exit_.cause, cause)))`:

```lean
Exit.mergeFinalizer_success :
  Exit.mergeFinalizer (Exit.success value) finalizer = finalizer
Exit.mergeFinalizer_success_failure :
  Exit.mergeFinalizer (Exit.success value) (Exit.failure finalizerCause) =
    Exit.failure finalizerCause
Exit.mergeFinalizer_failure_success :
  Exit.mergeFinalizer (Exit.failure cause) (Exit.success value) =
    Exit.success value
Exit.mergeFinalizer_failure_failure :
  Exit.mergeFinalizer (Exit.failure cause) (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause)
```

**Correction to the packet brief.** The brief asked for "success finalizer
leaves the exit unchanged" as a law of the finalizer merge. The bytes do not
say that: `catchCause` does not intercept a successful finalizer, so
`combineFinalizerCause(failedExit, successfulFinalizer)` is the *successful*
`Effect<void>`, and the original exit is restored by the caller's
`flatMap(..., (_) => exit)` at `internal/effect.ts:4023-4028`. That caller-side
composite is modelled separately and exactly, so the brief's obligation is met
where the behaviour actually lives:

```lean
Exit.restoreAfterFinalizer_success_finalizer :
  Exit.restoreAfterFinalizer self (Exit.success value) = self
Exit.restoreAfterFinalizer_failure_failure :
  Exit.restoreAfterFinalizer (Exit.failure cause) (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause)
Exit.restoreAfterFinalizer_success_failure :
  Exit.restoreAfterFinalizer (Exit.success value) (Exit.failure finalizerCause) =
    Exit.failure finalizerCause
```

`restoreAfterFinalizer` is
`match mergeFinalizer self finalizer with | .success _ => self | .failure c =>
.failure c`. It reproduces the `OnExit` `contA` arm as well as the `contE` arm,
because a failing finalizer short-circuits the `flatMap` in both. It claims
nothing about the `op.OnExit` census row, which also covers stack push and the
`contAll` mask and is not modelled here.

`exitAsVoidAll` at `internal/effect.ts:2024-2038`:

```lean
Exit.asVoidAll_reasons :
  (Exit.asVoidAll exits).causeReasons = exits.flatMap Exit.causeReasons
Exit.asVoidAll_nil : Exit.asVoidAll [] = Exit.success ()
Exit.asVoidAll_all_success :
  (forall exit, exit ∈ exits -> exists value, exit = Exit.success value) ->
    Exit.asVoidAll exits = Exit.success ()
Exit.asVoidAll_failure :
  exits.flatMap Exit.causeReasons = reason :: rest ->
    Exit.asVoidAll exits = Exit.failure (Cause.mk (reason :: rest))
Exit.asVoidAll_empty_cause :
  Exit.asVoidAll [Exit.failure Cause.empty] = Exit.success ()
Exit.asVoidAll_keeps_duplicates :
  Exit.asVoidAll [Exit.failure (Cause.mk [reason]),
      Exit.failure (Cause.mk [reason])] =
    Exit.failure (Cause.mk [reason, reason])
```

`asVoidAll_reasons` is the exact concatenation order and holds unconditionally,
including the success case where both sides are `[]`. `asVoidAll_empty_cause`
is the sharp consequence of `failures.length === 0` rather than "any failed
exit": a `Failure` carrying an empty cause contributes no reason, so the join
succeeds. `asVoidAll_keeps_duplicates` records that the join is *not*
`causeCombine`: it concatenates without deduplicating.

## Census row to obligation map

Every clause of every assigned row has a named obligation. Clause text is the
census summary line, split at its conjunctions.

| Row | Clause | Obligation |
| --- | --- | --- |
| `cause.flat-reasons` | "a flat readonly array of reasons" | `Cause.mk`/`Cause.reasons` signature; one field |
| | "with no tree" | `Cause.ext`, and `E4-SEM-CE-001` |
| | "no sequential or parallel distinction" | `Cause.ext`, `Cause.combine_no_new_reason` |
| | "equality is pairwise over the ordered reasons" | `Cause.eq_iff_pointwise`, `Cause.eq_iff` |
| `cause.reason-fail` | "a Fail reason carries the typed error" | `Reason.fail` signature, `Reason.error_fail`, `Reason.fail_inj`, `Cause.fail_reasons` |
| | "and its annotations" | `Reason.annotations_fail`, `Reason.fail_inj` |
| `cause.reason-die` | "a Die reason carries an unknown defect" | `Reason.die` signature over the admitted `δ`, `Reason.defect_die`, `Reason.die_inj`, `Cause.die_reasons` |
| | "and its annotations" | `Reason.annotations_die`, `Reason.die_inj` |
| `cause.reason-interrupt` | "carries an optional interruptor fiber id" | `Reason.interrupt : Option ι -> …`, `Cause.interrupt_reasons` |
| | "equality compares that id together with the annotations" | `Reason.interrupt_inj` |
| `cause.combine-union` | "treats the empty cause as an identity" | `Cause.combine_empty_left`, `Cause.combine_empty_right` |
| | "otherwise takes the set union of reasons" | `Cause.combine_reasons`, `Cause.mem_combine`, `Cause.combine_order`, `Cause.combine_nodup`, `Cause.dedup_*` |
| | "returning the original when the result is structurally equal" | `Cause.combine_self`; reference preservation refused under `CAUSE-FB-REFERENCE-EQ` |
| `cause.finalizer-merge` | "a finalizer failure under a failed exit is merged into the exit cause by causeCombine" | `Exit.mergeFinalizer_failure_failure`, `Exit.restoreAfterFinalizer_failure_failure` |
| | "under a successful exit the finalizer failure stands alone" | `Exit.mergeFinalizer_success_failure`, `Exit.restoreAfterFinalizer_success_failure` |
| `cause.squash` | "returns the first Fail error" | `Cause.squash_error`, `Cause.squash_fail`, `Cause.squash_fail_over_die` |
| | "else the first Die defect" | `Cause.squash_defect`, `Cause.squash_die` |
| | "else an Error naming interruption without error" | `Cause.squash_interrupted`, `Cause.squash_interrupt`; message bytes refused under `CAUSE-FB-ERROR-MESSAGE` |
| | (fourth arm, not in the summary) | `Cause.squash_empty`, `Cause.squash_emptyCause_iff` |
| `cause.annotations` | "reason annotations are a per-reason string map" | `ReasonAnnotations` structure, `Reason.annotations_*`, `keys_eq`, `keys_nodup`, `lookup_eq` |
| | "remembered per original error object in a WeakMap" | refused: `Reason.host_memory_refused`, boundary `CAUSE-FB-WEAKMAP` |
| | "and merged on construction" | `ReasonAnnotations.annotate_entries` with `overwrite := true` is the merge; the *trigger* is the refused WeakMap read |
| | "annotate never overwrites an existing key unless asked" | `ReasonAnnotations.lookup_annotate_kept`, `lookup_annotate_overwrite`, `lookup_annotate_new`, `annotate_empty`, `annotate_keys` |
| `exit.success-failure` | "an Exit is Success carrying a value or Failure carrying a Cause" | `Exit.cases_receipt`, `Exit.success_ne_failure`, `Exit.success_inj`, `Exit.failure_inj`, `Exit.cause_*` |
| | "and each is itself a primitive that can be stepped" | **not modelled**; needs the continuation-machine calculus. The row stays `partial` |
| `exit.reason-alphabet` | "the public reason alphabet is exactly Fail, Die and Interrupt" | `ReasonTag.all_nodup`, `ReasonTag.mem_all`, `ReasonTag.cases_receipt`, `Reason.tag_mem_all` |
| | "with no further cases" | `Reason.cases_receipt`, `Squashed.cases_receipt` for the squash side |
| `rule.cause-has-no-structure` | "causeCombine is a set union of reasons" | `Cause.mem_combine`, `Cause.combine_order` |
| | "there is no sequential or parallel cause node" | `Cause.ext`, `Cause.combine_no_new_reason`, `E4-SEM-CE-001` |

`exit.success-failure` is the only assigned row this packet cannot make green.
Ten of eleven are green-able; the eleventh is green-able for its first clause
and explicitly deferred for its second.

## Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `E4-SEM-CE-001` | a tree-shaped cause with sequential and parallel nodes is a faithful richer carrier | keep one flat ordered reason list; `Cause.ext` makes the reason list the whole content, and combine introduces no node |
| `E4-SEM-CE-002` | `causeCombine` is concatenation | deduplicate by first occurrence; freeze `dedup_cons`, `combine_reasons`, and the `combine_self` short circuit |
| `E4-SEM-CE-003` | squash may report whichever reason appears first, or may prefer a defect | partition first, then choose: a `Fail` anywhere beats a `Die` anywhere, and the fourth `emptyCause` arm is distinct from `interruptedWithoutError` |
| `E4-SEM-CE-004` | `annotate` may overwrite an existing key, or may move an overwritten key to the end | keep existing values unless `overwrite := true`, and keep the key's slot when overwriting; `annotate ∅ = id` |
| `E4-SEM-CE-005` | a finalizer failure under a successful exit may be dropped in favour of the exit | `mergeFinalizer` returns the finalizer under a successful exit; the exit-restoring composite is a separate named operation |
| `E4-SEM-CE-006` | any failed exit in the list makes `exitAsVoidAll` fail | test the concatenated reasons, not the exits: a `Failure` with an empty cause joins to success, and the join keeps duplicates |
| `E4-SEM-CE-007` | a canonical finite set (`Effect4.Data.Row`) can carry a cause | retain operand order; `combine` is not commutative and order changes `squash` |

The seven witnesses are finite self-contained breaker models in
`Test/Counterexamples/Machine/Semantics/CauseExit.lean`. They prove the attacks,
not the production laws, and they remain executable after the repair lands.

## Trust and acceptance

The checker is Lean's kernel at the pinned toolchain. `decide` is allowed for
finite propositions. `native_decide`, `sorry`, `admit`, `Classical.choice`, and
new axioms are not allowed in the packet or the implementation.

Known axiom traps for this packet, recorded in `COORDINATION.md` "Operational
facts worth not rediscovering" and relevant here because every annotation key
is a `String`:

- `simp` on a positive `String` disequality pulls `Classical.choice`; use
  `decide`. `ReasonAnnotations.order_retained` and every `lookup_annotate_*`
  proof passes through key comparison and must avoid it.
- `decreasing_by` pulls `Quot.sound`; `Cause.dedup` as frozen is structurally
  recursive and needs neither.
- Build `Decidable` instances with `inferInstanceAs` so the ground `decide`
  checks in the battery still reduce in the kernel.

The breaker phase is accepted when

```sh
lake env lean Test/Counterexamples/Machine/Semantics/CauseExit.lean
```

exits zero, while

```sh
lake env lean Test/Machine/Semantics/CauseExitContract.lean
lake env lean Test/Machine/Semantics/CauseExitAxiomReport.lean
```

both exit nonzero with *only* unknown-identifier and unknown-constant
diagnostics for the fenced `Effect4.*` names. A parse error, an import error,
or a failure in the battery's own helper code is not a clean red result. Both
red modules are declared in `test/fixtures/trust-gate/known-red.txt`, which is
self-checking in both directions: they must be removed the moment they go
green.

The builder phase requires all three files plus the complete project test suite
to exit zero, with `#print axioms` receipts inside `propext`/`Quot.sound` for
every public theorem. It does not authorize any coverage-number change: the
runtime-coverage join in `Test/Audit/RuntimeCoverage.lean` is a separate
packet with a separate claim, as recorded in `docs/research/CAUSE-DAG.md`.

## Open question

**One universe or four.** The frozen signatures put `ε`, `δ`, `ι`, `α`, and the
exit value `β` in a single `Type u`. This matches the house style of
`src/Effect4/Machine/Fibers.lean` and `src/Effect4/Data/Row.lean`, keeps the
five-parameter ascriptions readable, and admits every instantiation the near
packets need (`ι := Effect4.FiberId`, `α := Effect4.Json`, `ε` a user error
type). It forbids mixing universes across the five parameters — for example an
`ε : Type` with a `δ : Type 1`.

Recommendation: keep the single universe. Splitting it is a purely additive
signature change if a later packet genuinely needs it, and every theorem
statement above is universe-agnostic. Raising it now would cost readability in
about ninety ascriptions for a case no current packet has.
