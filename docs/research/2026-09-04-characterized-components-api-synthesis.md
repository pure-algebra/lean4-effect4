# Characterized components: the API, reconciled from three reports

- **Date:** 2026-09-04
- **Record type:** Synthesis and rulings. Reconciles the three research reports of the same
  date into one API and one order of work. Where the reports disagree, the ruling is stated
  with its reason; where they agree, the agreement is recorded once.
- **Inputs:**
  - [2026-09-04-semantic-api-type-design.md](2026-09-04-semantic-api-type-design.md) (TD):
    Lean type design judged by kernel and elaborator ergonomics; 211 citations.
  - [2026-09-04-effect-internals-proof-map.md](2026-09-04-effect-internals-proof-map.md) (IM):
    rc.112 internals inventory, what is reified, what to model next; 323 citations.
  - [2026-09-04-registry-and-cas-lineage.md](2026-09-04-registry-and-cas-lineage.md) (RL):
    the CAS lineage, registry record types, drift gates, the Effect face; 143 citations.
- **Status:** proposal. Nothing below has been elaborated. Per TD R12 and the Pass A/Pass B
  rule, a compiled skeleton precedes any signature freeze.

## 0. The one-paragraph answer

A characterized component is a first-order machine `S → L → Option S` whose labels carry the
answers, together with named inductive invariants, a *reading* of words as deliveries, a
delivery grade stated relative to a failure model, a suite of decidable tests, and mutants the
suite must kill, all projected to a flat manifest whose every name is checked at elaboration
time against the environment and against pinned source spans. The registry is a
content-addressed store of those flat records, never of the typed bundles, so adding a
component re-elaborates nothing but itself. Evidence sits on three rungs, pinned, replayed,
proved, and a claim's rung is a function of its evidence, so a claim cannot outrank what backs
it. The Queue is the first inhabitant because its proofs exist; Semaphore and Latch are the
first components built on the fiber machine because they are what the machine's task alphabet
needs; PubSub is the first whose grade has real content.

## 1. Where the three reports agree

These are settled and need no further discussion.

| Point | TD | IM | RL |
| --- | --- | --- | --- |
| The step is total-or-disabled, `S → L → Option S`, answers in the label | 1.1, 3.1 | 4.1 | (implied by fixtures) |
| Invariants are extrinsic `structure … : Prop` with named clauses | 1.2, 3.2 | 4.1 | |
| Frame laws never certify; mutants killed by trace suites do | 1.6, 3.7 | 2.5 | 1.2 (lean-model-0.3) |
| Grade is a record of independent Bool axes, meet pointwise, not a rung enum | 3.4 | 4.2 | 2.2 |
| The grade is relative to a failure model given as boundary labels | 3.4 | 4.2 | 2.2 |
| Pins are spans with a span digest; line numbers are advisory | 3.8 | 4.8 | 2.2 |
| No SHA-256 inside the kernel; scripts produce and check digests | 3.8 | | 3.2 |
| The flat-row-plus-elaborator-check idiom of RuntimeCoverage is the join | 1.8, 3.9 | 2.1 | 0, 2.2 |
| Replay never turns a claim green | 3.9 | 4.9 | 2.2 |
| Coverage percentage falls when Queue, PubSub, Semaphore are vendored | | 4.9 | |
| No `Set`, no Mathlib, no `Σ` in stored data | 2, 3.9 | | 2.2 |

## 2. The disagreements, and the rulings

### 2.1 What the registry stores: typed bundles or flat records

TD 3.9 rules the registry is a list of component *names*, each component module holding its own
manifest and `#characterize` call, so that adding one is O(1) rebuild. RL 2.1 rules one
`Store Item` over a sum type so that `put` deduplicates pins across claims and the path trie
serves every query.

**Ruling: both, in two layers.** The typed bundles (`Guarded`, `Graded`, `Mutant`) live in the
component's own module and never leave it; `#characterize` checks them there. Each module
exports exactly one `Manifest` value, flat, `Canonical`. A separate aggregation module builds the
`Store Item` from the manifests for the views and the Effect face. That module is O(N) to
rebuild, and it is the only one; it contains no proofs, so its rebuild cost is a JSON walk. This
is the same split `Effect4/Arch/Views.lean` already makes between proof carriers and view
documents.

### 2.2 The grade axes

TD 3.4 proposes `{noLoss, noDup, order}`; RL 2.2 proposes `{noLoss, noDup}`; IM 4.2 proposes
`{noLoss, noDup, order}` and adds that Semaphore's and Latch's grades are not delivery grades at
all (fairness and wake-up). TD R4 says the axis set is a freeze surface and must be fixed before
the store is populated; TD R9 says the `order` axis is false as stated for multi-consumer
components unless the reading is indexed by client.

**Ruling: three axes, client-indexed reading, grade optional per component.**

```lean
structure Grade where
  noLoss : Bool
  noDup  : Bool
  order  : Bool
deriving DecidableEq, Repr, Inhabited
```

`Reading` takes a `Client` index from the start (TD R9), so `order` means "per client, the
delivered sequence is a prefix of the accepted sequence" and is stated once for Queue (one
client) and PubSub (many). Semaphore and Latch carry `Guarded` properties only and no
`GradeRow`; a component without a delivery reading has no grade, and the manifest says so
rather than carrying a vacuous `⟨false,false,false⟩`. A fourth axis is not added now: TD R4's
advice to enumerate axes for all seven planned components was taken, and fairness, wake-up and
lease properties are all better stated as `Guarded` sentences than as bits, because they do not
compose by meet.

### 2.3 The failure model

TD 3.4 gives `Failure L` typed over the label alphabet with named escape clauses each requiring a
reachability witness; RL 2.2 gives `FailureModel` with `boundaryLabels : List String` and a note.

**Ruling: typed in the module, spelled in the manifest.** `Failure L` is the typed object the
`Graded` bundle takes; its `Spelling` erasure is the `FailureModel` record the store holds. The
escape clauses stay, with their witnesses, because "the escape clauses are not decorative"
(TD 1.15). IM 4.2's list of boundary labels for Queue is adopted verbatim: shutdown, sliding
overflow, dropping refusal, interrupt of a parked offerer; for PubSub add publish with no
subscribers and slide.

### 2.4 The pin record

TD 3.8 keeps byte offsets and a span digest and leaves the text out of Lean; RL 2.2 keeps an
anchor, line offsets, the span digest and the literal text lines so a pin is self-verifying
offline; IM 4.8 notes the census generator already emits `file | lines | span-sha256` from an
anchor.

**Ruling: RL's shape, because the generator already produces it and because the only pinned
`Queue.ts` on this machine lives in a `node_modules` directory outside any repository (TD R6).**
The text is kept. Lean checks well-formedness and that `text.length` agrees with the offsets;
the script checks digests. A pin is addressed by `["pin", package, version, file, spanSha256]`.

```lean
structure Pin where
  package     : String
  version     : String
  file        : String
  fileSha256  : String
  anchor      : String
  lineStart   : Nat
  lineEnd     : Nat
  spanSha256  : String
  text        : List String
deriving DecidableEq, Repr, Inhabited
```

### 2.5 Evidence and rungs

TD 3.9 enumerates six evidence kinds (pinned, proved, exhaustivelyDecided, replayed, assumed,
unknown); RL 2.2 enumerates three constructors (pin, fixture, thm) with the rung a function of
the constructor and `Claim.coherent` decidable.

**Ruling: RL's mechanism with TD's vocabulary.**

```lean
inductive Rung where | pinned | replayed | proved
deriving DecidableEq, Repr

inductive Evidence where
  | pin     (spanSha256 guard : String)
  | fixture (id sha256 : String)
  | thm     (name axioms : String)
  | decided (name domain : String)      -- kernel `decide` over a named finite domain
  | assumed (premise : String)          -- reaches no rung
deriving DecidableEq, Repr

def Evidence.rung : Evidence → Option Rung
  | .pin _ _     => some .pinned
  | .fixture _ _ => some .replayed
  | .thm _ _     => some .proved
  | .decided _ _ => some .proved
  | .assumed _   => none
```

A claim's declared rung must be at most the maximum rung its evidence reaches; a claim with only
`assumed` evidence has no rung and is `held`, the foldlab-ssex status (RL 1.2). `unknown` is
not a constructor: an obligation with no evidence is a manifest row with an empty evidence
list, which `#characterize` reports as held.

### 2.6 What comes first: Queue, or Semaphore and Latch

IM 3.3 recommends Semaphore, Latch, Queue, PubSub, because the first two force the shared
fiber-machine changes (a wider `Task` alphabet, coalescing schedule guards, dispatcher identity)
that Queue also needs when it is integrated with `Effect4/Deep`. The owner's stated intent is to
copy the Queue as the first example.

**Ruling: Queue first as a standalone component, then Semaphore and Latch as the first
machine-integrated components, then Queue's integration, then PubSub.** The distinction is
between the B1 queue of effect-nats-verified, whose `wake` is a label and which needs no `Task`
change, and a queue that posts to the Deep dispatcher. The standalone queue exercises every
part of the API (machine, invariant, reading, grade, tests, mutants, pins, manifest, checker)
with proofs that already exist, which is what a first inhabitant is for. Its manifest records
`assumed "scheduled wake-up is modelled as a label"` against the runtime integration
obligation, so the gap is a row, not a secret.

### 2.7 Composition

TD 5 shows the generic `meet_sound` is three lines and pushes all difficulty into per-pair
reading-agreement hypotheses (`hagree`), and TD R1 warns the registry composes statements, not
proofs. RL 2.2 composes grades along `Usage` edges with the composite rung the minimum of the
backing rungs. IM 4.7 rules Stream, Channel and Sink get a grade calculus, not a machine.

**Ruling: all three, with one guard.** A `Usage` edge carries a composite grade and a composite
rung; the composite is never higher than `proved` unless the `hagree` theorem for that pair is
a named theorem in the environment. Until then the edge's rung is the minimum of `replayed` and
the backing rungs, and the edge's residual names the missing agreement theorem. No `Composed`
typeclass.

## 3. The API, in one place

Namespace `Effect4.Char`. Lean core plus `Effect4.Store` only. `set_option autoImplicit false`.

```lean
-- Machine.lean
structure Machine (S L : Type) where
  init : S
  step : S → L → Option S

def Machine.run (M : Machine S L) : S → List L → Option S
def Machine.accepts (M : Machine S L) (w : List L) : Bool
inductive Machine.Reach (M : Machine S L) : S → Prop
structure Inductive (M : Machine S L) (I : S → Prop) : Prop where
  init : I M.init
  step : ∀ {s s' l}, I s → M.step s l = some s' → I s'
theorem Machine.reach_ind …        -- the one strengthened induction, exported once

-- Reading.lean
abbrev Item := Nat
structure Reading (S L C : Type) where
  accepts : L → Option (C × Item)
  emits   : L → List (C × Item)
  residue : S → C → List Item
def Reading.acc (R) (c : C) (w : List L) : List Item
def Reading.del (R) (c : C) (w : List L) : List Item

-- Grade.lean
structure Grade where noLoss noDup order : Bool
def Grade.meet, Grade.le, top, bot; six lattice theorems by cases <;> rfl
structure Failure (L : Type) where
  name : String
  boundary : List L
  escapes : List String
def Failure.hit [DecidableEq L] (F) (w : List L) : Bool
def Grade.holds (R : Reading S L C) (F) (g) (c : C) (w) (s) : Bool
def Machine.Sound (M) (R) (F) (g) : Prop :=
  ∀ c w s, M.run M.init w = some s → Grade.holds R F g c w s = true
theorem Machine.sound_mono, meet_sound_self, sound_of_boundary_subset

-- Kit.lean
structure Guarded (S L : Type)            -- law + positive witness + negative witness
structure Graded (S L C : Type) [DecidableEq L]  -- Sound + one witness per escape + quiet word
structure Entry where id family sentence : String
def Guarded.entry, Graded.entry

-- Test.lean
structure Test (S L : Type) where name labels accept residue
def Test.run, Suite, Suite.run
structure Mutant (S L : Type) where id attacks represents machine
def Mutant.killed, Mutant.survivesSome

-- Pin.lean   (section 2.4)
-- Evidence.lean   (section 2.5)
-- Manifest.lean
structure Spelling (L : Type) where spell : L → String; all : List L
structure Verb where label : String; pins : List String   -- span digests
structure GradeRow where failure escapes grade evidence
structure Claim where id component verb kind summary rung evidence residual
structure Manifest where
  component invariants laws entries grades receipts mutants : …
  labels : List String
  verbs : List Verb
  claims : List Claim
instance : Canonical Manifest
syntax "#characterize " term : command   -- the checker, one per component module

-- Registry.lean   (the aggregation module, no proofs)
inductive Item | pin | component | verb | failureModel | claim | fixture | grade | usage | link
abbrev Registry := Store Item
def Registry.ofManifests : List Manifest → List Pin → List Fixture → List Usage → Registry
```

What `#characterize` checks, merged from TD 3.9 and RL 2.2: every invariant name is a
`structure … : Prop`; every law and receipt name is a theorem with the declared axiom receipt;
every `Entry.id` comes from a bundle declared in this module; every entry and every grade row
is some mutant's `attacks`; every escape has a witness; labels equal the spelling of the
alphabet and are duplicate-free; every verb label is in the alphabet; every pin is well-formed;
every claim is coherent with its evidence; the `#check` ascription block names exactly the
frozen surface, in order.

## 4. The Queue instance, as it will be written

From TD 4, unchanged except for the client index, which is the unit client for a queue.

- Carriers: `QState = {buffer : List Item, status : QStatus, taker : Bool}`,
  `QLabel = offer m | takeAll c | wake c | takePark | takeExit e | fail e | shutdown`.
- Invariant: `QInv cap` with named clauses `capacity`, `doneEmpty`, `closingNonEmpty`,
  `takerOnlyWhenOpenEmpty`.
- Equation (C), the characterizing statement:

```lean
theorem queue_conservation_gen (cap : Nat) (w : List QLabel) (s₀ s : QState)
    (hinv : QInv cap s₀) (hclean : boundaryFree w = true)
    (hrun : (queue cap).run s₀ w = some s) :
    queueReading.acc () w ++ s₀.buffer = queueReading.del () w ++ s.buffer
```

  Structural induction on `w` with `s₀` generalized; the only invariant clause consumed is
  `doneEmpty`. Corollaries: `queue_noLoss_at_quiescence`, `queue_fifo`, `queue_noDup` (the last
  with `nodupB (acc w)` as a hypothesis on the word, because a client that offers the same item
  twice is delivered it twice, correctly).
- Grade: `(queue cap).Sound queueReading queueCrash ⟨true, true, true⟩` under
  `queueCrash.boundary = [shutdown] ++ fail _`.
- Tests: seven, including two negatives. Mutants: three, named by the theorem each attacks;
  `Q-W1` is the one-element-pull mutant the frame laws could not exclude.
- Pins: nine, one per internal helper of `Queue.ts:1955-2114`, plus `offer`, `failCauseUnsafe`,
  `takeBetween`, `takeUnsafe`, `shutdown`, `sizeUnsafe`. `releaseCapacity` is pinned at its
  rc.112 head, line 2037, not the rc.111 line 2040 the design note cites.
- Claims: conservation at `proved`; the transliteration itself at `replayed` once schema-2
  fixtures replay in effect-nats; the runtime integration at `held` with an `assumed` row.

## 5. Order of work

Merged from RL 5 (smallest first, each with its gate) and IM 3.3 and 4.9 (dependency order).

| # | Step | Touches | Gate |
| --- | --- | --- | --- |
| 1 | Compile the Pass A skeleton: `Machine`, `Reading`, `Grade`, `Kit`, `Test`, `Pin`, `Evidence`, `Manifest` with the six lattice theorems and `sound_mono` | `Effect4/Char/*.lean` (new) | builds; TD R12's three expected snags resolved |
| 2 | `Pin` as data: ten pins from spans already cited in `Effect4/Deep/Witnesses.lean` doc comments, with text | `Effect4/Char/Pins/Rc112.lean`, `Effect4Test/Char/PinContract.lean` | `#guard` on text length and digest literals |
| 3 | Pin generator and checker, stamped, in the sweep | `scripts/generate-registry-pins.sh`, `scripts/check-registry-pins.sh`, `scripts/sweep.sh` | sweep row hits on second run |
| 4 | `scripts/check-stdlib-census.sh`: closes the 17 unchecked file pins of `Effect4/StdLib/Rc112.lean` | one script, one sweep row | planted-defect self-test |
| 5 | Vendor `Queue.ts` and `Semaphore.ts` into `vendor/effect-4.0.0-rc.112/src`; add `PORT-MANIFEST.md` rows; census rows as `absent` | vendor, manifest, `RuntimeCoverage.lean` totals | coverage gate passes with the lower percentage stated in the commit |
| 6 | The Queue component: port `EffectQueue` to the API, prove (C) and corollaries, tests, mutants, manifest, `#characterize` | `Effect4/Char/Queue/*.lean` | the checker, in the default build |
| 7 | `#characterize` command elaborator, modelled on `checkWitnesses` | `Effect4/Char/Characterize.lean` | fails on a planted bad manifest |
| 8 | Semaphore, then Latch, on the fiber machine: widen `Deep.Fibers.Task`, add coalescing guards, addressable dispatcher | `Effect4/Deep/Fibers.lean`, `Effect4/Char/{Semaphore,Latch}/*` | census rows go green; avatar corpus unchanged |
| 9 | Queue integration with the dispatcher; the `assumed` row retires | `Effect4/Char/Queue/Runtime.lean` | the held claim becomes proved |
| 10 | Registry aggregation and the fifth Arch view; the Effect face `gradeOf(component, verb, failure)` returning grade, rung, evidence, residual | `Effect4/Char/Registry.lean`, `Effect4/Arch/Views.lean`, generated TS | `ArchContract`-style receipts |
| 11 | `Usage` edges: `Stream.fromQueue → Channel.fromQueueArray → Queue.takeAll` as the first composite grade, rung `min` | `Effect4/Char/Usage.lean`, `scripts/check-registry-usage.sh` | composite `#guard`; sweep row |
| 12 | PubSub | `Effect4/Char/PubSub/*` | first grade with real content: `noLoss = false` under publish-with-no-subscribers |

Steps 1 to 4 are hours each. Steps 5 to 7 are days. Step 8 is the first change to the frozen
scheduler surface and goes through the fiber assurance freeze chain. Steps 10 to 12 are a wave.

## 6. Open questions the owner must rule on

1. **Axis set, final.** `{noLoss, noDup, order}` is proposed. The alternative is two axes now and
   `order` as a `Guarded` sentence. Ruling needed before step 1, since `Grade` is a freeze
   surface (TD R4).
2. **Manifest authored or derived.** TD R3 recommends authored for the frozen surface and
   derived for the completeness check. Ruling needed before step 7.
3. **Kill rate.** TD R8 recommends a survivor is a build failure and no rate is published.
   Ruling needed before step 6.
4. **Where the pinned source lives.** The only rc.112 `Queue.ts` on this machine is under
   `~/Dev/foldlab/library/effects/node_modules`. Step 5 vendors it; until then the pin
   generator reads that path through `EFFECT4_EFFECT_NODE_MODULES`.
