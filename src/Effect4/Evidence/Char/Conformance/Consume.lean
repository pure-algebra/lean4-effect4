import Effect4.Evidence.Char.Conformance.VectorSet

/-!
# Conformance.Consume: the target, the receipt, and `consume`

Owner: the check against an implementation. A `Target` names what is being
conformed to (component, model digest, pin set, failure model). A `Receipt` is a
named `Bool` over first-order data, keyed by a vector's address and the
implementation pin set's address. `consume` replays a vector set through an oracle and joins the receipts
in; it is idempotent and monotone in both arguments.

Where it sits in the semantic compiler: the **back end**. The intermediate
representation goes in, addressed evidence comes out. Lean holds one oracle,
`replayAgainst`, a second machine; the TypeScript driver of `04-harness` is the
other, and it emits this exact `Receipt` shape. What it makes mechanical: the
question "has this vector been replayed against this implementation" is a key
lookup, and "did the mutant move the fixture" and "did the driver assert" are one
`Bool` (`receiptOf_replayAgainst_holds`).

## The algebra

| | |
| --- | --- |
| Carrier | `Implementation`, `Target`, `Receipt`, `Receipts := GSet Receipt`; all `deriving DecidableEq, Repr`, `Canonical` |
| Operations | `Implementation.addr`, `Target.addr`, `Target.pin`, `Receipt.addr`, `receiptOf`, `consume`, `replayAgainst`, `Receipts.verdict`, `Receipts.failures`, `Receipt.asFixtureEvidence` |
| Laws | `consume_mono_receipts`, `consume_idem`, `consume_mono_left`, `consume_mono_right`, `receiptOf_replayAgainst_holds`, `self_replay_holds`, `consume_self_verdict` |
| Structure | `consume T o rs vs = rs ⊔ ofList (o '' facts vs)`: the join with the image of an oracle; the receipts form the G-Set of `Conformance/GSet.lean`; `verdict` is the fold of `holds` under `&&`, the meet of the two-element lattice |
| Payoff | deletes receipt bookkeeping, the second run of a replay already made, and a separate kill checker for the harness |
| Anti-vacuity | `Conformance/Cell.lean`: a self-replay with verdict `true` beside a mutant replay with verdict `false` and ten named failures |
| Generation | receipts are emitted by `consume` or by the generated driver; `Target` is derived from the manifest and the pin table |

A receipt that holds is the `replayed` rung's evidence and never more: it
projects to the `(id, sha256)` pair `Evidence.fixture` takes in `05-registry`. A
failing receipt is a finding, not evidence. Two receipts for one vector and one
pin set with different verdicts are both kept and the verdict is then `false`: a
replay that is not deterministic is a finding, never a green.
-/

set_option autoImplicit false

namespace Effect4.Char

open Effect4.Store

instance : Canonical Digest := ⟨fun d => encode d.bytes⟩

instance : Canonical (Failure String) := ⟨fun F => encode (F.name, F.excluded, F.escapes)⟩

/-- **The implementation pin set**: the bytes and the run mode a receipt is about,
and nothing about the model. Its address is the `pin` key of every receipt. The
model digest is deliberately outside it: a vector is a fact that carries its own
expectation, so extending the alphabet moves the manifest and leaves every old
receipt keyed as it was. Driver bytes are also outside it, for the same reason. -/
structure Implementation where
  /-- The package, e.g. `"effect"`. -/
  package : String
  /-- The version, e.g. `"4.0.0-rc.112"`. -/
  version : String
  /-- Span digests of the pinned verbs, in verb order. -/
  pins : List Digest
  /-- The run mode the determinism argument of `04-harness/03` is made for: `"runSync"`. -/
  driver : String
  /-- The host pin (the node version, or `"absent"`). -/
  host : String
deriving DecidableEq, Repr

instance : Canonical Implementation :=
  ⟨fun i => encode (i.package, i.version, i.pins, i.driver, i.host)⟩

/-- The address of the pin set: the `pin` key of a receipt. -/
def Implementation.addr (i : Implementation) : Digest := digestOf i

/-- **The conformance target**: which component, which model, which implementation,
under which failure model. Its address names the whole in `Characterized`; a
receipt is keyed by `implementation.addr` alone. -/
structure Target where
  /-- The component id, e.g. `"queue"`. -/
  component : String
  /-- The address of the component's manifest (its model digest). -/
  model : Digest
  /-- The implementation pin set. -/
  implementation : Implementation
  /-- The failure model, with kinds spelled (`Failure.excludedSpelled` in Core). -/
  failure : Failure String
deriving DecidableEq, Repr

instance : Canonical Target :=
  ⟨fun t => encode (t.component, t.model, t.implementation, t.failure)⟩

/-- The address. Derived, never stored. -/
def Target.addr (t : Target) : Digest := digestOf t

/-- The receipt key on the implementation side. -/
def Target.pin (t : Target) : Digest := t.implementation.addr

/-- **A receipt**: a named `Bool` over first-order data, keyed by the vector's
address and the implementation pin set's address. The shape of
`06-gates/01-decidable-receipt.md` with the two keys added; the TypeScript
driver emits this exact shape. -/
structure Receipt where
  /-- Always `"replay"` here; the gate's obligation vocabulary. -/
  obligation : String
  /-- `digestOf` the fact. -/
  vector : Digest
  /-- `Implementation.addr`: the pin set, never the model and never the driver bytes. -/
  pin : Digest
  /-- The verdict. -/
  holds : Bool
  /-- What was compared and, on `false`, what was found. Never a summary. -/
  detail : String
deriving DecidableEq, Repr

instance : Canonical Receipt :=
  ⟨fun r => encode (r.obligation, r.vector, r.pin, r.holds, r.detail)⟩

/-- The address of a receipt: what `Evidence.fixture` names. -/
def Receipt.addr (r : Receipt) : Digest := digestOf r

/-- The grow-only set of receipts. -/
abbrev Receipts := GSet Receipt

/-- The gate: the fold of `holds` under `&&`. -/
def Receipts.verdict (rs : Receipts) : Bool := rs.elems.all Receipt.holds

/-- The failing receipts, for the diagnostic. -/
def Receipts.failures (rs : Receipts) : List Receipt := rs.elems.filter fun r => !r.holds

/-- **The receipt is the `replayed` rung's evidence.** A holding receipt projects
to the `(id, sha256)` pair `Evidence.fixture` takes in `Effect4/Char/Evidence.lean`:
`id` is the vector's address and `sha256` is the receipt's own address, which
carries the pin key inside it. A failing receipt is evidence of nothing; it is a
finding. A receipt never reaches `proved`. -/
def Receipt.asFixtureEvidence (r : Receipt) : Option (String × String) :=
  if r.holds then some (r.vector.hex, r.addr.hex) else none

section Consume

variable {S L C : Type} [DecidableEq L] [DecidableEq C] [Canonical L] [Canonical C]

/-- One receipt: the oracle's verdict on one fact, keyed by fact and pin set. -/
def receiptOf (T : Target) (replay : Fact L C → Bool) (f : Fact L C) : Receipt :=
  { obligation := "replay"
    vector := digestOf f
    pin := T.pin
    holds := replay f
    detail := s!"{T.component}: word of length {f.word.length}, accept={f.accept}" }

/-- **Consume.** Replay every fact of a vector set through an oracle and join the
receipts in. `join` with the image of a function, so it is idempotent and
monotone in both arguments by the G-Set laws. -/
def consume (T : Target) (replay : Fact L C → Bool) (rs : Receipts) (vs : VectorSet L C) :
    Receipts :=
  rs.join (GSet.ofList (vs.facts.map (receiptOf T replay)))

/-- Consuming never loses a receipt. -/
theorem consume_mono_receipts (T : Target) (replay : Fact L C → Bool) (rs : Receipts)
    (vs : VectorSet L C) : GSet.Sub rs (consume T replay rs vs) :=
  GSet.sub_join_left _ _

/-- Consuming is idempotent: replaying a set already consumed adds nothing. -/
theorem consume_idem (T : Target) (replay : Fact L C → Bool) (rs : Receipts)
    (vs : VectorSet L C) :
    GSet.Equiv (consume T replay (consume T replay rs vs) vs) (consume T replay rs vs) := by
  unfold consume
  exact GSet.equiv_trans (GSet.join_assoc _ _ _)
    (GSet.join_equiv (GSet.equiv_refl _) (GSet.join_idem _))

/-- Consuming is monotone in the receipts. -/
theorem consume_mono_left (T : Target) (replay : Fact L C → Bool) {rs rs' : Receipts}
    (h : GSet.Sub rs rs') (vs : VectorSet L C) :
    GSet.Sub (consume T replay rs vs) (consume T replay rs' vs) :=
  GSet.join_mono h (GSet.sub_refl _)

/-- Consuming is monotone in the vectors: more vectors, more receipts, none lost. -/
theorem consume_mono_right (T : Target) (replay : Fact L C → Bool) (rs : Receipts)
    {vs vs' : VectorSet L C} (h : GSet.Sub vs vs') :
    GSet.Sub (consume T replay rs vs) (consume T replay rs vs') :=
  GSet.join_mono (GSet.sub_refl _) (GSet.ofList_mono fun r hr => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hr
    exact List.mem_map.2 ⟨f, VectorSet.facts_mono h hf, rfl⟩)

/-- Lean's own oracle: replay a fact against a second machine by recomputing the
fact there. The model against itself is the identity check; a mutant against the
model is a kill check. -/
def replayAgainst (M' : Machine S L) (R : Reading S L C) (clients : List C) :
    Fact L C → Bool :=
  fun f => decide (factOf M' R clients f.word = f)

/-- **Direction 1 is Direction 2.** A receipt from `replayAgainst M'` fails exactly
when the fact separates `M'`: "the fixture moved" and "the driver asserts" are one
`Bool`. -/
theorem receiptOf_replayAgainst_holds (T : Target) (M' : Machine S L) (R : Reading S L C)
    (clients : List C) (f : Fact L C) :
    (receiptOf T (replayAgainst M' R clients) f).holds =
      !decide (factOf M' R clients f.word ≠ f) := by
  simp [receiptOf, replayAgainst]

/-- A sound set replayed against its own model holds everywhere. -/
theorem self_replay_holds (T : Target) (M : Machine S L) (R : Reading S L C) (clients : List C)
    {vs : VectorSet L C} (hs : VectorSet.Sound M R clients vs) (f : Fact L C)
    (hf : f ∈ vs.facts) : (receiptOf T (replayAgainst M R clients) f).holds = true := by
  obtain ⟨p, hp⟩ := VectorSet.facts_mem.1 hf
  simp [receiptOf, replayAgainst, (hs f p (GSet.has_of_mem hp)).symm]

/-- The whole verdict of a self-replay from empty receipts is `true`. -/
theorem consume_self_verdict (T : Target) (M : Machine S L) (R : Reading S L C)
    (clients : List C) {vs : VectorSet L C} (hs : VectorSet.Sound M R clients vs) :
    (consume T (replayAgainst M R clients) GSet.empty vs).verdict = true := by
  unfold consume Receipts.verdict
  refine List.all_eq_true.2 fun r hr => ?_
  have hr' := GSet.mem_ofList.1 (by
    have := GSet.has_of_mem hr
    rw [GSet.has_join, GSet.has_empty, Bool.false_or] at this
    exact this)
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hr'
  exact self_replay_holds T M R clients hs f hf

end Consume

end Effect4.Char
