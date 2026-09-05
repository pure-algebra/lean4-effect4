import Effect4.Char.Manifest

/-!
# Conformance.Consume: the target and `consume`

Owner: the check against an implementation. A `Target` names what is being conformed to: the
component, the **reference** to its manifest, the **reference** to the implementation pin set,
and the failure model. `consume` replays a vector set through an oracle and joins the receipts
in; it is idempotent and monotone in both arguments. The two carriers a receipt is keyed by,
`Implementation` and `Receipt`, are declared in `Conformance/Receipt.lean`, below
`Char/Evidence.lean`, because `Evidence.fixture` names a `Receipt` and `Target` names a
`Manifest`; that module's header has the ordering argument.

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
| Carrier | `Target`; `Implementation`, `Receipt`, `Receipts := GSet Receipt` next door; all `deriving DecidableEq, Repr`, all `Content` |
| Operations | `Target.pin`, `receiptOf`, `consume`, `replayAgainst`, `Receipts.verdict`, `Receipts.failures`, `Receipt.asFixtureEvidence`; the address of any of them is the store's `address` |
| Laws | `consume_mono_receipts`, `consume_idem`, `consume_mono_left`, `consume_mono_right`, `receiptOf_replayAgainst_holds`, `self_replay_holds`, `consume_self_verdict` |
| Structure | `consume T o rs vs = rs ⊔ ofList (o '' facts vs)`: the join with the image of an oracle; the receipts form the G-Set of `Conformance/GSet.lean`; `verdict` is the fold of `holds` under `&&`, the meet of the two-element lattice |
| Payoff | deletes receipt bookkeeping, the second run of a replay already made, and a separate kill checker for the harness |
| Anti-vacuity | `Conformance/Cell.lean`: a self-replay with verdict `true` beside a mutant replay with verdict `false` and ten named failures |
| Generation | receipts are emitted by `consume` or by the generated driver; `Target` is derived from the manifest and the pin table |

The four address helpers this module used to carry — `Implementation.addr`, `Target.addr`,
`Receipt.addr` and `Vector.addr` next door — are gone: a node's address is `Effect4.Store.address`
and nothing else (facts note §2, "two spellings and two meanings"). So are the two hand
instances it declared for types it does not own: `Canonical Digest` is the store's
(`Store/Canonical.lean:435`) and `Canonical (Failure String)` is generated in
`Char/Derived.lean`.
-/

set_option autoImplicit false

namespace Effect4.Char

open Effect4.Store

/-- **The conformance target**: which component, which model, which implementation,
under which failure model. Its address names the whole in `Characterized`; a
receipt is keyed by the implementation reference alone. -/
structure Target where
  /-- The component id, e.g. `"queue"`. -/
  component : String
  /-- The component's manifest, by reference: the node the model is. -/
  model : Ref Manifest
  /-- The implementation pin set, by reference. -/
  implementation : Ref Implementation
  /-- The failure model, with kinds spelled (`Failure.excludedSpelled` in Core). -/
  failure : Failure String
deriving DecidableEq, Repr

/-- The receipt key on the implementation side. It is the field, now that the field is the
reference: a target and its receipts agree on one address with no digest recomputed. -/
def Target.pin (t : Target) : Ref Implementation := t.implementation

theorem Target.pin_eq (t : Target) : t.pin = t.implementation := rfl

section Consume

variable {S L C : Type} [DecidableEq L] [DecidableEq C] [Canonical L] [Canonical C]

/-- One receipt: the oracle's verdict on one fact, keyed by the fact's node and the pin set's
node. The vector key is `anyRef f`, the fact's address at kind `vector`, because a `Receipt`
is monomorphic and cannot name `Fact L C`. -/
def receiptOf (T : Target) (replay : Fact L C → Bool) (f : Fact L C) : Receipt :=
  { obligation := "replay"
    vector := anyRef f
    pin := T.pin
    holds := replay f
    detail := s!"{T.component}: word of length {f.word.length}, accept={f.accept}" }

set_option linter.unusedSectionVars false in
/-- The vector key of a receipt is the fact's own reference, at kind `vector`. -/
theorem receiptOf_vector (T : Target) (replay : Fact L C → Bool) (f : Fact L C) :
    (receiptOf T replay f).vector = anyRef f := rfl

set_option linter.unusedSectionVars false in
/-- The pin key of a receipt is the target's implementation reference. -/
theorem receiptOf_pin (T : Target) (replay : Fact L C → Bool) (f : Fact L C) :
    (receiptOf T replay f).pin = T.implementation := rfl

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

/-! ## Receipts -/

#print axioms Target.pin
#print axioms Target.pin_eq
#print axioms receiptOf
#print axioms receiptOf_vector
#print axioms receiptOf_pin
#print axioms consume
#print axioms consume_mono_receipts
#print axioms consume_idem
#print axioms consume_mono_left
#print axioms consume_mono_right
#print axioms replayAgainst
#print axioms receiptOf_replayAgainst_holds
#print axioms self_replay_holds
#print axioms consume_self_verdict

end Effect4.Char
