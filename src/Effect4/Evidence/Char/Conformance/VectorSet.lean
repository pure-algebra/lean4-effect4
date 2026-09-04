import Effect4.Evidence.Char.Conformance.GSet
import Effect4.Evidence.Char.Conformance.Vector

/-!
# Conformance.VectorSet: the grow-only set of vectors

Owner: `VectorSet L C`, the G-Set of `(Fact, Provenance)` pairs, and the three
things one asks of it: is a fact held (`holds`), under a tag (`tagged`), and is
every fact held the model's own (`Sound`). Plus the kill question: does some
held fact separate a second machine from the model (`kills`).

Where it sits in the semantic compiler: the **module** of the intermediate
representation, the unit that generators write and `consume` reads. What it
makes mechanical: soundness is closed under join (`sound_join`), so a set
assembled from any number of sound generators by any number of front ends is
sound with no per-assembly argument; and a kill is monotone (`kills_mono`), so a
mutant once killed stays killed under every extension.

## The algebra

| | |
| --- | --- |
| Carrier | `VectorSet L C := GSet (Fact L C × Provenance)` |
| Operations | `holds`, `tagged`, `facts`, `tagsOf`, `vectors`, `factCount`, `address`, `kills`, `killer`, `soundB` |
| Laws | `sound_join`, `sound_ofList`, `sound_of_sub`, `sound_of_soundB`, `soundB_of_sound`, `kills_mono`, `facts_mem`, `facts_mono` |
| Structure | the G-Set of `Conformance/GSet.lean` at one carrier; `Sound` is a predicate closed under the join, i.e. an ideal of the semilattice |
| Payoff | deletes the per-generator soundness argument and the "is the mutant still dead after we added vectors" question |
| Anti-vacuity | `Conformance/Cell.lean`: a set that kills a mutant, and a smaller set that does not (`enumeration_alone_spares_lossy`) |
| Generation | populated only by the generators of `Conformance/Generators.lean` |
-/

set_option autoImplicit false

namespace Effect4.Char

/-- The grow-only set of `(fact, tag)` pairs. The vector is the fibre over a fact. -/
abbrev VectorSet (L C : Type) := GSet (Fact L C × Provenance)

namespace VectorSet

variable {S L C : Type} [DecidableEq L] [DecidableEq C]

/-- Is this fact held, under any tag. -/
def holds (vs : VectorSet L C) (f : Fact L C) : Bool :=
  vs.elems.any fun x => decide (x.1 = f)

/-- Is this fact held under this tag. -/
def tagged (vs : VectorSet L C) (f : Fact L C) (p : Provenance) : Bool :=
  vs.has (f, p)

/-- The facts held, each once, in first-seen order. -/
def facts (vs : VectorSet L C) : List (Fact L C) :=
  (GSet.ofList (vs.elems.map Prod.fst)).elems

/-- The tags on one fact, in first-seen order. -/
def tagsOf (vs : VectorSet L C) (f : Fact L C) : List Provenance :=
  (vs.elems.filter fun x => decide (x.1 = f)).map Prod.snd

/-- The fixture face: one `Vector` per fact. A projection; nothing is stored twice. -/
def vectors (vs : VectorSet L C) : List (Vector L C) :=
  vs.facts.map fun f => ⟨f, vs.tagsOf f⟩

/-- The number of facts held (the number of fixture rows). -/
def factCount (vs : VectorSet L C) : Nat := vs.facts.length

/-- The address of the set: `digestOf` its list state. What a `Manifest` carries. -/
def address [Effect4.Store.Canonical L] [Effect4.Store.Canonical C] (vs : VectorSet L C) :
    Effect4.Store.Digest :=
  Effect4.Store.digestOf vs

/-- **Soundness of a set**: every fact held is the model's own fact for its word. -/
def Sound (M : Machine S L) (R : Reading S L C) (clients : List C) (vs : VectorSet L C) : Prop :=
  ∀ (f : Fact L C) (p : Provenance), vs.has (f, p) = true → f = factOf M R clients f.word

/-- Soundness as a receipt. -/
def soundB (M : Machine S L) (R : Reading S L C) (clients : List C) (vs : VectorSet L C) : Bool :=
  vs.elems.all fun x => decide (x.1 = factOf M R clients x.1.word)

theorem sound_of_soundB {M : Machine S L} {R : Reading S L C} {clients : List C}
    {vs : VectorSet L C} (h : soundB M R clients vs = true) : Sound M R clients vs :=
  fun f p hp => decide_eq_true_iff.1 ((List.all_eq_true.1 h) (f, p) (GSet.mem_of_has hp))

theorem soundB_of_sound {M : Machine S L} {R : Reading S L C} {clients : List C}
    {vs : VectorSet L C} (h : Sound M R clients vs) : soundB M R clients vs = true :=
  List.all_eq_true.2 fun x hx => decide_eq_true_iff.2 (h x.1 x.2 (GSet.has_of_mem hx))

/-- Soundness is closed under join: a sound extension of a sound set is sound. -/
theorem sound_join {M : Machine S L} {R : Reading S L C} {clients : List C}
    {vs vs' : VectorSet L C} (h : Sound M R clients vs) (h' : Sound M R clients vs') :
    Sound M R clients (vs.join vs') := fun f p hp => by
  rw [GSet.has_join, Bool.or_eq_true] at hp
  exact hp.elim (h f p) (h' f p)

/-- Soundness of `ofList` from soundness of every listed pair. -/
theorem sound_ofList {M : Machine S L} {R : Reading S L C} {clients : List C}
    {xs : List (Fact L C × Provenance)} (h : ∀ x ∈ xs, x.1 = factOf M R clients x.1.word) :
    Sound M R clients (GSet.ofList xs) :=
  fun f p hp => h (f, p) (GSet.mem_ofList.1 hp)

/-- Soundness transports down inclusion. -/
theorem sound_of_sub {M : Machine S L} {R : Reading S L C} {clients : List C}
    {vs vs' : VectorSet L C} (hsub : GSet.Sub vs vs') (h : Sound M R clients vs') :
    Sound M R clients vs := fun f p hp => h f p (hsub _ hp)

/-- Does some held fact separate a second machine from the model: the second
machine's own fact for the word differs. "The fixture moved" and "the driver
asserts" are one `Bool` (`receiptOf_replayAgainst_holds` in `Conformance/Consume.lean`). -/
def kills (M' : Machine S L) (R : Reading S L C) (clients : List C) (vs : VectorSet L C) : Bool :=
  vs.elems.any fun x => decide (factOf M' R clients x.1.word ≠ x.1)

/-- The kill witness: the first fact that separates, if any. -/
def killer (M' : Machine S L) (R : Reading S L C) (clients : List C) (vs : VectorSet L C) :
    Option (Fact L C) :=
  (vs.elems.find? fun x => decide (factOf M' R clients x.1.word ≠ x.1)).map Prod.fst

/-- Killing is monotone: a larger set kills whatever a smaller one kills. -/
theorem kills_mono {M' : Machine S L} {R : Reading S L C} {clients : List C}
    {vs vs' : VectorSet L C} (hsub : GSet.Sub vs vs') (h : kills M' R clients vs = true) :
    kills M' R clients vs' = true := by
  unfold kills at h ⊢
  obtain ⟨x, hx, hk⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨x, GSet.mem_of_has (hsub x (GSet.has_of_mem hx)), hk⟩

theorem facts_mem {vs : VectorSet L C} {f : Fact L C} :
    f ∈ vs.facts ↔ ∃ p, (f, p) ∈ vs.elems := by
  unfold facts
  constructor
  · intro h
    have h' := GSet.has_of_mem h
    rw [GSet.has_ofList, GSet.hasL_iff_mem, List.mem_map] at h'
    obtain ⟨x, hx, rfl⟩ := h'
    exact ⟨x.2, hx⟩
  · rintro ⟨p, hp⟩
    apply GSet.mem_of_has
    rw [GSet.has_ofList, GSet.hasL_iff_mem, List.mem_map]
    exact ⟨(f, p), hp, rfl⟩

/-- The facts of a subset are facts of the superset. -/
theorem facts_mono {vs vs' : VectorSet L C} (hsub : GSet.Sub vs vs') {f : Fact L C}
    (h : f ∈ vs.facts) : f ∈ vs'.facts := by
  obtain ⟨p, hp⟩ := facts_mem.1 h
  exact facts_mem.2 ⟨p, GSet.mem_of_has (hsub _ (GSet.has_of_mem hp))⟩

end VectorSet

end Effect4.Char
