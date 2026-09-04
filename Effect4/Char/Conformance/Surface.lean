import Effect4.Char.Conformance.Generators
import Effect4.Char.Conformance.Consume
import Effect4.Char.Evidence

/-!
# Conformance.Surface: the three functions, and phase 1 characterized

Owner: the API a coding LLM drives. Three functions:

| Function | In | Out |
| --- | --- | --- |
| `characterize` | machine, reading, clients, alphabet, suite, mutants, depth | a `VectorSet` |
| `extend` | a `VectorSet` and more | the join |
| `consume` (`Conformance/Consume.lean`) | a `Target`, an oracle, receipts so far, a `VectorSet` | the receipts |

and one record, `Characterized`, which is phase 1 of a component: the addresses
of the target, the vector set and the receipts, plus a rung per claim. The
fixture of `04-harness` schema 3 is a projection of the vector set
(`VectorSet.toFixture`), never a second encoding.

Where it sits in the semantic compiler: the **driver**. What it makes
mechanical: the whole pipeline from the five authored parts to addressed
evidence is three calls, and a coding LLM extends a component by giving the
first call more input and joining, never by editing a vector.

## The algebra

| | |
| --- | --- |
| Carrier | `Characterized`, `ClaimRung`, `Fixture L C`, `FixtureRow L C`; all `deriving DecidableEq, Repr`, `Canonical` |
| Operations | `characterize`, `extend`, `Characterized.ofParts`, `VectorSet.toFixture` |
| Laws | `characterize_sound`, `characterize_mono_depth`, `characterize_mono_tests`, `characterize_mono_mutants`, `characterize_mono_alpha`, `extend_keeps`, `extend_adds`, `extend_sound`, `toFixture_rows` |
| Structure | `characterize` is a join of the four generators, hence monotone in every input and sound; `extend` is `GSet.join` |
| Payoff | deletes any per-component pipeline and the "which generator produced this" question at the surface |
| Anti-vacuity | `Conformance/Cell.lean` |
| Generation | this is the substrate; a component supplies inputs only |
-/

set_option autoImplicit false

namespace Effect4.Char

open Effect4.Store

section Surface

variable {S L C : Type} [DecidableEq L] [DecidableEq C]

/-- **`characterize`**: the five hand-authored parts in, a vector set out.

Give it the machine `M`, the reading `R`, the clients to read, the finite label
alphabet to enumerate over, the authored suite, the declared mutants and a depth.
You get every vector the model decides from those inputs: authored tests, mutant
separations, every accepted word up to the depth, and every one-step refusal.
Every vector is a fact about `M` (`characterize_sound`). To get more vectors,
give it more of any input and `extend`; nothing is ever lost
(`characterize_mono_depth` and the other `_mono` theorems). Doctests are joined
in with `fromDoctests`, because they carry a ratifier. -/
def characterize (M : Machine S L) (R : Reading S L C) (clients : List C) (alpha : List L)
    (ts : Suite L C) (ms : List (Mutant S L)) (k : Nat) : VectorSet L C :=
  (((fromSuite M R clients ts).join (fromMutants M R clients ts ms)).join
    (enumerate M R clients alpha k)).join (enumerateRefused M R clients alpha k)

/-- **`extend`**: join more vectors in. `GSet.join` under the name the workflow
uses: `extend old (characterize … larger inputs …)` holds everything `old` held
(`extend_keeps`) plus the new (`extend_adds`). Order and repetition do not
matter (`GSet.join_comm`, `GSet.join_assoc`, `GSet.join_idem`). -/
def extend (vs more : VectorSet L C) : VectorSet L C := vs.join more

theorem extend_keeps (vs more : VectorSet L C) : GSet.Sub vs (extend vs more) :=
  GSet.sub_join_left vs more

theorem extend_adds (vs more : VectorSet L C) : GSet.Sub more (extend vs more) :=
  GSet.sub_join_right vs more

theorem extend_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    {vs more : VectorSet L C} (h : VectorSet.Sound M R clients vs)
    (h' : VectorSet.Sound M R clients more) : VectorSet.Sound M R clients (extend vs more) :=
  VectorSet.sound_join h h'

theorem characterize_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (ts : Suite L C) (ms : List (Mutant S L)) (k : Nat) :
    VectorSet.Sound M R clients (characterize M R clients alpha ts ms k) :=
  VectorSet.sound_join
    (VectorSet.sound_join
      (VectorSet.sound_join (fromSuite_sound M R clients ts) (fromMutants_sound M R clients ts ms))
      (enumerate_sound M R clients alpha k))
    (enumerateRefused_sound M R clients alpha k)

theorem characterize_mono_depth (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (ts : Suite L C) (ms : List (Mutant S L)) (k n : Nat) :
    GSet.Sub (characterize M R clients alpha ts ms k)
      (characterize M R clients alpha ts ms (k + n)) :=
  GSet.join_mono
    (GSet.join_mono (GSet.sub_refl _) (enumerate_mono_depth M R clients alpha k n))
    (enumerateRefused_mono_depth M R clients alpha k n)

theorem characterize_mono_tests (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (ts more : Suite L C) (ms : List (Mutant S L)) (k : Nat) :
    GSet.Sub (characterize M R clients alpha ts ms k)
      (characterize M R clients alpha (ts ++ more) ms k) :=
  GSet.join_mono
    (GSet.join_mono
      (GSet.join_mono (fromSuite_mono M R clients ts more)
        (fromMutants_mono_tests M R clients ts more ms))
      (GSet.sub_refl _))
    (GSet.sub_refl _)

theorem characterize_mono_mutants (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (ts : Suite L C) (ms more : List (Mutant S L)) (k : Nat) :
    GSet.Sub (characterize M R clients alpha ts ms k)
      (characterize M R clients alpha ts (ms ++ more) k) :=
  GSet.join_mono
    (GSet.join_mono
      (GSet.join_mono (GSet.sub_refl _) (fromMutants_mono_mutants M R clients ts ms more))
      (GSet.sub_refl _))
    (GSet.sub_refl _)

/-- Adding a verb is enlarging the alphabet; every vector over the old alphabet
survives. Refusals are not monotone in the alphabet by construction (a label the
old alphabet lacked can be enabled where an old label was refused, which adds a
refusal rather than removing one), so the theorem is stated for the accepted
enumeration, which is where the alphabet enters. -/
theorem characterize_mono_alpha (M : Machine S L) (R : Reading S L C) (clients : List C)
    {alpha alpha' : List L} (hsub : ∀ l ∈ alpha, l ∈ alpha') (ts : Suite L C)
    (ms : List (Mutant S L)) (k : Nat) :
    GSet.Sub (((fromSuite M R clients ts).join (fromMutants M R clients ts ms)).join
        (enumerate M R clients alpha k))
      (((fromSuite M R clients ts).join (fromMutants M R clients ts ms)).join
        (enumerate M R clients alpha' k)) :=
  GSet.join_mono (GSet.sub_refl _) (enumerate_mono_alpha M R clients hsub k)

end Surface

/-! ## Phase 1 characterized, and its projections -/

/-- One claim id and the rung it sits on. The rung is the registry's typed
`RungOrHeld` (`Effect4/Char/Evidence.lean`; R5 keeps `Claim`, `Evidence`, `Grade`
typed), and its canonical bytes are its spelling, so this row and the registry
agree on one encoding. -/
structure ClaimRung where
  claim : String
  rung : RungOrHeld
deriving DecidableEq, Repr, Inhabited

instance : Canonical ClaimRung := ⟨fun c => encode (c.claim, c.rung.spelling)⟩

/-- **Phase 1 characterized.** A component, the address of its target, of its
vector set, of its receipts, and the rung per claim. The fixture and the
registry `Fixture` entity are projections of the set the `vectors` address
names, never a second encoding. -/
structure Characterized where
  component : String
  target : Digest
  vectors : Digest
  receipts : Digest
  claims : List ClaimRung
deriving DecidableEq, Repr

instance : Canonical Characterized :=
  ⟨fun c => encode (c.component, c.target, c.vectors, c.receipts, c.claims)⟩

/-- Build the phase 1 record from the three values it addresses. -/
def Characterized.ofParts {L C : Type} [Canonical L] [Canonical C] (T : Target)
    (vs : VectorSet L C) (rs : Receipts) (claims : List ClaimRung) : Characterized :=
  { component := T.component
    target := T.addr
    vectors := vs.address
    receipts := digestOf rs
    claims := claims }

/-- One fixture row: `04-harness/01-fixture-format.md` schema 3, generic over the
component. `accept` and `readings` are the fact's fields; `name` is the first
tag's spelling plus the row's index. -/
structure FixtureRow (L C : Type) where
  name : String
  word : List L
  accept : Bool
  readings : List (ClientReading C)
  tags : List String
deriving DecidableEq, Repr

/-- The fixture envelope of `04-harness/01-fixture-format.md`: schema 3, producer
`Effect4.Char`, driver `runSync`. -/
structure Fixture (L C : Type) where
  schema : Nat := 3
  producer : String := "Effect4.Char"
  component : String
  manifest : String
  pin : String
  driver : String := "runSync"
  traces : List (FixtureRow L C)
deriving DecidableEq, Repr

/-- **The fixture is a projection of the vector set.** One row per fact, in
first-seen order, tags spelled. Nothing is re-encoded: the row's `word`,
`accept` and `readings` are the `Fact`'s fields. -/
def VectorSet.toFixture {L C : Type} [DecidableEq L] [DecidableEq C] (T : Target)
    (vs : VectorSet L C) : Fixture L C :=
  { component := T.component
    manifest := T.model.hex
    pin := T.pin.hex
    traces := (vs.vectors.zipIdx.map fun (v, i) =>
      { name := (v.tags.head?.map Provenance.spell).getD "vector" ++ "#" ++ toString i
        word := v.fact.word
        accept := v.fact.accept
        readings := v.fact.readings
        tags := v.tags.map Provenance.spell }) }

/-- One fixture row per fact held. -/
theorem VectorSet.toFixture_rows {L C : Type} [DecidableEq L] [DecidableEq C] (T : Target)
    (vs : VectorSet L C) : (vs.toFixture T).traces.length = vs.factCount := by
  simp [VectorSet.toFixture, VectorSet.vectors, VectorSet.factCount]

end Effect4.Char
