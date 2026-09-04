import Effect4.Evidence.Char.Core
import Effect4.Store.Digest
import Effect4.Store.JsonCanonical

/-!
# Char.Evidence

Owner: what a claim rests on, and the rule that a claim never outranks it.

Three carriers. `Rung` is the chain `pinned < replayed < proved`; `RungOrHeld`
adjoins a bottom, `none`, which is HELD: a claim written down but not asserted.
`Evidence` has five constructors and its rung is a function of the
constructor, never a field, so no evidence record can name a rung it does not
reach. `Claim` declares a rung and lists its evidence by address; `supported`
folds the evidence with `join`, and `coherent` decides that the declared rung is
at most the supported one.

The algebra: `RungOrHeld` under `join` is a bounded join-semilattice on a
pointed chain, and `supportedOf` is the monoid homomorphism from
`(List Evidence, ++, [])` into it. That is the whole of "evidence joins": adding
evidence never lowers a rung (`supportedOf_mono`), a claim backed only by
assumptions is HELD (`supported_none_of_all_assumed`), and a rung is not a
function of an evidence count (`supported_not_by_count`). "Composition meets"
is the other direction, `meet`, which the registry takes along a usage path.

Ruling R5: `Claim` and `Evidence` stay typed all the way down so the kernel can
decide them; their store payload is still the JSON projection through the one
`Canonical Json` instance. `Claim.evidence` holds addresses, not values, so a
theorem cited by four claims is one store entry, and `supported` takes the
resolver as an argument rather than naming a registry type.

Rungs and vocabulary: `docs/research/2026-09-04-characterized-components-api-synthesis.md`
section 2.5; the record and the theorems:
`workshop/Char/05-registry/03-claims-held-and-monotonicity.md`.
-/

namespace Effect4.Char

open Effect4.Store
open Effect4.Arch

/-- The three rungs a claim can reach, as a chain. -/
inductive Rung where
  | pinned
  | replayed
  | proved
deriving DecidableEq, Repr, Inhabited

/-- The manifest spelling of a rung. -/
def Rung.spelling : Rung → String
  | .pinned => "pinned"
  | .replayed => "replayed"
  | .proved => "proved"

/-- The position on the chain. -/
def Rung.rank : Rung → Nat
  | .pinned => 0
  | .replayed => 1
  | .proved => 2

/-- A rung, or HELD. `none` is the bottom element, not a fourth rung. -/
abbrev RungOrHeld := Option Rung

namespace RungOrHeld

/-- The position on the pointed chain: HELD is `0`, a rung is one above its own rank. -/
def rank : RungOrHeld → Nat
  | none => 0
  | some r => r.rank + 1

/-- The manifest spelling; HELD spells as `"held"`. -/
def spelling : RungOrHeld → String
  | none => "held"
  | some r => r.spelling

/-- The chain order, as a `Bool`. -/
def le (a b : RungOrHeld) : Bool := decide (a.rank ≤ b.rank)

/-- The join: the higher of the two. Evidence joins. -/
def join (a b : RungOrHeld) : RungOrHeld := if a.rank < b.rank then b else a

/-- The meet: the lower of the two. Composition meets. -/
def meet (a b : RungOrHeld) : RungOrHeld := if a.rank < b.rank then a else b

/-- `rank` is injective, which is what makes every lattice law a fact about `Nat`. -/
theorem rank_injective {a b : RungOrHeld} (h : a.rank = b.rank) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some s => cases s <;> simp [rank, Rung.rank] at h
  | some r =>
    cases b with
    | none => cases r <;> simp [rank, Rung.rank] at h
    | some s => cases r <;> cases s <;> simp [rank, Rung.rank] at h <;> rfl

theorem le_iff (a b : RungOrHeld) : le a b = true ↔ a.rank ≤ b.rank := by
  simp [le]

theorem rank_join (a b : RungOrHeld) : (join a b).rank = max a.rank b.rank := by
  unfold join; split <;> omega

theorem rank_meet (a b : RungOrHeld) : (meet a b).rank = min a.rank b.rank := by
  unfold meet; split <;> omega

theorem join_comm (a b : RungOrHeld) : join a b = join b a :=
  rank_injective (by rw [rank_join, rank_join, Nat.max_comm])

theorem join_assoc (a b c : RungOrHeld) : join (join a b) c = join a (join b c) :=
  rank_injective (by simp only [rank_join, Nat.max_assoc])

theorem join_idem (a : RungOrHeld) : join a a = a :=
  rank_injective (by simp only [rank_join, Nat.max_self])

/-- HELD is the unit of the join. -/
theorem join_bot (a : RungOrHeld) : join a none = a :=
  rank_injective (by rw [rank_join]; show max a.rank 0 = a.rank; exact Nat.max_zero _)

theorem bot_join (a : RungOrHeld) : join none a = a :=
  rank_injective (by rw [rank_join]; show max 0 a.rank = a.rank; exact Nat.zero_max _)

theorem le_refl (a : RungOrHeld) : le a a = true := by simp [le]

theorem le_trans {a b c : RungOrHeld} (hab : le a b = true) (hbc : le b c = true) :
    le a c = true :=
  (le_iff a c).mpr (Nat.le_trans ((le_iff a b).mp hab) ((le_iff b c).mp hbc))

theorem le_join_left (a b : RungOrHeld) : le a (join a b) = true :=
  (le_iff _ _).mpr (by rw [rank_join]; exact Nat.le_max_left _ _)

theorem le_join_right (a b : RungOrHeld) : le b (join a b) = true :=
  (le_iff _ _).mpr (by rw [rank_join]; exact Nat.le_max_right _ _)

theorem meet_le_left (a b : RungOrHeld) : le (meet a b) a = true :=
  (le_iff _ _).mpr (by rw [rank_meet]; exact Nat.min_le_left _ _)

theorem meet_le_right (a b : RungOrHeld) : le (meet a b) b = true :=
  (le_iff _ _).mpr (by rw [rank_meet]; exact Nat.min_le_right _ _)

/-- `join` is monotone in its second argument. -/
theorem join_le_join {a b c : RungOrHeld} (h : le b c = true) :
    le (join a b) (join a c) = true := by
  rw [le_iff, rank_join, rank_join]
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _, Nat.le_trans ((le_iff b c).mp h) (Nat.le_max_right _ _)⟩

end RungOrHeld

/-- What a claim can rest on. The rung is a function of the constructor. -/
inductive Evidence where
  /-- A span of pinned source, by its span digest, and the name of the `#guard`
  that decided the pin's well-formedness. Reaches `pinned`. -/
  | pin (spanSha256 guard : String)
  /-- A replay fixture, by the id of the vector and the digest of its receipt.
  Reaches `replayed`, whatever the corpus size: replay never turns a claim green. -/
  | fixture (id sha256 : String)
  /-- A theorem, by name, with its canonical axiom receipt and the digest of its
  frozen ascription text. Reaches `proved`. -/
  | thm (name axioms statementSha256 : String)
  /-- A kernel `decide` over a named finite domain. Reaches `proved`, and obliges
  the claim's residual to name the domain. -/
  | decided (name domain statementSha256 : String)
  /-- A premise taken on trust, written down. Reaches no rung. -/
  | assumed (premise : String)
deriving DecidableEq, Repr, Inhabited

namespace Evidence

/-- The rung an evidence record reaches. Not a field: a function of the constructor. -/
def rung : Evidence → RungOrHeld
  | .pin _ _ => some .pinned
  | .fixture _ _ => some .replayed
  | .thm _ _ _ => some .proved
  | .decided _ _ _ => some .proved
  | .assumed _ => none

/-- The constructor's spelling, the `_tag` of the payload. -/
def tag : Evidence → String
  | .pin _ _ => "pin"
  | .fixture _ _ => "fixture"
  | .thm _ _ _ => "thm"
  | .decided _ _ _ => "decided"
  | .assumed _ => "assumed"

def isAssumed : Evidence → Bool
  | .assumed _ => true
  | _ => false

/-- An evidence record reaches no rung exactly when it is an assumption. -/
theorem rung_eq_none_iff (e : Evidence) : e.rung = none ↔ e.isAssumed = true := by
  cases e <;> simp [rung, isAssumed]

/-- The record as store content, per ruling R5: a tagged object whose keys are
in constructor-argument order. -/
def json : Evidence → Json
  | .pin spanSha256 guard =>
      .obj [("_tag", .str "pin"), ("spanSha256", .str spanSha256), ("guard", .str guard)]
  | .fixture id sha256 =>
      .obj [("_tag", .str "fixture"), ("id", .str id), ("sha256", .str sha256)]
  | .thm name axioms statementSha256 =>
      .obj [ ("_tag", .str "thm"), ("name", .str name), ("axioms", .str axioms)
           , ("statementSha256", .str statementSha256) ]
  | .decided name domain statementSha256 =>
      .obj [ ("_tag", .str "decided"), ("name", .str name), ("domain", .str domain)
           , ("statementSha256", .str statementSha256) ]
  | .assumed premise =>
      .obj [("_tag", .str "assumed"), ("premise", .str premise)]

/-- The address: the digest of the payload through the one `Canonical Json`. -/
def address (e : Evidence) : Digest := digestOf e.json

end Evidence

instance : Canonical Evidence := ⟨fun e => encode e.json⟩

/-- The rung a list of evidence supports: the join over the list, HELD when it
is empty. A monoid homomorphism from `(List Evidence, ++, [])`. -/
def supportedOf : List Evidence → RungOrHeld :=
  List.foldr (fun e acc => RungOrHeld.join e.rung acc) none

theorem supportedOf_nil : supportedOf [] = none := rfl

theorem supportedOf_cons (e : Evidence) (es : List Evidence) :
    supportedOf (e :: es) = RungOrHeld.join e.rung (supportedOf es) := rfl

/-- The homomorphism law. -/
theorem supportedOf_append (u v : List Evidence) :
    supportedOf (u ++ v) = RungOrHeld.join (supportedOf u) (supportedOf v) := by
  induction u with
  | nil => simp [supportedOf_nil, RungOrHeld.bot_join]
  | cons e r ih => simp [supportedOf_cons, ih, RungOrHeld.join_assoc]

/-- Every listed record is at most what the list supports. -/
theorem le_supportedOf_of_mem {e : Evidence} {es : List Evidence} (h : e ∈ es) :
    RungOrHeld.le e.rung (supportedOf es) = true := by
  induction es with
  | nil => cases h
  | cons a r ih =>
    rw [supportedOf_cons]
    cases List.mem_cons.mp h with
    | inl hea => rw [hea]; exact RungOrHeld.le_join_left _ _
    | inr hmem => exact RungOrHeld.le_trans (ih hmem) (RungOrHeld.le_join_right _ _)

/-- **Monotonicity.** Adding evidence never lowers the supported rung. -/
theorem supportedOf_mono {u v : List Evidence} (h : u.Sublist v) :
    RungOrHeld.le (supportedOf u) (supportedOf v) = true := by
  induction h with
  | slnil => exact RungOrHeld.le_refl _
  | cons a _ ih =>
    rw [supportedOf_cons]
    exact RungOrHeld.le_trans ih (RungOrHeld.le_join_right _ _)
  | cons_cons a _ ih =>
    rw [supportedOf_cons, supportedOf_cons]
    exact RungOrHeld.join_le_join ih

/-- **HELD is forced** when nothing but assumptions back a claim. -/
theorem supported_none_of_all_assumed (es : List Evidence)
    (h : ∀ e ∈ es, e.isAssumed = true) : supportedOf es = none := by
  induction es with
  | nil => rfl
  | cons e r ih =>
    rw [supportedOf_cons, (Evidence.rung_eq_none_iff e).mpr (h e (List.mem_cons_self ..)),
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    rfl

/-- **The kept refutation.** A rung is not a function of an evidence count: one
theorem outranks any number of assumptions. No theorem may read a rung off a
length. -/
theorem supported_not_by_count :
    ∃ u v : List Evidence, u.length < v.length ∧
      RungOrHeld.le (supportedOf v) (supportedOf u) = true :=
  ⟨[.thm "t" "none" "s"], [.assumed "a", .assumed "b"], by decide, by decide⟩

/-- What kind of statement a claim makes. A closed vocabulary. -/
inductive ClaimKind where
  | equation
  | invariant
  | traceProperty
  | gradeClause
  | integration
deriving DecidableEq, Repr, Inhabited

def ClaimKind.spelling : ClaimKind → String
  | .equation => "equation"
  | .invariant => "invariant"
  | .traceProperty => "traceProperty"
  | .gradeClause => "gradeClause"
  | .integration => "integration"

/-- The only registry record that asserts anything, and so the only one with a
coherence obligation. `evidence` holds addresses; `summary` and `residual` are
authored sentences and are the two fields no generator derives. -/
structure Claim where
  /-- Stable for the life of the claim; one name binds the Lean surface, the
  manifest row and the registry path. -/
  id : String
  component : String
  /-- `none` means the claim is about the component as a whole. -/
  verb : Option String
  kind : ClaimKind
  /-- What is asserted, one sentence. Authored. -/
  summary : String
  /-- The declared rung. `none` is HELD. -/
  rung : RungOrHeld
  /-- The addresses of the evidence records, in a fixed order. -/
  evidence : List Digest
  /-- Where the evidence stops. Authored. -/
  residual : String
deriving DecidableEq, Repr, Inhabited

namespace Claim

/-- A claim written down but not asserted. -/
def held (c : Claim) : Bool := c.rung.isNone

/-- The rung the claim's evidence supports, given the resolver from address to
record. An address the resolver does not know contributes nothing. -/
def supported (c : Claim) (evidenceAt : Digest → Option Evidence) : RungOrHeld :=
  supportedOf (c.evidence.filterMap evidenceAt)

/-- The decidable half of coherence: the declared rung is at most the supported one. -/
def coherent (c : Claim) (evidenceAt : Digest → Option Evidence) : Bool :=
  RungOrHeld.le c.rung (c.supported evidenceAt)

/-- **A claim never outranks its evidence.** Definitionally the coherence check;
stated as a theorem because it is the sentence the registry's reader looks for. -/
theorem not_outranks (c : Claim) (evidenceAt : Digest → Option Evidence)
    (h : c.coherent evidenceAt = true) :
    RungOrHeld.le c.rung (c.supported evidenceAt) = true := h

/-- Every record a claim resolves is at most the claim's support. -/
theorem evidence_le_supported (c : Claim) (evidenceAt : Digest → Option Evidence)
    (e : Evidence) (h : e ∈ c.evidence.filterMap evidenceAt) :
    RungOrHeld.le e.rung (c.supported evidenceAt) = true :=
  le_supportedOf_of_mem h

/-- The trie name: `["claim", component, verbOrStar, id]`. -/
def path (c : Claim) : Path :=
  ["claim", c.component, c.verb.getD "*", c.id]

/-- The claim as store content, per ruling R5. Evidence crosses as hex addresses. -/
def json (c : Claim) : Json :=
  .obj
    [ ("type", .str "claim")
    , ("id", .str c.id)
    , ("component", .str c.component)
    , ("verb", match c.verb with | some v => .str v | none => .null)
    , ("kind", .str c.kind.spelling)
    , ("summary", .str c.summary)
    , ("rung", .str c.rung.spelling)
    , ("evidence", .arr (c.evidence.map fun d => Json.str d.hex))
    , ("residual", .str c.residual) ]

/-- The address: the digest of the payload through the one `Canonical Json`. -/
def address (c : Claim) : Digest := digestOf c.json

end Claim

instance : Canonical Claim := ⟨fun c => encode c.json⟩

end Effect4.Char
