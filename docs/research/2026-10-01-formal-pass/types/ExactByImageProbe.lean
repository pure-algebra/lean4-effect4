import Effect4.Laws.Schema.Codec
import Effect4.Schema.Bridge

/-!
# Seat TYPES, formal pass (2026-10-01): from a retraction to an exact embedding (K2)

Research probe, outside every root; nothing imports it.

Row 128 (ruled 2026-10-01) calls `Ty.ofSchema` and the JSON codec retractions until their
exactness theorems land, and names the repairs (a whole-check comparison, the `var` repair, a
canonical-branch check in `decode`, a named key-order normaliser). This probe states the K2 law
in the partial-isomorphism form the literature uses and checks one general fact about it:

* §1 (proved, generic). Any (write, read) pair with the retraction law becomes an exact
  embedding modulo a normaliser `N` when the read is guarded by the writer's image:
  `readExact f = some a → ∃ f', write a = some f' ∧ N f' = N f` (exactness), the retraction is
  kept, the guard only refuses, and when `read` is `N`-invariant the guarded read answers
  EXACTLY the `N`-classes of the images (a partial isomorphism between the domain and the
  image modulo `N`; Rendel and Ostermann's partial isomorphism, a lawful prism up to `N`).
* §2 (proved and tested) on the tree's codec at canonical types: the guarded `decode` keeps
  `decode_of_encode` and is exact; it refuses the data probe's V2 witness, the `Success` image
  that today decodes at `union (except nat nat) (exitOf nat nat)` to the value whose encoding is
  the `Failure` image.
* §3 (tested) on the tree's `ofSchema`: the guarded read refuses the V1 witnesses (a check
  read by its id alone) and keeps the retraction on closed types.

The guard is the cheapest repair, not the only one: making `decodeRaw`'s union arm and
`ofSchema`'s check comparison exact by construction gives the same theorem without the
re-encoding cost.
-/

set_option autoImplicit false

namespace Research.TypesSeat.Exact

open Effect4 Effect4.Program Effect4.Machine

/-! ## §1 The general fact -/

section Generic
variable {A F : Type} [DecidableEq F]

/-- The image-checked read: answer `a` only when the writer gives the input back modulo `N`. -/
def readExact (write : A → Option F) (read : F → Option A) (N : F → F) (f : F) : Option A :=
  (read f).filter (fun a => decide ((write a).map N = some (N f)))

variable {write : A → Option F} {read : F → Option A} {N : F → F}

/-- The guard only refuses. -/
theorem readExact_le {f : F} {a : A} (h : readExact write read N f = some a) : read f = some a := by
  unfold readExact at h
  rw [Option.filter_eq_some_iff] at h
  exact h.1

/-- **Exactness modulo `N`** (K2's third law). -/
theorem readExact_exact {f : F} {a : A} (h : readExact write read N f = some a) :
    ∃ f', write a = some f' ∧ N f' = N f := by
  unfold readExact at h
  rw [Option.filter_eq_some_iff] at h
  have hg := of_decide_eq_true h.2
  cases hw : write a with
  | none => rw [hw] at hg; exact absurd hg (by simp only [Option.map_none, reduceCtorEq, not_false_eq_true])
  | some f' =>
    rw [hw, Option.map_some, Option.some.injEq] at hg
    exact ⟨f', rfl, hg⟩

/-- **The retraction is kept** (K2's second law). -/
theorem readExact_retract {a : A} {f : F} (hw : write a = some f) (hr : read f = some a) :
    readExact write read N f = some a := by
  unfold readExact
  rw [Option.filter_eq_some_iff]
  refine ⟨hr, decide_eq_true ?_⟩
  rw [hw, Option.map_some]

/-- **A partial isomorphism modulo `N`.** When `read` cannot tell `N`-equivalent inputs apart
and is a retraction of `write`, the guarded read answers exactly the `N`-classes of the images. -/
theorem readExact_iff
    (hret : ∀ a f, write a = some f → read f = some a)
    (hinv : ∀ f, read (N f) = read f) {f : F} {a : A} :
    readExact write read N f = some a ↔ ∃ f', write a = some f' ∧ N f' = N f := by
  constructor
  · exact readExact_exact
  · rintro ⟨f', hw, hN⟩
    have hr : read f = some a := by
      rw [← hinv f, ← hN, hinv f']
      exact hret a f' hw
    unfold readExact
    rw [Option.filter_eq_some_iff]
    refine ⟨hr, decide_eq_true ?_⟩
    rw [hw, Option.map_some, hN]

end Generic

/-! ## §2 The JSON codec at canonical types -/

/-- The canonical-branch check: decode, then require the encoder to give the input back. The
key-order normaliser is `id` here; with records it is the named field sort (row 119). -/
def decodeExact (t : Ty) (j : Json) : Option Val :=
  readExact (Schema.encode t) (Schema.decode t) id j

theorem decodeExact_retract {t : CTy} {v : Val} {j : Json} (h : Schema.encode t.toRaw v = some j) :
    decodeExact t.toRaw j = some v :=
  readExact_retract h (Schema.decode_of_encode h)

theorem decodeExact_exact {t : Ty} {j : Json} {v : Val} (h : decodeExact t j = some v) :
    Schema.encode t v = some j := by
  obtain ⟨j', hw, hj⟩ := readExact_exact h
  rw [hw]
  exact congrArg some hj

theorem decodeExact_sound {t : CTy} {j : Json} {v : Val} (h : decodeExact t.toRaw j = some v) :
    Val.hasTy v t.toRaw = true :=
  Schema.hasTy_decode (readExact_le h)

def overlap : Ty := .union (.except .nat .nat) (.exitOf .nat .nat)
def jFailure : Json := .obj [("_tag", .str "Failure"), ("failure", Effect4.Arch.Json.ofNat 1)]
def jSuccess : Json := .obj [("_tag", .str "Success"), ("value", Effect4.Arch.Json.ofNat 1)]

-- tested: today two images decode to one value (decode is not injective, so not exact)
#guard Schema.decode overlap jFailure = some (.ctor 0 [.nat 1])
#guard Schema.decode overlap jSuccess = some (.ctor 0 [.nat 1])
-- tested: the guarded decode keeps the encoder's image and refuses the other one
#guard decodeExact overlap jFailure = some (.ctor 0 [.nat 1])
#guard decodeExact overlap jSuccess = none
-- tested (RED CONTROL for the guard's necessity): the unguarded decode's answer on `jSuccess`
-- re-encodes to a different JSON value
#guard Schema.encode overlap (.ctor 0 [.nat 1]) ≠ some jSuccess

/-! ## §3 The schema bridge -/

/-- The schema writer is total; the guarded read compares the whole representation. -/
def ofSchemaExact (r : Representation) : Option Ty :=
  readExact (fun t => some (Schema.Bridge.schema t)) Schema.Bridge.ofSchema id r

theorem ofSchemaExact_retract {t : Ty} (h : t.closed = true) :
    ofSchemaExact (Schema.Bridge.schema t) = some t :=
  readExact_retract rfl (Schema.Bridge.ofSchema_schema t h)

theorem ofSchemaExact_exact {r : Representation} {t : Ty} (h : ofSchemaExact r = some t) :
    Schema.Bridge.schema t = r := by
  obtain ⟨r', hw, hr⟩ := readExact_exact h
  cases hw
  exact hr

/-- V1a of the data probe: a filter group whose own id is `isInt`, holding a `>= 5` check. -/
def groupedInt : Representation :=
  .number none [Effect4.Schema.Check.group
    (Effect4.Schema.Check.named "effect/schema/isGreaterThanOrEqualTo"
      (.obj [("minimum", Effect4.Arch.Json.ofNat 5)])) []
    none (some ⟨"effect/schema/isInt", .null, none⟩)]

-- tested: today it reads back as `int`; the guarded read refuses it
#guard Schema.Bridge.ofSchema groupedInt = some .int
#guard ofSchemaExact groupedInt = none
-- tested: the retraction on an ordinary closed type survives the guard
#guard ofSchemaExact (Schema.Bridge.schema (.prod .nat (.option .string))) = some (.prod .nat (.option .string))

end Research.TypesSeat.Exact

#print axioms Research.TypesSeat.Exact.readExact_le
#print axioms Research.TypesSeat.Exact.readExact_exact
#print axioms Research.TypesSeat.Exact.readExact_retract
#print axioms Research.TypesSeat.Exact.readExact_iff
#print axioms Research.TypesSeat.Exact.decodeExact_retract
#print axioms Research.TypesSeat.Exact.decodeExact_exact
#print axioms Research.TypesSeat.Exact.decodeExact_sound
#print axioms Research.TypesSeat.Exact.ofSchemaExact_retract
#print axioms Research.TypesSeat.Exact.ofSchemaExact_exact
