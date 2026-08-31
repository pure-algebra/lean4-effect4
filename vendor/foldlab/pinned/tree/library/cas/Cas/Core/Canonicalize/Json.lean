import Cas.Core.Canonicalize
import Cas.Values.Json

/-!
# The key-sorting method — CAS-003's spelling normalizer, packaged

The first `Canonicalizer` instance: `canonValue` sorts every object's
fields by key, recursively, with the same comparator `renderCompact`
sorts by. Fields canonicalize before they sort, so the recursion is
structural — the same discipline as the printers.

What is proved here:

- `canonValue_idem` — the method is idempotent, so it packages as
  `canonJson : Canonicalizer Value`;
- `canonValue_of_canonical` — canonically spelled values are fixed
  points: the method never touches what is already canonical;
- `canonJson_preserves_renderCompact` — the preservation law: the
  method never changes the canonical bytes, so it is admissible for
  the CAS-003 observation, and form equality implies byte equality
  (`renderCompact_eq_of_equiv`).

The fixed-point set is deliberately LARGER than `Value.Canonical`: an
object with duplicate keys sorts stably and is fixed once sorted, yet
never satisfies the strict-order predicate. Duplicate keys are an
admission question (refusal territory), not a normalization question —
this method reorders spellings and nothing else. The guard theorem
(no-duplicate keys ⇒ the representative is `Value.Canonical`) is the
named next statement of this slice.

Direction-law position: normalize-side only (the acquisition loop's
NORMALIZE verb, for hoovered carriers arriving in foreign key order).
Never applied on the load path — renormalize-on-read stays a named
defect.

discharges(values-canonicalize-misfile): relocated to its stratum at
the meta-home migration. The module was `Cas/Values/Canonicalize.lean`
and imported `Cas.Core.Canonicalize` to package `canonValue` as the
store's `Canonicalizer Value` instance — a `Cas`-stratum module by the
strata rule, excluded from the `CasValues` library while sitting in
`Cas/Values/`. It now sits beside the class it instantiates, as
`Cas/Core/Canonicalize/Json.lean`, and the directory and the stratum
agree.

The namespace did NOT move with the file, deliberately: `Cas.Json` is
where `Value` and its printers live, and `canonValue` is a function of
the value plane whatever library holds it. The directory names the
STRATUM, the namespace names the mathematical object; only the first
of those was wrong.
-/

namespace Cas.Json

mutual

/-- Key-sorting canonicalization: every object's fields sorted by key,
recursively; scalars unchanged. Fields canonicalize before they sort,
so the recursion stays structural. -/
def canonValue : Value → Value
  | .null => .null
  | .bool b => .bool b
  | .nat n => .nat n
  | .int i => .int i
  | .str s => .str s
  | .arr xs => .arr (canonItems xs)
  | .obj fields =>
    .obj ((canonFields fields).mergeSort fun a b => decide (a.1 ≤ b.1))

def canonItems : List Value → List Value
  | [] => []
  | x :: rest => canonValue x :: canonItems rest

def canonFields : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: rest => (k, canonValue v) :: canonFields rest

end

theorem canonFields_eq_map (fs : List (String × Value)) :
    canonFields fs = fs.map fun f => (f.1, canonValue f.2) := by
  induction fs with
  | nil => rfl
  | cons f rest ih => cases f; simp [canonFields, ih]

/-- Mapping a function that fixes every member is the identity.

Public because the reference-bearing twin of this method
(`Cas.canonR`, `Cas/Core/Refs.lean`) discharges its own idempotence
with the same two facts. Two carriers, one determination — the
alternative is a second copy of a proof that is already here. -/
theorem map_eq_self_of_mem {β : Type _} {f : β → β} :
    ∀ {l : List β}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, h x (by simp),
      map_eq_self_of_mem fun a ha => h a (by simp [ha])]

/-- Strict key order gives the (non-strict, Bool-valued) order the
canonical machinery sorts by. -/
private theorem le_of_key_lt {a b : String} (h : a < b) : a ≤ b :=
  Std.le_of_not_ge fun hge => hge h

/-- The sort's output is key-ordered — transitivity and totality of the
string order, discharged once for both pair carriers. Generic in the
value type on purpose: the same fact serves `Value` fields here and
`RValue` fields in `Cas/Core/Refs.lean`. -/
theorem pairwise_mergeSort_keys {β : Type _}
    (l : List (String × β)) :
    ((l.mergeSort fun a b => decide (a.1 ≤ b.1)).Pairwise
      fun a b => decide (a.1 ≤ b.1) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact Std.le_trans hab hbc
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Std.le_total

mutual

/-- The method is idempotent: a second pass finds every object already
sorted and every subvalue already normalized. -/
theorem canonValue_idem : ∀ v, canonValue (canonValue v) = canonValue v
  | .null => rfl
  | .bool _ => rfl
  | .nat _ => rfl
  | .int _ => rfl
  | .str _ => rfl
  | .arr xs => by
    simp only [canonValue]
    rw [canonItems_idem xs]
  | .obj fields => by
    simp only [canonValue]
    have hfix :
        canonFields
            ((canonFields fields).mergeSort fun a b => decide (a.1 ≤ b.1)) =
          (canonFields fields).mergeSort fun a b => decide (a.1 ≤ b.1) := by
      rw [canonFields_eq_map]
      apply map_eq_self_of_mem
      intro f hf
      have hmem : f ∈ canonFields fields := (List.mem_mergeSort).mp hf
      have hfx : canonValue f.2 = f.2 := canonFields_fix fields f hmem
      calc (f.1, canonValue f.2) = (f.1, f.2) := by rw [hfx]
        _ = f := rfl
    rw [hfix, List.mergeSort_of_pairwise (pairwise_mergeSort_keys _)]

theorem canonItems_idem : ∀ xs, canonItems (canonItems xs) = canonItems xs
  | [] => rfl
  | x :: rest => by
    simp only [canonItems]
    rw [canonValue_idem x, canonItems_idem rest]

/-- Every field the normalizer emits carries a normalized value — the
membership form the sorted case consumes. -/
theorem canonFields_fix :
    ∀ fs : List (String × Value), ∀ f ∈ canonFields fs,
      canonValue f.2 = f.2
  | [], f, h => by simp [canonFields] at h
  | (k, v) :: rest, f, h => by
    simp only [canonFields, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact canonValue_idem v
    · exact canonFields_fix rest f h

end

/-- The packaged method. -/
def canonJson : Canonicalizer Value := ⟨canonValue, canonValue_idem⟩

mutual

/-- Canonically spelled values are fixed points: the method never
touches what is already canonical. -/
theorem canonValue_of_canonical : ∀ v, v.Canonical → canonValue v = v
  | .null, _ => rfl
  | .bool _, _ => rfl
  | .nat _, _ => rfl
  | .int _, _ => rfl
  | .str _, _ => rfl
  | .arr xs, h => by
    simp only [canonValue]
    rw [canonItems_of_canonical xs h]
  | .obj fields, h => by
    obtain ⟨hsorted, hfields⟩ := h
    simp only [canonValue]
    rw [canonFields_of_canonical fields hfields,
      List.mergeSort_of_pairwise
        (hsorted.imp fun hab => by simpa using le_of_key_lt hab)]

theorem canonItems_of_canonical :
    ∀ xs, CanonicalItems xs → canonItems xs = xs
  | [], _ => rfl
  | x :: rest, h => by
    simp only [canonItems]
    rw [canonValue_of_canonical x h.1, canonItems_of_canonical rest h.2]

theorem canonFields_of_canonical :
    ∀ fs, CanonicalFields fs → canonFields fs = fs
  | [], _ => rfl
  | (k, v) :: rest, h => by
    simp only [canonFields]
    rw [canonValue_of_canonical v h.1, canonFields_of_canonical rest h.2]

end

/-- Canonical spellings are canonical forms of the packaged method. -/
theorem canonJson_isCanon_of_canonical {v : Value} (h : v.Canonical) :
    canonJson.IsCanon v :=
  canonValue_of_canonical v h

/-! ## Preservation — the method never changes the canonical bytes -/

private theorem renderCompactFields_map (l : List (String × Value)) :
    renderCompactFields l = l.map fun f => (f.1, renderCompact f.2) := by
  induction l with
  | nil => rfl
  | cons f rest ih => cases f; simp [renderCompactFields, ih]

/-- Rendering commutes with the key sort: the comparator reads keys
only, and rendering preserves keys. -/
private theorem renderCompactFields_mergeSort (l : List (String × Value)) :
    renderCompactFields (l.mergeSort fun a b => decide (a.1 ≤ b.1)) =
      (renderCompactFields l).mergeSort fun a b => decide (a.1 ≤ b.1) := by
  rw [renderCompactFields_map, renderCompactFields_map]
  exact List.map_mergeSort fun a _ b _ => rfl

mutual

/-- The preservation law, value grain: normalizing never changes the
canonical bytes. `renderCompact` sorts at render time, so pre-sorting
is invisible to it — proved, not assumed, because the sort is stable
and the comparator reads keys only. -/
theorem renderCompact_canonValue :
    ∀ v, renderCompact (canonValue v) = renderCompact v
  | .null => rfl
  | .bool _ => rfl
  | .nat _ => rfl
  | .int _ => rfl
  | .str _ => rfl
  | .arr xs => by
    simp only [canonValue, renderCompact]
    rw [renderCompactItems_canon xs]
  | .obj fields => by
    simp only [canonValue, renderCompact]
    rw [renderCompactFields_mergeSort, renderCompactFields_canon fields,
      List.mergeSort_of_pairwise (pairwise_mergeSort_keys _)]

theorem renderCompactItems_canon :
    ∀ xs, renderCompactItems (canonItems xs) = renderCompactItems xs
  | [] => rfl
  | x :: rest => by
    simp only [canonItems, renderCompactItems]
    rw [renderCompact_canonValue x, renderCompactItems_canon rest]

theorem renderCompactFields_canon :
    ∀ fs, renderCompactFields (canonFields fs) = renderCompactFields fs
  | [] => rfl
  | (k, v) :: rest => by
    simp only [canonFields, renderCompactFields]
    rw [renderCompact_canonValue v, renderCompactFields_canon rest]

end

/-- The packaged preservation law: `canonJson` is admissible for the
CAS-003 observation. -/
theorem canonJson_preserves_renderCompact :
    canonJson.Preserves renderCompact :=
  fun v => renderCompact_canonValue v

/-- Form equality implies byte equality: two values with one
representative render to identical canonical bytes. -/
theorem renderCompact_eq_of_equiv {v w : Value}
    (h : canonJson.Equiv v w) : renderCompact v = renderCompact w :=
  canonJson.eq_obs_of_equiv canonJson_preserves_renderCompact h

end Cas.Json
