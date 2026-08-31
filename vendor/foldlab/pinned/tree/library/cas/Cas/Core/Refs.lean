import Cas.Core.Node
import Cas.Core.Store
import Cas.Core.Canonicalize.Json

/-!
# Typed references: the marker grammar and the `Root` type

The type model of the library's typed-DAG layer. A typed reference
appears in a payload as exactly `{"$ref": k}`, and the k-th marker in
canonical byte order carries index k into the node's reference array —
one representation by construction. Three clauses:

- **Forced indexes.** Markers scanned in canonical traversal order (the
  order the compact renderer emits — codepoint-sorted keys) must read
  exactly `0, 1, …, n-1`, with exactly `n` reference entries.
  `wellRefIndexed` is the decode-side judge.
- **Sharing repeats entries.** The same target referenced twice is two
  markers and two reference entries; no dedup law exists.
- **Collision refuses.** The reserved key outside the exact marker
  shape refuses at encode (`lower` answers `none`) and at decode
  (`markerScan` answers `none`) — never an escape, which would give one
  user value two spellings and split its content identity.

Every traversal canonicalizes first (sort object fields after the
recursion, the renderer's own trick), so assignment and scan walk the
same order with structural recursion only. The scan side reuses
`Cas.Json.canonValue` — the packaged CAS-003 normalizer, already proved
idempotent and byte-preserving — rather than carrying a second copy of
it; the encode side needs the reference-bearing twin `canonR`, which is
the same method on `RValue` and discharges its idempotence from the
same two lemmas.

The coherence law `markerScan ∘ lower = range` is DISCHARGED IN GENERAL
below (`markerScan_lower`), no longer only guarded over the fixtures.
The fixtures stay as executable regression pins.

`Root α` is the typed root itself: an address claimed at a kind tag,
carrying the decoded type as a phantom index. Its edge form is an
ordinary `Ref`, which is what lets the store's admission law check
typed edges with no projection-side machinery — and in a `Closed`
store, every resident edge dereferences at its declared kind
(`Store.Closed` is exactly that statement).

discharges(values-refs-misfile): relocated to its stratum at the
meta-home migration. The module was `Cas/Values/Refs.lean` and states
store semantics outright — it imports `Cas.Core.Node` and
`Cas.Core.Store`, and `Root.closed_deref` quantifies over
`Store.Closed` — a `Cas`-stratum module by the strata rule, excluded
from the `CasValues` library while sitting in `Cas/Values/`. It now
sits beside the store it speaks of, as `Cas/Core/Refs.lean`, and the
directory and the stratum agree.

The namespace was already `Cas`, which is what every other `Cas/Core`
module declares; only the directory was wrong, and only the directory
moved.
-/

namespace Cas

open Json

/-- The reserved marker key. -/
def refKey : String := "$ref"

/-- Recognize the exact marker shape: one field, the reserved key, a
natural index. Anything else is not a marker. -/
def asMarker : Value → Option Nat
  | .obj [(k, .nat n)] => if k = refKey then some n else none
  | _ => none

/-! ## The decode-side judge

Canonicalization on the scan side is `Cas.Json.canonValue`
(`Cas/Core/Canonicalize/Json.lean`): the packaged CAS-003 method, with
`canonValue_idem` and `renderCompact_canonValue` already proved. This
model states nothing about it that is not already a theorem there. -/

mutual

/-- Marker indexes of a canonicalized value, in traversal order.
`none` is the collision refusal: the reserved key outside the exact
marker shape. -/
def scanCanon : Value → Option (List Nat)
  | .null | .bool _ | .nat _ | .int _ | .str _ => some []
  | .arr xs => scanItems xs
  | .obj fields =>
    match asMarker (.obj fields) with
    | some k => some [k]
    | none =>
      if fields.any (·.1 = refKey) then none
      else scanFields fields

def scanItems : List Value → Option (List Nat)
  | [] => some []
  | x :: rest =>
    match scanCanon x, scanItems rest with
    | some ks, some more => some (ks ++ more)
    | _, _ => none

def scanFields : List (String × Value) → Option (List Nat)
  | [] => some []
  | (_, v) :: rest =>
    match scanCanon v, scanFields rest with
    | some ks, some more => some (ks ++ more)
    | _, _ => none

end

/-- Marker indexes in canonical byte order, collision refused. -/
def markerScan (v : Value) : Option (List Nat) := scanCanon (Json.canonValue v)

/-- The forced-index law: markers read `0…n-1` in canonical order and
the reference array carries exactly `n` entries. -/
def wellRefIndexed (v : Value) (refCount : Nat) : Bool :=
  match markerScan v with
  | some ks => decide (ks = List.range refCount)
  | none => false

/-! ## The encode direction — reference-bearing trees lowered to a
payload value plus the reference array, indexes assigned in canonical
order. -/

/-- A value with typed-reference leaves — what a projection encodes
before lowering. -/
inductive RValue where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  | arr (xs : List RValue)
  | obj (fields : List (String × RValue))
  | link (r : Ref)

mutual

def canonR : RValue → RValue
  | .null => .null
  | .bool b => .bool b
  | .nat n => .nat n
  | .int i => .int i
  | .str s => .str s
  | .link r => .link r
  | .arr xs => .arr (canonRItems xs)
  | .obj fields =>
    .obj ((canonRFields fields).mergeSort fun a b => decide (a.1 ≤ b.1))

def canonRItems : List RValue → List RValue
  | [] => []
  | x :: rest => canonR x :: canonRItems rest

def canonRFields : List (String × RValue) → List (String × RValue)
  | [] => []
  | (k, v) :: rest => (k, canonR v) :: canonRFields rest

end

mutual

/-- Lower a canonicalized tree: links become markers carrying the next
index, references accumulate in traversal order, and a user object
mentioning the reserved key refuses the whole encode. -/
def lowerCanon : RValue → List Ref → Option (Value × List Ref)
  | .null, acc => some (.null, acc)
  | .bool b, acc => some (.bool b, acc)
  | .nat n, acc => some (.nat n, acc)
  | .int i, acc => some (.int i, acc)
  | .str s, acc => some (.str s, acc)
  | .link r, acc => some (.obj [(refKey, .nat acc.length)], acc ++ [r])
  | .arr xs, acc =>
    match lowerItems xs acc with
    | some (vs, acc') => some (.arr vs, acc')
    | none => none
  | .obj fields, acc =>
    if fields.any (·.1 = refKey) then none
    else
      match lowerFields fields acc with
      | some (fs, acc') => some (.obj fs, acc')
      | none => none

def lowerItems : List RValue → List Ref → Option (List Value × List Ref)
  | [], acc => some ([], acc)
  | x :: rest, acc =>
    match lowerCanon x acc with
    | some (v, acc') =>
      match lowerItems rest acc' with
      | some (vs, acc'') => some (v :: vs, acc'')
      | none => none
    | none => none

def lowerFields :
    List (String × RValue) → List Ref →
      Option (List (String × Value) × List Ref)
  | [], acc => some ([], acc)
  | (k, v) :: rest, acc =>
    match lowerCanon v acc with
    | some (v', acc') =>
      match lowerFields rest acc' with
      | some (fs, acc'') => some ((k, v') :: fs, acc'')
      | none => none
    | none => none

end

/-- The encoder: canonicalize, then assign indexes in traversal order.
`none` is the collision refusal. -/
def lower (v : RValue) : Option (Value × List Ref) := lowerCanon (canonR v) []

/-! ## The links a tree carries, in canonical traversal order

`linksOf` reads off the reference array a tree WILL produce, without
lowering it. Stating the coherence law against this function rather
than against an existential is what makes it usable by a projection:
the bridge's agreement law is `refs = linksOf (canonR …)` composed with
a canonicity fact about its own image, not a re-derivation of the
traversal. -/

mutual

/-- The references a canonicalized tree carries, in traversal order. -/
def linksOf : RValue → List Ref
  | .null | .bool _ | .nat _ | .int _ | .str _ => []
  | .link r => [r]
  | .arr xs => linksItems xs
  | .obj fields => linksFields fields

def linksItems : List RValue → List Ref
  | [] => []
  | x :: rest => linksOf x ++ linksItems rest

def linksFields : List (String × RValue) → List Ref
  | [] => []
  | (_, v) :: rest => linksOf v ++ linksFields rest

end

/-! ## Fixtures — the executable law -/

def addrA : Addr32 := ⟨List.replicate 32 1, by simp⟩
def addrB : Addr32 := ⟨List.replicate 32 2, by simp⟩

def refA : Ref := ⟨5, addrA⟩
def refB : Ref := ⟨7, addrB⟩

/-- Declaration order disagrees with canonical order — the load-bearing
fixture: the link under `a` is assigned index 0 although declared
second. -/
def orderFixture : RValue :=
  .obj [("b", .link refA), ("a", .link refB)]

def refFixtures : List RValue :=
  [ .obj [("author", .link refA), ("title", .str "hi")]
  , orderFixture
  , .arr [.link refA, .link refA]
  , .obj [("z", .nat 3), ("list", .arr [.link refB, .obj [("deep", .link refA)]])]
  , .obj [("data", .obj [(refKey, .nat 0)])]
  , .obj [(refKey, .str "x"), ("y", .nat 1)]
  , .obj [("k", .arr [.nat 1, .nat 2])] ]

-- The coherence guard: every lowered fixture satisfies the decode-side
-- judge — assignment and scan walk one order.
#guard refFixtures.all fun fixture =>
  match lower fixture with
  | some (payload, refs) => wellRefIndexed payload refs.length
  | none => true

-- The two collision fixtures refuse, the rest lower.
#guard (refFixtures.map fun f => (lower f).isSome)
  == [true, true, true, true, false, false, true]

-- Canonical assignment: the `a`-declared-second link takes index 0,
-- so the reference array leads with its target.
#guard (lower orderFixture).map (fun (_, refs) => refs) == some [refB, refA]

/-- A marker at index `k`. -/
def marker (k : Nat) : Value := .obj [(refKey, .nat k)]

-- The forced-index law refuses disorder, gaps, duplication, count
-- mismatch, malformed markers, and payload collisions.
#guard wellRefIndexed (.obj [("a", marker 0), ("b", marker 1)]) 2 == true
#guard wellRefIndexed (.obj [("a", marker 1), ("b", marker 0)]) 2 == false
#guard wellRefIndexed (.arr [marker 0, marker 2]) 3 == false
#guard wellRefIndexed (.arr [marker 0, marker 0]) 2 == false
#guard wellRefIndexed (.arr [marker 0]) 2 == false
#guard wellRefIndexed (.obj [(refKey, .nat 0), ("x", .nat 1)]) 1 == false
#guard wellRefIndexed (.obj [(refKey, .str "0")]) 1 == false
#guard wellRefIndexed (.obj [("k", .nat 1)]) 0 == true

/-! ## The coherence law — `markerScan ∘ lower = range`, in general

This model's own named follow-up, discharged. The fixtures above are
now regression pins on a theorem rather than the only evidence for it,
and every projection that lowers a reference-bearing tree gets the
forced-index law for free instead of guarding it per kind.

The induction is a single pass with three conclusions, because they are
mutually load-bearing and separating them would mean walking the tree
three times: lowering a CANONICAL tree

1. produces a CANONICAL value — `markerScan` canonicalizes before it
   scans, so without this the scan is looking at a different tree;
2. appends exactly `linksOf` of the tree to the accumulator — which is
   what makes the reference array a function of the tree and not of the
   traversal; and
3. lays the marker indexes down as `range' acc.length (links).length` —
   the contiguous block starting where the accumulator already stood.

The accumulator generality in (3) is what makes the induction go
through at all: a subtree's markers are forced relative to the
references its LEFT SIBLINGS already contributed, so the statement has
to be about a block at an offset, never about `range` from zero. The
top-level law is the `acc = []` instance. -/

/-- Concatenating adjacent index blocks. -/
private theorem range'_append (s m n : Nat) :
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
  simp

theorem canonRFields_eq_map (fs : List (String × RValue)) :
    canonRFields fs = fs.map fun f => (f.1, canonR f.2) := by
  induction fs with
  | nil => rfl
  | cons f rest ih => cases f; simp [canonRFields, ih]

mutual

/-- The reference-bearing method is idempotent, exactly as its
value-plane twin is — same proof, same two lemmas, one carrier apart. -/
theorem canonR_idem : ∀ r, canonR (canonR r) = canonR r
  | .null => rfl
  | .bool _ => rfl
  | .nat _ => rfl
  | .int _ => rfl
  | .str _ => rfl
  | .link _ => rfl
  | .arr xs => by
    simp only [canonR]
    rw [canonRItems_idem xs]
  | .obj fields => by
    simp only [canonR]
    have hfix :
        canonRFields
            ((canonRFields fields).mergeSort fun a b => decide (a.1 ≤ b.1)) =
          (canonRFields fields).mergeSort fun a b => decide (a.1 ≤ b.1) := by
      rw [canonRFields_eq_map]
      apply Json.map_eq_self_of_mem
      intro f hf
      have hmem : f ∈ canonRFields fields := (List.mem_mergeSort).mp hf
      have hfx : canonR f.2 = f.2 := canonRFields_fix fields f hmem
      calc (f.1, canonR f.2) = (f.1, f.2) := by rw [hfx]
        _ = f := rfl
    rw [hfix, List.mergeSort_of_pairwise (Json.pairwise_mergeSort_keys _)]

theorem canonRItems_idem : ∀ xs, canonRItems (canonRItems xs) = canonRItems xs
  | [] => rfl
  | x :: rest => by
    simp only [canonRItems]
    rw [canonR_idem x, canonRItems_idem rest]

/-- Every field the method emits carries a normalized value. -/
theorem canonRFields_fix :
    ∀ fs : List (String × RValue), ∀ f ∈ canonRFields fs, canonR f.2 = f.2
  | [], f, h => by simp [canonRFields] at h
  | (k, v) :: rest, f, h => by
    simp only [canonRFields, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact canonR_idem v
    · exact canonRFields_fix rest f h

end

/-- A canonical object, unpacked: its fields are individually normal AND
key-ordered. Both halves are needed downstream and both are consequences
of the one fixed-point equation, so they are read off it once. -/
theorem canonR_obj_fix {fields : List (String × RValue)}
    (h : canonR (.obj fields) = .obj fields) :
    canonRFields fields = fields ∧
      fields.Pairwise (fun a b => decide (a.1 ≤ b.1) = true) := by
  simp only [canonR, RValue.obj.injEq] at h
  have hcf : canonRFields fields = fields := by
    rw [canonRFields_eq_map]
    apply Json.map_eq_self_of_mem
    intro f hf
    have hmem : f ∈ canonRFields fields :=
      (List.mem_mergeSort).mp (by rw [h]; exact hf)
    have hfx : canonR f.2 = f.2 := canonRFields_fix fields f hmem
    calc (f.1, canonR f.2) = (f.1, f.2) := by rw [hfx]
      _ = f := rfl
  refine ⟨hcf, ?_⟩
  have := Json.pairwise_mergeSort_keys (canonRFields fields)
  rw [h] at this
  exact this

/-- Key order on the pairs is key order on the keys — the transfer the
object case needs, because the lowered fields agree with the source
fields on KEYS and on nothing else. -/
private theorem pairwise_keys_iff {β : Type _} (l : List (String × β)) :
    l.Pairwise (fun a b => decide (a.1 ≤ b.1) = true) ↔
      (l.map (·.1)).Pairwise (fun a b => decide (a ≤ b) = true) := by
  rw [List.pairwise_map]

mutual

/-- The coherence induction. See the section note for why the three
conclusions travel together. -/
theorem lowerCanon_coh :
    ∀ (r : RValue) (acc : List Ref) (v : Value) (acc' : List Ref),
      canonR r = r → lowerCanon r acc = some (v, acc') →
        Json.canonValue v = v ∧ acc' = acc ++ linksOf r ∧
          scanCanon v = some (List.range' acc.length (linksOf r).length)
  | .null, acc, v, acc', _, h => by
    simp only [lowerCanon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, by simp [linksOf], by simp [scanCanon, linksOf]⟩
  | .bool b, acc, v, acc', _, h => by
    simp only [lowerCanon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, by simp [linksOf], by simp [scanCanon, linksOf]⟩
  | .nat n, acc, v, acc', _, h => by
    simp only [lowerCanon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, by simp [linksOf], by simp [scanCanon, linksOf]⟩
  | .int i, acc, v, acc', _, h => by
    simp only [lowerCanon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, by simp [linksOf], by simp [scanCanon, linksOf]⟩
  | .str s, acc, v, acc', _, h => by
    simp only [lowerCanon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, by simp [linksOf], by simp [scanCanon, linksOf]⟩
  | .link r, acc, v, acc', _, h => by
    simp only [lowerCanon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    refine ⟨by simp [Json.canonValue, Json.canonFields], by simp [linksOf], ?_⟩
    simp [scanCanon, asMarker, linksOf]
  | .arr xs, acc, v, acc', hc, h => by
    have hxs : canonRItems xs = xs := by
      simpa only [canonR, RValue.arr.injEq] using hc
    simp only [lowerCanon] at h
    split at h
    next vs acc'' hi =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, ha⟩ := h
      subst hv; subst ha
      obtain ⟨hcan, hacc, hscan⟩ := lowerItems_coh xs acc vs acc'' hxs hi
      exact ⟨by simp only [Json.canonValue, hcan],
        by simpa only [linksOf] using hacc,
        by simpa only [scanCanon, linksOf] using hscan⟩
    next => exact nomatch h
  | .obj fields, acc, v, acc', hc, h => by
    obtain ⟨hcf, hpair⟩ := canonR_obj_fix hc
    simp only [lowerCanon] at h
    split at h
    next => exact nomatch h
    next hany =>
      simp only [Bool.not_eq_true, List.any_eq_false] at hany
      split at h
      next gs acc'' hf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, ha⟩ := h
        subst hv; subst ha
        obtain ⟨hcan, hkeys, hacc, hscan⟩ :=
          lowerFields_coh fields acc gs acc'' hcf hf
        -- The lowered fields carry the source keys, so they inherit
        -- both the key order and the absence of the reserved key.
        have hgpair : gs.Pairwise (fun a b => decide (a.1 ≤ b.1) = true) :=
          (pairwise_keys_iff gs).mpr
            (by rw [hkeys]; exact (pairwise_keys_iff fields).mp hpair)
        have hgany : ∀ g ∈ gs, ¬ (g.1 = refKey) := by
          intro g hg hk
          have : g.1 ∈ fields.map (·.1) := by
            rw [← hkeys]; exact List.mem_map_of_mem hg
          obtain ⟨f, hfmem, hfeq⟩ := List.mem_map.mp this
          exact absurd (hfeq.trans hk) (by simpa using hany f hfmem)
        refine ⟨?_, by simpa only [linksOf] using hacc, ?_⟩
        · simp only [Json.canonValue, hcan,
            List.mergeSort_of_pairwise hgpair]
        · have hmark : asMarker (.obj gs) = none := by
            unfold asMarker
            split
            next k n hgs =>
              have hgs' : gs = [(k, Value.nat n)] := by injection hgs
              have : (k, Value.nat n) ∈ gs := by rw [hgs']; simp
              exact if_neg (hgany _ this)
            next => rfl
          have hno : gs.any (·.1 = refKey) = false := by
            simp only [List.any_eq_false]
            intro g hg
            simpa using hgany g hg
          simp only [scanCanon, hmark, hno, linksOf]
          exact hscan
      next => exact nomatch h

theorem lowerItems_coh :
    ∀ (xs : List RValue) (acc : List Ref) (vs : List Value) (acc' : List Ref),
      canonRItems xs = xs → lowerItems xs acc = some (vs, acc') →
        Json.canonItems vs = vs ∧ acc' = acc ++ linksItems xs ∧
          scanItems vs = some (List.range' acc.length (linksItems xs).length)
  | [], acc, vs, acc', _, h => by
    simp only [lowerItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, by simp [linksItems], by simp [scanItems, linksItems]⟩
  | x :: rest, acc, vs, acc', hc, h => by
    obtain ⟨hx, hrest⟩ : canonR x = x ∧ canonRItems rest = rest := by
      simp only [canonRItems, List.cons.injEq] at hc
      exact hc
    simp only [lowerItems] at h
    split at h
    next v acc1 h1 =>
      split at h
      next ws acc2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, ha⟩ := h
        subst hv; subst ha
        obtain ⟨hcan1, hacc1, hscan1⟩ := lowerCanon_coh x acc v acc1 hx h1
        obtain ⟨hcan2, hacc2, hscan2⟩ := lowerItems_coh rest acc1 ws acc2 hrest h2
        refine ⟨by simp only [Json.canonItems, hcan1, hcan2], ?_, ?_⟩
        · rw [hacc2, hacc1, linksItems, List.append_assoc]
        · have hlen : acc1.length = acc.length + (linksOf x).length := by
            rw [hacc1]; simp
          simp only [scanItems, hscan1, hlen] at hscan2 ⊢
          rw [hscan2, linksItems]
          simp only [List.length_append]
          rw [range'_append]
      next => exact nomatch h
    next => exact nomatch h

theorem lowerFields_coh :
    ∀ (fs : List (String × RValue)) (acc : List Ref)
      (gs : List (String × Value)) (acc' : List Ref),
      canonRFields fs = fs → lowerFields fs acc = some (gs, acc') →
        Json.canonFields gs = gs ∧ gs.map (·.1) = fs.map (·.1) ∧
          acc' = acc ++ linksFields fs ∧
          scanFields gs = some (List.range' acc.length (linksFields fs).length)
  | [], acc, gs, acc', _, h => by
    simp only [lowerFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, ha⟩ := h
    subst hv; subst ha
    exact ⟨rfl, rfl, by simp [linksFields], by simp [scanFields, linksFields]⟩
  | (k, x) :: rest, acc, gs, acc', hc, h => by
    obtain ⟨hx, hrest⟩ : canonR x = x ∧ canonRFields rest = rest := by
      simp only [canonRFields, List.cons.injEq, Prod.mk.injEq] at hc
      exact ⟨hc.1.2, hc.2⟩
    simp only [lowerFields] at h
    split at h
    next v acc1 h1 =>
      split at h
      next ws acc2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, ha⟩ := h
        subst hv; subst ha
        obtain ⟨hcan1, hacc1, hscan1⟩ := lowerCanon_coh x acc v acc1 hx h1
        obtain ⟨hcan2, hkeys2, hacc2, hscan2⟩ :=
          lowerFields_coh rest acc1 ws acc2 hrest h2
        refine ⟨by simp only [Json.canonFields, hcan1, hcan2], ?_, ?_, ?_⟩
        · simp only [List.map_cons, hkeys2]
        · rw [hacc2, hacc1, linksFields, List.append_assoc]
        · have hlen : acc1.length = acc.length + (linksOf x).length := by
            rw [hacc1]; simp
          simp only [scanFields, hscan1, hlen] at hscan2 ⊢
          rw [hscan2, linksFields]
          simp only [List.length_append]
          rw [range'_append]
      next => exact nomatch h
    next => exact nomatch h

end

/-- **The coherence law.** The markers a lowered payload carries read
`0, 1, …, n-1` in canonical byte order, and the reference array is
exactly the tree's own links in that order. Both halves at once, because
the forced-index law is only worth anything alongside the statement of
WHICH references the indexes point into. -/
theorem markerScan_lower {r : RValue} {payload : Value} {refs : List Ref}
    (h : lower r = some (payload, refs)) :
    refs = linksOf (canonR r) ∧
      markerScan payload = some (List.range refs.length) := by
  obtain ⟨hcan, hacc, hscan⟩ :=
    lowerCanon_coh (canonR r) [] payload refs (canonR_idem r) h
  have hrefs : refs = linksOf (canonR r) := by simpa using hacc
  refine ⟨hrefs, ?_⟩
  simp only [markerScan, hcan]
  rw [hscan, hrefs]
  simp [List.range_eq_range']

/-- The decode-side judge accepts every lowered payload — the fixtures'
`#guard` above, now a theorem for every tree. -/
theorem wellRefIndexed_lower {r : RValue} {payload : Value} {refs : List Ref}
    (h : lower r = some (payload, refs)) :
    wellRefIndexed payload refs.length = true := by
  simp only [wellRefIndexed, (markerScan_lower h).2]
  simp

/-! ## The typed root -/

/-- A typed root: an address whose resident is claimed at kind `tag`,
with the decoded type carried as a phantom index. The runtime mirror is
`Root<A>` — a branded content id. -/
structure Root (α : Type u) where
  tag : UInt8
  addr : Addr32

/-- A typed root's edge form: the ordinary reference the node carries,
which is what the admission law checks. -/
def Root.ref (r : Root α) : Ref := ⟨r.tag, r.addr⟩

/-- A root dereferences in a store when a node resides at its address
at the declared kind. -/
def Root.resolvesIn (r : Root α) (σ : Store) : Prop :=
  ∃ n, σ r.addr = some n ∧ n.tag = r.tag

/-- In a closed store, every resident typed edge dereferences at its
declared kind: the projection layer's "follow a `Root`" is total over
admitted graphs. -/
theorem Root.closed_deref {σ : Store} (hσ : Store.Closed σ)
    {a : Addr32} {n : Node} (ha : σ a = some n)
    {α : Type u} (r : Root α) (hr : r.ref ∈ n.refs) :
    r.resolvesIn σ := by
  obtain ⟨m, hm, htag⟩ := hσ a n ha r.ref hr
  exact ⟨m, hm, htag⟩

end Cas
