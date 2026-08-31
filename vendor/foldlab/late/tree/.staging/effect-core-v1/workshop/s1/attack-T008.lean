import Cas.Lift.Taxonomy

/-!
# BREAKER attack on `EC1-T008` (`workshop/s1/T008.lean`), slice `EC1-S1`

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review` — the target
claims `PROVED-STRONGER`, so this is an assurance review run adversarially.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T008.lean
```

§0 is a VERBATIM re-declaration of `T008.lean`'s carrier. Nothing is imported
from `T008.lean` — it is not a Lake module — so every result below is
RE-DERIVED from the definitions rather than assumed. Re-derivation is itself a
check: an unsound landed proof would leave these attacks open.

`Cas.Lift.Taxonomy` is imported read-only, as the target does.
-/

namespace EffectCoreV1.AttackT008

/-! ## §0 — the target's carrier, re-declared verbatim -/

inductive SurfaceDisposition where
  | reifiedPrimitive
  | derivedExpansion
  | separateSubcalculus
  | pureOrHostOnlyClosedOutsideProg
  | projectOwnedReplacementOrForeignOp
  | targetOnly
  | excludedInternal
  deriving DecidableEq, Repr

structure SurfaceRow (κ : Type) where
  rowKey : κ
  surfaceDisposition : SurfaceDisposition
  deriving DecidableEq, Repr

structure PublicSurface (κ : Type) where
  keys : List κ
  rows : List (SurfaceRow κ)
  deriving DecidableEq, Repr

def PublicSurface.dispositionOf {κ : Type} [DecidableEq κ]
    (s : PublicSurface κ) (k : κ) : Option SurfaceDisposition :=
  (s.rows.find? (fun r => decide (r.rowKey = k))).map (·.surfaceDisposition)

inductive RowKey where
  | succeed
  | failCause
  | multipartHeaders
  deriving DecidableEq, Repr

structure PublicSurfaceWF {κ : Type} [DecidableEq κ] (s : PublicSurface κ) :
    Prop where
  covers : ∀ k ∈ s.keys, ∃ r ∈ s.rows, r.rowKey = k
  keysNodup : (s.rows.map (·.rowKey)).Nodup
  publicNotExcluded :
    ∀ r ∈ s.rows, r.rowKey ∈ s.keys → r.surfaceDisposition ≠ .excludedInternal

instance {κ : Type} [DecidableEq κ] (s : PublicSurface κ) :
    Decidable (PublicSurfaceWF s) :=
  decidable_of_iff
    ((∀ k ∈ s.keys, ∃ r ∈ s.rows, r.rowKey = k)
      ∧ (s.rows.map (·.rowKey)).Nodup
      ∧ (∀ r ∈ s.rows, r.rowKey ∈ s.keys →
          r.surfaceDisposition ≠ .excludedInternal))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
     fun h => ⟨h.covers, h.keysNodup, h.publicNotExcluded⟩⟩

inductive SurfaceDefect (κ : Type) where
  | unclassified (k : κ)
  | multiplyClassified (k : κ)
  | publicExcludedInternal (k : κ)
  deriving DecidableEq, Repr

def firstDupKey {κ : Type} [DecidableEq κ] : List κ → Option κ
  | [] => none
  | k :: t =>
    match t.any (fun x => decide (x = k)) with
    | true => some k
    | false => firstDupKey t

def checkSurface {κ : Type} [DecidableEq κ] (s : PublicSurface κ) :
    Except (SurfaceDefect κ) Unit :=
  match s.keys.find?
      (fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) with
  | some k => .error (.unclassified k)
  | none =>
    match firstDupKey (s.rows.map (·.rowKey)) with
    | some k => .error (.multiplyClassified k)
    | none =>
      match s.rows.find?
          (fun r => decide (r.rowKey ∈ s.keys)
            && decide (r.surfaceDisposition = .excludedInternal)) with
      | some r => .error (.publicExcludedInternal r.rowKey)
      | none => .ok ()

def SurfaceDisposition.publicAll : List SurfaceDisposition :=
  [.reifiedPrimitive, .derivedExpansion, .separateSubcalculus,
   .pureOrHostOnlyClosedOutsideProg, .projectOwnedReplacementOrForeignOp,
   .targetOnly]

def CheckedSurface (κ : Type) [DecidableEq κ] : Type :=
  { s : PublicSurface κ // PublicSurfaceWF s }

/-- `Except` carries no derived `DecidableEq` in core. Rather than mint one,
the verdict is PROJECTED and the projection proved faithful in both directions,
so every rejection theorem below is still stated at full fidelity —
`checkSurface s = .error e`, never a projection standing in for it. -/
def defectOf {κ : Type} (e : Except (SurfaceDefect κ) Unit) :
    Option (SurfaceDefect κ) :=
  match e with
  | .ok _ => none
  | .error d => some d

theorem eq_error_iff {κ : Type} (e : Except (SurfaceDefect κ) Unit)
    (d : SurfaceDefect κ) : e = .error d ↔ defectOf e = some d := by
  cases e with
  | ok u => cases u; simp [defectOf]
  | error x => simp [defectOf]

theorem eq_ok_iff {κ : Type} (e : Except (SurfaceDefect κ) Unit) :
    e = .ok () ↔ defectOf e = none := by
  cases e with
  | ok u => cases u; simp [defectOf]
  | error x => simp [defectOf]

/-- Distinct entries cannot share a key when the row keys are duplicate-free. -/
theorem nodup_key_unique {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α},
      x ∈ l → y ∈ l → f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x y hx _ _; simp at hx
  | cons a t ih =>
    intro hnd x y hx hy h
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨y, hy', h.symm⟩) hnot
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (List.mem_map.mpr ⟨x, hx', h⟩) hnot
      · exact ih hnd' hx' hy' h

/-- The ledger search agrees with any row carrying the key. Stated on
`keysNodup` ALONE — the target's `dispositionOf_agrees` demands the whole of
`PublicSurfaceWF`, and §6 needs the weaker form. -/
theorem dispositionOf_agrees_of_nodup {κ : Type} [DecidableEq κ]
    (s : PublicSurface κ) (hnd : (s.rows.map (·.rowKey)).Nodup)
    {k : κ} {r : SurfaceRow κ} (hr : r ∈ s.rows) (hrk : r.rowKey = k) :
    s.dispositionOf k = some r.surfaceDisposition := by
  show (s.rows.find? (fun x => decide (x.rowKey = k))).map
    (·.surfaceDisposition) = some r.surfaceDisposition
  rcases hl : s.rows.find? (fun x : SurfaceRow κ => decide (x.rowKey = k)) with
    _ | e
  · exact absurd (decide_eq_true hrk) (List.find?_eq_none.mp hl r hr)
  · have hmem : e ∈ s.rows := List.mem_of_find?_eq_some hl
    have hkey : e.rowKey = k :=
      of_decide_eq_true
        (List.find?_some
          (p := fun x : SurfaceRow κ => decide (x.rowKey = k)) hl)
    show some e.surfaceDisposition = some r.surfaceDisposition
    rw [nodup_key_unique (·.rowKey) hnd hmem hr (hkey.trans hrk.symm)]

/-! ## §1 — independent kernel cross-check of `checkSurface_ok_iff`

The target proves `checkSurface s = .ok () ↔ PublicSurfaceWF s` by per-clause
reflection, which is `PROOF-DAG.md:16`'s prescribed Checker route. Here the
same equivalence is confirmed by the KERNEL on a ten-ledger battery, evaluating
both sides independently. This does not reprove the universal — that is the
point of `PROOF-DAG.md:16`'s prohibited shortcut, "using successful examples as
completeness" — it is a cross-check that the two sides do not disagree on any
ledger this review could build. -/

def isOk {κ : Type} (e : Except (SurfaceDefect κ) Unit) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

/-- The battery cross-check below is therefore about the verdict itself. -/
theorem isOk_eq_true_iff {κ : Type} (e : Except (SurfaceDefect κ) Unit) :
    isOk e = true ↔ e = .ok () := by
  cases e with
  | ok u => cases u; simp [isOk]
  | error x => simp [isOk]

def goodSurface : PublicSurface RowKey where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows :=
    [⟨.succeed, .reifiedPrimitive⟩,
     ⟨.failCause, .derivedExpansion⟩,
     ⟨.multipartHeaders, .separateSubcalculus⟩]

def droppedSurface : PublicSurface RowKey where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.failCause, .reifiedPrimitive⟩]

def dupSurface : PublicSurface RowKey where
  keys := [.succeed]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.succeed, .targetOnly⟩]

/-- `EC1-F82` at this carrier: the SAME two rows, permuted. -/
def dupSurfacePerm : PublicSurface RowKey where
  keys := [.succeed]
  rows := [⟨.succeed, .targetOnly⟩, ⟨.succeed, .reifiedPrimitive⟩]

def excludedSurface : PublicSurface RowKey where
  keys := [.succeed]
  rows := [⟨.succeed, .excludedInternal⟩]

def doubleDefect : PublicSurface RowKey where
  keys := [.succeed, .failCause, .multipartHeaders]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.succeed, .targetOnly⟩]

def censusGap : PublicSurface RowKey where
  keys := [.succeed, .failCause]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.failCause, .derivedExpansion⟩]

/-- The empty ledger. A degenerate positive: `PublicSurfaceWF` holds of it and
the checker accepts, so `PublicSurfaceWF` alone constrains nothing about
whether a ledger says anything at all. -/
def emptySurface : PublicSurface RowKey where
  keys := []
  rows := []

/-- **The gap this review is reporting.** A public key universe with a
DUPLICATED key. Every clause of `PublicSurfaceWF` holds. -/
def dupKeysSurface : PublicSurface RowKey where
  keys := [.succeed, .succeed]
  rows := [⟨.succeed, .reifiedPrimitive⟩]

/-- An internal row (key outside `keys`) classified `excludedInternal`, which
`EC1-K07` positively REQUIRES to be admissible. Guards against a checker that
over-rejects. -/
def internalExcluded : PublicSurface RowKey where
  keys := [.succeed]
  rows := [⟨.succeed, .reifiedPrimitive⟩, ⟨.failCause, .excludedInternal⟩]

def battery : List (PublicSurface RowKey) :=
  [goodSurface, droppedSurface, dupSurface, dupSurfacePerm, excludedSurface,
   doubleDefect, censusGap, emptySurface, dupKeysSurface, internalExcluded]

/-- **Cross-check.** On every ledger in the battery the decider and the
well-formedness predicate agree, each computed independently by the kernel. -/
theorem battery_decider_agrees_with_wf :
    ∀ s ∈ battery, isOk (checkSurface s) = decide (PublicSurfaceWF s) := by
  decide

/-- The battery is not all-accept or all-reject, so the agreement above is not
trivially satisfied. -/
theorem battery_is_mixed :
    (battery.filter (fun s => isOk (checkSurface s))).length = 5
      ∧ (battery.filter (fun s => !(isOk (checkSurface s)))).length = 5 := by
  decide

/-! ## §2 — vacuity probe, and the genericity claim tested off the scratch enum

The target's headline is stated under `PublicSurfaceWF s` and `k ∈ s.keys`.
Both must be simultaneously inhabitable or the theorem quantifies over nothing.
The target's own positive control is at its three-value scratch `RowKey`. Here
the premises are inhabited at a DIFFERENT key type, so the non-vacuity is not
an artifact of the scratch model, and the generic statement is exercised at a
carrier the scratch enum cannot reach. -/

/-- Effect module paths as the real ledger would key them, including the deep
`MultipartParser` module `EC1-CE020` proved absent from the old bank. -/
def strSurface : PublicSurface String where
  keys :=
    ["effect/Effect",
     "effect/unstable/http/MultipartParser/HeadersParser",
     "effect/unstable/http/MultipartParser/Search"]
  rows :=
    [⟨"effect/Effect", .reifiedPrimitive⟩,
     ⟨"effect/unstable/http/MultipartParser/HeadersParser",
       .separateSubcalculus⟩,
     ⟨"effect/unstable/http/MultipartParser/Search", .separateSubcalculus⟩,
     ⟨"effect/internal/Scheduler", .excludedInternal⟩]

/-- **The premises are inhabited at a non-scratch key type.** `decide` is the
kernel evaluating `String` equality, not the three-value enum. -/
theorem strSurface_is_wf : PublicSurfaceWF strSurface := by decide

theorem strSurface_is_accepted : checkSurface strSurface = .ok () :=
  (eq_ok_iff _).mpr (by decide)

/-- **The conclusion has content here, not just a shape.** The deep module
`EC1-F59` names is classified, and the classification is a real value. -/
theorem strSurface_classifies_the_deep_module :
    strSurface.dispositionOf
        "effect/unstable/http/MultipartParser/HeadersParser"
      = some .separateSubcalculus := by
  decide

/-- The internal row is present and excluded, and the public rows are not: the
`EC1-K07` split is exercised in both directions at this carrier. -/
theorem strSurface_keeps_the_internal_row :
    strSurface.dispositionOf "effect/internal/Scheduler"
        = some .excludedInternal
      ∧ "effect/internal/Scheduler" ∉ strSurface.keys := by
  decide

/-! ## §3 — `EC1-F60` replayed off the scratch enum

The target's three mutant-rejection theorems are `rfl` at `RowKey`. Confirmed
here at `String`, so the rejection is not an artifact of a three-value key
type. -/

def strDropped : PublicSurface String where
  keys :=
    ["effect/Effect", "effect/unstable/http/MultipartParser/HeadersParser"]
  rows := [⟨"effect/Effect", .reifiedPrimitive⟩]

def strDuplicated : PublicSurface String where
  keys := ["effect/Effect"]
  rows :=
    [⟨"effect/Effect", .reifiedPrimitive⟩, ⟨"effect/Effect", .targetOnly⟩]

def strExcluded : PublicSurface String where
  keys := ["effect/Effect"]
  rows := [⟨"effect/Effect", .excludedInternal⟩]

theorem strDropped_is_rejected :
    checkSurface strDropped
      = .error (.unclassified
          "effect/unstable/http/MultipartParser/HeadersParser") :=
  (eq_error_iff _ _).mpr (by decide)

theorem strDuplicated_is_rejected :
    checkSurface strDuplicated
      = .error (.multiplyClassified "effect/Effect") :=
  (eq_error_iff _ _).mpr (by decide)

theorem strExcluded_is_rejected :
    checkSurface strExcluded
      = .error (.publicExcludedInternal "effect/Effect") :=
  (eq_error_iff _ _).mpr (by decide)

/-! ## §4 — FINDING: the checker admits a duplicated PUBLIC KEY

`PublicSurfaceWF.keysNodup` constrains `s.rows`, never `s.keys`. Nothing in
`PublicSurfaceWF` and nothing in `checkSurface` decides `s.keys.Nodup`, so a
generated ledger whose recursively resolved public universe lists one module
twice is accepted as well-formed.

`CONTRACT-PACKET.md:213` is the clause this crosses: "Alias exposures collapse
to one canonical declaration WITHOUT DISAPPEARING." An alias that fails to
collapse appears in `U_row` twice, which is exactly `dupKeysSurface`, and
`EC1-F03` (duplicate an ID) is the falsifier shape. The target's disclosed
omissions list the ledger fields it did not model — `admissionProfiles`,
`familyRoles`, `effectReachability`, `A/E/R`, `primaryCarrierId` — but not this
one, which is a property of the two fields it DID model.

This is not a refutation of `surface_disposition_exact`: §4c proves the
headline survives. It is a hole in the DECIDER, which is the instrument the
target argues is what makes `EC1-F60` able to fire. -/

/-- **The witness.** A duplicated public key is well-formed and accepted. -/
theorem dupKeys_passes_wf_and_the_checker :
    PublicSurfaceWF dupKeysSurface
      ∧ checkSurface dupKeysSurface = .ok ()
      ∧ ¬ dupKeysSurface.keys.Nodup :=
  ⟨by decide, (eq_ok_iff _).mpr (by decide), by decide⟩

/-- The consequence: any count over the accepted key universe is wrong. The
ledger classifies ONE module and reports a two-element public universe. -/
theorem accepted_key_count_overstates :
    dupKeysSurface.keys.length = 2
      ∧ dupKeysSurface.keys.eraseDups.length = 1
      ∧ dupKeysSurface.rows.length = 1 := by
  decide

/-- The census clause does not repair it either: `CensusComplete` is a
one-directional membership obligation, so it is satisfied by the duplicated
universe exactly as it is by the clean one. -/
def CensusComplete {κ : Type} (U : List κ) (s : PublicSurface κ) : Prop :=
  ∀ k ∈ U, k ∈ s.keys

theorem census_does_not_repair_duplicate_keys :
    CensusComplete [RowKey.succeed] dupKeysSurface
      ∧ ¬ dupKeysSurface.keys.Nodup := by
  constructor
  · unfold CensusComplete
    decide
  · decide

/-- **§4c — the headline survives.** `dupKeysSurface` is well-formed, so the
target's `surface_disposition_exact` applies to it and still returns exactly one
non-excluded disposition. The gap is representational, not a soundness break:
the duplicated key is harmless to the disposition map and harmful to anything
that counts or enumerates `keys`. -/
theorem headline_survives_the_duplicate_key :
    dupKeysSurface.dispositionOf .succeed = some .reifiedPrimitive
      ∧ SurfaceDisposition.reifiedPrimitive ≠ .excludedInternal := by
  decide

/-- The repair is one decidable clause, and it separates the two ledgers the
current checker cannot tell apart. -/
abbrev keysNodupClause {κ : Type} [DecidableEq κ] (s : PublicSurface κ) :
    Prop := s.keys.Nodup

theorem the_repair_separates_them :
    keysNodupClause goodSurface ∧ ¬ keysNodupClause dupKeysSurface := by
  decide

/-! ## §5 — FINDING: two of the three diagnostics are not validated

The target proves `unclassified_diagnostic_is_accurate` FROM the checker's
output, via `checkSurface_unclassified_source`. Its sibling
`multiplyClassified_diagnostic_is_accurate` is stated from
`firstDupKey (s.rows.map (·.rowKey)) = some k` INSTEAD — an internal search
result, not the checker's verdict — and no theorem connects the two. The third
constructor, `publicExcludedInternal`, has no accuracy theorem at all.

Both bridges are provable, so this is proof debt rather than a break, and both
are discharged here. The second one is worth having for a further reason: its
proof CONSUMES the clause order, and the target lists clause order as "a choice
made here, not a packet ruling". -/

section Diagnostics

variable {κ : Type} [DecidableEq κ]

theorem firstDupKey_cons_true {k : κ} {t : List κ}
    (h : t.any (fun x => decide (x = k)) = true) :
    firstDupKey (k :: t) = some k := by
  show (match t.any (fun x => decide (x = k)) with
        | true => some k | false => firstDupKey t) = some k
  rw [h]

theorem firstDupKey_cons_false {k : κ} {t : List κ}
    (h : t.any (fun x => decide (x = k)) = false) :
    firstDupKey (k :: t) = firstDupKey t := by
  show (match t.any (fun x => decide (x = k)) with
        | true => some k | false => firstDupKey t) = firstDupKey t
  rw [h]

theorem firstDupKey_eq_none_iff (l : List κ) :
    firstDupKey l = none ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons a t ih =>
    cases hb : t.any (fun x => decide (x = a)) with
    | true =>
      have hmem : a ∈ t := by
        obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp hb
        exact (of_decide_eq_true hxa) ▸ hx
      constructor
      · intro h
        rw [firstDupKey_cons_true hb] at h
        simp at h
      · intro h
        exact absurd hmem (List.nodup_cons.mp h).1
    | false =>
      have hnot : a ∉ t := fun hc => by
        have hx : t.any (fun x => decide (x = a)) = true :=
          List.any_eq_true.mpr ⟨a, hc, decide_eq_true rfl⟩
        rw [hb] at hx
        exact Bool.noConfusion hx
      rw [firstDupKey_cons_false hb]
      exact ⟨fun h => List.nodup_cons.mpr ⟨hnot, ih.mp h⟩,
             fun h => ih.mpr (List.nodup_cons.mp h).2⟩

/-- **The missing bridge, part one.** The `multiplyClassified` diagnostic really
does come from the checker, so the target's accuracy theorem attaches to a
verdict rather than to an internal search. -/
theorem checkSurface_multiplyClassified_source (s : PublicSurface κ) {k : κ}
    (h : checkSurface s = .error (.multiplyClassified k)) :
    firstDupKey (s.rows.map (·.rowKey)) = some k := by
  rw [checkSurface] at h
  cases hcov : s.keys.find?
      (fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) with
  | some k' => rw [hcov] at h; simp at h
  | none =>
    rw [hcov] at h
    cases hdup : firstDupKey (s.rows.map (·.rowKey)) with
    | some k'' =>
      rw [hdup] at h
      simp at h
      rw [h]
    | none =>
      exfalso
      rw [hdup] at h
      cases hexc : s.rows.find?
          (fun r => decide (r.rowKey ∈ s.keys)
            && decide (r.surfaceDisposition = .excludedInternal)) with
      | some r => rw [hexc] at h; simp at h
      | none => rw [hexc] at h; simp at h

/-- **The missing bridge, part two.** The `publicExcludedInternal` diagnostic —
the one the target validates nowhere — is accurate, and in the sharp form: the
key it names is public and the LEDGER SEARCH returns `excludedInternal` for it.
The proof needs `firstDupKey ... = none`, which only the clause ORDER supplies;
under a checker that ran the exclusion clause first this statement would be
false in its sharp form. -/
theorem publicExcluded_diagnostic_is_accurate (s : PublicSurface κ) {k : κ}
    (h : checkSurface s = .error (.publicExcludedInternal k)) :
    k ∈ s.keys ∧ s.dispositionOf k = some .excludedInternal := by
  rw [checkSurface] at h
  cases hcov : s.keys.find?
      (fun k => !(s.rows.any (fun r => decide (r.rowKey = k)))) with
  | some k' => rw [hcov] at h; simp at h
  | none =>
    rw [hcov] at h
    cases hdup : firstDupKey (s.rows.map (·.rowKey)) with
    | some k'' => rw [hdup] at h; simp at h
    | none =>
      rw [hdup] at h
      cases hexc : s.rows.find?
          (fun r => decide (r.rowKey ∈ s.keys)
            && decide (r.surfaceDisposition = .excludedInternal)) with
      | none => rw [hexc] at h; simp at h
      | some r =>
        rw [hexc] at h
        simp at h
        subst h
        have hmem : r ∈ s.rows := List.mem_of_find?_eq_some hexc
        have hp := List.find?_some
          (p := fun r : SurfaceRow κ => decide (r.rowKey ∈ s.keys)
            && decide (r.surfaceDisposition = .excludedInternal)) hexc
        have hand := (Bool.and_eq_true ..).mp hp
        have hk : r.rowKey ∈ s.keys := of_decide_eq_true hand.1
        have hd : r.surfaceDisposition = SurfaceDisposition.excludedInternal :=
          of_decide_eq_true hand.2
        refine ⟨hk, ?_⟩
        have hnd : (s.rows.map (·.rowKey)).Nodup :=
          (firstDupKey_eq_none_iff _).mp hdup
        exact hd ▸ dispositionOf_agrees_of_nodup s hnd hmem rfl

end Diagnostics

/-! ## §6 — `EC1-F82`: permute a duplicate-key raw row

`EC1-F82` is "permute a duplicate-key raw row and assert equal normalization".
At this carrier `dispositionOf` is a `find?`, so it is ORDER SENSITIVE on a
duplicated key, and the target proves only the one-sided
`dupSurface_lookup_picks_the_first`. The permutation is built here and the
divergence exhibited.

The falsifier is nonetheless DEFENDED, in the strong direction: `keysNodup`
alone makes `dispositionOf` a MEMBERSHIP characterisation, which is manifestly
permutation-invariant. That equivalence is the general result the target's
one-directional `dispositionOf_agrees` leaves on the table. -/

/-- The permutation really is one: same rows, opposite order. -/
theorem dupSurfacePerm_is_a_permutation :
    dupSurfacePerm.rows = dupSurface.rows.reverse
      ∧ dupSurfacePerm.keys = dupSurface.keys := by
  decide

/-- **`EC1-F82` fires on the raw carrier.** Permuting the duplicate-key ledger
changes the answer. -/
theorem permutation_changes_the_disposition :
    dupSurface.dispositionOf .succeed = some .reifiedPrimitive
      ∧ dupSurfacePerm.dispositionOf .succeed = some .targetOnly
      ∧ dupSurface.dispositionOf .succeed
          ≠ dupSurfacePerm.dispositionOf .succeed := by
  decide

/-- **`EC1-F82` is defended.** Both permutations are rejected by the decider
with the same diagnostic, so no accepted ledger exhibits the divergence. -/
theorem both_permutations_are_rejected :
    checkSurface dupSurface = .error (.multiplyClassified .succeed)
      ∧ checkSurface dupSurfacePerm
          = .error (.multiplyClassified .succeed) :=
  ⟨(eq_error_iff _ _).mpr (by decide), (eq_error_iff _ _).mpr (by decide)⟩

/-- **The positive law, proved from `keysNodup` alone.** Under duplicate-free
row keys the search is exactly ledger membership — an order-free description, so
`EC1-F82` cannot reach an accepted ledger. Stronger than the target's
`dispositionOf_agrees`, which gives only the right-to-left direction. -/
theorem dispositionOf_iff_mem {κ : Type} [DecidableEq κ]
    (s : PublicSurface κ) (hnd : (s.rows.map (·.rowKey)).Nodup)
    (k : κ) (d : SurfaceDisposition) :
    s.dispositionOf k = some d
      ↔ ∃ r ∈ s.rows, r.rowKey = k ∧ r.surfaceDisposition = d := by
  constructor
  · intro h
    have h' : (s.rows.find? (fun x : SurfaceRow κ => decide (x.rowKey = k))).map
        (·.surfaceDisposition) = some d := h
    rcases hl : s.rows.find? (fun x : SurfaceRow κ => decide (x.rowKey = k)) with
      _ | e
    · rw [hl] at h'; simp at h'
    · rw [hl] at h'
      have hd : e.surfaceDisposition = d := Option.some.inj h'
      refine ⟨e, List.mem_of_find?_eq_some hl, ?_, hd⟩
      exact of_decide_eq_true
        (List.find?_some
          (p := fun x : SurfaceRow κ => decide (x.rowKey = k)) hl)
  · rintro ⟨r, hr, hrk, hrd⟩
    exact hrd ▸ dispositionOf_agrees_of_nodup s hnd hr hrk

/-! ## §7 — falsifiers with no carrier in this row, stated rather than skipped

* `EC1-F01` (delete a target block), `EC1-F02` (swap an answer type in
  `Resume`), `EC1-F08` (unregistered host callback), `EC1-F20` (pure atom reads
  a mutable counter), `EC1-F87` (touch `Sig`): the target mints no `Prog`, no
  `Sig`, no `Handler` and no answer type. `EFFECTS-BACKEND` R14a is satisfied by
  construction — every carrier here is effect-free first-order data outside
  `Prog` — so these falsifiers have no target rather than being survived.
* `EC1-F86` (a second meaning for an inhabited `Cas.Schema.El` code): no schema
  universe is minted; `SurfaceDisposition` is a scratch seven-value enum in a
  scratch namespace, proposed for nothing.
* `EC1-F80` (cutover with an open edge): the target asserts no cutover.

`EC1-F59` and `EC1-F60` are the two that do bear, and are exercised in §3, §4
and §6. `EC1-F03` is exercised in §4.

§7a records the one falsifier the target's own omissions name but no theorem
reaches, so the ceiling below is not softer than the evidence. -/

/-- **§7a.** The estate's own HAND MIRROR caveat, cited read-only, is the
untouched half. `Cas/Lang/RefusalMap.lean:172-176` says a Lean enum and its
TypeScript twin are kept in step only by being written beside each other. The
`RefusalCode` gate below is real and re-derived, and it still says nothing about
any TypeScript file: `all_complete` closes the LEAN side only. -/
theorem estate_gate_is_lean_side_only (c : Cas.Lift.RefusalCode) :
    c ∈ Cas.Lift.RefusalCode.all
      ∧ Cas.Lift.RefusalCode.all.length = 20 :=
  ⟨Cas.Lift.RefusalCode.all_complete c, by decide⟩

/-! ## §8 — the target's own vacuity findings, re-derived

If the target's diagnosis of the DAG row were wrong, these would not close. -/

def UniqueEq {δ : Type} (v : δ) : Prop :=
  ∃ d, v = d ∧ ∀ e, v = e → e = d

theorem bang_is_free {α δ : Type} (f : α → δ) (x : α) : UniqueEq (f x) :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- The DAG row `PROOF-DAG.md:200` holds of every ledger, including all three
mutants, with both premises discarded. Re-derived independently. -/
theorem the_dag_row_is_vacuous {κ : Type} (s : PublicSurface κ) :
    ∀ r ∈ s.rows, UniqueEq r.surfaceDisposition :=
  fun r _ => bang_is_free SurfaceRow.surfaceDisposition r

/-- **The one place this review sharpens the target's §12.** The target's
`restatement_implies_the_schematic_row` states the schematic row with NO
hypothesis — it is `the_dag_row_is_vacuous` under a different name, and the
implication it is named for follows only because the consequent is a theorem.
The honest form of "nothing is lost" is that the row carries no information at
all, which is this: the schematic row is EQUIVALENT to `True`, uniformly. -/
theorem the_dag_row_is_equivalent_to_True {κ : Type} (s : PublicSurface κ) :
    (∀ r ∈ s.rows, UniqueEq r.surfaceDisposition) ↔ True :=
  ⟨fun _ => trivial, fun _ => the_dag_row_is_vacuous s⟩

/-- And the restated theorem is NOT equivalent to `True`: it fails on a
representable ledger. So the replacement is strict in the direction that
matters, re-derived without appeal to the target. -/
theorem droppedSurface_really_drops :
    RowKey.multipartHeaders ∈ droppedSurface.keys
      ∧ droppedSurface.dispositionOf .multipartHeaders = none := by decide

theorem the_restatement_is_not_equivalent_to_True :
    ¬ ∀ (s : PublicSurface RowKey) (k : RowKey), k ∈ s.keys →
        ∃ d : SurfaceDisposition,
          s.dispositionOf k = some d ∧ d ≠ .excludedInternal := by
  intro h
  obtain ⟨d, hd, _⟩ :=
    h droppedSurface .multipartHeaders droppedSurface_really_drops.1
  rw [droppedSurface_really_drops.2] at hd
  simp at hd

/-! ### §8a — two precision gaps in the target's prose

Both are gaps between a theorem and the words used for it. Neither is a Lean
defect; both would be inherited by the packet if the words were copied. -/

/-- The sharpest form of the target's §11. The checker green-lights a ledger
that classifies NOTHING. `PublicSurfaceWF` is a consistency property and never a
completeness one, so §11's separate census clause is mandatory rather than
decoration. -/
theorem the_empty_ledger_is_accepted :
    PublicSurfaceWF emptySurface
      ∧ checkSurface emptySurface = .ok ()
      ∧ emptySurface.rows = [] :=
  ⟨by decide, (eq_ok_iff _).mpr (by decide), rfl⟩

def ext1 : RowKey → SurfaceDisposition
  | .succeed => .reifiedPrimitive
  | .failCause => .reifiedPrimitive
  | .multipartHeaders => .targetOnly

def ext2 : RowKey → SurfaceDisposition
  | .succeed => .reifiedPrimitive
  | .failCause => .reifiedPrimitive
  | .multipartHeaders => .derivedExpansion

/-- `raw_disposition_is_genuinely_partial` states that the ledger's own lookup
is `none` at a public key. That is a PARTIALITY statement, not the
non-existence statement the target's prose reaches for ("no
`κ → SurfaceDisposition` reading of the ledger is available"). Total readings
agreeing with the drop mutant everywhere it speaks do exist — here are two,
disagreeing exactly at the dropped key. What actually fails is DETERMINATION:
the ledger does not pin the value, which is the real content and the real
argument for §7's checked carrier. -/
theorem the_drop_mutant_has_two_total_readings :
    droppedSurface.dispositionOf .succeed = some (ext1 .succeed)
      ∧ droppedSurface.dispositionOf .failCause = some (ext1 .failCause)
      ∧ droppedSurface.dispositionOf .succeed = some (ext2 .succeed)
      ∧ droppedSurface.dispositionOf .failCause = some (ext2 .failCause)
      ∧ ext1 .multipartHeaders ≠ ext2 .multipartHeaders := by
  decide

/-! ## §9 — the ceiling

Everything above is a statement about scratch carriers. Confirmed by inspection
outside Lean this pass, and recorded here because no theorem can say it:

* `formal/effect-core-v1/EffectCore/Generated/` does not exist; `EC1-H11` is
  `PENDING HARNESS` (`PROOF-DAG.md:492`). No generated `rc.112` ledger is in the
  tree in Lean-consumable form, so `covers` and `keysNodup` are discharged of
  NOTHING real.
* `library/cas/lake-manifest.json` reads `"packages": []` and
  `lean-toolchain` reads `leanprover/lean4:v4.33.1`: the target's `∃!`
  unavailability claim is confirmed.
* `Cas/Lift/Taxonomy.lean:208-220` really is a twenty-row `all` with
  `all_complete` at `:215` and the wire `#guard` at `:220`;
  `Cas/Core/Admission.lean:60` really is `checkRefs_ok_iff`;
  `Cas/Lang/RefusalMap.lean:172-176` really carries the HAND MIRROR caveat and
  `:181` really is `| danglingReference`. The target's correction of
  `.staging/agent-reports/2026-08-31-effect-core-local-anchors.md` is accurate.
-/

end EffectCoreV1.AttackT008

/-! ## Kernel receipts -/

#print axioms EffectCoreV1.AttackT008.eq_error_iff
#print axioms EffectCoreV1.AttackT008.eq_ok_iff
#print axioms EffectCoreV1.AttackT008.isOk_eq_true_iff
#print axioms EffectCoreV1.AttackT008.battery_decider_agrees_with_wf
#print axioms EffectCoreV1.AttackT008.battery_is_mixed
#print axioms EffectCoreV1.AttackT008.strSurface_is_wf
#print axioms EffectCoreV1.AttackT008.strSurface_is_accepted
#print axioms EffectCoreV1.AttackT008.strSurface_classifies_the_deep_module
#print axioms EffectCoreV1.AttackT008.strSurface_keeps_the_internal_row
#print axioms EffectCoreV1.AttackT008.strDropped_is_rejected
#print axioms EffectCoreV1.AttackT008.strDuplicated_is_rejected
#print axioms EffectCoreV1.AttackT008.strExcluded_is_rejected
#print axioms EffectCoreV1.AttackT008.dupKeys_passes_wf_and_the_checker
#print axioms EffectCoreV1.AttackT008.accepted_key_count_overstates
#print axioms EffectCoreV1.AttackT008.census_does_not_repair_duplicate_keys
#print axioms EffectCoreV1.AttackT008.headline_survives_the_duplicate_key
#print axioms EffectCoreV1.AttackT008.the_repair_separates_them
#print axioms EffectCoreV1.AttackT008.firstDupKey_cons_true
#print axioms EffectCoreV1.AttackT008.firstDupKey_cons_false
#print axioms EffectCoreV1.AttackT008.firstDupKey_eq_none_iff
#print axioms EffectCoreV1.AttackT008.checkSurface_multiplyClassified_source
#print axioms EffectCoreV1.AttackT008.publicExcluded_diagnostic_is_accurate
#print axioms EffectCoreV1.AttackT008.dupSurfacePerm_is_a_permutation
#print axioms EffectCoreV1.AttackT008.permutation_changes_the_disposition
#print axioms EffectCoreV1.AttackT008.both_permutations_are_rejected
#print axioms EffectCoreV1.AttackT008.dispositionOf_iff_mem
#print axioms EffectCoreV1.AttackT008.estate_gate_is_lean_side_only
#print axioms EffectCoreV1.AttackT008.nodup_key_unique
#print axioms EffectCoreV1.AttackT008.dispositionOf_agrees_of_nodup
#print axioms EffectCoreV1.AttackT008.droppedSurface_really_drops
#print axioms EffectCoreV1.AttackT008.bang_is_free
#print axioms EffectCoreV1.AttackT008.the_dag_row_is_vacuous
#print axioms EffectCoreV1.AttackT008.the_dag_row_is_equivalent_to_True
#print axioms EffectCoreV1.AttackT008.the_restatement_is_not_equivalent_to_True
#print axioms EffectCoreV1.AttackT008.the_empty_ledger_is_accepted
#print axioms EffectCoreV1.AttackT008.the_drop_mutant_has_two_total_readings
