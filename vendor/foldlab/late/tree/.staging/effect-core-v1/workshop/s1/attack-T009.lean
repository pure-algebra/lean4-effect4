import Cas.Lang.RefusalMap
import Cas.Schema.Guarded

/-!
# ATTACK on `EC1-T009` (`workshop/s1/T009.lean`) — breaker witnesses

Slice `EC1-S1`. Skill stage: `lean-assurance-review`.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T009.lean
```

`T009.lean` is not a module of any lake target, so it cannot be imported.
Section §0 below is its lines 111-1032 COPIED VERBATIM — carriers, `Grounded`,
`ExpandsTo`, `SurfaceMappingWF`, `find?`, `out`, `settles`, `checkB`, the
soundness chain and `checkB_iff`. Every witness after §0 therefore attacks the
DELIVERED door, not a paraphrase of it. Nothing under `library/` or `formal/`
is touched and no packet `.md` is edited.

The attack sections are §A1-§A9 at the end of the file, after `end
EffectCoreT009`.
-/

namespace EffectCoreT009

/-! ## §1 — the carriers

Transcribed from `REIFICATION-CHECKLIST.md:525-618` (`SurfaceRow`,
`admissionProfiles`, and the mapping tagged union at `:581-597`) and `:494-502`
(the seven dispositions and their required mappings). Deliberately minimal in
every dimension no theorem below touches: `A/E/R` transforms, family roles,
class-product transfers, observations and obligation sets are all omitted. The
one place the model is faithful in full is the mapping union, which is where the
row lives. -/

/-- Invariant 15: "Every subcalculus has a typed handler or total lowering." -/
inductive SubcalcInterp (H : Type) where
  | lowering
  | handler (h : H)
  deriving DecidableEq

/-- Why a profile is refused. The third arm is the estate's OWN clause carrier
(`Cas/Lang/RefusalMap.lean:106`), reused rather than re-spelled: invariant 24 and
§17 ruling R11 forbid a second CAS refusal family. -/
inductive RefusalReason where
  | typeDiagnostic
  | admissionDiagnostic
  | casClause (c : Cas.Lang.Refusal.Clause)
  deriving DecidableEq

/-- The profile mapping, arm for arm from `REIFICATION-CHECKLIST.md:581-597`.

`Id` is the profile-id universe and `H` the direct-handler-id universe; both are
parameters because `PROOF-DAG.md` §17 conditions 3 and 14 are OPEN. -/
inductive Mapping (Id H : Type) where
  | primitive (directHandlerId : H)
  | expansion (referencedProfileIds : List Id)
  | subcalculus (interpretation : SubcalcInterp H)
  | pure
  | foreign (directHandlerId : H)
  | target (targetAdapterId : String)
  | refusal (reason : RefusalReason)
  deriving DecidableEq

/-- `REIFICATION-CHECKLIST.md:577`. -/
inductive Decision where
  | accepted | refused | targetOnly
  deriving DecidableEq

/-- One admission profile. -/
structure Profile (Id H : Type) where
  id : Id
  decision : Decision
  mapping : Mapping Id H
  deriving DecidableEq

/-- One generated ledger row. `effectBearing` stands for
`effectReachability ≠ []`; `REIFICATION-CHECKLIST.md:455` — "The symbol
aggregate is effect-bearing if any overload/member is". -/
structure SurfaceRow (K Id H : Type) where
  rowKey : K
  effectBearing : Bool
  profiles : List (Profile Id H)
  deriving DecidableEq

/-- The generated ledger (`EC1-D006`). -/
structure PublicSurface (K Id H : Type) where
  rows : List (SurfaceRow K Id H)
  deriving DecidableEq

namespace Mapping

variable {Id H : Type}

/-- A mapping is a LEAF when it names its own witness outright. `expansion` is
the only non-leaf arm: it names other profiles instead. -/
def isLeaf : Mapping Id H → Bool
  | .expansion _ => false
  | _ => true

/-- The profiles a mapping defers to. `Cas/Schema/Guarded.lean:90`
`Ast.bareRefs` is the estate's shipped edge generator of exactly this kind. -/
def refs : Mapping Id H → List Id
  | .expansion rs => rs
  | _ => []

/-- The arms that name a term-level artifact rather than a declared boundary.
`expansion` counts — it names an expansion id and referenced profiles — which is
exactly why §2 has no force. -/
def constructive : Mapping Id H → Bool
  | .primitive _ => true
  | .expansion _ => true
  | .subcalculus _ => true
  | .foreign _ => true
  | _ => false

/-- `EC1-K07`'s "explicit non-Core boundary". -/
def isBoundary : Mapping Id H → Bool
  | .pure => true
  | .target _ => true
  | .refusal _ => true
  | _ => false

/-- The direct Core handler this profile owns, if any. Invariant 10: "Exactly
primitive and registered-foreign profiles own direct Core handler IDs"; the
`subcalculus (.handler h)` arm is invariant 15's typed handler. -/
def handler? : Mapping Id H → Option H
  | .primitive h => some h
  | .foreign h => some h
  | .subcalculus (.handler h) => some h
  | _ => none

/-- The arms that own no handler ID. -/
def handlerless : Mapping Id H → Bool
  | .expansion _ => true
  | .subcalculus .lowering => true
  | .pure => true
  | .target _ => true
  | .refusal _ => true
  | _ => false

/-- A leaf defers to nobody. Used by every soundness and completeness step
below. -/
theorem refs_eq_nil_of_isLeaf {m : Mapping Id H} (h : m.isLeaf = true) :
    m.refs = [] := by
  cases m <;> first | rfl | exact Bool.noConfusion h

/-- An `expansion` is the only arm with references. -/
theorem isLeaf_eq_false_iff {m : Mapping Id H} :
    m.isLeaf = false ↔ ∃ rs, m = .expansion rs := by
  cases m <;> simp [isLeaf]

end Mapping

namespace PublicSurface

variable {K Id H : Type}

/-- Every profile the ledger carries. -/
def profiles (s : PublicSurface K Id H) : List (Profile Id H) :=
  s.rows.flatMap (·.profiles)

theorem mem_profiles {s : PublicSurface K Id H} {r : SurfaceRow K Id H}
    {p : Profile Id H} (hr : r ∈ s.rows) (hp : p ∈ r.profiles) :
    p ∈ s.profiles :=
  List.mem_flatMap.mpr ⟨r, hr, hp⟩

end PublicSurface

/-! ## §2 — the row as written, at an arbitrary universe

`PROOF-DAG.md:207` deleted `exists! v, evalPure e env = v` and the same-input
function-equality forms as "tautologies for any Lean function". `EC1-T009` is
that deletion in disjunctive clothing: `constructive OR boundary` is a
disjunction over an exhaustive tagged union, so `cases` closes it with every
premise dead.

The scout established this over a four-element scratch id enum. Here `K`, `Id`
and `H` are arbitrary, so the finding cannot be an artifact of a finite model:
the row holds over EVERY row-key, profile-id and handler-id universe, including
uninhabited ones. -/

section AsWritten

variable {K Id H : Type}

/-- **Finding 1.** The row's disjunction holds of EVERY mapping, over EVERY id
and handler universe. No surface, no `PublicSurfaceWF`, no row, no
`effectBearing`, no ledger. -/
theorem T009_as_written (m : Mapping Id H) :
    m.constructive = true ∨ m.isBoundary = true := by
  cases m <;> first | exact .inl rfl | exact .inr rfl

/-- The same statement wearing the row's own quantifiers, with all three
premises visibly discarded. The underscores are the finding: `PublicSurfaceWF`
is an arbitrary predicate here, so no strengthening of `EC1-D009` can rescue the
row. -/
theorem T009_as_written_ignores_every_premise
    (PublicSurfaceWF : PublicSurface K Id H → Prop)
    (s : PublicSurface K Id H) (_hd : PublicSurfaceWF s) :
    ∀ r ∈ s.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

end AsWritten

/-! ## §3 — the statement that has content, and the scouted premise bundle

`Grounded` is the witness relation the row is missing: this profile's mapping
BOTTOMS OUT — either it is a leaf (a direct handler, a subcalculus
interpretation, or a declared non-Core boundary) or it is an expansion every one
of whose referenced profiles bottoms out.

Stated relationally, exactly as the estate states `Document.Guarded`
(`Cas/Schema/Guarded.lean:180`) as the ABSENCE OF A CYCLE and never as its
decision procedure restated. The decision procedure arrives in §5 and is proved
adequate against this relation, not substituted for it. -/

section Content

variable {K Id H : Type}

/-- The mapping graph bottoms out at `i`. -/
inductive Grounded (s : PublicSurface K Id H) : Id → Prop where
  | leaf {i : Id} (p : Profile Id H) (hp : p ∈ s.profiles) (hi : p.id = i)
      (hleaf : p.mapping.isLeaf = true) : Grounded s i
  | expand {i : Id} (p : Profile Id H) (hp : p ∈ s.profiles) (hi : p.id = i)
      (hne : p.mapping.isLeaf = false)
      (hrefs : ∀ q ∈ p.mapping.refs, Grounded s q) : Grounded s i

/-- The expansion edge, oriented so that `WellFounded` says "no infinite
unfolding". `Cas/Schema/Guarded.lean:163` `Document.Edge` is the same object at
the estate's shipped reference table. -/
def ExpandsTo (s : PublicSurface K Id H) (q p : Id) : Prop :=
  ∃ pr ∈ s.profiles, pr.id = p ∧ q ∈ pr.mapping.refs

/-- Well-formedness of the generated mapping ledger, each clause named by the
mutation it excludes and the invariant it transcribes. This is the scout's
bundle verbatim; §5 proves all five clauses follow from one decidable `Bool`. -/
structure SurfaceMappingWF (s : PublicSurface K Id H) : Prop where
  /-- `admissionProfiles` is NonEmpty (`REIFICATION-CHECKLIST.md:571`); zero
  "missing profile mappings" (invariant 25). Excludes §8.1. -/
  profilesNonempty : ∀ r ∈ s.rows, r.effectBearing = true → r.profiles ≠ []
  /-- One profile per `profileId` — `EC1-CE030`'s duplicate-free repair at the
  profile carrier (invariants 6/8). §7 proves it load-bearing for the DECIDED
  route even though §3 does not use it. -/
  idsNodup : (s.profiles.map (·.id)).Nodup
  /-- Invariant 14: every expansion is closed over mapped profiles. Excludes
  §8.2. -/
  refsResolve : ∀ p ∈ s.profiles, ∀ q ∈ p.mapping.refs,
      ∃ p' ∈ s.profiles, p'.id = q
  /-- The `derivedExpansion` disposition's own "termination/acyclicity
  evidence" (`REIFICATION-CHECKLIST.md:497`), which `EC1-T009` does not
  inherit. Excludes §8.3. -/
  expansionWF : WellFounded (ExpandsTo s)
  /-- Invariant 10: "no other profile owns a duplicate handler". Excludes §8.4.
  Shape of `Refusal.Clause.hosts_nodup` (`Cas/Lang/RefusalMap.lean:288`). -/
  handlersNodup : (s.profiles.filterMap (·.mapping.handler?)).Nodup

/-- Every id that names a profile is grounded. This is the whole content of the
word *constructive*: the witness is EXTRACTED by a terminating unfolding, not
asserted by a type. Only `refsResolve` and `expansionWF` are used. -/
theorem grounded_of_wf (s : PublicSurface K Id H) (h : SurfaceMappingWF s)
    (i : Id) : (∃ pr ∈ s.profiles, pr.id = i) → Grounded s i := by
  refine h.expansionWF.induction
    (C := fun i => (∃ pr ∈ s.profiles, pr.id = i) → Grounded s i) i ?_
  intro x ih hx
  obtain ⟨pr, hpr, hid⟩ := hx
  by_cases hleaf : pr.mapping.isLeaf = true
  · exact Grounded.leaf pr hpr hid hleaf
  · refine Grounded.expand pr hpr hid (by simpa using hleaf) ?_
    intro q hq
    exact ih q ⟨pr, hpr, hid, hq⟩ (h.refsResolve pr hpr q hq)

/-- **`EC1-T009`, restated so it has content — the scouted statement.**

Every effect-bearing row carries at least one admission profile, and every one
of its profiles' mappings bottoms out, by a terminating unfolding through
`referencedProfileIds`, in a direct handler, a subcalculus interpretation, or a
declared non-Core boundary.

FALSE on §8.1's ledger, FALSE on §8.2's, FALSE on §8.3's. That is what makes the
`EC1-H11` mapping counters attack this theorem rather than nothing. -/
theorem surface_mapping_grounded (s : PublicSurface K Id H)
    (h : SurfaceMappingWF s) :
    ∀ r ∈ s.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded s p.id := by
  intro r hr he
  refine ⟨h.profilesNonempty r hr he, ?_⟩
  intro p hp
  exact grounded_of_wf s h p.id ⟨p, PublicSurface.mem_profiles hr hp, rfl⟩

/-- The row carrying its stated `PublicSurfaceWF` dependency — for an ARBITRARY
predicate, which is the honest encoding of the scout's observation (d) that the
premise "contributes no step of the argument". `T008` is not a proof dependency
of `T009`, and `REIFICATION-CHECKLIST.md:517` says so outright: "The row-level
disposition is never used to infer them." -/
theorem surface_mapping_grounded_with_dead_premise
    (PublicSurfaceWF : PublicSurface K Id H → Prop)
    (s : PublicSurface K Id H) (_hd : PublicSurfaceWF s)
    (h : SurfaceMappingWF s) :
    ∀ r ∈ s.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded s p.id :=
  surface_mapping_grounded s h

/-- The schematic row is a CONSEQUENCE of the restated one — indeed of nothing
at all — so no content is lost by replacing it. -/
theorem restatement_implies_the_schematic_row (s : PublicSurface K Id H) :
    ∀ r ∈ s.rows, ∀ p ∈ r.profiles,
      p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ p _ => T009_as_written p.mapping

end Content

/-! ## §4 — ledger lookup, and its adequacy for `Grounded`'s existential

`Grounded` says "SOME profile of the ledger carries this id". Any checker says
"THE profile the lookup returns". §7 proves those are different claims; this
section proves they agree under `idsNodup`. -/

section Lookup

variable {K Id H : Type}

/-- Two ledger profiles with one id are one profile. Proved here rather than
imported: this toolchain is core Lean with no Mathlib (`library/cas` pins
`leanprover/lean4:v4.33.1` with an empty `.lake/packages`), and
`List.inj_on_of_nodup_map` does not exist in it. -/
theorem eq_of_nodup_ids {l : List (Profile Id H)}
    (hnd : (l.map (·.id)).Nodup) {p q : Profile Id H}
    (hp : p ∈ l) (hq : q ∈ l) (h : p.id = q.id) : p = q := by
  induction l with
  | nil => cases hp
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hna, hnt⟩ := hnd
    rcases List.mem_cons.mp hp with rfl | hp'
    · rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨q, hq', h.symm⟩) hna
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd (List.mem_map.mpr ⟨p, hp', h⟩) hna
      · exact ih hnt hp' hq'

variable [DecidableEq Id]

namespace PublicSurface

/-- The ledger lookup: `profileId ↦ profile`. -/
def find? (s : PublicSurface K Id H) (i : Id) : Option (Profile Id H) :=
  s.profiles.find? (fun p => decide (p.id = i))

/-- The out-edges of an id. A dangling id has none, which is why resolution and
acyclicity are independent: `Cas/Schema/Guarded.lean:76` states the same fact
about the same shape in prose. `settles` below therefore checks BOTH. -/
def out (s : PublicSurface K Id H) (i : Id) : List Id :=
  match s.find? i with
  | some p => p.mapping.refs
  | none => []

theorem find?_mem {s : PublicSurface K Id H} {i : Id} {q : Profile Id H}
    (h : s.find? i = some q) : q ∈ s.profiles ∧ q.id = i := by
  simp only [PublicSurface.find?] at h
  refine ⟨List.mem_of_find?_eq_some h, of_decide_eq_true ?_⟩
  exact List.find?_some (p := fun (x : Profile Id H) => decide (x.id = i)) h

theorem out_eq_of_find? {s : PublicSurface K Id H} {i : Id} {p : Profile Id H}
    (h : s.find? i = some p) : s.out i = p.mapping.refs := by
  simp [out, h]

/-- **Lookup adequacy.** Under `idsNodup`, the lookup returns exactly the
profile `Grounded`'s existential is talking about. -/
theorem find?_eq_some_of_mem {s : PublicSurface K Id H}
    (hnd : (s.profiles.map (·.id)).Nodup) {p : Profile Id H}
    (hp : p ∈ s.profiles) : s.find? p.id = some p := by
  cases hf : s.find? p.id with
  | none =>
    exact absurd (by simp : decide (p.id = p.id) = true)
      (List.find?_eq_none.mp hf p hp)
  | some p' =>
    obtain ⟨hp', hid⟩ := find?_mem hf
    exact congrArg some (eq_of_nodup_ids hnd hp' hp hid)

end PublicSurface

end Lookup

/-! ## §5 — the decision procedure, and checker SOUNDNESS

The scout's `expansionWF : WellFounded (ExpandsTo s)` is an ORACLE. `EC1-H11` is
a harness over a generated JSON ledger; a harness cannot exhibit a
`WellFounded`. This section replaces it with a `Bool`.

`settles` is `Cas/Schema/Guarded.lean:201` `Document.settles` transplanted to the
profile carrier, with one addition: each step also demands that the id RESOLVE.
`Guarded.settles` does not need that, because it decides acyclicity alone and a
dangling name has no outgoing edge. `Grounded` needs both — the profile must
exist AND the unfolding must terminate — so the two checks travel together and
resolution closure comes out of the same pass. -/

section Decide

variable {K Id H : Type} [DecidableEq Id]

namespace PublicSurface

/-- Fuel-bounded settling: does every unfolding path out of `i` resolve at every
step and run out within `fuel` steps? Structural on the fuel, so there is no
termination question. -/
def settles (s : PublicSurface K Id H) : Nat → Id → Bool
  | 0, i => (s.find? i).isSome && (s.out i).isEmpty
  | n + 1, i => (s.find? i).isSome && (s.out i).all (fun q => s.settles n q)

/-- Settling at ANY fuel already witnesses resolution. -/
theorem find?_isSome_of_settles {s : PublicSurface K Id H} {n : Nat} {i : Id}
    (h : s.settles n i = true) : (s.find? i).isSome = true := by
  cases n with
  | zero => exact (Bool.and_eq_true _ _ |>.mp h).1
  | succ k => exact (Bool.and_eq_true _ _ |>.mp h).1

/-- **CHECKER SOUNDNESS, the core step.** A settling id is grounded. No
`WellFounded`, no `Nodup`, no separate resolution premise: the fuel IS the
termination witness and the `isSome` conjunct IS the resolution witness. -/
theorem grounded_of_settles (s : PublicSurface K Id H) :
    ∀ (n : Nat) (i : Id), s.settles n i = true → Grounded s i := by
  intro n
  induction n with
  | zero =>
    intro i h
    obtain ⟨hsome, hempty⟩ := Bool.and_eq_true _ _ |>.mp h
    obtain ⟨p, hf⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hp, hid⟩ := find?_mem hf
    have hrefs : p.mapping.refs = [] := by
      rw [← out_eq_of_find? hf]; exact List.isEmpty_iff.mp hempty
    by_cases hleaf : p.mapping.isLeaf = true
    · exact Grounded.leaf p hp hid hleaf
    · refine Grounded.expand p hp hid (by simpa using hleaf) ?_
      intro q hq
      rw [hrefs] at hq
      cases hq
  | succ k ih =>
    intro i h
    obtain ⟨hsome, hall⟩ := Bool.and_eq_true _ _ |>.mp h
    obtain ⟨p, hf⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hp, hid⟩ := find?_mem hf
    by_cases hleaf : p.mapping.isLeaf = true
    · exact Grounded.leaf p hp hid hleaf
    · refine Grounded.expand p hp hid (by simpa using hleaf) ?_
      intro q hq
      refine ih q (List.all_eq_true.mp hall q ?_)
      rw [out_eq_of_find? hf]; exact hq

/-- **Resolution closure is a CONSEQUENCE of settling**, not an extra premise:
every referenced profile is itself settled, hence resolves. Needs `idsNodup`,
because the clause quantifies over EVERY profile carrying the id while `settles`
inspects the one the lookup returns. -/
theorem refsResolve_of_settles (s : PublicSurface K Id H) (n : Nat)
    (hnd : (s.profiles.map (·.id)).Nodup)
    (hall : ∀ p ∈ s.profiles, s.settles n p.id = true) :
    ∀ p ∈ s.profiles, ∀ q ∈ p.mapping.refs, ∃ p' ∈ s.profiles, p'.id = q := by
  intro p hp q hq
  have hf : s.find? p.id = some p := find?_eq_some_of_mem hnd hp
  have hout : q ∈ s.out p.id := by rw [out_eq_of_find? hf]; exact hq
  have hs := hall p hp
  cases n with
  | zero =>
    obtain ⟨_, hempty⟩ := Bool.and_eq_true _ _ |>.mp hs
    rw [List.isEmpty_iff.mp hempty] at hout
    cases hout
  | succ k =>
    obtain ⟨_, hallq⟩ := Bool.and_eq_true _ _ |>.mp hs
    have hq' := List.all_eq_true.mp hallq q hout
    obtain ⟨p', hf'⟩ := Option.isSome_iff_exists.mp (find?_isSome_of_settles hq')
    obtain ⟨hp', hid'⟩ := find?_mem hf'
    exact ⟨p', hp', hid'⟩

/-- **The `WellFounded` oracle, DISCHARGED.** Every predecessor chain of
`ExpandsTo` descends the fuel, so a fully settled ledger has a well-founded
expansion relation. This is what a harness cannot produce and the kernel can.

Ids naming no profile are accessible for free — they have no predecessors — so
the statement quantifies over the whole id universe, exactly as the scout's
premise does. -/
theorem expansionWF_of_settles (s : PublicSurface K Id H) (n : Nat)
    (hnd : (s.profiles.map (·.id)).Nodup)
    (hall : ∀ p ∈ s.profiles, s.settles n p.id = true) :
    WellFounded (ExpandsTo s) := by
  have key : ∀ (m : Nat) (i : Id), s.settles m i = true → Acc (ExpandsTo s) i := by
    intro m
    induction m with
    | zero =>
      intro i h
      obtain ⟨hsome, hempty⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨p, hf⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hp, hid⟩ := find?_mem hf
      refine Acc.intro _ (fun q hq => ?_)
      obtain ⟨pr, hpr, hprid, hqin⟩ := hq
      have : pr = p := eq_of_nodup_ids hnd hpr hp (by rw [hprid, hid])
      subst this
      rw [← out_eq_of_find? hf, List.isEmpty_iff.mp hempty] at hqin
      cases hqin
    | succ k ih =>
      intro i h
      obtain ⟨hsome, hallq⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨p, hf⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hp, hid⟩ := find?_mem hf
      refine Acc.intro _ (fun q hq => ?_)
      obtain ⟨pr, hpr, hprid, hqin⟩ := hq
      have : pr = p := eq_of_nodup_ids hnd hpr hp (by rw [hprid, hid])
      subst this
      refine ih q (List.all_eq_true.mp hallq q ?_)
      rw [out_eq_of_find? hf]; exact hqin
  refine ⟨fun i => ?_⟩
  by_cases hi : ∃ p ∈ s.profiles, p.id = i
  · obtain ⟨p, hp, rfl⟩ := hi
    exact key n p.id (hall p hp)
  · refine Acc.intro _ (fun q hq => ?_)
    obtain ⟨pr, hpr, hprid, _⟩ := hq
    exact absurd ⟨pr, hpr, hprid⟩ hi

/-- **THE DOOR.** One `Bool`, computable on a generated ledger, carrying every
clause of `SurfaceMappingWF`. Its five conjuncts are, in order: invariant 25
(no effect-bearing row without a profile), invariants 6/8 (`EC1-CE030`'s
duplicate-free discipline), invariant 10 (handler uniqueness), and — in the last
conjunct alone — invariant 14 (resolution closure) together with
`REIFICATION-CHECKLIST.md:497`'s termination evidence.

`fuel` is a parameter here; §6.5 proves `fuel = |profiles|` is the bound at
which the check is also COMPLETE, so that is the value a harness supplies. -/
def checkB [DecidableEq H] (s : PublicSurface K Id H) (fuel : Nat) : Bool :=
  (s.rows.all fun r => !r.effectBearing || !r.profiles.isEmpty)
    && decide ((s.profiles.map (·.id)).Nodup)
    && decide ((s.profiles.filterMap (·.mapping.handler?)).Nodup)
    && s.profiles.all (fun p => s.settles fuel p.id)

theorem profilesNonempty_of_checkB [DecidableEq H] {s : PublicSurface K Id H} {fuel : Nat}
    (h : s.checkB fuel = true) :
    ∀ r ∈ s.rows, r.effectBearing = true → r.profiles ≠ [] := by
  intro r hr he
  have h1 := (Bool.and_eq_true _ _ |>.mp
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h).1).1).1
  have := List.all_eq_true.mp h1 r hr
  rw [he] at this
  simpa using this

theorem idsNodup_of_checkB [DecidableEq H] {s : PublicSurface K Id H} {fuel : Nat}
    (h : s.checkB fuel = true) : (s.profiles.map (·.id)).Nodup :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h).1).1).2

theorem handlersNodup_of_checkB [DecidableEq H] {s : PublicSurface K Id H} {fuel : Nat}
    (h : s.checkB fuel = true) :
    (s.profiles.filterMap (·.mapping.handler?)).Nodup :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp
    (Bool.and_eq_true _ _ |>.mp h).1).2

theorem settles_of_checkB [DecidableEq H] {s : PublicSurface K Id H} {fuel : Nat}
    (h : s.checkB fuel = true) :
    ∀ p ∈ s.profiles, s.settles fuel p.id = true :=
  fun p hp => List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).2 p hp

end PublicSurface

/-- **CHECKER SOUNDNESS, packaged.** One decidable `Bool` implies the WHOLE
scouted premise bundle, `expansionWF` included. This is the step that removes
the oracle: `EC1-H11` computes `checkB`, and the kernel converts it into
`SurfaceMappingWF`.

It is the `Cas/Schema/Guarded.lean:378` `references_guarded_decidable` /
`:421 Decidable Document.Guarded` discipline at the profile carrier, and it
inherits that module's caveat verbatim: the door decides CONSTRUCTIBILITY, not
PRODUCTIVITY. A ledger that passes has a terminating unfolding; nothing here
says the unfolded result MEANS anything. -/
theorem surfaceMappingWF_of_checkB [DecidableEq H] (s : PublicSurface K Id H) (fuel : Nat)
    (h : s.checkB fuel = true) : SurfaceMappingWF s where
  profilesNonempty := PublicSurface.profilesNonempty_of_checkB h
  idsNodup := PublicSurface.idsNodup_of_checkB h
  refsResolve := PublicSurface.refsResolve_of_settles s fuel
    (PublicSurface.idsNodup_of_checkB h) (PublicSurface.settles_of_checkB h)
  expansionWF := PublicSurface.expansionWF_of_settles s fuel
    (PublicSurface.idsNodup_of_checkB h) (PublicSurface.settles_of_checkB h)
  handlersNodup := PublicSurface.handlersNodup_of_checkB h

/-- **`EC1-T009`, decided.** The row's conclusion from a `Bool` a harness can
compute. This is the form `EC1-H11` can actually run, and the form on which its
mapping counters bite. -/
theorem surface_mapping_grounded_decided [DecidableEq H] (s : PublicSurface K Id H) (fuel : Nat)
    (h : s.checkB fuel = true) :
    ∀ r ∈ s.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded s p.id :=
  surface_mapping_grounded s (surfaceMappingWF_of_checkB s fuel h)

end Decide

/-! ## §6 — checker COMPLETENESS

Soundness alone leaves a checker free to refuse everything. `Cas/Backend/Canon.lean:199-215`
records the estate's own name for that hole ("satisfied by a canonicalizer that
throws services away") and `Cas/Schema/Guarded.lean` closes the analogous hole
with a completeness half. This section is that half. -/

section Complete

variable {K Id H : Type} [DecidableEq Id]

/-- The pigeonhole: a duplicate-free list drawn from `t` is no longer than `t`.
Proved here because the toolchain is core Lean with no Mathlib; this is
`Cas/Schema/Guarded.lean:316 nodup_length_le` at an arbitrary id universe rather
than at `String`. The induction erases the head from `t` at every step, which is
what turns "no duplicates" into a length bound. -/
theorem nodup_length_le : ∀ {l t : List Id}, l.Nodup →
    (∀ x ∈ l, x ∈ t) → l.length ≤ t.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, t, hnd, hsub => by
    have hmem : a ∈ t := hsub a (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ x ∈ l, x ∈ t.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd'.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem _ hx))
    have hlen := nodup_length_le hnd'.2 hsub'
    have herase : (t.erase a).length + 1 = t.length := by
      rw [List.length_erase_of_mem hmem]
      exact Nat.succ_pred_eq_of_pos (List.length_pos_of_mem hmem)
    simp only [List.length_cons]
    omega

namespace PublicSurface

/-- Settling is monotone in the fuel. -/
theorem settles_succ (s : PublicSurface K Id H) :
    ∀ (n : Nat) (i : Id), s.settles n i = true → s.settles (n + 1) i = true := by
  intro n
  induction n with
  | zero =>
    intro i h
    obtain ⟨hsome, hempty⟩ := Bool.and_eq_true _ _ |>.mp h
    have : s.out i = [] := List.isEmpty_iff.mp hempty
    simp [settles, hsome, this]
  | succ k ih =>
    intro i h
    obtain ⟨hsome, hall⟩ := Bool.and_eq_true _ _ |>.mp h
    refine Bool.and_eq_true _ _ |>.mpr ⟨hsome, List.all_eq_true.mpr ?_⟩
    intro q hq
    exact ih q (List.all_eq_true.mp hall q hq)

theorem settles_le (s : PublicSurface K Id H) {m n : Nat} (hmn : m ≤ n) {i : Id}
    (h : s.settles m i = true) : s.settles n i = true := by
  induction n with
  | zero => exact Nat.le_zero.mp hmn ▸ h
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact settles_succ s k i (ih (Nat.lt_succ_iff.mp hlt))
    · exact Nat.le_antisymm hmn hge ▸ h

/-- A common fuel for a whole list of settling ids. -/
theorem exists_fuel_all (s : PublicSurface K Id H) :
    ∀ (l : List Id), (∀ q ∈ l, ∃ n, s.settles n q = true) →
      ∃ n, ∀ q ∈ l, s.settles n q = true := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, by simp⟩
  | cons a t ih =>
    intro h
    obtain ⟨na, hna⟩ := h a (List.mem_cons_self ..)
    obtain ⟨nt, hnt⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    refine ⟨max na nt, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact settles_le s (Nat.le_max_left na nt) hna
    · exact settles_le s (Nat.le_max_right na nt) (hnt q hq')

/-- **CHECKER COMPLETENESS.** A grounded id settles at some fuel.

`idsNodup` is REQUIRED and §7 proves it necessary: `Grounded` says SOME profile
carrying the id bottoms out, while `settles` inspects THE profile the lookup
returns. -/
theorem settles_of_grounded (s : PublicSurface K Id H)
    (hnd : (s.profiles.map (·.id)).Nodup) {i : Id} (hg : Grounded s i) :
    ∃ n, s.settles n i = true := by
  induction hg with
  | leaf p hp hi hleaf =>
    subst hi
    have hf : s.find? p.id = some p := find?_eq_some_of_mem hnd hp
    refine ⟨0, ?_⟩
    have hout : s.out p.id = [] := by
      rw [out_eq_of_find? hf, Mapping.refs_eq_nil_of_isLeaf hleaf]
    simp [settles, hf, hout]
  | expand p hp hi _ _ ih =>
    subst hi
    have hf : s.find? p.id = some p := find?_eq_some_of_mem hnd hp
    obtain ⟨n, hn⟩ := exists_fuel_all s p.mapping.refs ih
    refine ⟨n + 1, ?_⟩
    refine Bool.and_eq_true _ _ |>.mpr ⟨by simp [hf], List.all_eq_true.mpr ?_⟩
    intro q hq
    rw [out_eq_of_find? hf] at hq
    exact hn q hq

/-- **ADEQUACY.** Under `idsNodup`, the decidable search and the relation agree
exactly. This is the `Cas/Core/Admission.lean:60 checkRefs_ok_iff` shape at the
profile carrier — soundness and completeness in one `iff` — and it is
`PROOF-DAG.md:516`'s sanctioned checker route, not its prohibited shortcut.

Note carefully what it is NOT: `Grounded` is defined WITHOUT reference to
`settles`, so this is not the checker restated. That independence is what keeps
the row out of the `PROOF-DAG.md:207` tautology family a second time. -/
theorem grounded_iff_exists_settles (s : PublicSurface K Id H)
    (hnd : (s.profiles.map (·.id)).Nodup) (i : Id) :
    Grounded s i ↔ ∃ n, s.settles n i = true :=
  ⟨settles_of_grounded s hnd, fun ⟨n, h⟩ => grounded_of_settles s n i h⟩

/-! ### §6.5 — completeness at a fuel the harness can name

`grounded_iff_exists_settles` says a grounded id settles at SOME fuel. A harness
cannot run "some fuel". This subsection proves the bound is the ledger's own
size, by the argument `Cas/Schema/Guarded.lean` runs at its reference table: an
unsettled id walks further than the ledger has profiles, so it repeats one, and
the repeat is a cycle — and a grounded id lies on no cycle.

The walk is extracted RELATIVE TO GROUNDING rather than absolutely, because
`settles` here also checks resolution: a `false` could mean "dangling" instead of
"too deep", and only grounding rules that out. -/

/-- One expansion step, read off the lookup. `Cas/Schema/Guarded.lean:163`
`Document.Edge` at this carrier. -/
def Edge (s : PublicSurface K Id H) (i q : Id) : Prop := q ∈ s.out i

/-- The transitive closure, as an inductive relation, so a cycle is
`ReachPlus s a a` and needs no list surgery to state
(`Cas/Schema/Guarded.lean:168`). -/
inductive ReachPlus (s : PublicSurface K Id H) : Id → Id → Prop
  | edge {i q : Id} : s.Edge i q → ReachPlus s i q
  | step {i q r : Id} : s.Edge i q → ReachPlus s q r → ReachPlus s i r

/-- One edge costs one unit of fuel. -/
theorem settles_step {s : PublicSurface K Id H} {n m : Id} {fuel : Nat}
    (he : s.Edge n m) (hs : s.settles fuel n = true) :
    ∃ j, j < fuel ∧ s.settles j m = true := by
  have he' : m ∈ s.out n := he
  cases fuel with
  | zero =>
    obtain ⟨_, hempty⟩ := Bool.and_eq_true _ _ |>.mp hs
    rw [List.isEmpty_iff.mp hempty] at he'
    cases he'
  | succ k =>
    obtain ⟨_, hall⟩ := Bool.and_eq_true _ _ |>.mp hs
    exact ⟨k, Nat.lt_succ_self k, List.all_eq_true.mp hall m he'⟩

/-- Reaching descends the fuel (`Cas/Schema/Guarded.lean:252`). -/
theorem reachPlus_descends {s : PublicSurface K Id H} {n m : Id}
    (h : ReachPlus s n m) : ∀ {fuel : Nat}, s.settles fuel n = true →
      ∃ j, j < fuel ∧ s.settles j m = true := by
  induction h with
  | edge he => intro fuel hs; exact settles_step he hs
  | step he _ ih =>
    intro fuel hs
    obtain ⟨j, hj, hjs⟩ := settles_step he hs
    obtain ⟨i, hi, his⟩ := ih hjs
    exact ⟨i, Nat.lt_trans hi hj, his⟩

/-- An id on a cycle settles at NO fuel whatsoever — infinite descent, run as
strong induction (`Cas/Schema/Guarded.lean:266`). -/
theorem not_settles_of_cycle {s : PublicSurface K Id H} {a : Id}
    (hc : ReachPlus s a a) : ∀ fuel, s.settles fuel a = false := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    cases hs : s.settles fuel a with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjs⟩ := reachPlus_descends hc hs
      rw [ih j hj] at hjs
      exact Bool.noConfusion hjs

/-- A walk along expansion edges, as the list of ids it visits. -/
def Walk (s : PublicSurface K Id H) : List Id → Prop
  | [] => True
  | [_] => True
  | n :: m :: rest => s.Edge n m ∧ s.Walk (m :: rest)

theorem walk_reachPlus {s : PublicSurface K Id H} :
    ∀ {x : Id} {rest : List Id}, s.Walk (x :: rest) →
      ∀ {y : Id}, y ∈ rest → ReachPlus s x y
  | _, [], _, _, hy => absurd hy (by simp)
  | x, m :: rest, hw, y, hy => by
    obtain ⟨he, hrest⟩ := hw
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact .edge he
    · exact .step he (walk_reachPlus hrest hy')

/-- A walk that repeats an id contains a cycle AT ONE OF ITS OWN NODES. The
membership clause is what `Cas/Schema/Guarded.lean:390 walk_dup_cycle` drops and
this file needs: the repeated id must be shown grounded to reach the
contradiction. -/
theorem walk_dup_cycle {s : PublicSurface K Id H} :
    ∀ {l : List Id}, s.Walk l → ¬ l.Nodup → ∃ a ∈ l, ReachPlus s a a
  | [], _, hnd => absurd List.nodup_nil hnd
  | [_], _, hnd => absurd (by simp) hnd
  | x :: m :: rest, hw, hnd => by
    by_cases hx : x ∈ m :: rest
    · exact ⟨x, List.mem_cons_self .., walk_reachPlus hw hx⟩
    · have hnd' : ¬ (m :: rest).Nodup := fun h => hnd (List.nodup_cons.mpr ⟨hx, h⟩)
      obtain ⟨a, ha, hc⟩ := walk_dup_cycle hw.2 hnd'
      exact ⟨a, List.mem_cons_of_mem _ ha, hc⟩

/-- A grounded id resolves. -/
theorem find?_isSome_of_grounded {s : PublicSurface K Id H}
    (hnd : (s.profiles.map (·.id)).Nodup) {i : Id} (hg : Grounded s i) :
    ∃ p, s.find? i = some p := by
  cases hg with
  | leaf p hp hi _ => exact ⟨p, by rw [← hi]; exact find?_eq_some_of_mem hnd hp⟩
  | expand p hp hi _ _ => exact ⟨p, by rw [← hi]; exact find?_eq_some_of_mem hnd hp⟩

omit [DecidableEq Id] in
/-- A grounded id is one the ledger carries. -/
theorem mem_ids_of_grounded {s : PublicSurface K Id H} {i : Id}
    (hg : Grounded s i) : i ∈ s.profiles.map (·.id) := by
  cases hg with
  | leaf p hp hi _ => exact List.mem_map.mpr ⟨p, hp, hi⟩
  | expand p hp hi _ _ => exact List.mem_map.mpr ⟨p, hp, hi⟩

/-- Grounding descends along an expansion edge. -/
theorem grounded_edge {s : PublicSurface K Id H}
    (hnd : (s.profiles.map (·.id)).Nodup) {i q : Id}
    (hg : Grounded s i) (he : s.Edge i q) : Grounded s q := by
  have he' : q ∈ s.out i := he
  cases hg with
  | leaf p hp hi hleaf =>
    exfalso
    have hf : s.find? i = some p := by rw [← hi]; exact find?_eq_some_of_mem hnd hp
    rw [out_eq_of_find? hf, Mapping.refs_eq_nil_of_isLeaf hleaf] at he'
    cases he'
  | expand p hp hi _ hrefs =>
    have hf : s.find? i = some p := by rw [← hi]; exact find?_eq_some_of_mem hnd hp
    rw [out_eq_of_find? hf] at he'
    exact hrefs q he'

/-- A grounded id lies on no cycle. -/
theorem grounded_not_cycle {s : PublicSurface K Id H}
    (hnd : (s.profiles.map (·.id)).Nodup) {a : Id}
    (hg : Grounded s a) : ¬ ReachPlus s a a := by
  intro hc
  obtain ⟨n, hn⟩ := settles_of_grounded s hnd hg
  rw [not_settles_of_cycle hc n] at hn
  exact Bool.noConfusion hn

/-- **Walk extraction, relative to grounding.** An unsettled grounded id admits a
walk of exactly the failed fuel's length, every node of which is itself grounded
(`Cas/Schema/Guarded.lean:341 settles_false_walk`, with `n ∈ d.names` strengthened
to `Grounded`). -/
theorem grounded_walk_of_not_settles {s : PublicSurface K Id H}
    (hnd : (s.profiles.map (·.id)).Nodup) :
    ∀ (fuel : Nat) {i : Id}, Grounded s i → s.settles fuel i = false →
      ∃ w : List Id, w.length = fuel ∧ s.Walk (i :: w) ∧ ∀ x ∈ w, Grounded s x := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hg _
    exact ⟨[], rfl, trivial, by simp⟩
  | succ k ih =>
    intro i hg hs
    obtain ⟨p, hf⟩ := find?_isSome_of_grounded hnd hg
    have hsome : (s.find? i).isSome = true := by rw [hf]; rfl
    have hall : (s.out i).all (fun q => s.settles k q) = false := by
      have : ((s.find? i).isSome && (s.out i).all (fun q => s.settles k q)) = false := hs
      rw [hsome, Bool.true_and] at this
      exact this
    obtain ⟨q, hq, hqf⟩ := List.all_eq_false.mp hall
    have hqg : Grounded s q := grounded_edge hnd hg hq
    obtain ⟨w, hlen, hwalk, hwg⟩ := ih hqg (by simpa using hqf)
    refine ⟨q :: w, by simp [hlen], ⟨hq, hwalk⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hqg
    · exact hwg x hx'

/-- **COMPLETENESS AT THE LEDGER'S OWN SIZE.** A grounded id settles within
`|profiles|` steps — the fuel a harness can compute from the artifact it is
holding. The bound is exact for the same reason it is at
`Cas/Schema/Guarded.lean`: the walk's nodes are drawn from the ledger, so one
more node than the ledger has profiles forces a repeat. -/
theorem settles_of_grounded_at_size {s : PublicSurface K Id H}
    (hnd : (s.profiles.map (·.id)).Nodup) {i : Id} (hg : Grounded s i) :
    s.settles s.profiles.length i = true := by
  cases hs : s.settles s.profiles.length i with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨w, hlen, hwalk, hwg⟩ :=
      grounded_walk_of_not_settles hnd s.profiles.length hg hs
    have hgall : ∀ x ∈ i :: w, Grounded s x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hg
      · exact hwg x hx'
    have hsub : ∀ x ∈ i :: w, x ∈ s.profiles.map (·.id) :=
      fun x hx => mem_ids_of_grounded (hgall x hx)
    have hnotnodup : ¬ (i :: w).Nodup := by
      intro hnd2
      have hle := nodup_length_le hnd2 hsub
      rw [List.length_map, List.length_cons, hlen] at hle
      omega
    obtain ⟨a, ha, hc⟩ := walk_dup_cycle hwalk hnotnodup
    exact grounded_not_cycle hnd (hgall a ha) hc

end PublicSurface

/-- **The door, both ways.** At `fuel = |profiles|` the decidable check is
equivalent to the whole scouted premise bundle. Soundness is
`surfaceMappingWF_of_checkB`; completeness is `settles_of_grounded_at_size`
composed with `grounded_of_wf`.

This is `Cas/Schema/Guarded.lean:378 references_guarded_decidable` at the profile
carrier, and it inherits that theorem's own reading of what a door owes: it
refuses nothing sound, and it admits nothing unsound. It also inherits the
module's caveat verbatim — the door decides CONSTRUCTIBILITY, not PRODUCTIVITY. -/
theorem checkB_iff [DecidableEq H] (s : PublicSurface K Id H) :
    s.checkB s.profiles.length = true ↔ SurfaceMappingWF s := by
  refine ⟨surfaceMappingWF_of_checkB s s.profiles.length, fun h => ?_⟩
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr
    ⟨Bool.and_eq_true _ _ |>.mpr ⟨?_, decide_eq_true h.idsNodup⟩,
      decide_eq_true h.handlersNodup⟩, ?_⟩
  · refine List.all_eq_true.mpr (fun r hr => ?_)
    cases he : r.effectBearing with
    | false => simp
    | true =>
      have := h.profilesNonempty r hr he
      simp [this]
  · refine List.all_eq_true.mpr (fun p hp => ?_)
    exact PublicSurface.settles_of_grounded_at_size h.idsNodup
      (grounded_of_wf s h p.id ⟨p, hp, rfl⟩)

/-- The scouted premise bundle is DECIDABLE. `EC1-H11` needs no oracle. -/
instance [DecidableEq H] (s : PublicSurface K Id H) :
    Decidable (SurfaceMappingWF s) :=
  decidable_of_iff _ (checkB_iff s)

/-- A ledger the door refuses is not a well-formed ledger. This is what turns
each mutant below from "the check happens to fail" into "the ledger is
REFUTED". -/
theorem refused_of_checkB_false [DecidableEq H] {s : PublicSurface K Id H}
    (h : s.checkB s.profiles.length = false) : ¬ SurfaceMappingWF s :=
  fun hw => Bool.noConfusion (((checkB_iff s).mpr hw).symm.trans h)

end Complete
end EffectCoreT009

/-! # THE ATTACK

Everything above this line is `T009.lean:111-1032`, verbatim. Everything below
is the breaker's own work. -/

namespace AttackT009

open EffectCoreT009 EffectCoreT009.PublicSurface

/-! ## §A1 — the "dead premise" theorem carries no information

`surface_mapping_grounded_with_dead_premise` is reported as "strictly stronger
than instantiating it" and as turning `REIFICATION-CHECKLIST.md:517` into "a
kernel fact rather than a remark".

It is neither. Quantifying over an ARBITRARY predicate and then discarding it is
an eta-expansion: instantiate `P := fun _ => True` and the premise evaporates.
The two forms are INTERDERIVABLE for every conclusion whatsoever, so the
`with_dead_premise` variant is exactly as strong as the plain one and no
stronger. -/

section DeadPremise

variable {K Id H : Type}

/-- **A1.** For EVERY conclusion `C`, carrying an arbitrary predicate as a dead
premise is interderivable with not carrying it. -/
theorem dead_premise_is_eta (C : PublicSurface K Id H → Prop) :
    (∀ (P : PublicSurface K Id H → Prop) (s : PublicSurface K Id H), P s → C s)
      ↔ (∀ s : PublicSurface K Id H, C s) :=
  ⟨fun f s => f (fun _ => True) s trivial, fun f _ s _ => f s⟩

/-- **A1, applied to the delivered pair.** `surface_mapping_grounded_with_dead_premise`
and `surface_mapping_grounded` are the two sides of this `iff`. The
`with_dead_premise` form is therefore evidence about the RESTATEMENT the
implementer chose, not about `EC1-D009`, `EC1-T008`, or the DAG edge
`T009 -> T008`. -/
theorem dead_premise_adds_nothing :
    (∀ (P : PublicSurface K Id H → Prop) (s : PublicSurface K Id H), P s →
        (SurfaceMappingWF s → ∀ r ∈ s.rows, r.effectBearing = true →
          r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded s p.id))
      ↔ (∀ s : PublicSurface K Id H,
        (SurfaceMappingWF s → ∀ r ∈ s.rows, r.effectBearing = true →
          r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded s p.id)) :=
  dead_premise_is_eta _

/-- The same eta-expansion applied to `T009_as_written_ignores_every_premise`.
Quantifying over an arbitrary `PublicSurfaceWF` proves nothing that
`T009_as_written` did not already prove. -/
theorem as_written_dead_premise_adds_nothing :
    (∀ (P : PublicSurface K Id H → Prop) (s : PublicSurface K Id H), P s →
        (∀ r ∈ s.rows, r.effectBearing = true → ∀ p ∈ r.profiles,
          p.mapping.constructive = true ∨ p.mapping.isBoundary = true))
      ↔ (∀ s : PublicSurface K Id H,
        (∀ r ∈ s.rows, r.effectBearing = true → ∀ p ∈ r.profiles,
          p.mapping.constructive = true ∨ p.mapping.isBoundary = true)) :=
  dead_premise_is_eta _

end DeadPremise

/-! ## §A2 — the attack universes -/

inductive PId where
  | pA | pB | pC | pD
  deriving DecidableEq, Repr

inductive HId where
  | hPut | hAsk
  deriving DecidableEq, Repr

inductive RKey where
  | succeed | failCause | multipartHeaders
  deriving DecidableEq, Repr

abbrev Surface := PublicSurface RKey PId HId

/-! ## §A3 — the door admits a ledger with NO Core content whatsoever

`Grounded`'s `leaf` arm accepts every non-`expansion` arm, `refusal` included.
So a ledger in which every effect-bearing row is REFUSED bottoms out at every
id, passes `checkB` at its own size, satisfies the full scouted bundle, and
satisfies the delivered conclusion — while naming not one handler, not one
constructive mapping, and not one Core node.

This is the `Cas/Backend/Canon.lean:199-215` hole ("satisfied by a canonicalizer
that throws services away") at the level of the CONCLUSION rather than at the
level of the checker. The file names that hole for PRODUCTIVITY (§6.6) but not
for this: the door is silent about whether anything at all was reified. -/

def allRefusedSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .refused, .refusal .typeDiagnostic⟩]⟩,
    ⟨.failCause, true, [⟨.pB, .refused, .refusal (.casClause .dangling)⟩]⟩,
    ⟨.multipartHeaders, true, [⟨.pC, .refused, .refusal .admissionDiagnostic⟩]⟩]⟩

theorem allRefused_checkB :
    allRefusedSurface.checkB allRefusedSurface.profiles.length = true := by decide

theorem allRefused_wf : SurfaceMappingWF allRefusedSurface :=
  surfaceMappingWF_of_checkB _ _ allRefused_checkB

/-- The delivered conclusion, in full, on a ledger that reifies nothing. -/
theorem allRefused_satisfies_the_row :
    ∀ r ∈ allRefusedSurface.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded allRefusedSurface p.id :=
  surface_mapping_grounded _ allRefused_wf

/-- **A3.** And it has no Core content: every mapping is non-constructive and
the whole ledger owns zero handler ids. -/
theorem allRefused_has_no_core_content :
    allRefusedSurface.profiles.all (fun p => !p.mapping.constructive) = true
      ∧ allRefusedSurface.profiles.filterMap (·.mapping.handler?) = [] := by
  refine ⟨by decide, by decide⟩

/-- The empty ledger passes too — the trivial end of the same scale. -/
def emptySurface : Surface := ⟨[]⟩

theorem emptySurface_passes :
    emptySurface.checkB emptySurface.profiles.length = true := by decide

theorem emptySurface_wf : SurfaceMappingWF emptySurface :=
  surfaceMappingWF_of_checkB _ _ emptySurface_passes

/-! ## §A4 — `EC1-F60`, duplicate half: DUPLICATE ROW KEYS PASS THE DOOR

Invariant 25 (`REIFICATION-CHECKLIST.md:1244`): "The census closure summary must
be zero in missing/DUPLICATE ROW KEYS, profile gaps/overlaps, ...". `EC1-K07`:
"multiply classified ... effect-bearing rows are not [permitted]".

`SurfaceMappingWF` has no clause on `rowKey` at all, and `checkB` never looks at
one. Two rows carrying the SAME `SurfaceRowKey` — the exact defect invariant 25
counts — pass the door and satisfy the theorem. -/

def dupRowKeySurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩,
    ⟨.succeed, true, [⟨.pB, .accepted, .primitive .hAsk⟩]⟩]⟩

theorem dupRowKeySurface_really_duplicates :
    dupRowKeySurface.rows.map (·.rowKey) = [RKey.succeed, RKey.succeed] := by decide

theorem dupRowKey_passes :
    dupRowKeySurface.checkB dupRowKeySurface.profiles.length = true := by decide

/-- **A4.** A ledger with duplicate row keys satisfies the delivered
well-formedness bundle in full. -/
theorem dupRowKey_wf : SurfaceMappingWF dupRowKeySurface :=
  surfaceMappingWF_of_checkB _ _ dupRowKey_passes

theorem dupRowKey_satisfies_the_row :
    ∀ r ∈ dupRowKeySurface.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded dupRowKeySurface p.id :=
  surface_mapping_grounded _ dupRowKey_wf

/-! ## §A5 — `EC1-F59`: an omitted census row passes through unnoticed

`EC1-K07`: "The two deep MultipartParser modules named in
`REIFICATION-CHECKLIST.md` must appear."

`PublicSurface` is a bare `List SurfaceRow` with no relation to the pinned
package, and `SurfaceMappingWF` has no census-completeness clause. Deleting a
whole self-contained row from a passing ledger leaves a ledger that still
passes, still satisfies the bundle, and still satisfies the theorem. `EC1-F59`
cannot be run against this door. -/

def censusFull : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩,
    ⟨.multipartHeaders, true, [⟨.pB, .accepted, .primitive .hAsk⟩]⟩]⟩

def censusOmitted : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩]⟩

/-- **A5.** The full census and the census with a required deep module DELETED
are both admitted, indistinguishably. -/
theorem F59_passes_through :
    censusFull.checkB censusFull.profiles.length = true
      ∧ censusOmitted.checkB censusOmitted.profiles.length = true := by
  refine ⟨by decide, by decide⟩

theorem censusOmitted_wf : SurfaceMappingWF censusOmitted :=
  surfaceMappingWF_of_checkB _ _ (F59_passes_through.2)

/-! ### §A5b — `admissionProfiles` is NonEmpty UNCONDITIONALLY

`REIFICATION-CHECKLIST.md:571` writes `admissionProfiles: NonEmpty[{ ... }]` in
the required ledger row, with no `effectBearing` guard. `profilesNonempty` adds
one, and `checkB`'s first conjunct short-circuits on `!r.effectBearing`. A row
the generated JSON schema itself rejects is admitted by the door. -/

def emptyNonEffectRowSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩,
    ⟨.multipartHeaders, false, []⟩]⟩

theorem emptyNonEffectRow_passes :
    emptyNonEffectRowSurface.checkB emptyNonEffectRowSurface.profiles.length = true := by
  decide

theorem emptyNonEffectRow_wf : SurfaceMappingWF emptyNonEffectRowSurface :=
  surfaceMappingWF_of_checkB _ _ emptyNonEffectRow_passes

/-! ## §A6 — the `decision` field is inert

`REIFICATION-CHECKLIST.md:577` gives every profile a
`decision: accepted | refused | targetOnly`, and invariant 8 requires "every
profile has one decision AND its own mapping". `REIFICATION-CHECKLIST.md:494-502`
tabulates which mapping each disposition requires; invariant 12 confines
`modeledPure`; invariant 13 confines `targetOnly` to "a run/configuration/
observation boundary".

`Profile.decision` is declared in the carrier and then appears in NO definition,
NO clause of `SurfaceMappingWF`, and NO theorem. The door admits a ledger whose
every decision contradicts its own mapping. -/

def incoherentDecisionSurface : Surface :=
  ⟨[-- decision `refused`, yet the profile OWNS a direct Core handler
    ⟨.succeed, true, [⟨.pA, .refused, .primitive .hPut⟩]⟩,
    -- decision `accepted`, yet the mapping is a refusal
    ⟨.failCause, true, [⟨.pB, .accepted, .refusal .admissionDiagnostic⟩]⟩,
    -- decision `targetOnly`, yet the mapping is `pure`
    ⟨.multipartHeaders, true, [⟨.pC, .targetOnly, .pure⟩]⟩]⟩

theorem incoherentDecision_passes :
    incoherentDecisionSurface.checkB incoherentDecisionSurface.profiles.length = true := by
  decide

/-- **A6.** Every decision contradicts its mapping, and the bundle holds. -/
theorem incoherentDecision_wf : SurfaceMappingWF incoherentDecisionSurface :=
  surfaceMappingWF_of_checkB _ _ incoherentDecision_passes

theorem incoherentDecision_satisfies_the_row :
    ∀ r ∈ incoherentDecisionSurface.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded incoherentDecisionSurface p.id :=
  surface_mapping_grounded _ incoherentDecision_wf

/-- Rewrite every decision to `refused` and the door returns the same verdict at
every fuel: the check does not read the field. -/
def flipDecisions (s : Surface) : Surface :=
  ⟨s.rows.map (fun r =>
    ⟨r.rowKey, r.effectBearing, r.profiles.map (fun p => ⟨p.id, .refused, p.mapping⟩)⟩)⟩

def okChain : Surface :=
  ⟨[⟨.succeed, true,
      [⟨.pA, .accepted, .expansion [.pB]⟩,
       ⟨.pB, .accepted, .primitive .hPut⟩]⟩]⟩

theorem decision_is_inert :
    (flipDecisions okChain).checkB (flipDecisions okChain).profiles.length
      = okChain.checkB okChain.profiles.length
    ∧ okChain.checkB okChain.profiles.length = true := by
  refine ⟨by decide, by decide⟩

/-! ## §A7 — `EC1-F08` and `EC1-F20` cannot be run: the payload arms are empty

`REIFICATION-CHECKLIST.md:588-592` gives the `foreign` arm
`{ foreignOpId, implementationId, requestValueTy, answerValueTy, errorRow,
requirementRow, directHandlerId, worldFrameId, receiptCodecId }` and invariant
16 requires all of them. The model keeps `directHandlerId` and drops the other
eight — `implementationId` included, which is exactly the field `EC1-F08` (an
UNREGISTERED host callback) attacks.

`:586-588` gives `pure { meaning, totalityObligationId,
hostConformanceObligationId }` and invariant 12 requires "a total model and empty
frame". The model's `pure` arm is NULLARY, so `EC1-F20` (a pure atom that reads a
mutable counter) has no field to corrupt.

A ledger whose foreign profile names no implementation and whose pure profile
names no model passes the door. -/

def unregisteredForeignSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .foreign .hPut⟩]⟩,
    ⟨.failCause, true, [⟨.pB, .accepted, .pure⟩]⟩]⟩

/-- **A7.** `EC1-F08` and `EC1-F20` pass through: the fields they mutate are not
in the carrier. -/
theorem F08_F20_have_no_field_to_attack :
    unregisteredForeignSurface.checkB unregisteredForeignSurface.profiles.length = true := by
  decide

theorem unregisteredForeign_wf : SurfaceMappingWF unregisteredForeignSurface :=
  surfaceMappingWF_of_checkB _ _ F08_F20_have_no_field_to_attack

/-! ## §A8 — `handlersNodup` is not invariant 10

Invariant 10 (`REIFICATION-CHECKLIST.md:1210`): "EXACTLY primitive and
registered-foreign profiles own direct Core handler IDs; expansions close through
referenced operations, and no other profile owns a duplicate handler."

The schema distinguishes the two id namespaces by name:
`primitive { opDescId, termFormId, directHandlerId }` (`:582`) and
`subcalculus { subcalculusId, interpretation: lowering LoweringId | handler
HandlerId }` (`:585`). `Mapping.handler?` returns the SUBCALCULUS handler as
well, and `handlersNodup` takes `Nodup` of the merged list.

On the reading invariant 10's word "exactly" forces — a subcalculus handler is
not a direct Core handler id — the door REFUSES a legal ledger, and it refuses
it on that conjunct alone. -/

def subcalcCollisionSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩,
    ⟨.failCause, true, [⟨.pB, .accepted, .subcalculus (.handler .hPut)⟩]⟩]⟩

/-- **A8.** The door refuses it, and the OTHER three conjuncts all hold: the
refusal is entirely the namespace merge. -/
theorem subcalcCollision_refused_on_handlersNodup_alone :
    subcalcCollisionSurface.checkB subcalcCollisionSurface.profiles.length = false
      ∧ (subcalcCollisionSurface.rows.all
          fun r => !r.effectBearing || !r.profiles.isEmpty) = true
      ∧ (subcalcCollisionSurface.profiles.map (·.id)).Nodup
      ∧ (subcalcCollisionSurface.profiles.all
          (fun p => subcalcCollisionSurface.settles
            subcalcCollisionSurface.profiles.length p.id)) = true
      ∧ ¬ (subcalcCollisionSurface.profiles.filterMap (·.mapping.handler?)).Nodup := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem subcalcCollision_refused : ¬ SurfaceMappingWF subcalcCollisionSurface :=
  refused_of_checkB_false subcalcCollision_refused_on_handlersNodup_alone.1

/-! ## §A9 — an INDEPENDENT reference checker, and a differential sweep

`checkB` decides acyclicity by fuel-bounded settling. The reference below decides
it by explicit bounded reachability and separates resolution into its own pass;
it never calls `settles`. If `checkB_iff` were wrong at the fuel the file names,
the two would diverge somewhere in the sweep.

This is the falsifier `EC1-F03` (duplicate ids), `EC1-F60` (a permuted seven-way
mapping) and `EC1-F82` (a permuted duplicate-key row) bear on. The proof SURVIVES
it: that is evidence, not a finding. -/

def stepIds (s : Surface) (l : List PId) : List PId :=
  l.flatMap (fun i => s.out i)

def reachWithin (s : Surface) : Nat → List PId → List PId
  | 0, l => l
  | n + 1, l => l ++ reachWithin s n (stepIds s l)

/-- Resolution, by direct lookup of every reference. -/
def refResolves (s : Surface) : Bool :=
  s.profiles.all (fun p => p.mapping.refs.all (fun q => (s.find? q).isSome))

/-- Acyclicity, by asking whether any id is reachable from itself in one or more
steps within the ledger's own size. No fuel-bounded settling anywhere. -/
def refAcyclic (s : Surface) : Bool :=
  s.profiles.all (fun p =>
    !(reachWithin s s.profiles.length (s.out p.id)).contains p.id)

def refCheck (s : Surface) : Bool :=
  (s.rows.all fun r => !r.effectBearing || !r.profiles.isEmpty)
    && decide ((s.profiles.map (·.id)).Nodup)
    && decide ((s.profiles.filterMap (·.mapping.handler?)).Nodup)
    && refResolves s && refAcyclic s

/-- Every arm of the seven-way union, plus the shapes that separate them. -/
def mappingChoices : List (Mapping PId HId) :=
  [.pure, .primitive .hPut, .subcalculus .lowering,
   .refusal .typeDiagnostic, .target "adapter",
   .expansion [], .expansion [.pA], .expansion [.pB], .expansion [.pC],
   .expansion [.pA, .pB], .expansion [.pD]]

def family : List Surface :=
  mappingChoices.flatMap fun m1 =>
    mappingChoices.flatMap fun m2 =>
      mappingChoices.map fun m3 =>
        (⟨[⟨.succeed, true,
            [⟨.pA, .accepted, m1⟩, ⟨.pB, .accepted, m2⟩,
             ⟨.pC, .accepted, m3⟩]⟩]⟩ : Surface)

/-! The sweep is 11 mapping arms in each of three profile positions. `maxRecDepth`
is an ELABORATOR limit, not a trust setting: the kernel still checks every term
these three `decide`s produce, and the receipts below show it. -/
set_option maxRecDepth 40000 in
theorem family_size : family.length = 1331 := by decide

/-! **A9.** 1331 ledgers — every arm of the seven-way union in every position,
empty expansions, dangling references, self-loops and two-cycles included: the
delivered door and an independently written reference agree on every one.
`checkB_iff` survives the falsifier. -/
set_option maxRecDepth 40000 in
theorem differential_agrees :
    family.all (fun s => s.checkB s.profiles.length == refCheck s) = true := by decide

/-! The agreement is not the agreement of two constant functions: the sweep
splits 511 admitted / 820 refused. -/
set_option maxRecDepth 40000 in
theorem sweep_is_not_constant :
    (family.filter (fun s => s.checkB s.profiles.length)).length = 511
      ∧ (family.filter (fun s => !s.checkB s.profiles.length)).length = 820 := by
  refine ⟨by decide, by decide⟩

/-- `EC1-F03` at the profile-id carrier: every duplicate-id ledger over the same
arm set is refused, at the ledger's own fuel. -/
def dupFamily : List Surface :=
  mappingChoices.flatMap fun m1 =>
    mappingChoices.map fun m2 =>
      (⟨[⟨.succeed, true,
          [⟨.pA, .accepted, m1⟩, ⟨.pA, .accepted, m2⟩]⟩]⟩ : Surface)

set_option maxRecDepth 40000 in
theorem F03_every_duplicate_is_refused :
    dupFamily.all (fun s => !s.checkB s.profiles.length) = true := by decide

/-! ## §A10 — the fuel bound is tight; the performance caveat is NOT measurable here

The fuel `|profiles|` is not slack. A twelve-deep chain is admitted at the
ledger's own size and REFUSED at ten, so a harness that supplies any constant
fuel produces false refusals. This confirms the file's insistence that the fuel
be computed from the artifact.

§6.6's exponential caveat, by contrast, could not be reproduced. A doubling
ledger (`expansion [i+1, i+1]`) checks in CONSTANT wall time at
n = 8, 10, 12, 14, 18, 20, 22, 24 (0.5-0.7 s each, baseline included), because
the elaborator's `whnf` cache memoises the two structurally identical subterms
that make the walk exponential. The caveat is therefore about a HARNESS
implementation and cannot be exercised by `decide` at all. The estate's own
measurement stands as its evidence (`Cas/Schema/Guarded.lean:425-431`: 302 915 ms
on an acyclic 25-entry table), and `Document.settleAll` / `Document.guardedMemo`
(`:449`, `:468`) are the shipped memoised variants that `T009.lean` does not
transplant. -/

abbrev NSurface := PublicSurface RKey Nat HId

def chain (n : Nat) : NSurface :=
  ⟨[⟨.succeed, true,
      (List.range n).map (fun i =>
        ⟨i, .accepted, if i + 1 < n then .expansion [i + 1] else .primitive .hPut⟩)⟩]⟩

set_option maxRecDepth 200000 in
theorem chain12_admitted_at_the_ledger_size :
    (chain 12).checkB (chain 12).profiles.length = true := by decide

set_option maxRecDepth 200000 in
theorem chain12_falsely_refused_when_underfuelled :
    (chain 12).checkB 10 = false := by decide

end AttackT009

/-! ## Kernel receipts

31 receipts. No `sorry`, no `axiom`, no `native_decide`, and no `#eval` carrying
a claim: every count in this file is proved by `decide`. The only `set_option`
is `maxRecDepth`, an elaborator recursion limit that changes no trusted
component. -/

section AttackReceipts
open AttackT009

#print axioms AttackT009.dead_premise_is_eta
#print axioms AttackT009.dead_premise_adds_nothing
#print axioms AttackT009.as_written_dead_premise_adds_nothing
#print axioms AttackT009.allRefused_checkB
#print axioms AttackT009.allRefused_wf
#print axioms AttackT009.allRefused_satisfies_the_row
#print axioms AttackT009.allRefused_has_no_core_content
#print axioms AttackT009.emptySurface_passes
#print axioms AttackT009.emptySurface_wf
#print axioms AttackT009.dupRowKeySurface_really_duplicates
#print axioms AttackT009.dupRowKey_passes
#print axioms AttackT009.dupRowKey_wf
#print axioms AttackT009.dupRowKey_satisfies_the_row
#print axioms AttackT009.F59_passes_through
#print axioms AttackT009.censusOmitted_wf
#print axioms AttackT009.emptyNonEffectRow_passes
#print axioms AttackT009.emptyNonEffectRow_wf
#print axioms AttackT009.incoherentDecision_passes
#print axioms AttackT009.incoherentDecision_wf
#print axioms AttackT009.incoherentDecision_satisfies_the_row
#print axioms AttackT009.decision_is_inert
#print axioms AttackT009.F08_F20_have_no_field_to_attack
#print axioms AttackT009.unregisteredForeign_wf
#print axioms AttackT009.subcalcCollision_refused_on_handlersNodup_alone
#print axioms AttackT009.subcalcCollision_refused
#print axioms AttackT009.family_size
#print axioms AttackT009.differential_agrees
#print axioms AttackT009.sweep_is_not_constant
#print axioms AttackT009.F03_every_duplicate_is_refused
#print axioms AttackT009.chain12_admitted_at_the_ledger_size
#print axioms AttackT009.chain12_falsely_refused_when_underfuelled

end AttackReceipts
