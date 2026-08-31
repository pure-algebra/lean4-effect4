import Cas.Lang.RefusalMap
import Cas.Schema.Guarded

/-!
# `EC1-T009` — `surface_mapping_closed`, restated as GROUNDING and DECIDED

Slice `EC1-S1`. Skill stage: `lean-model-invariants` — the row is about the
representation of a generated ledger and the validation boundary that admits
it, so that stage's `wire/raw -> parse -> validate -> checked core` discipline
applies, together with its standing obligations *smart-constructor/validator
soundness* and *checker soundness and optional completeness*. Both are
discharged below (§5, §6), completeness at the ledger's own size; what the door
still does NOT decide is named in §6.6.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T009.lean
```

This file is OUTSIDE every lake target. It modifies nothing under `library/`
and nothing under `formal/effect-core-v1/`. Its intended home,
`formal/effect-core-v1/EffectCore/Surface/Closure.lean`, is a 309-byte reserved
stub and is deliberately not written to; a later integration step moves proofs
into modules.

## The DAG row

```text
EC1-T009 | surface_mapping_closed : PublicSurfaceWF s ->
           every effect-bearing row has a constructive mapping /
           direct-handler-or-boundary witness            | T008; generated mapping rows
```
(`PROOF-DAG.md:201`.)

## What is proved here

| § | Statement | Result |
|---|---|---|
| 2 | the DAG row verbatim, at an ARBITRARY id/handler/key universe | TRUE, and VACUOUS — it needs no ledger at all |
| 3 | `surface_mapping_grounded`, the scouted restatement, under the scouted premise bundle | TRUE |
| 3 | the `PublicSurfaceWF` premise is dead: the row holds for EVERY predicate whatsoever | TRUE |
| 4 | ledger lookup is adequate for the existential in `Grounded`, given `idsNodup` | TRUE |
| 5 | **checker SOUNDNESS**: one decidable `Bool` implies the whole scouted premise bundle | TRUE |
| 5 | the decided form of the row — a door a harness can actually run | TRUE |
| 6 | **checker COMPLETENESS**, at `fuel = |profiles|` — the fuel a harness computes from the artifact | TRUE, needs `idsNodup` |
| 6 | `checkB_iff` — the check DECIDES the premise bundle, and `Decidable (SurfaceMappingWF s)` | TRUE |
| 7 | `idsNodup` is NOT necessary for the scouted row but IS necessary once the acyclicity premise is DISCHARGED | TRUE, with witness |
| 8 | the four mutants the row admits — each REFUTED by the door — and the positive control | TRUE |

### What this file adds to the scout

The scout (`scout-T009.lean`) established that the DAG row is a tautology and
that the honest statement is grounding — a terminating unfolding through
`referencedProfileIds` into a direct handler, a subcalculus interpretation, or a
declared non-Core boundary. Its restatement takes

```text
expansionWF : WellFounded (ExpandsTo s)
```

as a PREMISE. That premise is an oracle: `EC1-H11` is a harness over a generated
JSON ledger, and a harness cannot exhibit a `WellFounded`. So the scouted
theorem, as it stands, converts one unverifiable assumption into another.

§5 and §6 remove the oracle. `PublicSurface.checkB` is a single `Bool`,
structurally recursive on fuel, and `checkB_iff` proves that at
`fuel = |profiles|` it is EQUIVALENT to the scouted premise bundle,
`expansionWF` included — so `SurfaceMappingWF` is decidable. The harness computes
a `Bool`; the kernel converts it into the theorem, and a failing check is a real
defect rather than a possible under-fuelling. That is the
`Cas/Schema/Guarded.lean` discipline transplanted to the profile carrier — the
one thing the scout explicitly listed as a check it had omitted ("I did not
transfer `Guarded.lean`'s decision procedure to the profile carrier").

§7 is a correction to the scout, not an extension of it. The scout reports
`idsNodup` as required by invariants 6/8 but "NOT a premise of this conclusion".
That is right for the scouted route and WRONG the moment the acyclicity premise
is discharged by a checker: `Grounded` and `ExpandsTo` quantify EXISTENTIALLY
over the ledger, while any checker resolves an id by LOOKUP. `dupIdSurface`
separates the two — it is grounded and its check is false at every fuel — so
completeness, and the `expansionWF` discharge, both fail without `idsNodup`.

### Reuse, never mint

`Refusal.reason`'s CAS arm is `Cas.Lang.Refusal.Clause`, the estate's shipped
clause carrier (`Cas/Lang/RefusalMap.lean:106`), per invariant 24 and §17 ruling
R11. No second CAS refusal enum is spelled. Nothing else here touches `Sig`,
`Prog`, `Handler`, `PProg`, `Refusal`, `Status`, `wp`, `wlp`, `Envelope` or
`Word`: this is `EFFECTS-BACKEND` R14a's pure discipline — effect-free work on
first-order data, stated OUTSIDE `Prog` as plain definitions.

The row-key, profile-id and handler-id universes are TYPE PARAMETERS, not
scratch enums. `PROOF-DAG.md` §17 freeze condition 3 (the closed alphabet and
direct-handler table) is OPEN, and condition 14 (protocol operation identity) is
OPEN; parameterising is how this file stays silent about both. It also makes §2
a sharper finding than a finite model could: the row is vacuous over an
ARBITRARY id universe, so its emptiness is not an artifact of a four-element
scratch enum.

### Honesty

A green elaboration here proves the stated propositions about the carriers
DEFINED IN THIS FILE and nothing else. No generated ledger exists —
`formal/effect-core-v1/EffectCore/Generated/` is not a directory and `EC1-H11`
is PENDING HARNESS — so every schema fact is transcribed from
`REIFICATION-CHECKLIST.md`, not read off an artifact. This file does not close
`EC1-T009`.
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

/-! ### §6.6 — what the door does NOT decide

`checkB_iff` decides `SurfaceMappingWF`. It does not decide that the ledger is
CORRECT, and three gaps are worth naming rather than leaving to be discovered:

* the `Cas/Schema/Guarded.lean` caveat transfers verbatim — CONSTRUCTIBILITY,
  not PRODUCTIVITY. A ledger that passes has an unfolding that terminates in a
  declared leaf; nothing here says the unfolded result MEANS anything, and no
  handler id is linked to a `Cas.Lang.Handler` value (§17 freeze condition 3 is
  OPEN);
* `settles` re-walks every path, so it is exponential on a ledger whose profiles
  each reference the next one twice. `Cas/Schema/Guarded.lean:430` records a
  measured 302 915 ms at 25 entries and ships a memoised variant beside it. That
  variant is NOT transplanted here, and a generated surface census is far larger
  than 25 rows;
* the mapping is modelled in two of the six dimensions `EC1-K07` demands of an
  effect-bearing row. The `A/E/R` transform, semantic family, observation,
  obligation set, and every `TypeClosureRow` edge are absent, so a green
  `checkB` is silent about all five. -/

/-! ## §7 — `idsNodup` is load-bearing for the DECIDED route

The scout reports `idsNodup` as required by invariants 6/8 but "NOT a premise of
this conclusion — grounding is existential in the lookup". That is correct for
§3: `grounded_of_wf` never uses it.

It is WRONG the moment the `expansionWF` oracle is discharged. `Grounded` and
`ExpandsTo` quantify EXISTENTIALLY over the ledger; `settles`, `checkB`, and
every possible checker resolve an id by LOOKUP. With duplicate ids those are
different claims, and this section separates them. -/

namespace Witness

/-- Scratch profile ids. -/
inductive PId where
  | pA | pB | pC | pMissing
  deriving DecidableEq, Repr

/-- Scratch direct-handler ids. Opaque: §17 freeze condition 3 (the closed
alphabet and direct-handler table) is OPEN, so nothing below links these to a
`Cas.Lang.Handler` value, and nothing below needs to. -/
inductive HId where
  | hPut | hAsk
  deriving DecidableEq, Repr

/-- Scratch surface row keys. -/
inductive RKey where
  | succeed | failCause | multipartHeaders
  deriving DecidableEq, Repr

abbrev Surface := PublicSurface RKey PId HId

/-- ONE id, TWO profiles: a cyclic expansion listed first, a `pure` boundary
listed second. The ledger is grounded at `pA` — the second profile is a leaf —
and no lookup-based checker can see it, because the lookup returns the first. -/
def dupIdSurface : Surface :=
  ⟨[⟨.succeed, true,
      [⟨.pA, .accepted, .expansion [.pA]⟩,
       ⟨.pA, .accepted, .pure⟩]⟩]⟩

theorem dupIdSurface_profiles :
    dupIdSurface.profiles
      = [⟨.pA, .accepted, .expansion [.pA]⟩, ⟨.pA, .accepted, .pure⟩] := rfl

theorem dupIdSurface_ids_not_nodup :
    ¬ (dupIdSurface.profiles.map (·.id)).Nodup := by decide

/-- It really is grounded: the SECOND profile is a declared non-Core boundary. -/
theorem dupIdSurface_grounded : Grounded dupIdSurface PId.pA :=
  Grounded.leaf ⟨.pA, .accepted, .pure⟩
    (by rw [dupIdSurface_profiles]; exact List.Mem.tail _ (List.Mem.head _)) rfl rfl

theorem dupIdSurface_find? :
    dupIdSurface.find? PId.pA = some ⟨.pA, .accepted, .expansion [.pA]⟩ := by
  decide

theorem dupIdSurface_out : dupIdSurface.out PId.pA = [PId.pA] := by decide

/-- **The separation.** No fuel settles it: the lookup loops. Infinite descent,
in the shape of `Cas/Schema/Guarded.lean:266 not_settles_of_cycle`. -/
theorem dupIdSurface_never_settles :
    ∀ n, dupIdSurface.settles n PId.pA = false := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    show ((dupIdSurface.find? PId.pA).isSome
      && (dupIdSurface.out PId.pA).all (fun q => dupIdSurface.settles k q)) = false
    rw [dupIdSurface_out]
    simp [ih]

/-- **Finding: `idsNodup` is necessary for COMPLETENESS.** Drop it and a
grounded ledger is refused at every fuel. `EC1-CE030`'s duplicate-free repair is
therefore not merely an invariant the packet happens to require here — it is a
premise of the checker's adequacy. -/
theorem completeness_needs_idsNodup :
    Grounded dupIdSurface PId.pA
      ∧ ¬ ∃ n, dupIdSurface.settles n PId.pA = true := by
  refine ⟨dupIdSurface_grounded, ?_⟩
  rintro ⟨n, hn⟩
  rw [dupIdSurface_never_settles n] at hn
  exact Bool.noConfusion hn

/-- And `checkB` refuses it — correctly, since `idsNodup` is one of its
conjuncts. The mutant is refused for the RIGHT reason, which is the point: the
door does not silently mis-handle a duplicate, it rejects it. -/
theorem dupIdSurface_checkB_false : ∀ n, dupIdSurface.checkB n = false := by
  intro n
  show (_ && decide ((dupIdSurface.profiles.map (·.id)).Nodup) && _ && _) = false
  rw [decide_eq_false dupIdSurface_ids_not_nodup]
  simp

theorem dupIdSurface_refused : ¬ SurfaceMappingWF dupIdSurface :=
  refused_of_checkB_false (dupIdSurface_checkB_false _)

end Witness

/-! ## §8 — the four mutants the schematic row admits, and the positive control

Each is DECIDED here rather than argued: `checkB` is a `Bool`, so a mutant's
refusal is a computation. -/

namespace Witness

/-! ### §8.1 — an effect-bearing row with NO admission profile

`EC1-K07`: "handlerless effect-bearing rows are not [permitted]".
`REIFICATION-CHECKLIST.md:571` makes `admissionProfiles` NonEmpty and invariant
25 requires the "missing profile mappings" counter to be zero. The schematic row
does not notice, because `∀ p ∈ []` is true. -/

def emptyProfileSurface : Surface := ⟨[⟨.multipartHeaders, true, []⟩]⟩

theorem T009_holds_on_the_empty_profile_mutant :
    ∀ r ∈ emptyProfileSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

theorem emptyProfileSurface_checkB_false :
    emptyProfileSurface.checkB emptyProfileSurface.profiles.length = false := by decide

theorem emptyProfileSurface_refused : ¬ SurfaceMappingWF emptyProfileSurface :=
  refused_of_checkB_false emptyProfileSurface_checkB_false

/-! ### §8.2 — a dangling expansion reference

Invariant 14: "Every `derivedGraph` expansion is closed over mapped profiles."
The schematic row does not say it. -/

def danglingSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .expansion [.pMissing]⟩]⟩]⟩

theorem T009_holds_on_the_dangling_mutant :
    ∀ r ∈ danglingSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

theorem danglingSurface_checkB_false :
    danglingSurface.checkB danglingSurface.profiles.length = false := by decide

theorem danglingSurface_refused : ¬ SurfaceMappingWF danglingSurface :=
  refused_of_checkB_false danglingSurface_checkB_false

/-! ### §8.3 — the main finding: a mapping graph that never reaches a handler

Two accepted, effect-bearing profiles. Each has a mapping. Each mapping is
`constructive` in the row's own sense. Every referenced profile id RESOLVES, so
invariant 14's "closed over mapped profiles" holds on its literal reading. And
no profile ever reaches a handler, a lowering, or a boundary, because the two
expand into each other.

`REIFICATION-CHECKLIST.md:497` demands "expansion law and termination/acyclicity
evidence" of the `derivedExpansion` DISPOSITION. That requirement is in neither
`EC1-T009`'s stated dependencies, nor `EC1-K07`, nor invariant 14. -/

def cycSurface : Surface :=
  ⟨[⟨.succeed, true,
      [⟨.pA, .accepted, .expansion [.pB]⟩,
       ⟨.pB, .accepted, .expansion [.pA]⟩]⟩]⟩

theorem cycSurface_refs_resolve :
    ∀ p ∈ cycSurface.profiles, ∀ q ∈ p.mapping.refs,
      ∃ p' ∈ cycSurface.profiles, p'.id = q := by decide

theorem cycSurface_ids_nodup : (cycSurface.profiles.map (·.id)).Nodup := by decide

theorem T009_holds_on_the_cyclic_mutant :
    ∀ r ∈ cycSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

/-- Nothing in it is grounded. The row is true; `EC1-K07`'s "handlerless
effect-bearing rows are not permitted" is violated; nothing connects the two. -/
theorem cyc_nothing_is_grounded : ∀ i, Grounded cycSurface i → False := by
  intro i h
  induction h with
  | leaf p hp _ hleaf =>
      have hp' : p ∈ [(⟨.pA, .accepted, .expansion [.pB]⟩ : Profile PId HId),
                      ⟨.pB, .accepted, .expansion [.pA]⟩] := hp
      rcases List.mem_cons.mp hp' with rfl | h1
      · exact Bool.noConfusion hleaf
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact Bool.noConfusion hleaf
        · cases h2
  | expand p hp _ _ _ ih =>
      have hp' : p ∈ [(⟨.pA, .accepted, .expansion [.pB]⟩ : Profile PId HId),
                      ⟨.pB, .accepted, .expansion [.pA]⟩] := hp
      rcases List.mem_cons.mp hp' with rfl | h1
      · exact ih .pB (List.Mem.head _)
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact ih .pA (List.Mem.head _)
        · cases h2

/-- **Resolvability does not supply acyclicity**, derived rather than asserted:
if the expansion relation were well-founded, §3 would ground `pA`. -/
theorem cyc_expansion_not_wf : ¬ WellFounded (ExpandsTo cycSurface) := by
  intro hwf
  refine cyc_nothing_is_grounded PId.pA
    (grounded_of_wf cycSurface
      ⟨by decide, cycSurface_ids_nodup, cycSurface_refs_resolve, hwf, by decide⟩
      .pA ⟨⟨.pA, .accepted, .expansion [.pB]⟩, List.Mem.head _, rfl⟩)

/-- And the door refuses it, at the fuel a harness computes from the ledger. -/
theorem cycSurface_checkB_false :
    cycSurface.checkB cycSurface.profiles.length = false := by decide

theorem cycSurface_refused : ¬ SurfaceMappingWF cycSurface :=
  refused_of_checkB_false cycSurface_checkB_false

/-! ### §8.4 — a duplicate direct handler

Invariant 10, which the schematic row drops entirely. The mutant is GROUNDED —
grounding is a reachability property and says nothing about uniqueness — so only
the `handlersNodup` conjunct refuses it. That is why it stays a separate
clause. -/

def duplicateHandlerSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩,
    ⟨.failCause, true, [⟨.pB, .accepted, .primitive .hPut⟩]⟩]⟩

theorem duplicateHandlerSurface_really_duplicates :
    duplicateHandlerSurface.profiles.filterMap (·.mapping.handler?)
      = [HId.hPut, HId.hPut] := by decide

theorem T009_holds_on_the_duplicate_handler_mutant :
    ∀ r ∈ duplicateHandlerSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

/-- Grounded, and still forbidden. -/
theorem duplicateHandlerSurface_grounded : Grounded duplicateHandlerSurface PId.pA :=
  Grounded.leaf ⟨.pA, .accepted, .primitive .hPut⟩ (List.Mem.head _) rfl rfl

theorem duplicateHandlerSurface_checkB_false :
    duplicateHandlerSurface.checkB duplicateHandlerSurface.profiles.length = false := by
  decide

theorem duplicateHandlerSurface_refused : ¬ SurfaceMappingWF duplicateHandlerSurface :=
  refused_of_checkB_false duplicateHandlerSurface_checkB_false

/-! ### §8.5 — the positive control, and the door opening

Nothing above is an artifact of an unsatisfiable well-formedness structure. A
ledger with a real expansion chain PASSES the decidable check, and §5 converts
that `Bool` into the full theorem — with no `WellFounded` supplied by hand. -/

def goodSurface : Surface :=
  ⟨[⟨.succeed, true,
      [⟨.pA, .accepted, .expansion [.pB]⟩,
       ⟨.pB, .accepted, .expansion [.pC]⟩,
       ⟨.pC, .accepted, .primitive .hPut⟩]⟩,
    ⟨.multipartHeaders, false,
      [⟨.pMissing, .refused, .refusal (.casClause .dangling)⟩]⟩]⟩

/-- The check PASSES, by computation, at the ledger's own size. -/
theorem goodSurface_checkB :
    goodSurface.checkB goodSurface.profiles.length = true := by decide

/-- **The door, opened.** The full conclusion of `EC1-T009` for this ledger,
obtained from a `Bool` — no `WellFounded` constructed by hand, no premise
assumed. This is the shape `EC1-H11` would run against a generated ledger. -/
theorem goodSurface_conclusion :
    ∀ r ∈ goodSurface.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded goodSurface p.id :=
  surface_mapping_grounded_decided goodSurface _ goodSurface_checkB

/-- And the scouted premise bundle itself, discharged by the same `Bool`. -/
theorem goodSurface_wf : SurfaceMappingWF goodSurface :=
  surfaceMappingWF_of_checkB goodSurface _ goodSurface_checkB

/-! ### §8.6 — a design question the packet has not asked

`Grounded` admits `expansion []`: an expansion that references nothing
terminates immediately, so it bottoms out. But it names no term-level artifact
either, and `EC1-K07` demands a "constructive mapping". Whether an empty
`referencedProfileIds` is a legal `derivedExpansion` or a generator defect is not
settled by `REIFICATION-CHECKLIST.md:497`, by invariant 14, or by anything this
file can decide. It is recorded, not answered: if the packet wants it excluded,
the clause belongs in `SurfaceMappingWF`, not in `Grounded`. -/

def emptyExpansionSurface : Surface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .expansion []⟩]⟩]⟩

theorem emptyExpansionSurface_passes :
    emptyExpansionSurface.checkB emptyExpansionSurface.profiles.length = true := by
  decide

theorem emptyExpansionSurface_grounded : Grounded emptyExpansionSurface PId.pA :=
  (surface_mapping_grounded_decided emptyExpansionSurface _
    emptyExpansionSurface_passes _ (List.Mem.head _) rfl).2 _ (List.Mem.head _)

end Witness

/-! ## §9 — the honesty half

`Cas/Lang/RefusalMap.lean` proves three things about its one-step join and
`EC1-T009` needs all three at its carrier: the disjunction is exhaustive
(`:252`), the two halves do not overlap (`:265`), and the boundary declaration
is honest rather than merely asserted (`:293`). -/

section Honesty

variable {Id H : Type}

/-- The `clause?_none_iff_hostOnly` (`Cas/Lang/RefusalMap.lean:265`) analogue:
exactly which arms own no handler. -/
theorem handler?_none_iff_handlerless (m : Mapping Id H) :
    m.handler? = none ↔ m.handlerless = true := by
  match m with
  | .primitive _ => simp [Mapping.handler?, Mapping.handlerless]
  | .expansion _ => simp [Mapping.handler?, Mapping.handlerless]
  | .subcalculus .lowering => simp [Mapping.handler?, Mapping.handlerless]
  | .subcalculus (.handler _) => simp [Mapping.handler?, Mapping.handlerless]
  | .pure => simp [Mapping.handler?, Mapping.handlerless]
  | .foreign _ => simp [Mapping.handler?, Mapping.handlerless]
  | .target _ => simp [Mapping.handler?, Mapping.handlerless]
  | .refusal _ => simp [Mapping.handler?, Mapping.handlerless]

/-- **`EC1-K07`'s word "handlerless" is the wrong notion.** "Handlerless" and
"boundary" are not complements: an `expansion` and a lowering-interpreted
`subcalculus` are handlerless and are not boundaries. Read literally, "handlerless
effect-bearing rows are not [permitted]" therefore condemns every
`derivedExpansion` and every `separateSubcalculus` closed by a total lowering —
which invariants 14 and 15 explicitly permit. `Grounded`, not handler-ownership,
is the notion the clause wants. -/
theorem handlerless_is_not_boundary (rs : List Id) :
    (Mapping.expansion rs : Mapping Id H).handlerless = true
      ∧ (Mapping.expansion rs : Mapping Id H).isBoundary = false
      ∧ (Mapping.subcalculus (H := H) (Id := Id) .lowering).handlerless = true
      ∧ (Mapping.subcalculus (H := H) (Id := Id) .lowering).isBoundary = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The `hostOnly_unmapped` (`Cas/Lang/RefusalMap.lean:293`) obligation: a
declared boundary owns no handler. FREE by typing here, because the schema's
`directHandlerId` lives INSIDE the `primitive`/`foreign` arms — and recording
that it is free is the honest report: it stays free only for as long as the
generated carrier keeps handler ownership inside the mapping union. -/
theorem boundary_owns_no_handler (m : Mapping Id H) (h : m.isBoundary = true) :
    m.handler? = none := by
  cases m <;> first | rfl | exact Bool.noConfusion h

end Honesty

end EffectCoreT009

/-! ## Kernel receipts

77 receipts follow. No `sorryAx`. No `sorry`, `axiom`, `native_decide`, or
`#eval` carrying a claim.

**`Classical.choice` is declared, and it is UPSTREAM.** Ten receipts carry
`[propext, Classical.choice, Quot.sound]`; every one of them passes through
`nodup_length_le`, whose proof uses core Lean's `List.erase` lemmas. Isolated
below: `List.length_erase_of_mem` and `List.mem_erase_of_ne` each report the same
triple on their own. It is also the ESTATE's ceiling for exactly this argument —
`Cas.Schema.nodup_length_le` and `Cas.Schema.references_guarded_decidable`,
the shipped pigeonhole and the shipped door this section transplants, report the
identical triple, printed below beside mine. Nothing here chooses classically;
the pigeonhole is inherited, not re-derived.

The remaining 67 receipts are `[propext, Quot.sound]`, `[propext]`, or
axiom-free. In particular the row's own content —
`surface_mapping_grounded`, `grounded_of_wf`, `grounded_of_settles`,
`expansionWF_of_settles`, `settles_of_grounded`, `surfaceMappingWF_of_checkB`
and `surface_mapping_grounded_decided` — reaches no further than
`[propext, Quot.sound]`. Only the FUEL BOUND of §6.5 costs `Classical.choice`,
and only through the estate's own lemma. -/

section Receipts
open EffectCoreT009 EffectCoreT009.PublicSurface EffectCoreT009.Witness

#print axioms EffectCoreT009.Mapping.refs_eq_nil_of_isLeaf
#print axioms EffectCoreT009.Mapping.isLeaf_eq_false_iff
#print axioms EffectCoreT009.PublicSurface.mem_profiles
#print axioms EffectCoreT009.T009_as_written
#print axioms EffectCoreT009.T009_as_written_ignores_every_premise
#print axioms EffectCoreT009.grounded_of_wf
#print axioms EffectCoreT009.surface_mapping_grounded
#print axioms EffectCoreT009.surface_mapping_grounded_with_dead_premise
#print axioms EffectCoreT009.restatement_implies_the_schematic_row
#print axioms EffectCoreT009.eq_of_nodup_ids
#print axioms EffectCoreT009.PublicSurface.find?_mem
#print axioms EffectCoreT009.PublicSurface.out_eq_of_find?
#print axioms EffectCoreT009.PublicSurface.find?_eq_some_of_mem
#print axioms EffectCoreT009.PublicSurface.find?_isSome_of_settles
#print axioms EffectCoreT009.PublicSurface.grounded_of_settles
#print axioms EffectCoreT009.PublicSurface.refsResolve_of_settles
#print axioms EffectCoreT009.PublicSurface.expansionWF_of_settles
#print axioms EffectCoreT009.PublicSurface.profilesNonempty_of_checkB
#print axioms EffectCoreT009.PublicSurface.idsNodup_of_checkB
#print axioms EffectCoreT009.PublicSurface.handlersNodup_of_checkB
#print axioms EffectCoreT009.PublicSurface.settles_of_checkB
#print axioms EffectCoreT009.surfaceMappingWF_of_checkB
#print axioms EffectCoreT009.surface_mapping_grounded_decided
#print axioms EffectCoreT009.nodup_length_le
#print axioms EffectCoreT009.PublicSurface.settles_succ
#print axioms EffectCoreT009.PublicSurface.settles_le
#print axioms EffectCoreT009.PublicSurface.exists_fuel_all
#print axioms EffectCoreT009.PublicSurface.settles_of_grounded
#print axioms EffectCoreT009.PublicSurface.grounded_iff_exists_settles
#print axioms EffectCoreT009.PublicSurface.settles_step
#print axioms EffectCoreT009.PublicSurface.reachPlus_descends
#print axioms EffectCoreT009.PublicSurface.not_settles_of_cycle
#print axioms EffectCoreT009.PublicSurface.walk_reachPlus
#print axioms EffectCoreT009.PublicSurface.walk_dup_cycle
#print axioms EffectCoreT009.PublicSurface.find?_isSome_of_grounded
#print axioms EffectCoreT009.PublicSurface.mem_ids_of_grounded
#print axioms EffectCoreT009.PublicSurface.grounded_edge
#print axioms EffectCoreT009.PublicSurface.grounded_not_cycle
#print axioms EffectCoreT009.PublicSurface.grounded_walk_of_not_settles
#print axioms EffectCoreT009.PublicSurface.settles_of_grounded_at_size
#print axioms EffectCoreT009.checkB_iff
#print axioms EffectCoreT009.refused_of_checkB_false
#print axioms EffectCoreT009.Witness.dupIdSurface_profiles
#print axioms EffectCoreT009.Witness.dupIdSurface_ids_not_nodup
#print axioms EffectCoreT009.Witness.dupIdSurface_grounded
#print axioms EffectCoreT009.Witness.dupIdSurface_find?
#print axioms EffectCoreT009.Witness.dupIdSurface_out
#print axioms EffectCoreT009.Witness.dupIdSurface_never_settles
#print axioms EffectCoreT009.Witness.completeness_needs_idsNodup
#print axioms EffectCoreT009.Witness.dupIdSurface_checkB_false
#print axioms EffectCoreT009.Witness.dupIdSurface_refused
#print axioms EffectCoreT009.Witness.T009_holds_on_the_empty_profile_mutant
#print axioms EffectCoreT009.Witness.emptyProfileSurface_checkB_false
#print axioms EffectCoreT009.Witness.emptyProfileSurface_refused
#print axioms EffectCoreT009.Witness.T009_holds_on_the_dangling_mutant
#print axioms EffectCoreT009.Witness.danglingSurface_checkB_false
#print axioms EffectCoreT009.Witness.danglingSurface_refused
#print axioms EffectCoreT009.Witness.cycSurface_refs_resolve
#print axioms EffectCoreT009.Witness.cycSurface_ids_nodup
#print axioms EffectCoreT009.Witness.T009_holds_on_the_cyclic_mutant
#print axioms EffectCoreT009.Witness.cyc_nothing_is_grounded
#print axioms EffectCoreT009.Witness.cyc_expansion_not_wf
#print axioms EffectCoreT009.Witness.cycSurface_checkB_false
#print axioms EffectCoreT009.Witness.cycSurface_refused
#print axioms EffectCoreT009.Witness.duplicateHandlerSurface_really_duplicates
#print axioms EffectCoreT009.Witness.T009_holds_on_the_duplicate_handler_mutant
#print axioms EffectCoreT009.Witness.duplicateHandlerSurface_grounded
#print axioms EffectCoreT009.Witness.duplicateHandlerSurface_checkB_false
#print axioms EffectCoreT009.Witness.duplicateHandlerSurface_refused
#print axioms EffectCoreT009.Witness.goodSurface_checkB
#print axioms EffectCoreT009.Witness.goodSurface_conclusion
#print axioms EffectCoreT009.Witness.goodSurface_wf
#print axioms EffectCoreT009.Witness.emptyExpansionSurface_passes
#print axioms EffectCoreT009.Witness.emptyExpansionSurface_grounded
#print axioms EffectCoreT009.handler?_none_iff_handlerless
#print axioms EffectCoreT009.handlerless_is_not_boundary
#print axioms EffectCoreT009.boundary_owns_no_handler

/-! ### Isolation of the `Classical.choice` entry

Upstream in core Lean, and the estate's own ceiling for the same argument. -/

#print axioms List.length_erase_of_mem
#print axioms List.mem_erase_of_ne
#print axioms Cas.Schema.nodup_length_le
#print axioms Cas.Schema.references_guarded_decidable

end Receipts
