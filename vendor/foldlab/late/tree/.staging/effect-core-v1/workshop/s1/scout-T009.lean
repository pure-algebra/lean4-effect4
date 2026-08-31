/-!
# Effect Core v1 — scout probe for `EC1-T009` (`surface_mapping_closed`)

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T009.lean
```

Stage: `lean-formalization-strategy`, **Pass A** (contract). Pass B is
unavailable for the same reason `scout-T008.lean` records: the target module
`formal/effect-core-v1/EffectCore/Surface/Closure.lean` is a 309-byte empty
stub, and `PublicSurface`, `SurfaceRowKey`, `SurfaceDisposition`,
`AdmissionProfile`, and every mapping carrier have **zero** definitions anywhere
in the estate's Lean. There is no signature to freeze.

Scouting only. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/`. This file is outside every lake target, exactly like
`../exhibits.lean`, `../counterexamples/Nondeterminism.lean`, `scout-T008.lean`
and `../../breaker-exhibits.lean`. It adds nothing to `Cas`, moves no byte,
promotes no name, and mints no second signature, refusal family, straight-line
program carrier, or CAS spelling: the scratch ledger below exists only to decide
the SHAPE of the row's statement.

The DAG's schematic signature (`PROOF-DAG.md:201`) is

    surface_mapping_closed :
      PublicSurfaceWF s ->
        every effect-bearing row has a
        constructive mapping / direct-handler-or-boundary witness

and its contract clause (`CONTRACT-PACKET.md`, `EC1-K07`) is

> Every effect-bearing row names an overload-derived `A/E/R` transform,
> semantic family, constructive mapping, direct handler or explicit non-Core
> boundary, observation, and obligation set. [...] unresolved, unclassified,
> multiply classified, or handlerless effect-bearing rows are not [permitted].

Seven findings, each with a kernel behind it:

* §1 the row is a **tautology on the mapping union** — `constructive OR
  boundary` is discharged by `cases m` alone, with `PublicSurfaceWF s`, the
  surface, the row, and `effect-bearing` all dead. This is the third instance in
  one slice of the pattern `PROOF-DAG.md:207` already used to delete two rows,
  joining `T003`/`T008`/`T035`/`T115`;
* §2 the row is TRUE of an **effect-bearing row with no admission profiles at
  all** — the `∀ p ∈ profiles` is vacuous. That is the exact mutation
  `EC1-H11`'s "mapping zero counters" and `REIFICATION-CHECKLIST.md` invariant
  25 ("missing profile mappings, missing required handlers") exist to catch;
* §3 the row is TRUE of a ledger whose expansion **references a profile that
  does not exist** (invariant 14's "closed over mapped profiles" violated);
* §4 **the main finding.** The row is TRUE of a ledger in which every profile
  has a mapping, every reference RESOLVES, and yet **no profile ever reaches a
  handler**, because the expansion graph is a two-cycle. Nothing in the row, in
  `EC1-K07`, or in invariant 14 excludes it. The word *constructive* has no
  force without a well-foundedness premise, and that premise is absent from the
  row's stated dependencies (`T008`; generated mapping rows);
* §5 the statement that has content: `Grounded`, an inductive "the mapping graph
  bottoms out", plus the theorem that a well-formed ledger grounds every profile
  of every effect-bearing row;
* §6 each premise is load-bearing, and **resolvability and acyclicity are
  independent** — the estate already says so in prose at
  `Cas/Schema/Guarded.lean:76` ("A dangling name has no outgoing edge, so it
  lies on no cycle"); here both halves are kernel facts;
* §7 the honesty half, transplanted from `Cas/Lang/RefusalMap.lean`, and a
  finding about `EC1-K07`'s word *handlerless*: read literally it condemns every
  `derivedExpansion` and every lowering-interpreted `separateSubcalculus`, since
  neither owns a handler ID. `Grounded`, not handler-ownership, is the right
  notion. §7 also carries invariant 10's handler-uniqueness clause, which the
  row drops entirely.

§8 is a positive control: nothing above is an artifact of an unsatisfiable
well-formedness structure.

## Anchors verified this pass (read, not inferred from the name)

`.staging/agent-reports/2026-08-31-effect-core-local-anchors.md:719` classifies
`T009` **SIMULATES** on a `RefusalMap` triple. All three resolve at the cited
lines:

* `library/cas/Cas/Lang/RefusalMap.lean:252` `CasErrorTag.mapped_or_hostOnly`
* `library/cas/Cas/Lang/RefusalMap.lean:265` `CasErrorTag.clause?_none_iff_hostOnly`
* `library/cas/Cas/Lang/RefusalMap.lean:293` `CasErrorTag.hostOnly_unmapped`

The classification is correct and the anchor is real, but it is a **one-step**
map over a seven-element enum decided by `cases t`. It models §7 exactly and
models §4 not at all. The report's second anchor, `tools/TrustCensus.lean`,
contains **zero** `theorem` declarations (verified by `grep -c`); it is a shape
precedent for ordered strata with a declared catch-all, not a theorem anchor.

The anchor the report **missed** is the estate's shipped answer to §4 and §6:

* `library/cas/Cas/Schema/Guarded.lean:168` `Document.ReachPlus`,
  `:173` `Document.Cyclic`, `:180` `Document.Guarded` (stated as the ABSENCE OF
  A CYCLE, never as the check restated), `:201` `Document.guarded`,
  `:378` `references_guarded_decidable`, `:421` the `Decidable` instance.

That is a name→entry reference table whose entries name other entries, with the
acyclicity of the bare-edge relation both stated relationally and DECIDED, at
fuel = table size, with soundness (`:252` `reachPlus_descends`) and completeness
(`:316` `nodup_length_le`, the pigeonhole). It is structurally the same object
as `profileId ↦ mapping.expansion.referencedProfileIds`. Its module header also
carries the caveat `T009` must inherit verbatim: the door decides
CONSTRUCTIBILITY, not PRODUCTIVITY — passing it does not establish that the
unfolded result means anything.

Secondary: `library/cas/Cas/IR/Reach.lean:416` `reach_acyclic`, the same
discipline where acyclicity is free because admission already refused the
alternative.
-/

namespace EffectCoreScoutT009

/-! ## §0 — the scratch carrier

Transcribed from `REIFICATION-CHECKLIST.md:525-618` (`SurfaceRow`,
`admissionProfiles`, and the `mapping` tagged union at `:581-597`) and
`:494-502` (the seven dispositions and their required mappings).
Deliberately minimal in every dimension the findings do not
touch: `A/E/R` transforms, family roles, class-product transfers, observations,
and obligation sets are all omitted, because every finding below is about the
SHAPE of the row's quantifier and its witness relation. The one place the model
is faithful in full is the mapping union, which is where the row lives. -/

/-- Profile identity. `pMissing` is the id §3 references without defining. -/
inductive ProfileId where
  | pA | pB | pC | pMissing
  deriving DecidableEq, Repr

/-- A direct Core handler ID (`REIFICATION-CHECKLIST.md:582`; `HandlerRow` at `:639`). -/
inductive HandlerId where
  | hPut | hAsk
  deriving DecidableEq, Repr

/-- A target adapter ID (`targetOnly`, `EC1-K07`). -/
inductive AdapterId where
  | runPromise
  deriving DecidableEq, Repr

/-- A refusal reason. In the real schema this is
`typeDiagnostic | admissionDiagnostic | casClause`, and invariant 24 pins the
third arm to the existing `Refusal.Clause` through the existing `RefusalMap` —
no second CAS refusal enum. Modeled here as one opaque arm because no finding
below depends on which reason it is. -/
inductive RefusalReason where
  | arbitraryThunk
  deriving DecidableEq, Repr

/-- Invariant 15: "Every subcalculus has a typed handler or total lowering." -/
inductive SubcalcInterp where
  | lowering
  | handler (h : HandlerId)
  deriving DecidableEq, Repr

/-- The profile mapping, arm for arm from `REIFICATION-CHECKLIST.md:581-597`.
`pure` collapses that schema's `pure` arm and its `typeOnly`/`hostOnly`
siblings: all three are R14a's discipline — effect-free work stays OUTSIDE
`Prog` — and all three are `EC1-K07`'s "explicit non-Core boundary". -/
inductive Mapping where
  | primitive (directHandlerId : HandlerId)
  | expansion (referencedProfileIds : List ProfileId)
  | subcalculus (interpretation : SubcalcInterp)
  | pure
  | foreign (directHandlerId : HandlerId)
  | target (targetAdapterId : AdapterId)
  | refusal (reason : RefusalReason)
  deriving DecidableEq, Repr

/-- `REIFICATION-CHECKLIST.md:577`. -/
inductive Decision where
  | accepted | refused | targetOnly
  deriving DecidableEq, Repr

/-- One admission profile. -/
structure Profile where
  id : ProfileId
  decision : Decision
  mapping : Mapping
  deriving DecidableEq, Repr

/-- Scratch `SurfaceRowKey` (`EC1-D007`), as in `scout-T008.lean`. -/
inductive RowKey where
  | succeed | failCause | multipartHeaders
  deriving DecidableEq, Repr

/-- One generated ledger row. `effectBearing` stands for
`effectReachability ≠ []`; `REIFICATION-CHECKLIST.md:455` — "The symbol
aggregate is effect-bearing if any overload/member is". -/
structure SurfaceRow where
  rowKey : RowKey
  effectBearing : Bool
  profiles : List Profile
  deriving DecidableEq, Repr

/-- Scratch `PublicSurface` (`EC1-D006`). -/
structure PublicSurface where
  rows : List SurfaceRow
  deriving DecidableEq, Repr

/-- Every profile in the ledger. -/
def PublicSurface.profiles (s : PublicSurface) : List Profile :=
  s.rows.flatMap (·.profiles)

theorem PublicSurface.mem_profiles {s : PublicSurface} {r : SurfaceRow}
    {p : Profile} (hr : r ∈ s.rows) (hp : p ∈ r.profiles) : p ∈ s.profiles :=
  List.mem_flatMap.mpr ⟨r, hr, hp⟩

/-- The mapping arms that name a term-level artifact rather than a declared
boundary. `expansion` counts: it names an `expansionId` and referenced
profiles. That is precisely why §4 is possible. -/
def Mapping.constructive : Mapping → Bool
  | .primitive _ => true
  | .expansion _ => true
  | .subcalculus _ => true
  | .foreign _ => true
  | _ => false

/-- The mapping arms that are `EC1-K07`'s "explicit non-Core boundary". -/
def Mapping.isBoundary : Mapping → Bool
  | .pure => true
  | .target _ => true
  | .refusal _ => true
  | _ => false

/-- The direct Core handler this profile owns, if any. Invariant 10: "Exactly
primitive and registered-foreign profiles own direct Core handler IDs"; the
`subcalculus (.handler h)` arm is invariant 15's typed handler. -/
def Mapping.handler? : Mapping → Option HandlerId
  | .primitive h => some h
  | .foreign h => some h
  | .subcalculus (.handler h) => some h
  | _ => none

/-- The arms that own no handler ID. -/
def Mapping.handlerless : Mapping → Bool
  | .expansion _ => true
  | .subcalculus .lowering => true
  | .pure => true
  | .target _ => true
  | .refusal _ => true
  | _ => false

/-- A mapping is a LEAF when it names its own witness outright. `expansion` is
the only non-leaf arm: it names other profiles instead. -/
def Mapping.isLeaf : Mapping → Bool
  | .expansion _ => false
  | _ => true

/-- The profiles a mapping defers to. `Cas/Schema/Guarded.lean:90`
`Ast.bareRefs` is the estate's shipped edge generator of exactly this kind. -/
def Mapping.refs : Mapping → List ProfileId
  | .expansion rs => rs
  | _ => []

/-! ## §1 — the row is a tautology on the mapping union

`PROOF-DAG.md:207` deleted `exists! v, evalPure e env = v` and the same-input
function-equality forms as "tautologies for any Lean function". `EC1-T009` is
the same deletion in disjunctive clothing: the mapping union is exhaustive by
construction, and every arm is on one side of the disjunction or the other, so
`cases` closes it. -/

/-- **Finding 1.** The row's disjunction holds of EVERY mapping. No surface, no
`PublicSurfaceWF`, no row, no `effectBearing`, no ledger. -/
theorem T009_as_written (m : Mapping) :
    m.constructive = true ∨ m.isBoundary = true := by
  cases m <;> first | exact .inl rfl | exact .inr rfl

/-- The same statement wearing the row's own quantifiers, with all three
premises visibly discarded. The underscores are the finding. -/
theorem T009_as_written_ignores_every_premise (_wf : True) (s : PublicSurface) :
    ∀ r ∈ s.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

/-! ## §2 — the row is true of an effect-bearing row with no profiles

`EC1-K07`: "handlerless effect-bearing rows are not [permitted]".
`REIFICATION-CHECKLIST.md:571` makes `admissionProfiles` NonEmpty, and
invariant 25 requires the "missing profile mappings" counter to be zero. None of
that is in the row, and a `∀ p ∈ []` is true. -/

def emptyProfileSurface : PublicSurface :=
  ⟨[⟨.multipartHeaders, true, []⟩]⟩

/-- The mutant really is the forbidden one: an effect-bearing public row with no
admission profile at all. -/
theorem emptyProfileSurface_is_handlerless :
    (⟨.multipartHeaders, true, []⟩ : SurfaceRow) ∈ emptyProfileSurface.rows
      ∧ emptyProfileSurface.profiles = [] := by
  decide

/-- **Finding 2.** The schematic row is TRUE of it. -/
theorem T009_holds_on_the_empty_profile_mutant :
    ∀ r ∈ emptyProfileSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

/-! ## §3 — the row is true of a dangling expansion reference

Invariant 14: "Every `derivedGraph` expansion is closed over mapped profiles."
The row does not say it. -/

def danglingProfile : Profile := ⟨.pA, .accepted, .expansion [.pMissing]⟩

def danglingSurface : PublicSurface := ⟨[⟨.succeed, true, [danglingProfile]⟩]⟩

theorem danglingSurface_profiles : danglingSurface.profiles = [danglingProfile] :=
  rfl

theorem danglingSurface_really_dangles :
    ¬ ∃ p ∈ danglingSurface.profiles, p.id = ProfileId.pMissing := by
  decide

/-- **Finding 3.** The schematic row is TRUE of it. -/
theorem T009_holds_on_the_dangling_mutant :
    ∀ r ∈ danglingSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

/-! ## §4 — the main finding: the row is true of a mapping graph that never
reaches a handler

Two accepted, effect-bearing profiles. Each has a mapping. Each mapping is
`constructive` in the row's own sense. Every referenced profile id RESOLVES, so
invariant 14's "closed over mapped profiles" holds on its literal reading. And
no profile ever reaches a handler, a lowering, or a boundary, because the two
expand into each other.

`REIFICATION-CHECKLIST.md:497` does require "expansion law and
termination/acyclicity evidence" of the `derivedExpansion` DISPOSITION. That
requirement is not in `EC1-T009`'s stated dependencies (`T008`; generated
mapping rows), not in `EC1-K07`, and not in invariant 14. This section is what
its absence costs. -/

def cycA : Profile := ⟨.pA, .accepted, .expansion [.pB]⟩
def cycB : Profile := ⟨.pB, .accepted, .expansion [.pA]⟩

def cycSurface : PublicSurface := ⟨[⟨.succeed, true, [cycA, cycB]⟩]⟩

theorem cycSurface_profiles : cycSurface.profiles = [cycA, cycB] := rfl

/-- Every reference resolves: the mutant is closed, not dangling. -/
theorem cycSurface_refs_resolve :
    ∀ p ∈ cycSurface.profiles, ∀ q ∈ p.mapping.refs,
      ∃ p' ∈ cycSurface.profiles, p'.id = q := by
  decide

/-- **Finding 4a.** The schematic row is TRUE of it. -/
theorem T009_holds_on_the_cyclic_mutant :
    ∀ r ∈ cycSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

/-- **The witness relation the row is missing.** "This profile's mapping bottoms
out": either it is a leaf — a direct handler, a subcalculus interpretation, or a
declared non-Core boundary — or it is an expansion every one of whose referenced
profiles bottoms out. The estate's shape for the same shipped object is
`Document.ReachPlus`/`Document.Guarded` (`Cas/Schema/Guarded.lean:168`/`:180`),
stated relationally there for the same reason it is stated relationally here: so
the property is the honest one and not the checker restated. -/
inductive Grounded (s : PublicSurface) : ProfileId → Prop where
  | leaf {i : ProfileId} (p : Profile) (hp : p ∈ s.profiles) (hi : p.id = i)
      (hleaf : p.mapping.isLeaf = true) : Grounded s i
  | expand {i : ProfileId} (p : Profile) (hp : p ∈ s.profiles) (hi : p.id = i)
      (hne : p.mapping.isLeaf = false)
      (hrefs : ∀ q ∈ p.mapping.refs, Grounded s q) : Grounded s i

/-- **Finding 4b — the counterexample.** In the cyclic ledger NO profile id is
grounded. The row is true; `EC1-K07`'s "handlerless effect-bearing rows are not
permitted" is violated; nothing connects the two. -/
theorem cyc_nothing_is_grounded : ∀ i, Grounded cycSurface i → False := by
  intro i h
  induction h with
  | leaf p hp _ hleaf =>
      rw [cycSurface_profiles] at hp
      cases hp with
      | head => exact Bool.noConfusion hleaf
      | tail _ h1 =>
        cases h1 with
        | head => exact Bool.noConfusion hleaf
        | tail _ h2 => cases h2
  | expand p hp _ _ _ ih =>
      rw [cycSurface_profiles] at hp
      cases hp with
      | head => exact ih .pB (List.Mem.head _)
      | tail _ h1 =>
        cases h1 with
        | head => exact ih .pA (List.Mem.head _)
        | tail _ h2 => cases h2

/-! ## §5 — the statement that has content

The witness relation of §4, plus the well-formedness the three mutants force.
`ExpandsTo s q p` is the expansion edge relation — `Cas/Schema/Guarded.lean:163`
`Document.Edge` at this carrier — oriented so that `WellFounded` means "no
infinite unfolding", which for a finite ledger is exactly `Document.Guarded`'s
absence of a cycle. -/

def ExpandsTo (s : PublicSurface) (q p : ProfileId) : Prop :=
  ∃ pr ∈ s.profiles, pr.id = p ∧ q ∈ pr.mapping.refs

/-- Well-formedness of the generated mapping ledger, each clause named by the
mutation it excludes and by the invariant it transcribes.

**Which clauses are premises and which are separate obligations.** Only
`profilesNonempty`, `refsResolve`, and `expansionWF` are used by
`grounded_of_wf`, and §6 proves each of the three necessary. `idsNodup` and
`handlersNodup` are carried because invariants 6/8/10 require them and because
`EC1-CE030`'s repair is the estate's standing discipline — but grounding is a
reachability property, so neither is a premise of the conclusion. §7's mutant is
the proof for `handlersNodup`: it is grounded and still forbidden.

**On the stated dependency `T009` → `T008`.** It is not a proof dependency at
this carrier: nothing about disposition totality helps ground a mapping, and
`REIFICATION-CHECKLIST.md:517` says so outright — "The row-level disposition is
never used to infer them." `PublicSurfaceWF` should still be carried, because it
is what makes `s.rows` the closed public universe rather than an arbitrary list;
it contributes no step of the grounding argument. -/
structure SurfaceMappingWF (s : PublicSurface) : Prop where
  /-- `admissionProfiles` is NonEmpty (`REIFICATION-CHECKLIST.md:571`); zero
  "missing profile mappings" (invariant 25). Excludes §2. -/
  profilesNonempty : ∀ r ∈ s.rows, r.effectBearing = true → r.profiles ≠ []
  /-- One profile per `profileId`. The `EC1-CE030` duplicate-free premise
  (`COUNTEREXAMPLES.md:94`) at the profile carrier, as `scout-T008.lean` §4
  carries it at the row carrier. -/
  idsNodup : (s.profiles.map (·.id)).Nodup
  /-- Invariant 14: every expansion is closed over mapped profiles. Excludes
  §3. -/
  refsResolve : ∀ p ∈ s.profiles, ∀ q ∈ p.mapping.refs,
      ∃ p' ∈ s.profiles, p'.id = q
  /-- The `derivedExpansion` disposition's own "termination/acyclicity
  evidence" (`REIFICATION-CHECKLIST.md:497`), which `EC1-T009` does not
  inherit. Excludes §4. Decided in the estate at
  `Cas/Schema/Guarded.lean:378` `references_guarded_decidable`. -/
  expansionWF : WellFounded (ExpandsTo s)
  /-- Invariant 10: "no other profile owns a duplicate handler". Excludes §7's
  mutant. Shape of `Refusal.Clause.hosts_nodup` (`Cas/Lang/RefusalMap.lean:288`)
  and `hosts_disjoint` (`:281`). -/
  handlersNodup : (s.profiles.filterMap (·.mapping.handler?)).Nodup

/-- Every id that names a profile is grounded. This is the whole content of the
word *constructive*: the witness is EXTRACTED by a terminating unfolding, not
asserted by a type. -/
theorem grounded_of_wf (s : PublicSurface) (h : SurfaceMappingWF s)
    (i : ProfileId) : (∃ pr ∈ s.profiles, pr.id = i) → Grounded s i := by
  refine h.expansionWF.induction
    (C := fun i => (∃ pr ∈ s.profiles, pr.id = i) → Grounded s i) i ?_
  intro x ih hx
  obtain ⟨pr, hpr, hid⟩ := hx
  by_cases hleaf : pr.mapping.isLeaf = true
  · exact Grounded.leaf pr hpr hid hleaf
  · refine Grounded.expand pr hpr hid (by simpa using hleaf) ?_
    intro q hq
    exact ih q ⟨pr, hpr, hid, hq⟩ (h.refsResolve pr hpr q hq)

/-- **`EC1-T009`, restated so it has content.** Every effect-bearing row carries
at least one admission profile, and every one of its profiles' mappings bottoms
out — by a terminating unfolding through `referencedProfileIds` — in a direct
handler, a subcalculus interpretation, or a declared non-Core boundary.

FALSE on §2's ledger, FALSE on §3's, FALSE on §4's. That is the point, and it is
what makes the `EC1-H11` mapping counters attack this theorem rather than
nothing. -/
theorem surface_mapping_grounded (s : PublicSurface) (h : SurfaceMappingWF s) :
    ∀ r ∈ s.rows, r.effectBearing = true →
      r.profiles ≠ [] ∧ ∀ p ∈ r.profiles, Grounded s p.id := by
  intro r hr he
  refine ⟨h.profilesNonempty r hr he, ?_⟩
  intro p hp
  exact grounded_of_wf s h p.id ⟨p, PublicSurface.mem_profiles hr hp, rfl⟩

/-- The schematic row is a CONSEQUENCE of the restated one — indeed of nothing
at all — so no content is lost by replacing it. -/
theorem restatement_implies_the_schematic_row (s : PublicSurface) :
    ∀ r ∈ s.rows, ∀ p ∈ r.profiles,
      p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ p _ => T009_as_written p.mapping

/-! ## §6 — every premise is load-bearing, and two of them are independent -/

/-- §2's ledger fails exactly `profilesNonempty`. -/
theorem emptyProfileSurface_fails_profilesNonempty :
    ¬ ∀ r ∈ emptyProfileSurface.rows, r.effectBearing = true →
        r.profiles ≠ [] := by
  intro h
  exact h ⟨.multipartHeaders, true, []⟩ (List.Mem.head _) rfl rfl

/-- §3's ledger fails exactly `refsResolve`. -/
theorem danglingSurface_fails_refsResolve :
    ¬ ∀ p ∈ danglingSurface.profiles, ∀ q ∈ p.mapping.refs,
        ∃ p' ∈ danglingSurface.profiles, p'.id = q := by
  intro h
  obtain ⟨p', hp', hid⟩ :=
    h danglingProfile (List.Mem.head _) .pMissing (List.Mem.head _)
  exact danglingSurface_really_dangles ⟨p', hp', hid⟩

theorem acc_of_no_pred {s : PublicSurface} {i : ProfileId}
    (h : ∀ q, ¬ ExpandsTo s q i) : Acc (ExpandsTo s) i :=
  Acc.intro i (fun q hq => absurd hq (h q))

theorem danglingSurface_no_pred {i : ProfileId} (h : i ≠ ProfileId.pA) :
    ∀ q, ¬ ExpandsTo danglingSurface q i := by
  rintro q ⟨pr, hpr, hid, _⟩
  rw [danglingSurface_profiles] at hpr
  cases hpr with
  | head => exact h hid.symm
  | tail _ h2 => cases h2

/-- §3's ledger is nevertheless ACYCLIC: an unresolved reference has no outgoing
edge, so it lies on no cycle. `Cas/Schema/Guarded.lean:76` states the same fact
about the same shape in prose — "A dangling name has no outgoing edge, so it
lies on no cycle and the decision is well defined without it." Here it is a
kernel fact, and it is what makes `refsResolve` and `expansionWF` INDEPENDENT
premises rather than one premise stated twice. -/
theorem danglingSurface_expansionWF : WellFounded (ExpandsTo danglingSurface) := by
  refine ⟨fun i => ?_⟩
  by_cases hpA : i = ProfileId.pA
  · subst hpA
    refine Acc.intro _ (fun q hq => ?_)
    obtain ⟨pr, hpr, _, hq'⟩ := hq
    rw [danglingSurface_profiles] at hpr
    cases hpr with
    | head =>
      have hq2 : q ∈ [ProfileId.pMissing] := hq'
      cases hq2 with
      | head => exact acc_of_no_pred (danglingSurface_no_pred (by decide))
      | tail _ h2 => cases h2
    | tail _ h2 => cases h2
  · exact acc_of_no_pred (danglingSurface_no_pred hpA)

/-- **`refsResolve` is necessary, and acyclicity does not supply it.** §3's
ledger is well-founded and its one effect-bearing row has a profile, yet that
profile is NOT grounded: the expansion names a profile the ledger does not
carry. -/
theorem danglingSurface_pA_not_grounded :
    ¬ Grounded danglingSurface ProfileId.pA := by
  intro h
  cases h with
  | leaf p hp _ hleaf =>
      rw [danglingSurface_profiles] at hp
      cases hp with
      | head => exact Bool.noConfusion hleaf
      | tail _ h2 => cases h2
  | expand p hp _ _ hrefs =>
      rw [danglingSurface_profiles] at hp
      cases hp with
      | head =>
        cases hrefs .pMissing (List.Mem.head _) with
        | leaf p' hp' hid _ =>
            rw [danglingSurface_profiles] at hp'
            cases hp' with
            | head => exact ProfileId.noConfusion hid
            | tail _ h2 => cases h2
        | expand p' hp' hid _ _ =>
            rw [danglingSurface_profiles] at hp'
            cases hp' with
            | head => exact ProfileId.noConfusion hid
            | tail _ h2 => cases h2
      | tail _ h2 => cases h2

/-- **`expansionWF` is necessary, and resolvability does not supply it.** §4's
ledger satisfies every other clause — its profiles are nonempty, its ids are
duplicate-free, every reference resolves, and it owns no handler at all — so its
expansion relation is exactly what must fail. Derived from §4b rather than
asserted: if the relation were well-founded, `grounded_of_wf` would ground
`pA`. -/
theorem cyc_expansion_not_wf : ¬ WellFounded (ExpandsTo cycSurface) := by
  intro hwf
  refine cyc_nothing_is_grounded ProfileId.pA
    (grounded_of_wf cycSurface
      ⟨by decide, by decide, cycSurface_refs_resolve, hwf, by decide⟩
      .pA ⟨cycA, List.Mem.head _, rfl⟩)

/-! ## §7 — the honesty half, and what `EC1-K07`'s word *handlerless* costs

`Cas/Lang/RefusalMap.lean` proves three things about its one-step join, and
`EC1-T009` needs all three at its carrier: the disjunction is exhaustive
(`:252`), the two halves do not overlap (`:265`), and the boundary declaration
is honest rather than merely asserted (`:293`). At this carrier the first is §1
and the third is free by typing, because the boundary arms carry no handler
field. The second is NOT free, and it is where the finding is. -/

/-- The `clause?_none_iff_hostOnly` (`:265`) analogue: exactly which arms own no
handler. -/
theorem handler?_none_iff_handlerless (m : Mapping) :
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

/-- **Finding 7a.** "Handlerless" and "boundary" are NOT complements: an
`expansion` and a lowering-interpreted `subcalculus` are handlerless and are not
boundaries. Read literally, `EC1-K07`'s "handlerless effect-bearing rows are not
[permitted]" therefore condemns every `derivedExpansion` and every
`separateSubcalculus` closed by a total lowering — which invariants 14 and 15
explicitly permit. `Grounded`, not handler-ownership, is the notion the clause
wants. -/
theorem handlerless_is_not_boundary :
    (Mapping.expansion []).handlerless = true
      ∧ (Mapping.expansion []).isBoundary = false
      ∧ (Mapping.subcalculus .lowering).handlerless = true
      ∧ (Mapping.subcalculus .lowering).isBoundary = false := by
  decide

/-- The boundary declaration is honest at this carrier: a boundary arm owns no
handler. Free by typing here, because the schema's `directHandlerId` lives
INSIDE the `primitive`/`foreign` arms. It is the `hostOnly_unmapped`
(`Cas/Lang/RefusalMap.lean:293`) obligation, and recording that it is free is
the honest report: it is free only for as long as the generated carrier keeps
handler ownership inside the mapping union. -/
theorem boundary_owns_no_handler (m : Mapping) (h : m.isBoundary = true) :
    m.handler? = none := by
  cases m <;> first | rfl | exact Bool.noConfusion h

/-- **Finding 7b — invariant 10, which the row drops entirely.** Two accepted
primitive profiles claiming the SAME direct handler ID. Every profile has a
mapping; every mapping is constructive; nothing expands, so the ledger is
trivially resolvable and well-founded. -/
def duplicateHandlerSurface : PublicSurface :=
  ⟨[⟨.succeed, true, [⟨.pA, .accepted, .primitive .hPut⟩]⟩,
    ⟨.failCause, true, [⟨.pB, .accepted, .primitive .hPut⟩]⟩]⟩

theorem duplicateHandlerSurface_really_duplicates :
    duplicateHandlerSurface.profiles.filterMap (·.mapping.handler?)
      = [HandlerId.hPut, HandlerId.hPut] := by
  decide

/-- The schematic row is TRUE of it, and so is §5's `Grounded` conclusion —
grounding is a reachability property and says nothing about uniqueness. Only
`handlersNodup` refuses it, which is why it is a separate clause. -/
theorem T009_holds_on_the_duplicate_handler_mutant :
    ∀ r ∈ duplicateHandlerSurface.rows, r.effectBearing = true →
      ∀ p ∈ r.profiles,
        p.mapping.constructive = true ∨ p.mapping.isBoundary = true :=
  fun _ _ _ p _ => T009_as_written p.mapping

theorem duplicateHandlerSurface_fails_handlersNodup :
    ¬ (duplicateHandlerSurface.profiles.filterMap (·.mapping.handler?)).Nodup := by
  rw [duplicateHandlerSurface_really_duplicates]
  decide

/-! ## §8 — the positive control

Nothing above is an artifact of an unsatisfiable well-formedness structure: a
ledger with a real expansion chain satisfies every clause and grounds every
profile. `pA` expands to `pB`, which expands to `pC`, which is a primitive with
a direct handler; a second, non-effect-bearing row closes at a declared
refusal boundary. -/

def goodA : Profile := ⟨.pA, .accepted, .expansion [.pB]⟩
def goodB : Profile := ⟨.pB, .accepted, .expansion [.pC]⟩
def goodC : Profile := ⟨.pC, .accepted, .primitive .hPut⟩
def goodR : Profile := ⟨.pMissing, .refused, .refusal .arbitraryThunk⟩

def goodSurface : PublicSurface :=
  ⟨[⟨.succeed, true, [goodA, goodB, goodC]⟩,
    ⟨.multipartHeaders, false, [goodR]⟩]⟩

theorem goodSurface_profiles :
    goodSurface.profiles = [goodA, goodB, goodC, goodR] := rfl

theorem goodSurface_pA_grounded : Grounded goodSurface ProfileId.pA := by
  refine Grounded.expand goodA (by rw [goodSurface_profiles]; exact List.Mem.head _)
    rfl rfl ?_
  intro q hq
  have hq2 : q ∈ [ProfileId.pB] := hq
  cases hq2 with
  | head =>
    refine Grounded.expand goodB
      (by rw [goodSurface_profiles]; exact List.Mem.tail _ (List.Mem.head _)) rfl rfl ?_
    intro q' hq'
    have hq3 : q' ∈ [ProfileId.pC] := hq'
    cases hq3 with
    | head =>
      exact Grounded.leaf goodC
        (by rw [goodSurface_profiles]
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) rfl rfl
    | tail _ h2 => cases h2
  | tail _ h2 => cases h2

theorem goodSurface_refs_resolve :
    ∀ p ∈ goodSurface.profiles, ∀ q ∈ p.mapping.refs,
      ∃ p' ∈ goodSurface.profiles, p'.id = q := by
  decide

theorem goodSurface_idsNodup : (goodSurface.profiles.map (·.id)).Nodup := by
  decide

theorem goodSurface_handlersNodup :
    (goodSurface.profiles.filterMap (·.mapping.handler?)).Nodup := by decide

theorem goodSurface_profilesNonempty :
    ∀ r ∈ goodSurface.rows, r.effectBearing = true → r.profiles ≠ [] := by
  decide

end EffectCoreScoutT009

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT009.T009_as_written
#print axioms EffectCoreScoutT009.T009_as_written_ignores_every_premise
#print axioms EffectCoreScoutT009.emptyProfileSurface_is_handlerless
#print axioms EffectCoreScoutT009.T009_holds_on_the_empty_profile_mutant
#print axioms EffectCoreScoutT009.danglingSurface_really_dangles
#print axioms EffectCoreScoutT009.T009_holds_on_the_dangling_mutant
#print axioms EffectCoreScoutT009.cycSurface_profiles
#print axioms EffectCoreScoutT009.cycSurface_refs_resolve
#print axioms EffectCoreScoutT009.T009_holds_on_the_cyclic_mutant
#print axioms EffectCoreScoutT009.cyc_nothing_is_grounded
#print axioms EffectCoreScoutT009.grounded_of_wf
#print axioms EffectCoreScoutT009.surface_mapping_grounded
#print axioms EffectCoreScoutT009.restatement_implies_the_schematic_row
#print axioms EffectCoreScoutT009.emptyProfileSurface_fails_profilesNonempty
#print axioms EffectCoreScoutT009.danglingSurface_fails_refsResolve
#print axioms EffectCoreScoutT009.acc_of_no_pred
#print axioms EffectCoreScoutT009.danglingSurface_expansionWF
#print axioms EffectCoreScoutT009.danglingSurface_pA_not_grounded
#print axioms EffectCoreScoutT009.cyc_expansion_not_wf
#print axioms EffectCoreScoutT009.handler?_none_iff_handlerless
#print axioms EffectCoreScoutT009.handlerless_is_not_boundary
#print axioms EffectCoreScoutT009.boundary_owns_no_handler
#print axioms EffectCoreScoutT009.duplicateHandlerSurface_really_duplicates
#print axioms EffectCoreScoutT009.T009_holds_on_the_duplicate_handler_mutant
#print axioms EffectCoreScoutT009.duplicateHandlerSurface_fails_handlersNodup
#print axioms EffectCoreScoutT009.goodSurface_pA_grounded
#print axioms EffectCoreScoutT009.goodSurface_refs_resolve
#print axioms EffectCoreScoutT009.goodSurface_idsNodup
#print axioms EffectCoreScoutT009.goodSurface_handlersNodup
#print axioms EffectCoreScoutT009.goodSurface_profilesNonempty
