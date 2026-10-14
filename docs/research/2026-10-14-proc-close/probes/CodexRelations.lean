import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.HostRuns
import Effects.Coalgebra
import ProofGraph.AxiomAudit

/-!
# Independent Q1/Q2 relation controls

Reviewed HEAD: bff5c1ccb34742381b21011893877cbfe9fd4a24; pinned Effects v0.10.1.
Placement: review controls for meaning-refines and inline-agrees, translation-simulation/R10.
Consumers: close-out L0's lifting interface and L1's observation-order definition.
This file changes no package or source declaration. Candidate contracts below are propositions,
not admitted theorems. The proved controls distinguish three different orders.
-/
set_option autoImplicit false
namespace Effect4.Probes.CodexRelations
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effects

/-! ## A result relation alone: the exact straightforward L0 extension -/
namespace Candidate
universe u v w
inductive Lift {S : Effects.Signature.{0, 0}} {A B : Type} {X : Type u} {Y : Type v}
    (Out : A → B → Prop) (R : X → Y → Prop) : Step S A X → Step S B Y → Prop
  | done {a : A} {b : B} (h : Out a b) : Lift Out R (.done a) (.done b)
  | call (op : S.Op) {f : S.Answer op → X} {g : S.Answer op → Y}
      (h : ∀ a, R (f a) (g a)) : Lift Out R (.call op f) (.call op g)

def IsSim {S : Effects.Signature.{0, 0}} {A B : Type} {X : Type u} {Y : Type v}
    (c : System S A X) (d : System S B Y) (Out : A → B → Prop) (R : X → Y → Prop) : Prop :=
  ∀ x y, R x y → ∀ step, c x = some step →
    ∃ step', d y = some step' ∧ Lift Out R step step'

def IsBisim {S : Effects.Signature.{0, 0}} {A B : Type} {X : Type u} {Y : Type v}
    (c : System S A X) (d : System S B Y) (Out : A → B → Prop) (R : X → Y → Prop) : Prop :=
  ∀ x y, R x y → OptionLift (Lift Out R) (c x) (d y)

/-- Proposed equality wrappers retain the original three-argument system relation shape.
A released package can keep today's names as these abbreviations and name the generalized
relations LiftR/IsSimR/IsBisimR. The old package's own constructor proofs still need updating. -/
abbrev LiftEq {S : Effects.Signature.{0, 0}} {A : Type} {X : Type u} {Y : Type v}
    (R : X → Y → Prop) : Step S A X → Step S A Y → Prop := Lift Eq R
abbrev IsSimEq {S : Effects.Signature.{0, 0}} {A : Type} {X : Type u} {Y : Type v}
    (c : System S A X) (d : System S A Y) (R : X → Y → Prop) := IsSim c d Eq R
abbrev IsBisimEq {S : Effects.Signature.{0, 0}} {A : Type} {X : Type u} {Y : Type v}
    (c : System S A X) (d : System S A Y) (R : X → Y → Prop) := IsBisim c d Eq R

/-- Equality compatibility is constructive; this is not definitional equality of the old
and new inductive Lift types, so constructor-level package clients require repair. -/
theorem lift_eq_iff {S : Effects.Signature.{0, 0}} {A : Type} {X : Type u} {Y : Type v}
    {R : X → Y → Prop} {p : Step S A X} {q : Step S A Y} :
    LiftEq R p q ↔ Effects.Step.Lift R p q := by
  constructor
  · intro h
    cases h with
    | done h => cases h; exact .done _
    | call op h => exact .call op h
  · intro h
    cases h with
    | done a => exact .done rfl
    | call op h => exact .call op h

theorem isSim_eq_iff {S : Effects.Signature.{0, 0}} {A : Type} {X : Type u} {Y : Type v}
    {c : System S A X} {d : System S A Y} {R : X → Y → Prop} :
    IsSimEq c d R ↔ Effects.IsSim c d R := by
  constructor <;> intro h x y hxy step hs
  · obtain ⟨step', hd, hl⟩ := h x y hxy step hs
    exact ⟨step', hd, lift_eq_iff.mp hl⟩
  · obtain ⟨step', hd, hl⟩ := h x y hxy step hs
    exact ⟨step', hd, lift_eq_iff.mpr hl⟩

theorem isBisim_eq_iff {S : Effects.Signature.{0, 0}} {A : Type} {X : Type u} {Y : Type v}
    {c : System S A X} {d : System S A Y} {R : X → Y → Prop} :
    IsBisimEq c d R ↔ Effects.IsBisim c d R := by
  constructor
  · intro h x y hxy
    exact (h x y hxy).imp (fun _ _ hl => lift_eq_iff.mp hl)
  · intro h x y hxy
    exact (h x y hxy).imp (fun _ _ hl => lift_eq_iff.mpr hl)

/-- Composition must compose BOTH the result and state relations. -/
theorem Lift.comp {S : Effects.Signature.{0, 0}} {A B C : Type} {X : Type u} {Y : Type v} {Z : Type w}
    {Out : A → B → Prop} {Out' : B → C → Prop} {R : X → Y → Prop} {R' : Y → Z → Prop}
    {p : Step S A X} {q : Step S B Y} {r : Step S C Z}
    (h : Lift Out R p q) (h' : Lift Out' R' q r) :
    Lift (fun a c => ∃ b, Out a b ∧ Out' b c) (fun x z => ∃ y, R x y ∧ R' y z) p r := by
  cases h with
  | done hab =>
    cases h' with
    | done hbc => exact .done ⟨_, hab, hbc⟩
  | call op hxy =>
    cases h' with
    | call _ hyz => exact .call op (fun a => ⟨_, hxy a, hyz a⟩)

/-- General Option result order: a cut is below every result. This alone does NOT
add the missing done-none/call case to a shape-preserving Step lifting. -/
def OptionBelow {A B : Type} (Out : A → B → Prop) : Option A → Option B → Prop
  | none, _ => True
  | some a, some b => Out a b
  | some _, none => False

/-- The cut ignores the store it leaves; only completed exits carry the output relation. -/
def CutResult {A B S T : Type} (Out : (A × S) → (B × T) → Prop) :
    (Option A × S) → (Option B × T) → Prop
  | (none, _), _ => True
  | (some a, s), (some b, t) => Out (a, s) (b, t)
  | (some _, _), (none, _) => False

/-- Proposed changed run theorem. Its heterogeneous conclusion must be existential and
relational. Equality's original run theorem can remain a wrapper of this contract. -/
def RunSoundContract {S : Effects.Signature.{0, 0}} {A B X Y σ : Type}
    (c : System S A X) (d : System S B Y) (Out : A → B → Prop) (R : X → Y → Prop) : Prop :=
  IsSim c d Out R → ∀ x y, R x y → ∀ (host : Comodel S σ) depth start finish a,
    c.run host depth x start = some (some a, finish) →
    ∃ b, d.run host depth y start = some (some b, finish) ∧ Out a b
end Candidate

/-! ## The omitted cross-constructor case -/
abbrev one : Effects.Signature.{0, 0} := ⟨Unit, fun _ => Unit⟩
abbrev natReply : Effects.Signature.{0, 0} := ⟨Unit, fun _ => Nat⟩
def bottomStep : Step one (Option Nat × Unit) Unit := .done (none, ())
def visibleStep : Step one (Option Nat × Unit) Unit := .call () (fun _ => ())

/-- Refutation of the literal L0 repair: every result relation, even True, still refuses
peel's done-cut against a visible call. Consumer: correct L0 before release. -/
theorem result_relation_does_not_make_cut_bottom
    (Out : (Option Nat × Unit) → (Option Nat × Unit) → Prop) (R : Unit → Unit → Prop) :
    ¬ Candidate.Lift Out R bottomStep visibleStep := by
  intro h
  cases h

/-- The missing ingredient can be a semantic-bottom classifier on Step, with the existing
system simulation applying it before constructor matching. Here is its exact lifted shape.
Cut-free equality uses Bottom := fun _ => False; peeled cuts use result.fst = none.
This is a candidate for the SAME package lifting, not a second Effect4 simulation framework. -/
inductive BottomLift {S : Effects.Signature.{0, 0}} {A B X Y : Type}
    (Bottom : A → Prop) (Out : A → B → Prop) (R : X → Y → Prop) :
    Step S A X → Step S B Y → Prop
  | bottom {a : A} (ha : Bottom a) (q : Step S B Y) : BottomLift Bottom Out R (.done a) q
  | done {a : A} {b : B} (h : Out a b) : BottomLift Bottom Out R (.done a) (.done b)
  | call (op : S.Op) {f : S.Answer op → X} {g : S.Answer op → Y}
      (h : ∀ a, R (f a) (g a)) : BottomLift Bottom Out R (.call op f) (.call op g)

theorem cross_constructor_bottom_is_available :
    BottomLift (fun x : Option Nat × Unit => x.1 = none)
      (Candidate.CutResult (fun a b : Nat × Unit => a = b))
      (fun _ _ : Unit => True) bottomStep visibleStep := by
  apply BottomLift.bottom
  rfl

/-! ## Minimal correction: normalize a semantic cut to the System cut -/
/-- All existing non-cut step observations remain unchanged; the semantic result none is
reclassified as the system frontier before the one package simulation engine reads it. -/
def normalizeCut {S : Effects.Signature.{0, 0}} {A S₁ X : Type} :
    Step S (Option A × S₁) X → Option (Step S (A × S₁) X)
  | .done (none, _) => none
  | .done (some a, s) => some (.done (a, s))
  | .call op next => some (.call op next)

def completedPeel {I S : Effects.Signature.{0, 0}} {A S₁ : Type}
    (step : (o : I.Op) → S₁ → I.Answer o × S₁) :
    System S (A × S₁) (Program (I ⊕ₛ S) (Option A) × S₁) :=
  fun ps => normalizeCut (Program.peel step ps.1 ps.2)

/-- Direct control at the pinned package API: peel returns SOME done for a semantic cut. -/
def unitInner (_ : one.Op) (s : Unit) : one.Answer () × Unit := ((), s)
theorem pinned_peel_turns_cut_into_done :
    (System.peel unitInner) ((Program.pure none : Program (one ⊕ₛ one) (Option Nat)), ()) =
      some (.done (none, ())) := rfl

theorem completed_peel_reclassifies_cut :
    (completedPeel unitInner) ((Program.pure none : Program (one ⊕ₛ one) (Option Nat)), ()) =
      none := rfl

theorem normalized_bottom_is_system_cut : normalizeCut bottomStep = none := rfl

theorem system_cut_simulates_any {S : Effects.Signature.{0, 0}} {A B Y : Type}
    (d : System S B Y) (Out : A → B → Prop) :
    Candidate.IsSim (fun _ : Unit => (none : Option (Step S A Unit))) d Out (fun _ _ => True) := by
  intro _ _ _ _ hs
  cases hs

/-! ## Raw structural limit is strictly stronger than completed observations -/
def asksThenCuts : Program one (Option Nat) := .vis () (fun _ => .pure none)
def cuts : Program one (Option Nat) := .pure none

def LimitApprox {S : Effects.Signature.{0, 0}} {A : Type}
    (p q : Nat → Program S (Option A)) : Prop :=
  ∀ k, ∃ j, Program.Approx (p k) (q j)

/-- The structural limit remains a sufficient certificate for the primary completed
observation inclusion. The reverse implication fails in the controls below. -/
theorem limit_sound_for_completed_observations {S : Effects.Signature.{0, 0}} {A σ : Type}
    {p q : Nat → Program S (Option A)} (h : LimitApprox p q) (host : Comodel S σ)
    (k : Nat) (start finish : σ) (a : A)
    (hr : host.run (p k) start = some (some a, finish)) :
    ∃ j, host.run (q j) start = some (some a, finish) := by
  obtain ⟨j, hj⟩ := h k
  exact ⟨j, host.run_approx hj hr⟩

/-- Admitted host pairs and their state relation. Nominal clients require a proved
request/answer equivariance premise here; an arbitrary Comodel need not respect renaming. -/
abbrev HostDomain (S : Effects.Signature.{0, 0}) :=
  ∀ {σ₁ σ₂ : Type}, Comodel S σ₁ → Comodel S σ₂ → (σ₁ → σ₂ → Prop) → Prop

/-- Equality specialization: the same host, with equal initial and final host state.
HEq permits writing this one instance of the heterogeneous interface without a second order. -/
def exactHosts (S : Effects.Signature.{0, 0}) : HostDomain S :=
  fun {σ₁ σ₂} h₁ h₂ H => ∃ (_ : σ₁ = σ₂), HEq h₁ h₂ ∧ ∀ x y, H x y ↔ HEq x y

/-- The primary observation order has witnesses after each actual completed run.
HostDomain names the required host compatibility; its equality instance quantifies all exact
hosts. The output relation covers both successful and failed ExitV observations and stores. -/
def ObsRefines {I S : Effects.Signature.{0, 0}} {A B S₁ S₂ : Type}
    (step₁ : (o : I.Op) → S₁ → I.Answer o × S₁)
    (step₂ : (o : I.Op) → S₂ → I.Answer o × S₂)
    (Rin : S₁ → S₂ → Prop) (Rout : (A × S₁) → (B × S₂) → Prop)
    (hosts : HostDomain S)
    (p : Nat → Program (I ⊕ₛ S) (Option A))
    (q : Nat → Program (I ⊕ₛ S) (Option B)) : Prop :=
  ∀ s t, Rin s t → ∀ {σ₁ σ₂ : Type} (h₁ : Comodel S σ₁) (h₂ : Comodel S σ₂)
    (H : σ₁ → σ₂ → Prop), hosts h₁ h₂ H → ∀ start₁ start₂, H start₁ start₂ →
    ∀ k a s' finish₁,
    ((Comodel.ofTotal step₁).route h₁).run (p k) (s, start₁) = some (some a, (s', finish₁)) →
    ∃ j b t' finish₂, ((Comodel.ofTotal step₂).route h₂).run (q j) (t, start₂) =
      some (some b, (t', finish₂)) ∧ Rout (a, s') (b, t') ∧ H finish₁ finish₂

/-- A call followed only by a cut never yields a completed value, for ANY host. -/
theorem asksThenCuts_no_completion {σ : Type} (host : Comodel one σ) (start finish : σ) (a : Nat) :
    host.run asksThenCuts start ≠ some (some a, finish) := by
  intro h
  unfold asksThenCuts at h
  cases ha : host.answer () start with
  | none => rw [Comodel.run_vis_none _ _ ha] at h; cases h
  | some reply =>
    rw [Comodel.run_vis_some _ _ ha] at h
    cases h

theorem no_structural_limit_for_observational_bottom :
    ¬ LimitApprox (fun _ => asksThenCuts) (fun _ => cuts) := by
  intro h
  obtain ⟨_, h⟩ := h 0
  cases h

/-- Non-vacuous quantifier control: at budget k, the right tree answers only replies below k. -/
def allReplies : Program natReply (Option Nat) := .vis () (fun n => .pure (some n))
def boundedReplies (k : Nat) : Program natReply (Option Nat) :=
  .vis () (fun n => if n < k then .pure (some n) else .pure none)

/-- The productive counterexample satisfies the monotone-budget requirement as well. -/
theorem boundedReplies_mono {i j : Nat} (hij : i ≤ j) :
    Program.Approx (boundedReplies i) (boundedReplies j) := by
  unfold boundedReplies
  apply Program.Approx.vis (S := natReply) ()
  intro n
  change Program.Approx (if n < i then .pure (some n) else .pure none)
    (if n < j then .pure (some n) else .pure none)
  by_cases hi : n < i
  · rw [if_pos hi, if_pos (Nat.lt_of_lt_of_le hi hij)]
    exact .done n
  · rw [if_neg hi]
    exact .cut _

theorem no_uniform_structural_limit : ¬ LimitApprox (fun _ => allReplies) boundedReplies := by
  intro h
  obtain ⟨j, hj⟩ := h 0
  cases hj with
  | vis _ below =>
    have hcut := below j
    simp only [Nat.lt_irrefl, if_false] at hcut
    cases hcut

/-- Every concrete completed run on the left is matched at some budget of the right.
The budget depends on the actual host reply; there is no uniform tree-wide budget. -/
theorem each_completed_observation_matches {σ : Type} (host : Comodel natReply σ)
    (start finish : σ) (a : Nat) (h : host.run allReplies start = some (some a, finish)) :
    ∃ j, host.run (boundedReplies j) start = some (some a, finish) := by
  unfold allReplies at h
  cases ha : host.answer () start with
  | none => rw [Comodel.run_vis_none _ _ ha] at h; cases h
  | some reply =>
    rw [Comodel.run_vis_some _ _ ha] at h
    cases h
    refine ⟨reply.1 + 1, ?_⟩
    unfold boundedReplies
    rw [Comodel.run_vis_some _ _ ha]
    simp only [Nat.lt_succ_self, if_true]
    rfl

/-! ## G7's sandwich still establishes the stronger structural limit -/
theorem sandwich_implies_limit_equivalence {S : Effects.Signature.{0, 0}} {A : Type}
    (p q : Nat → Program S (Option A))
    (qmono : ∀ k, Program.Approx (q k) (q (k + 1)))
    (left : ∀ k, Program.Approx (p k) (q (k + 1)))
    (right : ∀ k, Program.Approx (q (k + 1)) (p (k + 1))) :
    LimitApprox p q ∧ LimitApprox q p := by
  constructor
  · intro k
    exact ⟨k + 1, left k⟩
  · intro k
    cases k with
    | zero => exact ⟨1, (qmono 0).trans (right 0)⟩
    | succ k => exact ⟨k + 1, right k⟩

/-! ## Exact current handler/frame interfaces, as candidate obligations -/
abbrev CallHandler (table : RowTable) := Nat → Val → List (ParamTreeB table) → Ctx →
  Program (RowsSig table) (Option ExitV)

/-- The primitive frame obligation includes answers, not only disjoint write footprints.
For nominal clients AnswerRel must also relate returned handles and grow their renaming world. -/
def FrameCondition {S₁ S₂ : Type} (allowed : SyncOp → Prop)
    (step₁ : (o : StoreSig.Op) → S₁ → Val × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → Val × S₂)
    (R : S₁ → S₂ → Prop) (AnswerRel : Val → Val → Prop) : Prop :=
  ∀ o, allowed o → ∀ s t, R s t →
    R (step₁ o s).2 (step₂ o t).2 ∧ AnswerRel (step₁ o s).1 (step₂ o t).1

/-- Module frame premise with an explicit nominal world. Related client primitives may
use different mapped keys. Allocation may extend the world before its returned handle and
resulting stores are related. Merely sharing one SyncOp is the identity specialization only. -/
def NominalFrameCondition {W S₁ S₂ : Type}
    (worldLe : W → W → Prop) (allowed : W → SyncOp → Prop)
    (operations : W → SyncOp → SyncOp → Prop)
    (states : W → S₁ → S₂ → Prop) (values : W → Val → Val → Prop)
    (step₁ : (o : StoreSig.Op) → S₁ → Val × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → Val × S₂) : Prop :=
  ∀ w o₁ o₂, allowed w o₁ → operations w o₁ o₂ → ∀ s t, states w s t →
    ∃ w', worldLe w w' ∧ states w' (step₁ o₁ s).2 (step₂ o₂ t).2 ∧
      values w' (step₁ o₁ s).1 (step₂ o₂ t).1

/-- Row compatibility is independent of primitive-store framing. A host may inspect raw
handle data, so arbitrary Comodels do not satisfy this premise. OptionLift also retains exact
waiting correspondence, for the stronger prefix/at-rest laws needed by K3. -/
def HostRespects {W σ₁ σ₂ : Type} (table : RowTable)
    (worldLe : W → W → Prop)
    (requests : W → (RowSig table).Op → (RowSig table).Op → Prop)
    (answers : W → ExitV → ExitV → Prop) (states : W → σ₁ → σ₂ → Prop)
    (h₁ : Comodel (RowSig table) σ₁) (h₂ : Comodel (RowSig table) σ₂) : Prop :=
  ∀ w op₁ op₂, requests w op₁ op₂ → ∀ s t, states w s t →
    OptionLift (fun r₁ r₂ => ∃ w', worldLe w w' ∧
      answers w' r₁.1 r₂.1 ∧ states w' r₁.2 r₂.2)
      (h₁.answer op₁ s) (h₂.answer op₂ t)

/-- Exact identity frame instance for any primitive footprint; every step relates to itself. -/
theorem identity_frame (allowed : SyncOp → Prop) :
    FrameCondition allowed storeStep storeStep Eq Eq := by
  intro o _ s t h
  cases h
  exact ⟨rfl, rfl⟩

/-- A sufficient structural G7 certificate, with the present context/environment equality and
pointwise-related parameter frames made explicit. This is sufficient, not definitionally equal,
to completed-observation inclusion. A heterogeneous module lift needs a richer state/value frame. -/
def RefinesBStructural (table : RowTable) (bodies : List NativeEff) (e f : NativeEff) : Prop :=
  ∀ ctx env ps qs,
    List.Forall₂ (fun a b => ∀ ctx w, Program.Approx (a ctx w) (b ctx w)) ps qs →
    ∀ k, ∃ j, Program.Approx
      (denoteBlockB table bodies k ps e ctx env)
      (denoteBlockB table bodies j qs f ctx env)

/-! ## Primary pullback and exact handler-lift obligation

These are candidate interfaces, checked as proposition definitions, not proved laws. The
client-frame and equivariance predicates must be defined and proved independently before the
lift is frozen. In particular hc of cata_blockAlgB_approx supplies none of those premises.
-/
abbrev CtxEnvDomain := Ctx → List Val → Ctx → List Val → Prop
abbrev ParamsDomain (table : RowTable) := List (ParamTreeB table) → List (ParamTreeB table) → Prop

/-- The primary RefinesB pullback through the actual block meaning, allowing two body tables,
related contexts/environments and related parameter frames. Identity domains recover G7's
exact observation, but do not identify it with the stronger structural certificate above. -/
def RefinesB {S₁ S₂ : Type} (table : RowTable)
    (step₁ : (o : StoreSig.Op) → S₁ → Val × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → Val × S₂)
    (Rin : S₁ → S₂ → Prop) (Rout : (ExitV × S₁) → (ExitV × S₂) → Prop)
    (hosts : HostDomain (RowSig table))
    (inputs : CtxEnvDomain) (parameters : ParamsDomain table)
    (bodies₁ bodies₂ : List NativeEff) (e₁ e₂ : NativeEff) : Prop :=
  ∀ ctx₁ env₁ ctx₂ env₂, inputs ctx₁ env₁ ctx₂ env₂ →
    ∀ ps qs, parameters ps qs →
    ObsRefines step₁ step₂ Rin Rout hosts
      (fun k => denoteBlockB table bodies₁ k ps e₁ ctx₁ env₁)
      (fun k => denoteBlockB table bodies₂ k qs e₂ ctx₂ env₂)

/-- The call-handler premise itself uses the primary observation order. Parameters supplied
by the client are related at invocation, including their actual dynamic contexts. -/
def CallHandlersRefine {S₁ S₂ : Type} (table : RowTable)
    (step₁ : (o : StoreSig.Op) → S₁ → Val × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → Val × S₂)
    (Rin : S₁ → S₂ → Prop) (Rout : (ExitV × S₁) → (ExitV × S₂) → Prop)
    (hosts : HostDomain (RowSig table)) (values : Val → Val → Prop)
    (contexts : Ctx → Ctx → Prop) (parameters : ParamsDomain table)
    (call₁ call₂ : Nat → CallHandler table) : Prop :=
  ∀ j v w, values v w → ∀ as bs, parameters as bs → ∀ ctx₁ ctx₂, contexts ctx₁ ctx₂ →
    ObsRefines step₁ step₂ Rin Rout hosts
      (fun k => call₁ k j v as ctx₁) (fun k => call₂ k j w bs ctx₂)

/-- Exact wanted module-lift shape using the present block algebra and an extensible
nominal world. ClientFrame supplies located syntax/ownership admission. ClientEquivariant
must be defined independently from term, branch, context and callback compatibility under
world extension. Hosts supplies row request/reply/state compatibility. These predicates are
precise open interface requirements, not laws proved by hc or by merely naming a predicate.
The static identity frame above is the Unit-world specialization. -/
def HandlerLiftContract {W S₁ S₂ : Type} (table : RowTable)
    (step₁ : (o : StoreSig.Op) → S₁ → Val × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → Val × S₂)
    (worldLe : W → W → Prop) (allowed : W → SyncOp → Prop)
    (operations : W → SyncOp → SyncOp → Prop)
    (states : W → S₁ → S₂ → Prop)
    (outputs : W → (ExitV × S₁) → (ExitV × S₂) → Prop)
    (hosts : W → HostDomain (RowSig table)) (inputs : W → CtxEnvDomain)
    (values : W → Val → Val → Prop) (contexts : W → Ctx → Ctx → Prop)
    (parameters : W → ParamsDomain table)
    (ClientFrame ClientEquivariant : W → NativeEff → Prop)
    (call₁ call₂ : Nat → CallHandler table) : Prop :=
  NominalFrameCondition worldLe allowed operations states values step₁ step₂ →
  (∀ w, CallHandlersRefine table step₁ step₂ (states w) (outputs w) (hosts w)
    (values w) (contexts w) (parameters w) call₁ call₂) →
  ∀ w e, BodyRows table e = true → ClientFrame w e → ClientEquivariant w e →
    ∀ ctx₁ env₁ ctx₂ env₂, inputs w ctx₁ env₁ ctx₂ env₂ →
    ∀ ps qs, parameters w ps qs →
    ObsRefines step₁ step₂ (states w) (outputs w) (hosts w)
      (fun k => cata_eff (blockAlgB table k ps (call₁ k)) e ctx₁ env₁)
      (fun k => cata_eff (blockAlgB table k qs (call₂ k)) e ctx₂ env₂)

namespace Candidate
/-- A heterogeneous bisimulation yields related run results, not equality. Both outer
unanswered-host frontiers and inner depth cuts remain synchronized by OptionLift. -/
def RunBisimContract {S : Effects.Signature.{0, 0}} {A B X Y σ : Type}
    (c : System S A X) (d : System S B Y) (Out : A → B → Prop) (R : X → Y → Prop) : Prop :=
  IsBisim c d Out R → ∀ x y, R x y → ∀ (host : Comodel S σ) depth start,
    OptionLift (fun (r₁ : Option A × σ) (r₂ : Option B × σ) =>
      OptionLift Out r₁.1 r₂.1 ∧ r₁.2 = r₂.2)
      (c.run host depth x start) (d.run host depth y start)

/-- Relational composition changes both output and intermediate-state relations. -/
def SimCompositionContract {S : Effects.Signature.{0, 0}} {A B C X Y Z : Type}
    (c : System S A X) (d : System S B Y) (e : System S C Z)
    (Out : A → B → Prop) (Out' : B → C → Prop) (R : X → Y → Prop) (R' : Y → Z → Prop) : Prop :=
  IsSim c d Out R → IsSim d e Out' R' →
    IsSim c e (fun a c => ∃ b, Out a b ∧ Out' b c) (fun x z => ∃ y, R x y ∧ R' y z)
end Candidate

end Effect4.Probes.CodexRelations
