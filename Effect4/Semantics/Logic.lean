import Effect4.Semantics.Denotation

/-!
# Semantics.Logic

Owner: weakest-precondition, liberal, and total-correctness logic (DB-06).

`docs/DESIGN-BASIS.md` DB-06 classifies EffHOL's angle modality as a weakest
*liberal* precondition and makes the decomposition

```text
wp p post ↔ wlp p post ∧ total p
```

a pending obligation "for the chosen semantics before calling a judgment `wp`".
Packet D1 fixed that semantics: a checked flow denotes a
`Program (FullSig alphabet) (RunResult × Tape)`, and the runner is `interpret`
of it (T1, T2 in `Effect4/Semantics/Denotation.lean`). This module states the
logic over the free monad, relative to an *answer specification* — which
answers each operation may return — and discharges the decomposition once for
every program (`wp_iff_wlp_and_total`) and once more in the flow reading
(`Flow.wp_iff`), where partiality is exactly the unanswered frontier and the
refusal, never fuel (DB-04).

Soundness ties the box to `interpret`: for a deterministic handler whose
answers respect the specification at every state, the box of a program holds
of the value `interpret` produces (`box_sound`), and through T1/T2 of the value
the runner produces at the allotted fuel (`Flow.wlp_runDefault`,
`Flow.wp_runDefault`). Against a deterministic oracle the box *is* evaluation
(`box_ofOracle_iff`), which is what the receipts decide.

No `String` enters this module. Every theorem is within `propext`/`Quot.sound`.
-/

namespace Effect4.Logic

open Effects

universe uOp uAns uT

/-- An answer specification: which answers an operation may return. The
modalities quantify over exactly these answers. -/
def Spec (S : Signature.{uOp, uAns}) : Type (max uOp uAns) :=
  (operation : S.Op) → S.Answer operation → Prop

/-- No constraint: every answer is admissible. -/
def Spec.any (S : Signature.{uOp, uAns}) : Spec S := fun _ _ => True

/-- A deterministic oracle's answers, and only those. -/
def Spec.ofOracle {S : Signature.{uOp, uAns}}
    (oracle : (operation : S.Op) → S.Answer operation) : Spec S :=
  fun operation answer => answer = oracle operation

section Modalities

variable {S : Signature.{uOp, uAns}} {A B : Type uAns}

/-- The box: every admissible answer path that reaches a value reaches one
satisfying `post`. This is EffHOL's angle modality read as DB-06 reads it, a
weakest *liberal* precondition — an operation with no admissible answer makes
the box vacuous there. -/
def box (spec : Spec S) (post : A → Prop) : Program S A → Prop
  | .pure value => post value
  | .vis operation next => ∀ answer, spec operation answer → box spec post (next answer)

/-- The diamond: some admissible answer path reaches a value satisfying `post`. -/
def dia (spec : Spec S) (post : A → Prop) : Program S A → Prop
  | .pure value => post value
  | .vis operation next => ∃ answer, spec operation answer ∧ dia spec post (next answer)

/-- Totality: along every admissible path, every operation reached has an
admissible answer, so no path can stop at an unanswerable operation. -/
def total (spec : Spec S) : Program S A → Prop
  | .pure _ => True
  | .vis operation next =>
      (∃ answer, spec operation answer) ∧ ∀ answer, spec operation answer → total spec (next answer)

/-- The total weakest precondition: every path is answerable and ends in `post`. -/
def wp (spec : Spec S) (post : A → Prop) : Program S A → Prop
  | .pure value => post value
  | .vis operation next =>
      (∃ answer, spec operation answer) ∧ ∀ answer, spec operation answer → wp spec post (next answer)

/-- The weakest liberal precondition is the box. -/
abbrev wlp (spec : Spec S) (post : A → Prop) (program : Program S A) : Prop :=
  box spec post program

/-- DB-06, discharged over the free monad. -/
theorem wp_iff_wlp_and_total (spec : Spec S) (post : A → Prop) :
    ∀ program : Program S A, wp spec post program ↔ wlp spec post program ∧ total spec program
  | .pure value => by simp [wp, wlp, box, total]
  | .vis operation next => by
      simp only [wp, wlp, box, total]
      constructor
      · intro ⟨exists_, all⟩
        exact ⟨fun answer h => ((wp_iff_wlp_and_total spec post (next answer)).1 (all answer h)).1,
          exists_,
          fun answer h => ((wp_iff_wlp_and_total spec post (next answer)).1 (all answer h)).2⟩
      · intro ⟨allBox, exists_, allTotal⟩
        exact ⟨exists_, fun answer h =>
          (wp_iff_wlp_and_total spec post (next answer)).2 ⟨allBox answer h, allTotal answer h⟩⟩

theorem box_mono {spec : Spec S} {post post' : A → Prop} (weaker : ∀ a, post a → post' a) :
    ∀ program : Program S A, box spec post program → box spec post' program
  | .pure value, h => weaker value h
  | .vis _ next, h => fun answer admissible => box_mono weaker (next answer) (h answer admissible)

theorem box_congr {spec : Spec S} {post post' : A → Prop} (same : ∀ a, post a ↔ post' a)
    (program : Program S A) : box spec post program ↔ box spec post' program :=
  ⟨box_mono (fun a => (same a).1) program, box_mono (fun a => (same a).2) program⟩

theorem box_and (spec : Spec S) (p q : A → Prop) :
    ∀ program : Program S A,
      box spec (fun a => p a ∧ q a) program ↔ box spec p program ∧ box spec q program
  | .pure _ => Iff.rfl
  | .vis _ next => by
      simp only [box]
      constructor
      · intro h
        exact ⟨fun answer admissible => ((box_and spec p q (next answer)).1 (h answer admissible)).1,
          fun answer admissible => ((box_and spec p q (next answer)).1 (h answer admissible)).2⟩
      · intro ⟨hp, hq⟩ answer admissible
        exact (box_and spec p q (next answer)).2 ⟨hp answer admissible, hq answer admissible⟩

theorem box_true (spec : Spec S) : ∀ program : Program S A, box spec (fun _ => True) program
  | .pure _ => trivial
  | .vis _ next => fun answer _ => box_true spec (next answer)

/-- The box is a Kleisli law: sequencing threads the postcondition. -/
theorem box_bind (spec : Spec S) (post : B → Prop) :
    ∀ (program : Program S A) (next : A → Program S B),
      box spec post (program.bind next) ↔ box spec (fun a => box spec post (next a)) program
  | .pure _, _ => Iff.rfl
  | .vis _ rest, next => by
      simp only [Program.bind, box]
      constructor
      · intro h answer admissible
        exact (box_bind spec post (rest answer) next).1 (h answer admissible)
      · intro h answer admissible
        exact (box_bind spec post (rest answer) next).2 (h answer admissible)

theorem dia_mono {spec : Spec S} {post post' : A → Prop} (weaker : ∀ a, post a → post' a) :
    ∀ program : Program S A, dia spec post program → dia spec post' program
  | .pure value, h => weaker value h
  | .vis _ next, ⟨answer, admissible, h⟩ =>
      ⟨answer, admissible, dia_mono weaker (next answer) h⟩

/-- Under totality the box implies the diamond: an admissible path exists and
every admissible path satisfies `post`. -/
theorem dia_of_box_of_total {spec : Spec S} {post : A → Prop} :
    ∀ program : Program S A, total spec program → box spec post program → dia spec post program
  | .pure _, _, h => h
  | .vis _ next, ⟨⟨answer, admissible⟩, allTotal⟩, h =>
      ⟨answer, admissible,
        dia_of_box_of_total (next answer) (allTotal answer admissible) (h answer admissible)⟩

end Modalities

/-! ## The deterministic reading: an oracle makes the box evaluation -/

section Oracle

variable {S : Signature.{uOp, uAns}} {A : Type uAns}

/-- Run a program against a deterministic oracle. -/
def evalOracle (oracle : (operation : S.Op) → S.Answer operation) : Program S A → A
  | .pure value => value
  | .vis operation next => evalOracle oracle (next (oracle operation))

theorem total_ofOracle (oracle : (operation : S.Op) → S.Answer operation) :
    ∀ program : Program S A, total (Spec.ofOracle oracle) program
  | .pure _ => trivial
  | .vis operation next =>
      ⟨⟨oracle operation, rfl⟩, fun answer admissible => by
        cases admissible
        exact total_ofOracle oracle (next _)⟩

theorem box_ofOracle_iff (oracle : (operation : S.Op) → S.Answer operation) (post : A → Prop) :
    ∀ program : Program S A,
      box (Spec.ofOracle oracle) post program ↔ post (evalOracle oracle program)
  | .pure _ => Iff.rfl
  | .vis operation next => by
      simp only [box, evalOracle]
      constructor
      · intro h
        exact (box_ofOracle_iff oracle post (next _)).1 (h (oracle operation) rfl)
      · intro h answer admissible
        cases admissible
        exact (box_ofOracle_iff oracle post (next _)).2 h

theorem wp_ofOracle_iff (oracle : (operation : S.Op) → S.Answer operation) (post : A → Prop)
    (program : Program S A) :
    wp (Spec.ofOracle oracle) post program ↔ post (evalOracle oracle program) := by
  rw [wp_iff_wlp_and_total, and_iff_left (total_ofOracle oracle program)]
  exact box_ofOracle_iff oracle post program

end Oracle

/-! ## Soundness against `interpret`

A deterministic monad runs a computation from a state to a value and a state;
`StateT σ Id` and every `StateT` layer over another deterministic monad are
instances, which covers the runner's `RunM (StateT σ Id)`. A handler *respects*
a specification when its answer at every state is admissible; then the box of
a program holds of the value `interpret` produces. -/

section Soundness

/-- A monad whose computations run deterministically from a state. -/
class DetRun (M : Type uAns → Type uT) (σ : outParam (Type uAns)) [Monad M] where
  run : {α : Type uAns} → M α → σ → α × σ
  run_pure : ∀ {α : Type uAns} (a : α) (s : σ), run (pure a) s = (a, s)
  run_bind : ∀ {α β : Type uAns} (x : M α) (f : α → M β) (s : σ),
    run (x >>= f) s = run (f (run x s).1) (run x s).2

instance instDetRunStateTId {σ : Type uAns} : DetRun (StateT σ Id) σ where
  run x s := x.run s
  run_pure _ _ := rfl
  run_bind _ _ _ := rfl

instance instDetRunStateT {τ : Type uAns} {M : Type uAns → Type uAns} [Monad M] [LawfulMonad M]
    {σ : Type uAns} [DetRun M σ] : DetRun (StateT τ M) (τ × σ) where
  run x ts :=
    let r := DetRun.run (x.run ts.1) ts.2
    (r.1.1, (r.1.2, r.2))
  run_pure a ts := by
    show (let r := DetRun.run ((pure a : StateT τ M _).run ts.1) ts.2; (r.1.1, (r.1.2, r.2))) = _
    simp only [StateT.run_pure, DetRun.run_pure]
  run_bind x f ts := by
    show (let r := DetRun.run ((x >>= f).run ts.1) ts.2; (r.1.1, (r.1.2, r.2))) = _
    simp only [StateT.run_bind, DetRun.run_bind]

variable {S : Signature.{uOp, uAns}} {A : Type uAns}
variable {M : Type uAns → Type uT} [Monad M] {σ : Type uAns} [DetRun M σ]

/-- The handler's answer at every state is admissible. -/
def Respects (spec : Spec S) (handler : Handler S M) : Prop :=
  ∀ (operation : S.Op) (s : σ), spec operation (DetRun.run (handler.handle operation) s).1

theorem Respects.any (handler : Handler S M) : Respects (M := M) (σ := σ) (Spec.any S) handler :=
  fun _ _ => trivial

/-- Soundness of the box: what `interpret` computes satisfies the postcondition. -/
theorem box_sound {spec : Spec S} {handler : Handler S M} (respects : Respects spec handler)
    (post : A → Prop) :
    ∀ (program : Program S A) (s : σ),
      box spec post program → post (DetRun.run (interpret handler program) s).1
  | .pure _, s, h => by rw [interpret_pure, DetRun.run_pure]; exact h
  | .vis operation next, s, h => by
      rw [interpret_vis, DetRun.run_bind]
      exact box_sound respects post (next _) _ (h _ (respects operation s))

/-- Completeness of the diamond: what `interpret` computes is reachable. -/
theorem dia_complete {spec : Spec S} {handler : Handler S M} (respects : Respects spec handler)
    (post : A → Prop) :
    ∀ (program : Program S A) (s : σ),
      post (DetRun.run (interpret handler program) s).1 → dia spec post program
  | .pure _, s, h => by rw [interpret_pure, DetRun.run_pure] at h; exact h
  | .vis operation next, s, h => by
      rw [interpret_vis, DetRun.run_bind] at h
      exact ⟨_, respects operation s, dia_complete respects post (next _) _ h⟩

/-- A respected specification is total: any state witnesses an admissible answer. -/
theorem total_of_respects {spec : Spec S} {handler : Handler S M}
    (respects : Respects spec handler) (s : σ) :
    ∀ program : Program S A, total spec program
  | .pure _ => trivial
  | .vis operation next =>
      ⟨⟨_, respects operation s⟩, fun answer _ => total_of_respects respects s (next answer)⟩

end Soundness

end Effect4.Logic

/-! ## The flow reading

A flow's postcondition speaks about the answered value. A run that stops at
the unanswered frontier or is refused has no value, so it is outside the
liberal reading and inside `total`'s. Fuel does not appear: the denotation is
fuel-free (T2), and DB-04 keeps fuel exhaustion a live frontier of the
approximation, never a judgment about the program. -/

namespace Effect4.Flow

open Effects Effect4.Logic
open Effects.Trace (Val)

variable {Ty : Type} {alphabet : FlowAlphabet Ty}

/-- Every answered value satisfies `post`. -/
def answered (post : Val → Prop) (result : RunResult × Tape) : Prop :=
  ∀ value, result.1 = .done value → post value

/-- The run answered. -/
def answers (result : RunResult × Tape) : Prop :=
  ∃ value, result.1 = .done value

/-- The weakest liberal precondition of a flow against a tape and an input. -/
def wlp (spec : Spec (FullSig alphabet)) (flow : CheckedFlow alphabet) (tape : Tape)
    (input : Val) (post : Val → Prop) : Prop :=
  box spec (answered post) (denote flow tape input)

/-- Totality of a flow against a tape and an input: every admissible path answers. -/
def total (spec : Spec (FullSig alphabet)) (flow : CheckedFlow alphabet) (tape : Tape)
    (input : Val) : Prop :=
  box spec answers (denote flow tape input)

/-- The total weakest precondition of a flow. -/
def wp (spec : Spec (FullSig alphabet)) (flow : CheckedFlow alphabet) (tape : Tape)
    (input : Val) (post : Val → Prop) : Prop :=
  box spec (fun result => ∃ value, result.1 = .done value ∧ post value) (denote flow tape input)

/-- DB-06 in the flow reading. -/
theorem wp_iff (spec : Spec (FullSig alphabet)) (flow : CheckedFlow alphabet) (tape : Tape)
    (input : Val) (post : Val → Prop) :
    wp spec flow tape input post ↔ wlp spec flow tape input post ∧ total spec flow tape input := by
  unfold wp wlp total
  rw [← box_and]
  apply box_congr
  intro result
  constructor
  · intro ⟨value, hv, hp⟩
    refine ⟨fun value' hv' => ?_, ⟨value, hv⟩⟩
    rw [hv] at hv'
    cases hv'
    exact hp
  · intro ⟨all, value, hv⟩
    exact ⟨value, hv, all value hv⟩

/-- The value the runner produces at the allotted fuel, read through T1/T2. -/
theorem runDefault_result {σ : Type} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    (((runDefault flow service nameOf tape input).run log).run s).1.1 =
      (DetRun.run (interpret (traceHandler service nameOf) (denote flow tape input)) (log, s)).1.1 := by
  rw [runDefault_eq_interpretRun_denote]
  simp only [interpretRun, StateT.run_map, StateT.run_bind]
  rfl

/-- Soundness of the flow `wlp`: whatever the runner answers satisfies `post`. -/
theorem wlp_runDefault {σ : Type} {spec : Spec (FullSig alphabet)} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (respects : Respects (σ := Effect4.Trace.Log × σ) spec (traceHandler service nameOf))
    (tape : Tape) (input : Val) (post : Val → Prop) (h : wlp spec flow tape input post)
    (log : Effect4.Trace.Log) (s : σ) (value : Val) :
    (((runDefault flow service nameOf tape input).run log).run s).1.1 = .done value → post value := by
  rw [runDefault_result]
  exact box_sound respects (answered post) (denote flow tape input) (log, s) h value

/-- Soundness of the flow `wp`: the runner answers, and the answer satisfies `post`. -/
theorem wp_runDefault {σ : Type} {spec : Spec (FullSig alphabet)} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (respects : Respects (σ := Effect4.Trace.Log × σ) spec (traceHandler service nameOf))
    (tape : Tape) (input : Val) (post : Val → Prop) (h : wp spec flow tape input post)
    (log : Effect4.Trace.Log) (s : σ) :
    ∃ value, (((runDefault flow service nameOf tape input).run log).run s).1.1 = .done value ∧
      post value := by
  rw [runDefault_result]
  exact box_sound respects _ (denote flow tape input) (log, s) h

/-- Against an oracle the flow `wp` is a computation on the fuelled denotation,
which is what the receipts decide. -/
theorem wp_ofOracle_iff (oracle : (operation : (FullSig alphabet).Op) → (FullSig alphabet).Answer operation)
    (flow : CheckedFlow alphabet) (tape : Tape) (input : Val) (post : Val → Prop) :
    wp (Spec.ofOracle oracle) flow tape input post ↔
      ∃ value,
        (evalOracle oracle (denoteFuel (fuelFor flow.erase tape) flow.erase flow.erase.entry
          [input] tape)).1 = .done value ∧ post value := by
  unfold wp
  rw [Logic.box_ofOracle_iff, ← denoteFuel_eq_denote flow tape input (Nat.le_refl _)]

theorem wlp_ofOracle_iff (oracle : (operation : (FullSig alphabet).Op) → (FullSig alphabet).Answer operation)
    (flow : CheckedFlow alphabet) (tape : Tape) (input : Val) (post : Val → Prop) :
    wlp (Spec.ofOracle oracle) flow tape input post ↔
      answered post (evalOracle oracle (denoteFuel (fuelFor flow.erase tape) flow.erase
        flow.erase.entry [input] tape)) := by
  unfold wlp
  rw [Logic.box_ofOracle_iff, ← denoteFuel_eq_denote flow tape input (Nat.le_refl _)]

theorem total_ofOracle_iff (oracle : (operation : (FullSig alphabet).Op) → (FullSig alphabet).Answer operation)
    (flow : CheckedFlow alphabet) (tape : Tape) (input : Val) :
    total (Spec.ofOracle oracle) flow tape input ↔
      answers (evalOracle oracle (denoteFuel (fuelFor flow.erase tape) flow.erase
        flow.erase.entry [input] tape)) := by
  unfold total
  rw [Logic.box_ofOracle_iff, ← denoteFuel_eq_denote flow tape input (Nat.le_refl _)]

end Effect4.Flow
