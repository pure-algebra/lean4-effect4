import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.StoresLaws

/-!
# verify-StepLoop — ALG-01 at the step level: the declared `step_loop` obligation is false

Adversarial verifier of seat ALGEBRA, formal pass, 2026-10-01. The seat proved, at the level of
the judgment, that `StackAccepts` is not world-monotone (`P2.stackAccepts_not_mono`), and claimed
by reading that an allocating step then breaks `TypedState`, naming `step_evaluate`. This file
checks that claim against the declared ledger (`Typed/Assembly.lean:99-104`, `:170-171`):

* `typed_mBad`: the loaded `Ref.make(5)` machine with the seat's `.answer badNext` frame under the
  root is a `TypedState` at the initial world (the frame is accepted vacuously: no cell is
  declared, so no success fits `refOf nat`).
* `step_loop_refuted` (red): one `loop` of the root allocates cell 0 and leaves a machine no world
  types; so `M6Ledger.step_loop` is false at this instance. The contradiction uses only the
  frame's run clause on the new cell.
* `evaluate_keeps` (control): `evaluate` allocates nothing (`Machine/Fibers.lean:1849-1856`); on
  the same machine it keeps the typed state at the same world. The seat's example command is the
  wrong one; the allocation is `loop`'s (`EvaluateR.lean:297-305`).
* `bad_not_kripke_initial` (control): the seat's Kripke-closed judgment (P2's `FrameAcceptsK`,
  copied) refuses the bad frame at the initial world, so the amended typed state excludes `mBad`.
* `step_loop_good` (green): with a frame typed into `unit` on every success, the same step keeps
  the typed state at the world that declares the new cell. The failure is the frame's.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace FormalPass.AlgebraVerify.StepLoop

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Program.Typed.Contracts

abbrev TW := Effect4.Program.Typed.World

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
def m0 : RState := loadR refProg 20 20

def badNext : ExitV → RProgram
  | .success _ => .pure (.success (Val.str "x"))
  | .failure c => .pure (.failure c)

def withStack (s : List ScopeFrame) (f : RFiber) : RFiber :=
  { f with frame := { f.frame with stack := s } }

def mBad : RState := { m0 with fibers := m0.fibers.map (withStack [.answer badNext]) }

abbrev tin : EffTy := EffTy.pure (.refOf .nat)
abbrev unitTy : EffTy := EffTy.pure .unit
abbrev w0 : TW := initialWorld unitTy

theorem valid_withStack {rootTy : EffTy} {w : TW} {m : RState} (s : List ScopeFrame)
    (h : WorldValid rootTy w m) :
    WorldValid rootTy w { m with fibers := m.fibers.map (withStack s) } := by
  have hids : (m.fibers.map (withStack s)).map (·.id) = m.fibers.map (·.id) := by
    rw [List.map_map]
    rfl
  refine ⟨?_, ?_, h.heap, h.promises, ?_, h.tokenBound, h.tokenTargets, h.state, h.wf, h.cells,
    h.fiberClosed, h.heapClosed, h.promiseClosed, h.tokenClosed, h.root⟩
  · show w.ids = (m.fibers.map (withStack s)).map (·.id)
    rw [hids]
    exact h.ids
  · intro id
    show (w.Γ id).isSome = true ↔ id ∈ (m.fibers.map (withStack s)).map (·.id)
    rw [hids]
    exact h.fibers id
  · intro f hf token hp
    obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hf
    exact h.tokens f0 hf0 token hp

theorem valid_mBad : WorldValid unitTy w0 mBad :=
  valid_withStack _ (initial_world_valid unitTy refProg 20 20 ⟨rfl, rfl⟩)

theorem code_typed (w : TW) :
    TypedProg (refProg : ProgramSource) w tin (denoteR refProg refProg (rootPoint 20)) := by
  refine TypedProg.store (cert := Ty.nat) ⟨rfl, trivial⟩ ?_
  intro w' _ ans hpost
  obtain ⟨key, rfl, hs⟩ := hpost
  refine TypedProg.pure ?_
  rw [fitsExit_success_iff]
  change Typed.Fits w' (Val.cell key) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩

theorem stack_ok :
    StackAccepts (TypedProg (refProg : ProgramSource)) FitsExit (frameProtocols refProg) w0 tin unitTy
      [.answer badNext] := by
  refine .cons (.answer badNext fun ex hex => ?_) (.nil unitTy)
  cases ex with
  | success v =>
    exfalso
    rw [fitsExit_success_iff] at hex
    change Typed.Fits w0 v (.refOf .nat) at hex
    simp only [Typed.Fits] at hex
    split at hex
    · obtain ⟨t', ht, _⟩ := hex
      cases ht
    · exact hex
  | failure c =>
    refine .pure ?_
    rw [fitsExit_failure_iff] at hex ⊢
    exact hex


theorem typed_mBad : TypedState (refProg : ProgramSource) unitTy w0 mBad := by
  refine ⟨valid_mBad, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
          some unitTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨tin, code_typed w0, stack_ok, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

/-- The machine and queue after one `loop` of the root on the bad machine, exactly as
`StepPreserves` names them. -/
abbrev afterLoop : RState × List RCmd :=
  letI := termEvaluatorFor (refProg : ProgramSource).program
  driveStep (interpR (refProg : ProgramSource).program) mBad (.loop Api.root false) []

theorem post_fiber : ∃ f ∈ afterLoop.1.fibers, f.id = Api.root ∧
    f.frame.current = .pure (.success (Val.cell ⟨0⟩)) ∧ f.frame.stack = [.answer badNext] :=
  ⟨_, List.Mem.head _, rfl, rfl, rfl⟩

theorem post_untyped (w : TW) : ¬ TypedState (refProg : ProgramSource) unitTy w afterLoop.1 := by
  intro h
  obtain ⟨f, hf, hid, hcur, hst⟩ := post_fiber
  have hroot : expectOf w (.fiber f.id) = some unitTy := by
    rw [hid]
    exact h.1.root
  obtain ⟨tin', hprog, hstack, _⟩ := (h.2.1.c0 f hf).c0.c0 _ hroot
  rw [hcur] at hprog
  rw [hst] at hstack
  have hex := TypedProg.pure_inv hprog
  cases hstack with
  | cons head tail =>
    cases tail
    cases head with
    | answer next run =>
      have hp := TypedProg.pure_inv (run _ hex)
      rw [fitsExit_success_iff] at hp
      change Typed.Fits w (Val.str "x") .unit at hp
      simp only [Typed.Fits] at hp

/-- **The declared M6 obligation `step_loop` is false at this instance.** -/
theorem step_loop_refuted :
    ¬ StepPreserves (refProg : ProgramSource) unitTy (.loop Api.root false) := by
  intro h
  obtain ⟨w', _, ht, _⟩ := h w0 mBad [] typed_mBad (by
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    trivial)
  exact post_untyped w' ht

/-! ## Control: `evaluate` allocates nothing and keeps the bad machine typed -/

theorem valid_of_skeleton {rootTy : EffTy} {w : TW} {m m' : RState}
    (h : WorldValid rootTy w m)
    (ids : m'.fibers.map (·.id) = m.fibers.map (·.id))
    (parked : ∀ f' ∈ m'.fibers, ∃ f ∈ m.fibers, f'.id = f.id ∧ f'.parked = f.parked)
    (state : m'.state = m.state) (next : m'.nextToken = m.nextToken) : WorldValid rootTy w m' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.tokenTargets, ?_, ?_, h.cells,
    h.fiberClosed, h.heapClosed, h.promiseClosed, h.tokenClosed, h.root⟩
  · rw [ids]
    exact h.ids
  · intro id
    rw [ids]
    exact h.fibers id
  · intro key
    rw [state]
    exact h.heap key
  · intro key
    rw [state]
    exact h.promises key
  · intro f' hf' token hp
    obtain ⟨f, hf, hid, hpk⟩ := parked f' hf'
    rw [hid]
    exact h.tokens f hf token (hpk ▸ hp)
  · intro id token ty hty
    rw [next]
    exact h.tokenBound id token ty hty
  · rw [state]
    exact h.state
  · rw [state]
    exact h.wf

abbrev afterEval : RState × List RCmd :=
  letI := termEvaluatorFor (refProg : ProgramSource).program
  driveStep (interpR (refProg : ProgramSource).program) mBad (.evaluate Api.root) []

theorem afterEval_queue : afterEval.2 = [.loop Api.root false] := rfl

theorem valid_afterEval : WorldValid unitTy w0 afterEval.1 :=
  valid_of_skeleton valid_mBad rfl
    (fun f' hf' => by
      change f' ∈ [_] at hf'
      rw [List.mem_singleton] at hf'
      subst hf'
      exact ⟨_, List.Mem.head _, rfl, rfl⟩)
    rfl rfl

theorem typed_afterEval : TypedState (refProg : ProgramSource) unitTy w0 afterEval.1 := by
  refine ⟨valid_afterEval, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
          some unitTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨tin, code_typed w0, stack_ok, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

/-- **Control: on the same bad machine, `evaluate` keeps the typed state, at the same world.**
`evaluate` only marks the fiber running and queues `loop` (`Machine/Fibers.lean:1849-1856`); the
allocation is `loop`'s. So the seat's example command (`step_evaluate`) is the wrong one. -/
theorem evaluate_keeps :
    ∃ w', w0.leHost w' ∧ TypedState (refProg : ProgramSource) unitTy w' afterEval.1 ∧
      QueueOk (refProg : ProgramSource) w' afterEval.2 :=
  ⟨w0, leHost_refl w0, typed_afterEval, by
    rw [afterEval_queue]
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    trivial⟩

/-! ## Control: the seat's Kripke-closed judgment refuses the bad frame at the initial world

`FrameAcceptsK`/`StackAcceptsK` are the seat's P2 definitions, copied (probe files cannot import
each other). Only the `answer` arm is exercised. -/

section Kripke

variable (TP : TW → EffTy → RProgram → Prop) (Ex : TW → EffTy → ExitV → Prop)
  (hooks : FrameProtocols)

inductive FrameAcceptsK (w : TW) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → kind.hasExitArm ex = true →
        TP w' tout (next ex))
      (skip : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → kind.hasExitArm ex = false →
        Ex w' tout ex) :
      FrameAcceptsK w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → TP w' tout (next ex)) :
      FrameAcceptsK w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAcceptsK w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.asyncFinalizer w' tin tout name) :
      FrameAcceptsK w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAcceptsK w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.iterator w' tin tout name) :
      FrameAcceptsK w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : ∀ w', w.leHost w' → hooks.loop w' tin tout name cursor) :
      FrameAcceptsK w tin tout (.loop name cursor)

inductive StackAcceptsK (w : TW) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAcceptsK w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAcceptsK TP Ex hooks w tin middle frame)
      (tail : StackAcceptsK w middle tout rest) : StackAcceptsK w tin tout (frame :: rest)

end Kripke

def s1 : Stores := { Stores.empty with refs := [Val.nat 0] }

/-- The initial world after allocating cell 0 at `nat` (not claimed valid for any machine). -/
def w1 : TW :=
  { w0 with state := s1, Ρ := fun k => if k = ⟨0⟩ then some .nat else none }

theorem w0_le_w1 : w0.leHost w1 := by
  have hst : Stores.le w0.state w1.state :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have hrho : TableExtends w0.Ρ w1.Ρ := fun _ _ h => by cases h
  have hcells : CellCompatible w0 w1 := by
    unfold CellCompatible
    refine ⟨fun _ _ h => ?_, fun _ _ h => ?_⟩
    · unfold HeapTypedAt at h
      cases h.1
    · unfold PromiseTypedAt at h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, hst⟩, fun _ _ h => h, fun _ _ h => h, hrho, hcells,
    fun _ _ _ h => h⟩, fun _ _ h => h⟩

theorem cell0_fits_w1 : FitsExit w1 tin (.success (Val.cell ⟨0⟩)) := by
  rw [fitsExit_success_iff]
  change Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, by simp only [w1, if_pos], Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Control: the Kripke-closed judgment refuses the counterexample's frame at `w0`.** -/
theorem bad_not_kripke_initial :
    ¬ StackAcceptsK (TypedProg (refProg : ProgramSource)) FitsExit (frameProtocols refProg)
      w0 tin unitTy [.answer badNext] := by
  intro h
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | answer next run =>
      have hp := TypedProg.pure_inv (run w1 w0_le_w1 (.success (Val.cell ⟨0⟩)) cell0_fits_w1)
      rw [fitsExit_success_iff] at hp
      change Typed.Fits w1 (Val.str "x") .unit at hp
      simp only [Typed.Fits] at hp

/-! ## Green control: the same `loop` step with a frame typed at every world keeps the state typed -/

def goodNext : ExitV → RProgram
  | .success _ => .pure (.success Val.unit)
  | .failure c => .pure (.failure c)

def mGood : RState := { m0 with fibers := m0.fibers.map (withStack [.answer goodNext]) }

theorem stack_good (w : TW) :
    StackAccepts (TypedProg (refProg : ProgramSource)) FitsExit (frameProtocols refProg) w tin unitTy
      [.answer goodNext] := by
  refine .cons (.answer goodNext fun ex hex => ?_) (.nil unitTy)
  cases ex with
  | success v =>
    refine .pure ?_
    rw [fitsExit_success_iff]
    exact trivial
  | failure c =>
    refine .pure ?_
    rw [fitsExit_failure_iff] at hex ⊢
    exact hex

/-- The good frame is accepted by the Kripke-closed judgment too. -/
theorem stack_good_kripke (w : TW) :
    StackAcceptsK (TypedProg (refProg : ProgramSource)) FitsExit (frameProtocols refProg) w tin unitTy
      [.answer goodNext] :=
  .cons (.answer goodNext fun w' _ ex hex => by
    cases ex with
    | success v =>
      refine .pure ?_
      rw [fitsExit_success_iff]
      exact trivial
    | failure c =>
      refine .pure ?_
      rw [fitsExit_failure_iff] at hex ⊢
      exact hex) (.nil unitTy)

theorem typed_mGood : TypedState (refProg : ProgramSource) unitTy w0 mGood := by
  refine ⟨valid_withStack _ (initial_world_valid unitTy refProg 20 20 ⟨rfl, rfl⟩), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
          some unitTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨tin, code_typed w0, stack_good w0, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

abbrev afterGood : RState × List RCmd :=
  letI := termEvaluatorFor (refProg : ProgramSource).program
  driveStep (interpR (refProg : ProgramSource).program) mGood (.loop Api.root false) []

/-- The world after the allocation: cell 0 declared at `nat`, the machine's new stores. -/
def w1g : TW := w0.addRef afterGood.1.state ⟨0⟩ .nat

theorem afterGood_step :
    syncOpStep (.refMake (Val.nat 5)) Stores.empty = some (afterGood.1.state, Val.cell ⟨0⟩) := rfl

theorem w0_le_w1g : w0.leHost w1g := by
  have hst : Stores.le w0.state w1g.state :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have hrho : TableExtends w0.Ρ w1g.Ρ := insert_extends _ _ _ rfl
  have hcells : CellCompatible w0 w1g := by
    unfold CellCompatible
    refine ⟨fun _ _ h => ?_, fun _ _ h => ?_⟩
    · unfold HeapTypedAt at h
      cases h.1
    · unfold PromiseTypedAt at h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, hst⟩, fun _ _ h => h, fun _ _ h => h, hrho, hcells,
    fun _ _ _ h => h⟩, fun _ _ h => h⟩

theorem rho_w1g (key : RefKey) :
    w1g.Ρ key = if key = ⟨0⟩ then some Ty.nat else none := rfl

theorem valid_w1g : WorldValid unitTy w1g afterGood.1 := by
  have v0 := initial_world_valid unitTy refProg 20 20 ⟨rfl, rfl⟩
  have hids : afterGood.1.fibers.map (·.id) = m0.fibers.map (·.id) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ⟨?_, ?_⟩, v0.fiberClosed, ?_, v0.promiseClosed,
    v0.tokenClosed, v0.root⟩
  · rw [hids]
    exact v0.ids
  · intro id
    rw [hids]
    exact v0.fibers id
  · intro key
    rw [rho_w1g]
    change _ ↔ key.index < 1
    by_cases hk : key = ⟨0⟩
    · rw [if_pos hk, hk]
      exact ⟨fun _ => Nat.zero_lt_one, fun _ => rfl⟩
    · rw [if_neg hk]
      refine ⟨fun h => Bool.noConfusion h, fun hlt => ?_⟩
      exfalso
      apply hk
      cases key with
      | mk i =>
        change i < 1 at hlt
        have hi : i = 0 := by omega
        rw [hi]
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp
  · intro id token ty h
    cases h
  · intro id token ty h
    cases h
  · exact syncOpStep_wf _ _ _ _ Stores.empty_wf rfl afterGood_step
  · intro i v hv
    intro ty hty
    cases i with
    | zero =>
      change some (Val.nat 5) = some v at hv
      cases hv
      rw [rho_w1g, if_pos rfl] at hty
      cases hty
      rfl
    | succ j =>
      change none = some v at hv
      cases hv
  · intro i v hv
    cases hv
  · intro key ty h
    rw [rho_w1g] at h
    by_cases hk : key = ⟨0⟩
    · rw [if_pos hk] at h
      cases h
      rfl
    · rw [if_neg hk] at h
      cases h

theorem cell0_fits_w1g : FitsExit w1g tin (.success (Val.cell ⟨0⟩)) := by
  rw [fitsExit_success_iff]
  change Typed.Fits w1g (Val.cell ⟨0⟩) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, by rw [rho_w1g, if_pos rfl], Ty.sub_refl _, Ty.sub_refl _⟩

theorem typed_afterGood : TypedState (refProg : ProgramSource) unitTy w1g afterGood.1 := by
  refine ⟨valid_w1g, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
          some unitTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root unitTy Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨tin, TypedProg.pure cell0_fits_w1g, stack_good w1g,
        ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), ?_, ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
    intro i v hv ty hty
    cases i with
    | zero =>
      change some (Val.nat 5) = some v at hv
      cases hv
      rw [rho_w1g, if_pos rfl] at hty
      cases hty
      exact trivial
    | succ j =>
      change none = some v at hv
      cases hv
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

/-- **Green control: with a frame typed into `unit` on every success, the same `loop` step keeps
the typed state**, at the world that declares the new cell. So `step_loop_refuted` is the
frame's doing, not the step's. -/
theorem step_loop_good :
    ∃ w', w0.leHost w' ∧ TypedState (refProg : ProgramSource) unitTy w' afterGood.1 ∧
      QueueOk (refProg : ProgramSource) w' afterGood.2 :=
  ⟨w1g, w0_le_w1g, typed_afterGood, by
    intro c hc
    change c ∈ [_, _] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> trivial⟩

end FormalPass.AlgebraVerify.StepLoop

#print axioms FormalPass.AlgebraVerify.StepLoop.valid_mBad
#print axioms FormalPass.AlgebraVerify.StepLoop.code_typed
#print axioms FormalPass.AlgebraVerify.StepLoop.stack_ok
#print axioms FormalPass.AlgebraVerify.StepLoop.typed_mBad
#print axioms FormalPass.AlgebraVerify.StepLoop.post_fiber
#print axioms FormalPass.AlgebraVerify.StepLoop.post_untyped
#print axioms FormalPass.AlgebraVerify.StepLoop.step_loop_refuted
#print axioms FormalPass.AlgebraVerify.StepLoop.valid_of_skeleton
#print axioms FormalPass.AlgebraVerify.StepLoop.typed_afterEval
#print axioms FormalPass.AlgebraVerify.StepLoop.evaluate_keeps
#print axioms FormalPass.AlgebraVerify.StepLoop.w0_le_w1
#print axioms FormalPass.AlgebraVerify.StepLoop.bad_not_kripke_initial
#print axioms FormalPass.AlgebraVerify.StepLoop.stack_good_kripke
#print axioms FormalPass.AlgebraVerify.StepLoop.typed_mGood
#print axioms FormalPass.AlgebraVerify.StepLoop.valid_w1g
#print axioms FormalPass.AlgebraVerify.StepLoop.typed_afterGood
#print axioms FormalPass.AlgebraVerify.StepLoop.step_loop_good
