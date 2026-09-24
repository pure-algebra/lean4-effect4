import Effect4.Laws.Program.Typed.Stack
import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.Typing.CheckInversion

/-!
# Laws.Program.Typed.Assembly — the typed state of the reference machine

Slice 5's assembly (§3.5 of the brief, as amended): the generated predicate bundle `Preds`
instantiated with the strong judgments (`preds`), the typed state (`TypedState`: validity, the
generated whole-state predicate, and the active-delivery correlation), reachability
(`RReachable`), admitted host answers (`AnswerOk`), and the declared obligations the milestones
after slice 5 prove: initialization (`typedState_load`, M5) and the transition ledger, one
preservation obligation per command constructor (M6). `capture_lookup` is proved here.

Two limits of the generated bundle are recorded rather than papered over: `PendingOk` receives
the enclosing position, not the fiber, so it can only say every pending token is declared for
some fiber; `RaceOk` says each race's host is parked at a declared token, and the race's result
type is the host's declared token type through `ResumeOk` on the resume it enqueues.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-- The type a position is expected at: the root's and each fiber's declared type (D7). -/
def expectOf (w : World) : Expect → Option EffTy
  | .root => w.Γ Api.root
  | .fiber id => w.Γ id
  | .hook _ => none

/-- A completion at an effect type: an exit strongly, a reference completion through the
heap table. -/
def CompletionStrong (w : World) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => StrongExit w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub ty.answer = true

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. -/
def CaptureTyped (root : ProgramSource) (w : World) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check (nativeSignature root.table) env c.path (.acquireRelease acquire release) = .ok t ∧
    Checker.check (nativeSignature root.table) env (c.path ++ [0]) acquire = .ok a ∧
    EnvTyped w (env ++ [a.answer]) c.env ∧ ServicesOk w c.ctx.services

/-- The generated bundle, instantiated with the strong judgments. -/
def preds (root : ProgramSource) : Preds World where
  SavedOk w e x := ∀ ty, expectOf w e = some ty →
    Contracts.SavedOk (TypedProg root) StrongExit (frameProtocols root) w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → StrongExit w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProg root) w target token code
  ServiceOk w _ ctx := ServicesOk w ctx.services
  RaceOk w _ races := ∀ r ∈ races, (w.Θ r.host r.token).isSome = true
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrong w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → StrongValue w ty v
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c
  CaptureOk w _ c := CaptureTyped root w c

/-- The typed state: world validity, the generated whole-state predicate over `preds`, and the
active-delivery correlation: a parked fiber's saved stack expects its token's declared type. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) StrongExit (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

/-- A state some decision tape reaches from the loaded program. -/
def RReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, m = (replayR root.program fuel tape).machine

/-- A host answer is admitted: an answer to a fiber parked at that token fits the token's
declared type. Answers to anything else run inertly and impose nothing. -/
def AnswerOk (w : World) (m : RState) : Api.Decision → Prop
  | .answerAsync target token answer =>
    (∃ f, m.fiber? target = some f ∧ f.parked = .withGuard token) →
      ∃ ty, w.Θ target token = some ty ∧ CompletionStrong w ty answer
  | _ => True

/-- The queued commands carry typed resumes. -/
def QueueOk (root : ProgramSource) (w : World) (cmds : List RCmd) : Prop :=
  ∀ c ∈ cmds, match c with
    | .resume target token code => Contracts.ResumeOk (TypedProg root) w target token code
    | _ => True

/-- One command keeps the typed state and the queue typed, at some later world. -/
def StepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, TypedState root rootTy w m → QueueOk root w (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 ∧ QueueOk root w' r.2

/-! ## The capture lookup -/

theorem envTyped_append {w : World} {env : List Ty} {vals : List Val} {ty : Ty} {v : Val}
    (h : EnvTyped w env vals) (hv : StrongValue w ty v) : EnvTyped w (env ++ [ty]) (vals ++ [v]) := by
  refine ⟨by simp only [List.length_append, h.1, List.length_singleton], fun i t x ht hx => ?_⟩
  by_cases hi : i < env.length
  · rw [List.getElem?_append_left hi] at ht
    rw [List.getElem?_append_left (h.1 ▸ hi)] at hx
    exact h.2 i t x ht hx
  · have hge : env.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge] at ht
    rw [List.getElem?_append_right (h.1 ▸ hge)] at hx
    rw [← h.1] at hx
    cases hk : i - env.length with
    | zero =>
      rw [hk] at ht hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hx
      subst ht hx
      exact hv
    | succ k =>
      rw [hk] at ht
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at ht
      cases ht

/-- A capture's release runs at the point its path's `acquireRelease` checks it at: the
release child, over the checker's environment extended by the acquired value and the exit. -/
theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (h : CaptureTyped root w c)
    (hex : StrongValue w (.exitOf .unknown .unknown) exVal) :
    ∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, _⟩ := h
  obtain ⟨a', r, hacq', hrel, _, _⟩ := Checker.inv_acquireRelease _ _ _ _ _ t hcheck
  rw [hacq] at hacq'
  cases hacq'
  refine ⟨r, release, env ++ [a.answer, .exitOf .unknown .unknown], ?_, hrel, ?_⟩
  · show Node.at_ (.eff root.program) (c.path ++ [1]) = some (.eff release)
    rw [Agreement.Node.at_append, hnode]
    rfl
  · show EnvTyped w (env ++ [a.answer, .exitOf .unknown .unknown]) (c.env ++ [exVal])
    have := envTyped_append henv hex
    simpa only [List.append_assoc, List.singleton_append] using this

/-! ## Declared obligations

`typedState_load` (M5: initialization from an admitted source). The transition ledger (M6): one
preservation obligation per command constructor, one for a tape decision under admitted host
answers, and the capstone that every reachable state is typed. Declared, not proved. -/
namespace M3bAssembly

theorem typedState_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel)) := ⟨⟩

theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (_h : CaptureTyped root w c)
    (_hex : StrongValue w (.exitOf .unknown .unknown) exVal) : ProofGraph.Obligation
    (∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty) := ⟨⟩

end M3bAssembly

namespace M6Ledger

theorem step_evaluate (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.evaluate id)) := ⟨⟩

theorem step_loop (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.loop id yielding)) := ⟨⟩

theorem step_deliver (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.deliver id yielding)) := ⟨⟩

theorem step_finish (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (exit : ExitV) :
    ProofGraph.Obligation (StepPreserves root rootTy (.finish id exit)) := ⟨⟩

theorem step_resume (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat) (code : RProgram) :
    ProofGraph.Obligation (StepPreserves root rootTy (.resume id token code)) := ⟨⟩

theorem step_launch (root : ProgramSource) (rootTy : EffTy) (race : Nat) :
    ProofGraph.Obligation (StepPreserves root rootTy (.launch race)) := ⟨⟩

theorem step_enrollRace (root : ProgramSource) (rootTy : EffTy) (race : Nat) (child : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.enrollRace race child)) := ⟨⟩

theorem step_registrationDone (root : ProgramSource) (rootTy : EffTy) (race : Nat) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.registrationDone race yielding)) := ⟨⟩

theorem step_interruptTarget (root : ProgramSource) (rootTy : EffTy) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreserves root rootTy (.interruptTarget target who extra)) := ⟨⟩

theorem step_afterInterrupt (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (kind : ParkKind) :
    ProofGraph.Obligation (StepPreserves root rootTy (.afterInterrupt host yielding kind)) := ⟨⟩

theorem step_raceCancel (root : ProgramSource) (rootTy : EffTy) (race : Nat) (host : FiberId)
    (yielding : Bool) (remaining visited : List FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.raceCancel race host yielding remaining visited)) := ⟨⟩

theorem step_trackChild (root : ProgramSource) (rootTy : EffTy) (parent child : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.trackChild parent child)) := ⟨⟩

theorem step_observe (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) (exit : ExitV) (observer : Observer) :
    ProofGraph.Obligation (StepPreserves root rootTy (.observe fiber exit observer)) := ⟨⟩

theorem step_exitDone (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.exitDone fiber)) := ⟨⟩

theorem step_closeParAwait (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (fibers : List FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.closeParAwait host yielding fibers)) := ⟨⟩

theorem step_link (root : ProgramSource) (rootTy : EffTy) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreserves root rootTy (.link mode scope target interruptor extra)) := ⟨⟩

theorem step_drainDue (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (StepPreserves root rootTy .drainDue) := ⟨⟩

theorem step_wake (root : ProgramSource) (rootTy : EffTy) (list : WakeKey) (phase : WakePhase) :
    ProofGraph.Obligation (StepPreserves root rootTy (.wake list phase)) := ⟨⟩

/-- A tape decision keeps the typed state when its host answer, if any, is admitted. -/
theorem decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    ProofGraph.Obligation (∀ w m, TypedState root rootTy w m → AnswerOk w m d →
      ∃ w', w.leHost w' ∧ TypedState root rootTy w'
        (letI := termEvaluatorFor root.program
         stepDecisionState (interpR root.program) fuel m d).1) := ⟨⟩

/-- The capstone: every state an admitted tape reaches from an admitted source is typed. -/
theorem typedState_reachable (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      RReachable root fuel m → ∃ w, TypedState root rootTy w m) := ⟨⟩

end M6Ledger

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3bAssembly.capture_lookup :=
  @Effect4.Program.Typed.capture_lookup
#proof_wanted Effect4.Program.Typed.M3bAssembly.typedState_load
#typed_state_obligations Effect4.Program.Typed.M3bAssembly ceiling 1
  using aesop (rule_sets := [Effect4.TypedState])
#proof_wanted Effect4.Program.Typed.M6Ledger.step_evaluate
#proof_wanted Effect4.Program.Typed.M6Ledger.step_loop
#proof_wanted Effect4.Program.Typed.M6Ledger.step_deliver
#proof_wanted Effect4.Program.Typed.M6Ledger.step_finish
#proof_wanted Effect4.Program.Typed.M6Ledger.step_resume
#proof_wanted Effect4.Program.Typed.M6Ledger.step_launch
#proof_wanted Effect4.Program.Typed.M6Ledger.step_enrollRace
#proof_wanted Effect4.Program.Typed.M6Ledger.step_registrationDone
#proof_wanted Effect4.Program.Typed.M6Ledger.step_interruptTarget
#proof_wanted Effect4.Program.Typed.M6Ledger.step_afterInterrupt
#proof_wanted Effect4.Program.Typed.M6Ledger.step_raceCancel
#proof_wanted Effect4.Program.Typed.M6Ledger.step_trackChild
#proof_wanted Effect4.Program.Typed.M6Ledger.step_observe
#proof_wanted Effect4.Program.Typed.M6Ledger.step_exitDone
#proof_wanted Effect4.Program.Typed.M6Ledger.step_closeParAwait
#proof_wanted Effect4.Program.Typed.M6Ledger.step_link
#proof_wanted Effect4.Program.Typed.M6Ledger.step_drainDue
#proof_wanted Effect4.Program.Typed.M6Ledger.step_wake
#proof_wanted Effect4.Program.Typed.M6Ledger.decision_preserves
#proof_wanted Effect4.Program.Typed.M6Ledger.typedState_reachable
#typed_state_obligations Effect4.Program.Typed.M6Ledger ceiling 20
  using aesop (rule_sets := [Effect4.TypedState])
