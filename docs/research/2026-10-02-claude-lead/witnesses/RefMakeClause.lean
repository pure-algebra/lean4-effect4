import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
SOURCE-ONLY controls, pinned 973ebf969617ff65ab3a13616db3f81fe145adfa.
1. Concept 4, actual store-step ConfigTyped preservation; Concept 1 separates
   membership from physical raw-handle validity.
2. M6Ledger.step_loop/step_deliver through StoreClauseKeeps(refMake).
3. Exact existing storePre, SyncOp.validIn, syncOpStep and Stores.WF; unknown is
   the actual certificate. No reachable/configuration hypothesis is fabricated.
4. This refutes only the proposed generic pre -> validIn bridge. It is NOT a
   complete ConfigTyped, StoreClauseKeeps, M6 or reachable-program counterexample.
5. Identifies the exact premise needed before applying syncOpStep_wf in the
   shared store-family proof; scalar controls keep the ordinary positive path.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed.StoreFamilyControls
open Effect4 Effect4.Machine Effect4.Program

abbrev bad : Val := .handle 255 7

theorem unknown_pre (root : ProgramSource) (w : World) :
    storePre root w (.refMake bad) Ty.unknown :=
  ⟨rfl, live_of_keys_nil rfl⟩

theorem unknown_invalid (s : Stores) : bad.validIn s = false := rfl

theorem unknown_request_invalid (s : Stores) :
    SyncOp.validIn s (.refMake bad) = false := rfl

theorem unknown_actual_step (s : Stores) :
    syncOpStep (.refMake bad) s =
      some ({s with refs := s.refs ++ [bad]}, Val.cell ⟨s.refs.length⟩) := rfl

theorem unknown_after_not_wf (s : Stores) :
    ¬ ({s with refs := s.refs ++ [bad]} : Stores).WF := by
  intro wf
  have member : bad ∈ s.refs ++ [bad] :=
    List.mem_append_right _ List.mem_cons_self
  have valid := wf.1 bad member
  change false = true at valid
  cases valid

theorem pre_does_not_imply_valid (root : ProgramSource) (w : World) :
    ¬ (∀ (op : SyncOp) (cert : StoreCert op),
      storePre root w op cert → SyncOp.validIn w.state op = true) := by
  intro all
  have wrong := all (.refMake bad) Ty.unknown (unknown_pre root w)
  change false = true at wrong
  cases wrong

theorem scalar_pre (root : ProgramSource) (w : World) (n : Nat) :
    storePre root w (.refMake (.nat n)) Ty.nat := ⟨rfl, True.intro⟩

theorem scalar_request_valid (s : Stores) (n : Nat) :
    SyncOp.validIn s (.refMake (.nat n)) = true := rfl

theorem scalar_after_wf (s : Stores) (wf : s.WF) (n : Nat) :
    ({s with refs := s.refs ++ [.nat n]} : Stores).WF :=
  syncOpStep_wf (.refMake (.nat n)) s _ _ wf rfl rfl

#print axioms unknown_pre
#print axioms unknown_invalid
#print axioms unknown_request_invalid
#print axioms unknown_actual_step
#print axioms unknown_after_not_wf
#print axioms pre_does_not_imply_valid
#print axioms scalar_pre
#print axioms scalar_request_valid
#print axioms scalar_after_wf
end Effect4.Program.Typed.StoreFamilyControls

/-!
Append to RawValidityGap.lean. Same Concept4/M6 placement. These proofs inspect
all ConfigTyped fields by using the existing full frame-replacement theorem.
The last theorem is conditional on an actual Evaluating witness with no race
marker. It does NOT assert such a witness is reachable or supplied here.
Source-only; exact statements and current definitions are retained.
-/
namespace Effect4.Program.Typed.StoreFamilyControls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-- Regardless of the ghost world chosen afterward, the actual bad allocation
violates the mandatory store-WF field. No prestate assumption is used here. -/
theorem bad_current_cannot_settle {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    {next : Val → RProgram}
    (hc : f.frame.current = .vis (.inl (.refMake bad)) next) :
    ¬ SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y)) := by
  intro ⟨w', _, typed⟩
  have wf := typed.machine.wide.wf
  simp only [evaluateRawR, hc, unknown_actual_step] at wf
  change ({m.state with refs := m.state.refs ++ [bad]} : Stores).WF at wf
  exact unknown_after_not_wf m.state wf

def prependBad (f : RFiber) : RFiber :=
  {f with frame := {f.frame with current :=
    (.vis (.inl (.refMake bad)) (fun _ => f.frame.current))}}

/-- Full ConfigTyped is retained by the already-proved frame replacement. The
old checked continuation is reused at every later world; no field is omitted. -/
theorem prependBad_evaluating {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none) :
    Evaluating root rootTy w m rest (prependBad f) y := by
  have code : ∀ ty, w.Γ f.id = some ty →
      CodeOk root w (m.update f) f.id ty (prependBad f).frame := by
    intro ty declared
    obtain ⟨tin, current, stack, provenance⟩ := ev.code marker ty declared
    refine ⟨tin, ?_, stack, ⟨provenance.recorded, provenance.deferred⟩⟩
    exact TypedProg.store (op := .refMake bad) Ty.unknown (unknown_pre root w)
      (fun w' ord _ _ => typedProg_mono root w w' tin f.frame.current ord current)
  have typed := (configTyped_frame_step ev.typed rfl ev.look ev.running
    (prependBad f).frame code rfl).2 y
  rw [rupdate_rupdate m
    (show ({f with frame := (prependBad f).frame} : RFiber).id = f.id from rfl)] at typed
  exact ⟨typed, ev.stale, ev.running, ev.live⟩

/-- A non-marker Evaluating witness suffices to contradict the universal clause.
This is an invariant-interface counterexample, not a reachable-source execution. -/
theorem clause_refMake_false_of_evaluating {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none) :
    ¬ StoreClauseKeeps root rootTy (.refMake bad) := by
  intro keeps
  have badEv := prependBad_evaluating ev marker
  exact bad_current_cannot_settle rfl
    (keeps w m rest (prependBad f) y (fun _ => f.frame.current) badEv rfl)

#print axioms bad_current_cannot_settle
#print axioms prependBad_evaluating
#print axioms clause_refMake_false_of_evaluating
end Effect4.Program.Typed.StoreFamilyControls

/-!
Append after the checked StoreClauseFailure body. Concrete prestate for its
conditional theorem. Built from the actual loaded pure-nat root and the existing
full machine/fiber/queue constructors. Only the running flag is set to select an
ordinary delivery state. No reachable-source claim is made for the later
prepended malformed allocation. Source-only; coordinator owns compilation.
-/
namespace Effect4.Program.Typed.StoreFamilyControls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def root : ProgramSource := rootProgram
def rootTy : EffTy := EffTy.pure Ty.nat
def w0 : World := initialWorld rootTy root.sig.serviceTy
def m0 : RState := loadR rootProgram 1

def idleFiber : RFiber :=
  RunFiber.make Api.root (denoteR rootProgram rootProgram (rootPoint 1)) true
    (stores.budgetOf emptyCtx) emptyCtx

def runningFiber : RFiber := {idleFiber with running := true}
def runningMachine : RState := m0.update runningFiber

theorem loaded_typed : MachineTyped root rootTy w0 m0 := by
  apply machineTyped_load root rootTy 1 1 ⟨rfl, rfl⟩ rfl rfl
  change TypedProg root w0 rootTy (.pure (.success (.nat 0)))
  exact TypedProg.pure ⟨True.intro, True.intro⟩

theorem running_look : runningMachine.fiber? runningFiber.id = some runningFiber := rfl

theorem running_typed : MachineTyped root rootTy w0 runningMachine := by
  have old : FiberTyped root w0 m0 idleFiber :=
    loaded_typed.fiber List.mem_cons_self
  have wide : MachineWide root rootTy w0 runningMachine := by
    apply machineWide_rupdate (f := idleFiber) (g := runningFiber) loaded_typed.wide rfl
    · intro key hk
      change key ∈ ([] : List Guard.GuardKey) at hk
      cases hk
    · intro token r hr
      have absent : requestOfR (m0.update runningFiber) runningFiber.id token = none :=
        requestOfR_of_not_parked running_look (fun h => nomatch h)
      rw [absent] at hr
      cases hr
  have fresh : FiberTyped root w0 runningMachine runningFiber := by
    refine ⟨runFiberOk_congr old.ok rfl rfl rfl rfl rfl rfl rfl, (fun _ h => nomatch h), old.below, old.pendingShape,
      (fun h => False.elim (h rfl)), (fun _ h => nomatch h),
      (fun h => nomatch h), (fun h => nomatch h), old.deferredCause,
      old.pendingOwner, (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ _ _ h => nomatch h), old.targetsBelow, old.observersBelow⟩
  apply machineTyped_of wide
  intro f hf
  change f ∈ [runningFiber] at hf
  rw [List.mem_singleton] at hf
  subst hf
  exact fresh

theorem ordinary_evaluating : Evaluating root rootTy w0 m0 [] runningFiber false := by
  have emptyTyped : ConfigTyped root rootTy w0 runningMachine [] :=
    configTyped_tail (configTyped_tail
      (evaluate_entry root rootTy w0 runningMachine Api.root running_typed))
  have code : raceRegistrationR runningFiber.frame.current = none →
      ∀ ty, w0.Γ runningFiber.id = some ty →
        CodeOk root w0 runningMachine runningFiber.id ty runningFiber.frame := by
    intro _ ty declared
    change some rootTy = some ty at declared
    cases declared
    refine ⟨rootTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    change TypedProg root w0 rootTy (.pure (.success (.nat 0)))
    exact TypedProg.pure ⟨True.intro, True.intro⟩
  have typed := configTyped_cons_deliver emptyTyped running_look rfl rfl
    (fun h => nomatch h) false code
  exact ⟨typed, ⟨idleFiber, rfl, rfl⟩, rfl, rfl⟩

/-- Exact frozen operation-clause predicate, with every prestate field supplied.
The malformed frame is invariant-admitted, not claimed source-reachable. -/
theorem refMake_clause_false : ¬ StoreClauseKeeps root rootTy (.refMake bad) :=
  clause_refMake_false_of_evaluating ordinary_evaluating rfl

#print axioms loaded_typed
#print axioms running_look
#print axioms running_typed
#print axioms ordinary_evaluating
#print axioms refMake_clause_false
end Effect4.Program.Typed.StoreFamilyControls
