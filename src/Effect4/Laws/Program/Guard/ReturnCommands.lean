import Effect4.Laws.Machine.Eliminators
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Settle
import Effect4.Laws.Program.Interference

/-! Proof graph: generated command shapes, retained fiber identity,
then the empty-tail settle queue and its sole possible owner.
No whole-machine invariant or old-tail transport is asserted here. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.ReturnCommands
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.ReturnFields Effect4.Program.Guard.Settle

/-- Commands with no owner, reserved key, code site, or authority obligation. -/
def Simple : NCmd → Prop
  | .evaluate _ | .link _ _ _ _ _ | .trackChild _ _ | .drainDue
  | .interruptTarget _ _ _ => True
  | _ => False

def AllSimple (cs : List NCmd) : Prop := ∀ c ∈ cs, Simple c

/-- The three native action continuations. Their embedded parks have no race site. -/
def Local (id : FiberId) : NCmd → Prop
  | .afterInterrupt owner _ (.join _ _) | .afterInterrupt owner _ (.awaitAll _)
  | .closeParAwait owner _ _ | .raceCancel _ owner _ _ _ => owner = id
  | _ => False

inductive Nested (p : NativeEff) (table : RowTable) (it : NIter) : Prop
  | simple (commands : AllSimple it.nested)
  | owned (outcome : it.outcome = .commands) (front : List NCmd) (last : NCmd)
      (commands : it.nested = front ++ [last]) (simple : AllSimple front)
      (isLocal : Local it.fiber.id last)
  | registration (outcome : it.outcome = .commands) (rid : Nat) (race : NRace)
      (lookup : it.machine.race? rid = some race) (host : race.host = it.fiber.id)
      (park : (interpOf p table).parkOf it.fiber.frame.current = some (.ok (.race rid)))
      (commands : it.nested = [.launch rid, .registrationDone rid it.yielding])

theorem allSimple_nil : AllSimple [] := by simp [AllSimple]
theorem allSimple_append {xs ys : List NCmd} (hx : AllSimple xs) (hy : AllSimple ys) :
    AllSimple (xs ++ ys) := by simpa only [AllSimple, List.mem_append, or_imp, forall_and] using And.intro hx hy

theorem allSimple_map {α : Type} (xs : List α) (fn : α → NCmd)
    (h : ∀ x, Simple (fn x)) : AllSimple (xs.map fn) := by
  intro c hc
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hc
  exact h x

theorem allSimple_linkScope (interp : NInterp) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    AllSimple (linkScope interp m mode scope target who extra).2 := by
  have commands := (RunMachine.applyFiberEdits_shape
    (linkScopeEdits interp m mode scope target who extra).2
    (linkScopeEdits interp m mode scope target who extra).1).2
  intro command member
  obtain ⟨target, same⟩ := commands command member
  subst command
  exact True.intro

theorem stepFrame_nested (p : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Nested p table (evaluatePrim.stepFrame interp m f yielding) := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> exact .simple allSimple_nil

theorem finalizerOr_nested (p : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (exit : ExitV) :
    Nested p table (evaluatePrim.finalizerOr interp m f yielding exit) := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals repeat' first
    | exact .simple allSimple_nil
    | exact stepFrame_nested _ _ _ _ _ _
    | split

theorem withFiber_nested (p : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (action : Effect4.Program.Guard.ReturnFields.NAction) :
    Nested p table (evaluatePrim.withFiber interp m f yielding action) := by
  fun_cases evaluatePrim.withFiber interp m f yielding action
  case case1 | case2 | case3 =>
    apply Nested.simple
    simp only [start] at *
    aesop (add norm unfold [AllSimple, Simple])
  case case9 =>
    unfold evaluatePrim.interruptAs
    split
    · exact .simple allSimple_nil
    · exact .owned rfl [] _ rfl allSimple_nil rfl
  case case12 | case27 =>
    exact .owned rfl _ _ rfl (allSimple_map _ _ (fun _ => True.intro)) rfl
  case case17 | case18 =>
    unfold beginRace
    exact .simple allSimple_nil
  case case31 => exact .owned rfl [] _ rfl allSimple_nil rfl
  all_goals exact .simple allSimple_nil

theorem registerRace_nested (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (rid : Nat)
    (owned : FrameCodeOwned m f)
    (park : (interpOf p table).parkOf f.frame.current = some (.ok (.race rid))) :
    Nested p table (registerRace m f yielding rid) := by
  obtain ⟨race, lookup, host⟩ := raceCodeOwned_park_host p table m f.id f.frame.current rid owned.1 park
  have ridEq := race_id_of_lookup lookup
  simp only [registerRace, lookup]
  refine .registration rfl rid { race with registering := true } ?_ host park rfl
  simp only [race_lookup_updateRace, lookup, Option.map_some, ridEq, ↓reduceIte]

theorem evaluatePrim_nested (p : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (owned : FrameCodeOwned m f)
    (parkEq : interp.parkOf = (interpOf p table).parkOf) :
    Nested p table (evaluatePrim interp m f yielding) := by
  fun_cases evaluatePrim interp m f yielding
  case case5 =>
    apply registerRace_nested p table m f yielding _ owned
    rw [← parkEq]
    assumption
  case case10 => exact withFiber_nested p table interp m f yielding _
  case case11 | case16 => exact stepFrame_nested p table interp m f yielding
  case case2 | case12 =>
    apply Nested.simple
    simp only [AllSimple, Simple, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  case case14 | case15 => exact finalizerOr_nested p table interp m f yielding _
  all_goals exact .simple allSimple_nil

theorem exitScoped_nested (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (exit : ExitV)
    (owned : FrameCodeOwned m f) :
    Nested p table (exitScoped p m f yielding exit) := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_nested _ _ _ _ _ _ owned rfl
    | exact .simple allSimple_nil
    | split

theorem evaluateNative_nested (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (owned : FrameCodeOwned m f) :
    Nested p table (evaluateNative p m f yielding table) := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_nested _ _ _ _ _ _ owned rfl
    | exact exitScoped_nested _ _ _ _ _ _ owned
    | exact .simple allSimple_nil
    | split

/-- Only existence of an identifier, independent of the stored fiber's fields. -/
def Present (m : NativeMachine) (id : FiberId) : Prop := ∃ g ∈ m.fibers, g.id = id

theorem present_lookup {m : NativeMachine} {id : FiberId} {g : NFiber}
    (h : m.fiber? id = some g) : Present m id :=
  ⟨g, List.mem_of_find?_eq_some h, fiber_id_of_lookup h⟩

theorem lookup_present {m : NativeMachine} {id : FiberId} (h : Present m id) :
    ∃ g, m.fiber? id = some g := by
  obtain ⟨g, hg, gid⟩ := h
  cases hl : m.fiber? id with
  | some found => exact ⟨found, rfl⟩
  | none =>
    have miss := List.find?_eq_none.mp hl g hg
    simp [gid] at miss

theorem present_update (m : NativeMachine) (g : NFiber) (id : FiberId)
    (h : Present m id) : Present (m.update g) id := by
  obtain ⟨old, hm, hi⟩ := h
  refine ⟨if old.id = g.id then g else old, List.mem_map.mpr ⟨old, hm, rfl⟩, ?_⟩
  split
  · next he => exact he.symm.trans hi
  · exact hi

theorem present_modify (m : NativeMachine) (target id : FiberId) (fn : NFiber → NFiber)
    (h : Present m id) : Present (m.modify target fn) id := by
  unfold RunMachine.modify
  split
  · exact h
  · exact present_update _ _ _ h

theorem present_append (m : NativeMachine) (extra : List NFiber) (id : FiberId)
    (h : Present m id) : Present {m with fibers := m.fibers ++ extra} id := by
  obtain ⟨g, hm, hi⟩ := h
  exact ⟨g, List.mem_append_left _ hm, hi⟩

theorem present_map (m : NativeMachine) (fn : NFiber → NFiber) (id : FiberId)
    (same : ∀ g, (fn g).id = g.id) (h : Present m id) :
    Present {m with fibers := m.fibers.map fn} id := by
  obtain ⟨g, hm, hi⟩ := h
  exact ⟨fn g, List.mem_map.mpr ⟨g, hm, rfl⟩, (same g).trans hi⟩

/-- Forward lookup classification supplies the existing identifier-presence observation. -/
theorem present_of_lookupEdits {m n : NativeMachine} (edits : Moves.LookupEdits m n)
    (id : FiberId) (present : Present m id) : Present n id := by
  obtain ⟨old, found⟩ := lookup_present present
  obtain ⟨next, lookup, _⟩ := edits id old found
  exact present_lookup lookup

theorem present_forkFinalizers (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (programs : List NCode) (id : FiberId) (h : Present m id) :
    Present (forkFinalizers interp m f programs).1 id := by
  exact present_of_lookupEdits (Moves.InterferesWithLookup.forkFinalizers interp f m programs).lookup id h


theorem present_linkScope (interp : NInterp) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (id : FiberId)
    (h : Present m id) : Present (linkScope interp m mode scope target who extra).1 id := by
  exact present_of_lookupEdits (Moves.InterferesWithLookup.linkScope interp m mode scope target who extra).lookup id h


theorem stepFrame_present (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (id : FiberId) (h : Present m id) :
    Present (evaluatePrim.stepFrame interp m f yielding).machine id := by
  exact present_of_lookupEdits (Moves.stepFrame_interference interp m f yielding).lookup id h


theorem finalizerOr_present (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (id : FiberId) (h : Present m id) :
    Present (evaluatePrim.finalizerOr interp m f yielding exit).machine id := by
  exact present_of_lookupEdits (Moves.finalizerOr_interference interp m f yielding exit).lookup id h


theorem withFiber_present (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (action : Effect4.Program.Guard.ReturnFields.NAction)
    (id : FiberId) (h : Present m id) :
    Present (evaluatePrim.withFiber interp m f yielding action).machine id := by
  exact present_of_lookupEdits (Moves.withFiber_interference interp m f yielding action).lookup id h


theorem countdown_present (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool)
    (id : FiberId) (h : Present m id) :
    Present (countdownPark interp m f targets resumeWith failFast).1 id := by
  exact present_of_lookupEdits (Moves.InterferesWithLookup.countdownPark interp m f targets resumeWith failFast).lookup id h


theorem evaluatePrim_present (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (id : FiberId) (h : Present m id) :
    Present (evaluatePrim interp m f yielding).machine id := by
  exact present_of_lookupEdits (Moves.evaluatePrim_interference interp m f yielding).lookup id h


theorem exitScoped_present (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (id : FiberId) (h : Present m id) :
    Present (exitScoped p m f yielding exit).machine id := by
  exact present_of_lookupEdits (Moves.exitScoped_interference p m f yielding exit).lookup id h


theorem evaluateNative_present (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId)
    (h : Present m id) : Present (evaluateNative p m f yielding table).machine id := by
  exact present_of_lookupEdits (Moves.evaluateNative_interference p table m f yielding).lookup id h

/-- Queue safety together with the only possible command owner. -/
structure GeneratedQueue (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (commands : List NCmd) : Prop where
  queue : GuardQueue p table m commands
  owner : ∀ who ∈ commands.filterMap (commandOwner m), who = id

theorem simple_fields (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (c : NCmd) (simple : Simple c) :
    CommandAuthority p table m c ∧ commandOwner m c = none ∧
      commandKeys c = [] ∧ commandRaceSites c = [] := by
  cases c <;> simp_all [Simple, CommandAuthority, commandOwner, commandKeys, commandRaceSites]

theorem simple_owners (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (cs : List NCmd) (simple : AllSimple cs) : cs.filterMap (commandOwner m) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro c hc
  exact (simple_fields p table m c (simple c hc)).2.1

theorem simple_keys (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (cs : List NCmd) (simple : AllSimple cs) : cs.flatMap commandKeys = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro c hc
  exact (simple_fields p table m c (simple c hc)).2.2.1

theorem generatedQueue_simple (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (cs : List NCmd) (simple : AllSimple cs) : GeneratedQueue p table m id cs := by
  have owners := simple_owners p table m cs simple
  have keys := simple_keys p table m cs simple
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc; exact (simple_fields p table m c (simple c hc)).1
  · rw [owners]; exact List.nodup_nil
  · rw [keys]; exact reservedKeys_nil m
  · intro c hc; exact (simple_fields p table m c (simple c hc)).2.2.2
  · simp only [owners, List.not_mem_nil, false_implies, implies_true]

theorem generatedQueue_append_one (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (cs : List NCmd) (last : NCmd) (simple : AllSimple cs)
    (authority : CommandAuthority p table m last) (owner : commandOwner m last = some id)
    (keys : commandKeys last = []) (sites : commandRaceSites last = []) :
    GeneratedQueue p table m id (cs ++ [last]) := by
  have ownerList : (cs ++ [last]).filterMap (commandOwner m) = [id] := by
    simp only [List.filterMap_append, simple_owners p table m cs simple,
      List.filterMap_cons, owner, List.filterMap_nil, List.nil_append]
  have keyList : (cs ++ [last]).flatMap commandKeys = [] := by
    simp only [List.flatMap_append, simple_keys p table m cs simple,
      List.flatMap_cons, keys, List.flatMap_nil, List.nil_append]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (simple_fields p table m c (simple c hc)).1
    · exact (List.mem_singleton.mp hc) ▸ authority
  · rw [ownerList]; simp
  · rw [keyList]; exact reservedKeys_nil m
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (simple_fields p table m c (simple c hc)).2.2.2
    · exact (List.mem_singleton.mp hc) ▸ sites
  · intro who hw; exact List.mem_singleton.mp (ownerList ▸ hw)

theorem local_fields (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (c : NCmd) (isLocal : Local id c) (active : ActiveAt m id) :
    CommandAuthority p table m c ∧ commandOwner m c = some id ∧
      commandKeys c = [] ∧ commandRaceSites c = [] := by
  cases c <;> simp only [Local] at isLocal
  all_goals repeat' first
    | contradiction
    | (solve | subst_vars; exact ⟨active, rfl, rfl, rfl⟩)
    | split at isLocal
  all_goals simp_all [CommandAuthority, commandOwner, commandKeys, commandRaceSites]

theorem active_update (m : NativeMachine) (f : NFiber) (present : Present m f.id)
    (running : f.running = true) (park : f.parked = .notParked) :
    ActiveAt (m.update f) f.id := by
  obtain ⟨old, lookup⟩ := lookup_present present
  exact ⟨f, fiber_lookup_update_self lookup f rfl, running, park⟩

theorem generatedQueue_registration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (rid : Nat) (race : NRace)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (parked : f.parked = .notParked) (raceLookup : m.race? rid = some race)
    (host : race.host = f.id)
    (park : (interpOf p table).parkOf f.frame.current = some (.ok (.race rid))) :
    GeneratedQueue p table m f.id [.launch rid, .registrationDone rid yielding] := by
  have active : ActiveAt m f.id := ⟨f, lookup, running, parked⟩
  have launch : CommandAuthority p table m (.launch rid) := ⟨race, raceLookup, host ▸ active⟩
  have done : CommandAuthority p table m (.registrationDone rid yielding) :=
    ⟨race, f, raceLookup, host ▸ lookup, running, parked, park⟩
  have owners : ([.launch rid, .registrationDone rid yielding] : List NCmd).filterMap
      (commandOwner m) = [f.id] := by
    simp only [List.filterMap_cons, commandOwner, raceLookup, Option.map_some,
      host, List.filterMap_nil]
  refine ⟨⟨?_, ?_, reservedKeys_nil m, ?_⟩, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact launch
    · exact done
  · rw [owners]; simp
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  · intro who hw; exact List.mem_singleton.mp (owners ▸ hw)

theorem settleOutcome_generatedQueue (p : NativeEff) (table : RowTable) (it : NIter)
    (nested : Nested p table it) (present : Present it.machine it.fiber.id)
    (running : it.fiber.running = true) (ready : ReadyOutcome it) :
    GeneratedQueue p table (settleOutcome it.fiber.id [] it).1 it.fiber.id
      (settleOutcome it.fiber.id [] it).2 := by
  cases nested with
  | simple simple =>
    cases ho : it.outcome <;> simp only [settleOutcome, ho, List.append_nil]
    case continue_ | answered | finished =>
      have park : it.fiber.parked = .notParked := by simpa only [ReadyOutcome, ho] using ready
      exact generatedQueue_append_one p table _ _ _ _ simple
        (active_update _ _ present running park) rfl rfl rfl
    case commands => exact generatedQueue_simple p table _ _ _ simple
    case stuck why => exact generatedQueue_simple p table _ _ _ allSimple_nil
    case parked =>
      split
      · exact generatedQueue_append_one p table _ _ _ _ simple
          (active_update _ _ present running rfl) rfl rfl rfl
      · exact generatedQueue_simple p table _ _ _ simple
  | owned outcome front last commands simple isLocal =>
    have park : it.fiber.parked = .notParked := by simpa only [ReadyOutcome, outcome] using ready
    have active := active_update _ _ present running park
    have fields := local_fields p table _ _ last isLocal active
    simpa only [settleOutcome, outcome, List.append_nil, commands] using
      generatedQueue_append_one p table _ _ _ last simple fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
  | registration outcome rid race raceLookup host park commands =>
    have parked : it.fiber.parked = .notParked := by simpa only [ReadyOutcome, outcome] using ready
    obtain ⟨old, lookup⟩ := lookup_present present
    have result := generatedQueue_registration p table (it.machine.update it.fiber) it.fiber
      it.yielding rid race (fiber_lookup_update_self lookup it.fiber rfl) running parked raceLookup host park
    simpa only [settleOutcome, outcome, List.append_nil, commands] using result

/-- Scheduler messages prepend owner-free commands to the existing generated queue. -/
theorem generatedQueue_prepend (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (front rest : List NCmd) (simple : AllSimple front)
    (held : GeneratedQueue p table m id rest) :
    GeneratedQueue p table m id (front ++ rest) := by
  have owners := simple_owners p table m front simple
  refine ⟨guardQueue_append_noOwners p table
    (generatedQueue_simple p table m id front simple).queue held.queue owners, ?_⟩
  simpa only [List.filterMap_append, owners, List.nil_append] using held.owner

/-- Disposition either retains the simple message prefix or discards the whole queue. -/
theorem settleOutcome_generatedQueue_prepend (p : NativeEff) (table : RowTable)
    (it : NIter) (front : List NCmd) (simple : AllSimple front)
    (held : GeneratedQueue p table (settleOutcome it.fiber.id [] it).1 it.fiber.id
      (settleOutcome it.fiber.id [] it).2) :
    GeneratedQueue p table (settleOutcome it.fiber.id [] {it with nested := front ++ it.nested}).1
      it.fiber.id (settleOutcome it.fiber.id [] {it with nested := front ++ it.nested}).2 := by
  cases outcome : it.outcome <;> simp only [settleOutcome, outcome, List.append_nil] at held ⊢
  case stuck why => exact held
  case parked =>
    split <;> rename_i deferred
    all_goals simp only [deferred, ↓reduceIte] at held
    · simpa only [List.append_assoc] using generatedQueue_prepend p table _ _ _ _ simple held
    · exact generatedQueue_prepend p table _ _ _ _ simple held
  all_goals simpa only [List.append_assoc] using
    generatedQueue_prepend p table _ _ _ _ simple held

/-- Actual addressed edits retain the running owner's command fields before disposition. -/
theorem settle_generatedQueue (p : NativeEff) (table : RowTable) (it : NIter)
    (nested : Nested p table it) (present : Present it.machine it.fiber.id)
    (running : it.fiber.running = true) (ready : ReadyOutcome it) :
    GeneratedQueue p table (settle it.fiber.id [] it).1 it.fiber.id
      (settle it.fiber.id [] it).2 := by
  cases edits : it.edits with
  | nil =>
    simpa only [settle, edits] using
      settleOutcome_generatedQueue p table it nested present running ready
  | cons message tail =>
    obtain ⟨old, found⟩ := lookup_present present
    have installed := fiber_lookup_update_self found it.fiber rfl
    obtain ⟨owner, ownerFound, word⟩ :=
      (Moves.InterferesWithLookup.fiberEdits it.edits (it.machine.update it.fiber)).lookup
        it.fiber.id it.fiber installed
    have fields := word.controls (Or.inl running)
    have sameId := word.id
    let next : NIter := {it with machine := (applyFiberEdits it.edits
      (it.machine.update it.fiber)).1, fiber := owner, edits := []}
    have nextNested : Nested p table next := by
      cases nested with
      | simple simple => exact .simple simple
      | owned outcome front last commands simple isLocal =>
        refine .owned outcome front last commands simple ?_
        simpa only [next, sameId] using isLocal
      | registration outcome rid race raceLookup host park commands =>
        refine .registration outcome rid race ?_ ?_ ?_ commands
        · have races := congrArg (fun m : NativeMachine => m.races)
            (RunMachine.applyFiberEdits_shape it.edits (it.machine.update it.fiber)).1
          change (applyFiberEdits it.edits (it.machine.update it.fiber)).1.race? rid = some race
          unfold RunMachine.race?
          rw [races]
          exact raceLookup
        · simpa only [next, sameId] using host
        · simpa only [next, fields.1] using park
    have nextReady : ReadyOutcome next := by
      cases outcome : it.outcome <;>
        simp only [ReadyOutcome, next, outcome] at ready ⊢
      all_goals exact fields.2.1.trans ready
    have nextPresent : Present next.machine next.fiber.id := by
      simpa only [next, sameId] using present_lookup ownerFound
    have held := settleOutcome_generatedQueue p table next nextNested nextPresent
      (fields.2.2.2 running) nextReady
    have simple : AllSimple (applyFiberEdits it.edits (it.machine.update it.fiber)).2 := by
      intro command member
      obtain ⟨target, same⟩ := (RunMachine.applyFiberEdits_shape it.edits
        (it.machine.update it.fiber)).2 command member
      subst command
      exact True.intro
    have combined := settleOutcome_generatedQueue_prepend p table next _ simple held
    rw [edits] at ownerFound
    simpa only [settle, edits, ownerFound, next, sameId] using combined

theorem iteration_nested (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (owned : FrameCodeOwned m f) :
    letI := evaluatorFor p table
    Nested p table (iteration (interpOf p table) m f yielding) := by
  letI := evaluatorFor p table
  have top : FrameCodeOwned m (countOp (runloopTop f)) :=
    Effect4.Program.Guard.FrameOwned.runloopTop_owned m f owned
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using evaluateNative_nested p table m _ yielding top
  | some it =>
    have injected := Effect4.Program.Guard.FrameOwned.injectYield_owned m _ yielding it top hi
    simpa only [iteration, hi] using evaluateNative_nested p table it.machine it.fiber it.yielding
      injected.1

theorem injectYield_present (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (id : FiberId) (it : NIter) (present : Present m id)
    (injected : injectYield m f yielding = some it) : Present it.machine id := by
  unfold injectYield at injected
  split at injected
  · cases injected; exact present
  · cases injected

theorem iteration_present (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId)
    (h : Present m id) :
    letI := evaluatorFor p table
    Present (iteration (interpOf p table) m f yielding).machine id := by
  letI := evaluatorFor p table
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none => simpa only [iteration, hi] using evaluateNative_present p table m _ yielding id h
  | some it =>
    have present := injectYield_present m _ yielding id it h hi
    simpa only [iteration, hi] using evaluateNative_present p table it.machine it.fiber it.yielding id present

/-- Internal native settlement certificate with exactly the requested old-state premises. -/
theorem evaluateNative_generatedQueue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    GeneratedQueue p table (settle f.id [] (evaluateNative p m f yielding table)).1 f.id
      (settle f.id [] (evaluateNative p m f yielding table)).2 := by
  have owned := state.frameCodes f (List.mem_of_find?_eq_some lookup)
  have present := evaluateNative_present p table m f yielding f.id (present_lookup lookup)
  have id := Effect4.Program.Guard.Interruption.evaluateNative_id p table m f yielding
  have after := settle_generatedQueue p table (evaluateNative p m f yielding table)
    (evaluateNative_nested p table m f yielding owned) (id.symm ▸ present)
    ((evaluateNative_running p table m f yielding).trans running)
    (evaluateNative_ready p table m f yielding park)
  simpa only [id] using after

/-- Internal native iteration settlement certificate, including the sole-owner conclusion. -/
theorem iteration_generatedQueue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    GeneratedQueue p table (settle f.id [] (iteration (interpOf p table) m f yielding)).1 f.id
      (settle f.id [] (iteration (interpOf p table) m f yielding)).2 := by
  letI := evaluatorFor p table
  have owned := state.frameCodes f (List.mem_of_find?_eq_some lookup)
  have present := iteration_present p table m f yielding f.id (present_lookup lookup)
  have id := Effect4.Program.Guard.Interruption.iteration_id p table m f yielding
  have after := settle_generatedQueue p table (iteration (interpOf p table) m f yielding)
    (iteration_nested p table m f yielding owned) (id.symm ▸ present)
    ((iteration_running p table m f yielding).trans running)
    (iteration_ready p table m f yielding park)
  simpa only [id] using after

/-- Generated commands only: no old tail and no machine-state preservation premise. -/
theorem evaluateNative_guardQueue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    GuardQueue p table (settle f.id [] (evaluateNative p m f yielding table)).1
      (settle f.id [] (evaluateNative p m f yielding table)).2 :=
  (evaluateNative_generatedQueue p table m f yielding state lookup running park).queue

theorem evaluateNative_commandOwners (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    ∀ owner ∈ (settle f.id [] (evaluateNative p m f yielding table)).2.filterMap
      (commandOwner (settle f.id [] (evaluateNative p m f yielding table)).1), owner = f.id :=
  (evaluateNative_generatedQueue p table m f yielding state lookup running park).owner

theorem iteration_guardQueue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    GuardQueue p table (settle f.id [] (iteration (interpOf p table) m f yielding)).1
      (settle f.id [] (iteration (interpOf p table) m f yielding)).2 :=
  (iteration_generatedQueue p table m f yielding state lookup running park).queue

theorem iteration_commandOwners (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    ∀ owner ∈ (settle f.id [] (iteration (interpOf p table) m f yielding)).2.filterMap
      (commandOwner (settle f.id [] (iteration (interpOf p table) m f yielding)).1), owner = f.id :=
  (iteration_generatedQueue p table m f yielding state lookup running park).owner

end Effect4.Program.Guard.ReturnCommands
