import Effect4.Api

/-!
# Laws.Program.Guard.RaceSites: where a code can park on a race, and who owns it

The race sites of a code (`raceSites`, `stepRaceSites`, `actionRaceSites`), the ownership
predicates over them (`RaceCodeOwned`, `RaceIdsBelow`, `FrameCodeOwned`, `RaceHostsPreserved`,
`DeferredCodes`, `StoredCodeNoRace`, `HooksNoRace`) and the lemmas that every compiled code, hook
and stored answer registers no race. Stated once. `Guard/Core.lean` (the reachable-machine
induction) and `Guard/FrameOwned.lean` (the returned-frame ownership) both build on it. Until
2026-09-17 each carried its own copy of these fifty-nine declarations, and `Guard/Settle.lean`
carried three lemmas whose only work was to prove the two copies equal.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Effect4.Program.Guard

open Effect4 Effect4.Machine Effect4.Program

abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx

def raceSites : NCode → List Nat
  | .suspend (.park (.race race)) => [race]
  | .suspend (.store (.park (.race race))) => [race]
  | .onSuccess body _ => raceSites body
  | .onSuccessConst body next => raceSites body ++ raceSites next
  | .onFailure body _ => raceSites body
  | .onSuccessAndFailure body _ _ => raceSites body
  | .exitFrame body => raceSites body
  | .onExit body _ _ => raceSites body
  | _ => []

theorem raceSites_ofExit (exit : ExitV) : raceSites (Prim.ofExit exit) = [] := by
  cases exit <;> rfl

theorem raceSites_asyncRoute (op : NativeOp) (request : Term) (p : Point) :
    raceSites (asyncRoute op request p) = [] := by
  unfold asyncRoute
  split
  · split <;> rfl
  · repeat' first | split | rfl
  · repeat' first | split | rfl

theorem raceSites_compileEff (e : NativeEff) (p : Point) :
    raceSites (compileEff e p) = [] := by
  cases p
  rename_i path env fuel tape completed root
  cases e <;> cases fuel <;> unfold compileEff <;> dsimp only
  all_goals repeat' first
    | rfl
    | exact raceSites_asyncRoute _ _ _
    | exact raceSites_ofExit _
    | exact raceSites_compileEff _ _
    | split
termination_by sizeOf e
decreasing_by all_goals simp_all <;> decreasing_tactic

theorem raceSites_resolve (root : NativeEff) (p : Point) :
    raceSites (resolve root p) = [] := by
  unfold resolve
  split
  · exact raceSites_compileEff _ _
  · rfl

theorem raceSites_compileLayer (layer : LayerTerm NativeOp) (p : Point)
    (memo : MemoMapId) (scope : Nat) :
    raceSites (compileLayer layer p memo scope) = [] := by
  cases layer <;> simp only [compileLayer]
  all_goals first
    | exact raceSites_compileLayer _ _ _ _
    | rfl
    | (split <;> rfl)
termination_by sizeOf layer

theorem raceSites_resolveLayer (root : NativeEff) (p : Point) (memo : MemoMapId)
    (scope : Nat) : raceSites (resolveLayer root p memo scope) = [] := by
  unfold resolveLayer
  split
  · unfold resolveLayer.resolveLayerTerm
    repeat' first | split | exact raceSites_compileLayer _ _ _ _ | rfl
  · rfl

theorem raceSites_embed_ofExit (exit : ExitV) :
    raceSites (embed (Prim.ofExit exit)) = [] := by
  cases exit <;> rfl

theorem raceSites_finProgram (fin : FinName) (exit : ExitV) :
    raceSites (embed (finProgram fin exit)) = [] := by
  cases fin <;> unfold finProgram
  all_goals repeat' first | rfl | split

theorem raceSites_progOf (program : ProgName) : raceSites (embed (progOf program)) = [] := by
  cases program <;> unfold progOf
  all_goals repeat' first
    | rfl
    | exact raceSites_finProgram _ _
    | exact raceSites_progOf _
    | split
termination_by sizeOf program
decreasing_by all_goals simp_all <;> decreasing_tactic

theorem raceSites_store_contA (name : Name) (value : Val) :
    raceSites (embed (Effect4.Machine.contAOf name value)) = [] := by
  cases name <;> unfold Effect4.Machine.contAOf
  all_goals repeat' first
    | rfl
    | exact raceSites_embed_ofExit _
    | exact raceSites_progOf _
    | split

theorem raceSites_store_contE (name : Name) (cause : CauseV) :
    raceSites (embed (Effect4.Machine.contEOf name cause)) = [] := by
  cases name <;> unfold Effect4.Machine.contEOf
  all_goals first | rfl | exact raceSites_embed_ofExit _

theorem raceSites_completion (answer : Completion Val Err Defect FiberId Ann) :
    raceSites (embed (completionPrim answer)) = [] := by
  cases answer
  · exact raceSites_embed_ofExit _
  · rfl

theorem raceSites_cancelProgram (name : Name) :
    raceSites (embed (cancelProgram name)) = [] := by
  unfold cancelProgram
  repeat' first | rfl | split

theorem raceSites_cancelProgramOf (name : EffName) : raceSites (cancelProgramOf name) = [] := by
  unfold cancelProgramOf
  repeat' first | rfl | exact raceSites_cancelProgram _ | split

theorem raceSites_innerLayerAt (root : NativeEff) (p : Point) (memo : MemoMapId)
    (scope : Nat) : raceSites (innerLayerAt root p memo scope) = [] := by
  unfold innerLayerAt
  repeat' first
    | rfl
    | exact raceSites_resolveLayer _ _ _ _
    | exact raceSites_compileLayer _ _ _ _
    | split

theorem raceSites_regionCode (root : NativeEff) (region : Region) :
    raceSites (regionCode root region) = [] := by
  cases region <;> first
    | exact raceSites_resolve _ _
    | exact raceSites_resolveLayer _ _ _ _

theorem raceSites_contEOf (root : NativeEff) (name : EffName) (cause : CauseV) :
    raceSites (Effect4.Program.contEOf root name cause) = [] := by
  cases name <;> unfold Effect4.Program.contEOf
  all_goals repeat' first
    | rfl
    | exact raceSites_resolve _ _
    | exact raceSites_ofExit _
    | exact raceSites_store_contE _ _
    | split

set_option maxHeartbeats 800000 in
theorem raceSites_contAOf (root : NativeEff) (name : EffName) (value : Val) :
    raceSites (Effect4.Program.contAOf root name value) = [] := by
  cases name <;> unfold Effect4.Program.contAOf
  all_goals try simp only [raceSites, provideLayerWithK, provideLayerBodyK,
    updateThenK, buildWithScopeK, addCurrentMemoMapK, provideThenK, combineWithK,
    mergeContextsK, serviceLookupK, bindServiceK, constructionAt]
  all_goals repeat' first
    | simp only [raceSites, raceSites_resolve, raceSites_resolveLayer,
        raceSites_innerLayerAt, raceSites_regionCode, raceSites_ofExit,
        raceSites_store_contA, raceSites_finProgram]
    | rfl
    | split

theorem raceSites_suspendBodyAt (root : NativeEff) (thunk : EffThunk) :
    raceSites (suspendBodyAt root thunk) = [] := by
  cases thunk <;> unfold suspendBodyAt
  all_goals repeat' first
    | rfl
    | exact raceSites_resolve _ _
    | exact raceSites_compileEff _ _
    | exact raceSites_progOf _
    | split

def stepRaceSites : IterStep EffName EffThunk Val Err Defect FiberId Ann → List Nat
  | .resume next _ => raceSites next
  | _ => []

theorem raceSites_runStmts_yieldOf (root : NativeEff) (p : Point) (e : NativeEff)
    (bind : Bool) (fuel : Nat) (pc : List Nat) (env folded : List Val)
    (ih : ∀ pc env folded, stepRaceSites (runStmts root p fuel pc env folded).2 = []) :
    stepRaceSites (runStmts.yieldOf root p e bind fuel pc env folded).2 = [] := by
  have hc := raceSites_compileEff e
    { p with path := p.path ++ [0] ++ pc ++ [0, 0], env, fuel := fuel + 1 }
  cases bind <;>
    cases hcode : compileEff e
      { p with path := p.path ++ [0] ++ pc ++ [0, 0], env, fuel := fuel + 1 } <;>
    simp only [runStmts.yieldOf, hcode, stepRaceSites]
  all_goals first
    | exact ih _ _ _
    | simpa only [hcode] using hc

theorem raceSites_runStmts (root : NativeEff) (p : Point) (fuel : Nat)
    (pc : List Nat) (env folded : List Val) :
    stepRaceSites (runStmts root p fuel pc env folded).2 = [] := by
  induction fuel generalizing pc env folded with
  | zero => unfold runStmts; rfl
  | succ fuel ih =>
    unfold runStmts
    repeat' first
      | rfl
      | exact ih _ _ _
      | exact raceSites_runStmts_yieldOf root p _ _ fuel _ _ _ ih
      | split

theorem raceSites_closeDone (reasons : List (Reason Err Defect FiberId Ann)) :
    stepRaceSites (embedStep (closeDone reasons)) = [] := by
  cases reasons <;> rfl

theorem raceSites_closeSeqStep (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val) :
    stepRaceSites (embedStep (closeSeqStep remaining exit captured value)) = [] := by
  cases remaining
  · exact raceSites_closeDone _
  · exact raceSites_finProgram _ _

theorem raceSites_store_iterNext (name : Name) (value : Val) :
    stepRaceSites (embedStep (stores.iterNext name value).2) = [] := by
  cases name <;> first
    | rfl
    | exact raceSites_closeDone _
    | exact raceSites_closeSeqStep _ _ _ _

/-- The precise native hook premises for the independent frame-step lemma. -/
def HooksNoRace (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  (∀ name value, raceSites (interp.contA name value) = []) ∧
  (∀ name cause, raceSites (interp.contE name cause) = []) ∧
  (∀ thunk, raceSites (interp.suspendBody thunk) = []) ∧
  (∀ name cursor, raceSites (interp.loopEnter name cursor).code = [] ∧
    ∀ value, raceSites (interp.loopResume name cursor value).code = []) ∧
  (∀ name cause, raceSites (interp.cancelThenFail name cause) = []) ∧
  (∀ name value, stepRaceSites (interp.iterNext name value).2 = [])

/-- A loop's end registers no race: an exit or the wrong shape. -/
theorem raceSites_loopFinishAt (root : NativeEff) (q : Point) (cursor : Val) :
    raceSites (loopFinishAt root q cursor) = [] := by
  unfold loopFinishAt
  split
  · split <;> rfl
  · rfl

/-- A loop's next move registers no race: its body is a resolved point, its final code an
exit or the wrong shape. -/
theorem raceSites_loopNextAt (root : NativeEff) (q : Point) (cursor : Val) :
    raceSites (loopNextAt root q cursor).code = [] := by
  unfold loopNextAt
  split
  · split
    · exact raceSites_resolve _ _
    · exact raceSites_loopFinishAt _ _ _
    · rfl
  · rfl

theorem raceSites_loopResumeAt (root : NativeEff) (q : Point) (cursor answer : Val) :
    raceSites (loopResumeAt root q cursor answer).code = [] := by
  unfold loopResumeAt
  split
  · split
    · exact raceSites_loopNextAt _ _ _
    · rfl
  · rfl

theorem hooksNoRace_interpOf (root : NativeEff) (table : RowTable) :
    HooksNoRace (interpOf root table).toPrimInterp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact raceSites_contAOf root
  · exact raceSites_contEOf root
  · exact raceSites_suspendBodyAt root
  · intro name cursor
    refine ⟨?_, fun value => ?_⟩
    · cases name with
      | loop p => exact raceSites_loopNextAt root _ cursor
      | _ => rfl
    · cases name with
      | loop p => exact raceSites_loopResumeAt root _ cursor value
      | _ => rfl
  · intro name cause
    exact raceSites_cancelProgramOf name
  · intro name value
    cases name <;> first
      | rfl
      | exact raceSites_runStmts _ _ _ _ _ _
      | exact raceSites_store_iterNext _ _

theorem hooksNoRace_interpAt (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) : HooksNoRace (interpAt root completed table).toPrimInterp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name value
    exact raceSites_contAOf root _ value
  · intro name cause
    exact raceSites_contEOf root _ cause
  · intro thunk
    exact raceSites_suspendBodyAt root _
  · intro name cursor
    refine ⟨?_, fun value => ?_⟩
    · cases name with
      | loop p => exact raceSites_loopNextAt root _ cursor
      | _ => rfl
    · cases name with
      | loop p => exact raceSites_loopResumeAt root _ cursor value
      | _ => rfl
  · intro name cause
    exact raceSites_cancelProgramOf name
  · intro name value
    cases name <;> first
      | rfl
      | exact raceSites_runStmts _ _ _ _ _ _
      | exact raceSites_store_iterNext _ _

def actionRaceSites : NAction → List Nat
  | .fork code _ => raceSites code
  | .forkIn code _ _ => raceSites code
  | .forkScoped code _ => raceSites code
  | .setInterruptible code _ => raceSites code
  | .raceAll codes => codes.flatMap raceSites
  | .closePar codes => codes.flatMap raceSites
  | _ => []

def optionActionRaceSites : Option NAction → List Nat
  | none => []
  | some action => actionRaceSites action

theorem raceSites_actionEntrants (es : Effs NativeOp) (p : Point) :
    (actionAt.entrants es p).flatMap raceSites = [] := by
  cases es with
  | nil => rfl
  | cons e es =>
    simp only [actionAt.entrants, List.flatMap_cons, raceSites_compileEff, List.nil_append]
    exact raceSites_actionEntrants _ _
termination_by sizeOf es

theorem raceSites_actionAt (root : NativeEff) (p : Point) :
    optionActionRaceSites (actionAt root p) = [] := by
  unfold actionAt
  repeat' first
    | rfl
    | dsimp only
    | exact raceSites_resolve _ _
    | exact raceSites_actionEntrants _ _
    | split

theorem raceSites_forkScopedAt (root : NativeEff) (p : Point) (scope : Nat) :
    optionActionRaceSites (forkScopedAt root p scope) = [] := by
  unfold forkScopedAt
  split
  · exact raceSites_resolve _ _
  · rfl

theorem raceSites_actionOf (name : ActionName) :
    actionRaceSites (embedAction (actionOf name)) = [] := by
  cases name <;> unfold actionOf
  all_goals first
    | rfl
    | exact raceSites_progOf _
    | skip
  all_goals change (List.map _ _).flatMap raceSites = []
  all_goals rw [List.flatMap_map, List.flatMap_map]
  all_goals apply List.flatMap_eq_nil_iff.mpr
  all_goals intro x hx
  all_goals first | exact raceSites_progOf _ | exact raceSites_finProgram _ _

theorem raceSites_withFiberOf (root : NativeEff) (table : RowTable) (thunk : EffThunk) :
    optionActionRaceSites ((interpOf root table).withFiberOf thunk) = [] := by
  cases thunk <;> simp only [interpOf]
  all_goals repeat' first
    | rfl
    | exact raceSites_actionAt _ _
    | exact raceSites_forkScopedAt _ _ _
    | exact raceSites_actionOf _
    | exact raceSites_resolve _ _
    | exact raceSites_resolveLayer _ _ _ _
    | split

def RaceCodeOwned (m : NativeMachine) (fiber : FiberId) (code : NCode) : Prop :=
  ∀ raceId ∈ raceSites code, ∃ race, m.race? raceId = some race ∧ race.host = fiber

theorem raceCodeOwned_of_no_sites (m : NativeMachine) (fiber : FiberId) (code : NCode)
    (h : raceSites code = []) : RaceCodeOwned m fiber code := by
  intro raceId hr
  rw [h] at hr
  cases hr

abbrev NRace := Race EffName EffThunk Val Err Defect FiberId Ann

/-- Existing race references retain the same host as bookkeeping changes. -/
def RaceHostsPreserved (m n : NativeMachine) : Prop :=
  ∀ raceId race, m.race? raceId = some race →
    ∃ next, n.race? raceId = some next ∧ next.host = race.host

theorem raceCodeOwned_transport {m n : NativeMachine} (h : RaceHostsPreserved m n)
    {fiber : FiberId} {code : NCode} (owned : RaceCodeOwned m fiber code) :
    RaceCodeOwned n fiber code := by
  intro raceId hr
  obtain ⟨race, hm, hhost⟩ := owned raceId hr
  obtain ⟨next, hn, he⟩ := h raceId race hm
  exact ⟨next, hn, he.trans hhost⟩

theorem raceHostsPreserved_append (m : NativeMachine) (extra : List NRace) :
    RaceHostsPreserved m { m with races := m.races ++ extra } := by
  intro raceId race hm
  refine ⟨race, ?_, rfl⟩
  change m.races.find? (fun r => r.id = raceId) = some race at hm
  simp only [RunMachine.race?, List.find?_append, hm, Option.some_or]

theorem race_id_of_lookup {m : NativeMachine} {raceId : Nat} {race : NRace}
    (h : m.race? raceId = some race) : race.id = raceId :=
  of_decide_eq_true (List.find?_some (p := fun r : NRace => decide (r.id = raceId)) h)

theorem race_lookup_updateRace (m : NativeMachine) (race : NRace) (raceId : Nat) :
    (m.updateRace race).race? raceId =
      (m.race? raceId).map (fun old => if old.id = race.id then race else old) := by
  unfold RunMachine.updateRace RunMachine.race?
  rw [List.find?_map]
  have hp : (fun old : NRace => decide ((if old.id = race.id then race else old).id = raceId)) =
      (fun old : NRace => decide (old.id = raceId)) := by
    funext old
    split <;> simp_all
  rw [show ((fun r : NRace => decide (r.id = raceId)) ∘
      (fun old => if old.id = race.id then race else old)) = _ from hp]

theorem raceHostsPreserved_updateRace {m : NativeMachine} {race : NRace}
    (hr : m.race? race.id = some race) (next : NRace)
    (hid : next.id = race.id) (hhost : next.host = race.host) :
    RaceHostsPreserved m (m.updateRace next) := by
  intro raceId old hold
  by_cases he : old.id = next.id
  · have hlookup : m.race? race.id = some old := by
      simpa only [← hid, ← he, race_id_of_lookup hold] using hold
    have heq : old = race := Option.some.inj (hlookup.symm.trans hr)
    refine ⟨next, ?_, hhost.trans (congrArg Race.host heq.symm)⟩
    simp only [race_lookup_updateRace, hold, Option.map_some, he, ↓reduceIte]
  · refine ⟨old, ?_, rfl⟩
    simp only [race_lookup_updateRace, hold, Option.map_some, he, ↓reduceIte]

def RaceIdsBelow (m : NativeMachine) : Prop :=
  ∀ race ∈ m.races, race.id < m.nextRace

theorem race_lookup_fresh {m : NativeMachine} (bounds : RaceIdsBelow m) :
    m.race? m.nextRace = none := by
  apply List.find?_eq_none.mpr
  intro race hr h
  exact (Nat.ne_of_lt (bounds race hr)) (of_decide_eq_true h)

theorem raceCodeOwned_beginRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (entrants : List NCode)
    (bounds : RaceIdsBelow m) :
    RaceCodeOwned (beginRace (interpOf p table) m f yielding entrants).machine f.id
      (beginRace (interpOf p table) m f yielding entrants).fiber.frame.current := by
  intro raceId hr
  change raceId ∈ [m.nextRace] at hr
  have hid := List.mem_singleton.mp hr
  subst raceId
  let race : NRace := ⟨m.nextRace, f.id, m.nextToken,
    { Supervision.RaceAllState.initial [] with remaining := entrants.length }, false, entrants, false⟩
  refine ⟨race, ?_, rfl⟩
  change (m.races ++ [race]).find? (fun r => r.id = m.nextRace) = some race
  have hf : m.races.find? (fun r => r.id = m.nextRace) = none := race_lookup_fresh bounds
  simp only [List.find?_append, hf, Option.none_or, List.find?_cons,
    show decide (race.id = m.nextRace) = true from decide_eq_true rfl]

def FrameCodeOwned (m : NativeMachine) (f : NFiber) : Prop :=
  RaceCodeOwned m f.id f.frame.current ∧
    ∀ code ∈ f.frame.stack, RaceCodeOwned m f.id code

/-- Deferred completions are native store programs with no scheduler race sites. -/
def StoredCodeNoRace (code : Effect4.Machine.Program) : Prop := raceSites (embed code) = []

def DeferredCodes (d : DeferredStore) : Prop :=
  (∀ cell ∈ d.cells, ∀ code, cell.completion = some code → StoredCodeNoRace code) ∧
    ∀ owed ∈ d.due, StoredCodeNoRace owed.code

theorem deferredCodes_cellAt {d : DeferredStore} (hd : DeferredCodes d) {cell : DeferredKey}
    {c : DeferredCell} (h : d.cellAt cell = some c) :
    ∀ p, c.completion = some p → StoredCodeNoRace p :=
  hd.1 c (List.mem_of_getElem? h)

theorem deferredCodes_make {d : DeferredStore} (hd : DeferredCodes d) : DeferredCodes (d.make).2 := by
  refine ⟨fun cell hc p hp => ?_, hd.2⟩
  simp only [DeferredStore.make, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hd.1 cell hc p hp
  · cases hp

theorem deferredCodes_setCell {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey)
    {c : DeferredCell} (hc : ∀ p, c.completion = some p → StoredCodeNoRace p) :
    DeferredCodes (d.setCell cell c) := by
  refine ⟨fun cell' hc' p hp => ?_, hd.2⟩
  rcases List.mem_or_eq_of_mem_set hc' with hm | rfl
  · exact hd.1 cell' hm p hp
  · exact hc p hp

theorem deferredCodes_register {d : DeferredStore} (hd : DeferredCodes d) (cell : DeferredKey)
    (waiter : FiberId) (token : Nat) :
    DeferredCodes (d.register cell waiter token).1 ∧
      ∀ p, (d.register cell waiter token).2 = some p → StoredCodeNoRace p := by
  unfold DeferredStore.register
  cases hc : d.cellAt cell with
  | none => exact ⟨hd, fun p hp => by cases hp⟩
  | some c =>
    dsimp only
    cases hcomp : c.completion with
    | some effect =>
      dsimp only
      exact ⟨hd, fun p hp => by rw [← Option.some.inj hp]; exact deferredCodes_cellAt hd hc _ hcomp⟩
    | none =>
      dsimp only
      refine ⟨deferredCodes_setCell hd cell (fun p hp => ?_), fun p hp => by cases hp⟩
      simp only at hp
      cases hp

end Effect4.Program.Guard
