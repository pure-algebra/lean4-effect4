import Effect4.Api
import Effect4.Laws.Program.Guard.RaceSites
import Effect4.Laws.Machine.Handles

/-! Native returned-frame race ownership under existing internal invariants.
RaceIdsBelow and FrameCodeOwned express allocation bounds and frame ownership.
Completion data gives every stored answer its race-free code unconditionally. The native
evaluation laws use the two local premises. Settle connects them to the complete GuardState predicate.

Proof graph: frame-site and native-hook lemmas, safe Deferred answers,
and race-host transport establish primitive ownership; scoped entry/exit then
give evaluateNative_frameOwned, lifted through loop-top and yield injection to
iteration_frameOwned. No parent cause or fiber-id proof is duplicated.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program.Guard.FrameOwned
open Effect4 Effect4.Machine Effect4.Program

namespace FrameProof
abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NAnswer := ContAnswer EffName EffThunk Val Err Defect FiberId Ann
abbrev NPop := FramePop EffName EffThunk Val Err Defect FiberId Ann
abbrev NStep := FrameStep EffName EffThunk Val Err Defect FiberId Ann

def frameSites (f : NFrame) : List Nat := raceSites f.current ++ f.stack.flatMap raceSites

/-- The race sites of a pop's answer. -/
def answerSites : NAnswer → List Nat
  | ContAnswer.deferred _ => []
  | ContAnswer.replacement next => raceSites next
  | ContAnswer.frame frame => raceSites frame
  | ContAnswer.empty => []

/-- The race sites of an optional replacement. -/
def optSites : Option (NCode) → List Nat
  | some p => raceSites p
  | none => []

/-- The race sites a pop leaves: its answer's and its fiber's. -/
def popSites (pop : NPop) : List Nat :=
  answerSites pop.answer ++ frameSites pop.fiber

/-- The race sites a step leaves: the running fiber's; an exit has no code sites. -/
def stepSites : NStep → List Nat
  | FrameStep.running f => frameSites f
  | FrameStep.finished _ => []

theorem ensure_fst_sites (frame : NCode)
    (fiber : NFrame) :
    frameSites (frame.ensure fiber).1 ⊆ frameSites fiber := by
  cases frame <;> simp only [Prim.ensure] <;> (repeat' split) <;>
    simp only [frameSites, List.flatMap_cons, raceSites, List.nil_append] <;> sub_tac

theorem ensure_snd_sites (frame : NCode)
    (fiber : NFrame) :
    optSites (frame.ensure fiber).2 = [] := by
  cases frame <;> simp only [Prim.ensure] <;> (repeat' split) <;> rfl

theorem answerOf_sites (frame : NCode) (demand : Effect4.Arm)
    (replacement : Option (NCode))
    (ans : NAnswer)
    (h : frame.answerOf demand replacement = some ans) :
    answerSites ans ⊆ raceSites frame ++ optSites replacement := by
  unfold Prim.answerOf at h
  split at h
  · cases h
    exact List.subset_append_right _ _
  · split at h
    · cases h
      exact List.subset_append_left _ _
    · cases h

theorem passPushed_sites (demand : Effect4.Arm) (skip : Bool)
    (fiber : NFrame) :
    popSites (FrameFiber.passPushed demand skip fiber) ⊆ frameSites fiber := by
  unfold FrameFiber.passPushed
  split
  · next hstack =>
    simp only [popSites, answerSites, List.nil_append]
    exact List.Subset.refl _
  · next pushed below hstack =>
    simp only [popSites]
    have hfib : frameSites fiber =
        raceSites fiber.current ++ (pushed :: below).flatMap (raceSites) := by
      simp only [frameSites, hstack]
    rw [hfib]
    simp only [List.flatMap_cons]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · split
      · next ans hans =>
        split
        · exact List.nil_subset _
        · have := answerOf_sites pushed demand _ ans hans
          rw [ensure_snd_sites, List.append_nil] at this
          refine List.Subset.trans this ?_
          sub_tac
      · exact List.nil_subset _
    · refine List.Subset.trans (ensure_fst_sites pushed _) ?_
      simp only [frameSites]
      sub_tac

theorem joinPushed_sites (demand : Effect4.Arm) (skip : Bool)
    (afterHook : NFrame)
    (rest : List (NCode))
    (tail : NPop) :
    popSites (FrameFiber.joinPushed demand skip afterHook rest tail) ⊆
      frameSites afterHook ++ rest.flatMap (raceSites) ++ popSites tail := by
  have hpp := passPushed_sites demand skip afterHook
  unfold FrameFiber.joinPushed
  split
  · simp only [popSites] at hpp ⊢
    sub_tac
  · simp only [popSites, frameSites, List.flatMap_append] at hpp ⊢
    simp only [List.append_subset] at hpp
    refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
    · refine List.Subset.trans hpp.1 ?_; sub_tac
    · refine List.Subset.trans hpp.2.1 ?_; sub_tac
    · refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans hpp.2.2 ?_; sub_tac
      · sub_tac

theorem popFrom_sites (demand : Effect4.Arm) (skip : Bool) :
    ∀ (frames : List (NCode))
      (fiber : NFrame),
      popSites (FrameFiber.popFrom demand skip frames fiber) ⊆
        frames.flatMap (raceSites) ++ frameSites fiber
  | [], fiber => by
    simp only [FrameFiber.popFrom, popSites, answerSites, List.flatMap_nil, List.nil_append]
    exact List.Subset.refl _
  | frame :: rest, fiber => by
    have hens := ensure_fst_sites frame fiber
    have hpp := passPushed_sites demand skip (frame.ensure fiber).1
    have ih := popFrom_sites demand skip rest (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber
    have hjoin := joinPushed_sites demand skip (frame.ensure fiber).1 rest
      (FrameFiber.popFrom demand skip rest (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber)
    simp only [popSites] at hpp ih hjoin
    have hpf : frameSites (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber ⊆
        frameSites fiber :=
      List.Subset.trans (List.append_subset.mp hpp).2 hens
    simp only [FrameFiber.popFrom, List.flatMap_cons]
    split
    · next ans hans =>
      split
      · simp only [FrameFiber.passOn, popSites]
        refine List.Subset.trans hjoin ?_
        refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
        · refine List.Subset.trans hens ?_; sub_tac
        · sub_tac
        · refine List.Subset.trans ih ?_
          refine List.append_subset.mpr ⟨?_, ?_⟩
          · sub_tac
          · refine List.Subset.trans hpf ?_; sub_tac
      · simp only [popSites]
        have hak := answerOf_sites frame demand _ ans hans
        rw [ensure_snd_sites, List.append_nil] at hak
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · refine List.Subset.trans hak ?_; sub_tac
        · simp only [frameSites, List.flatMap_append]
          simp only [frameSites] at hens
          refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
          · refine List.Subset.trans (List.append_subset.mp hens).1 ?_; sub_tac
          · refine List.Subset.trans (List.append_subset.mp hens).2 ?_; sub_tac
          · sub_tac
    · simp only [FrameFiber.passOn, popSites]
      refine List.Subset.trans hjoin ?_
      refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
      · refine List.Subset.trans hens ?_; sub_tac
      · sub_tac
      · refine List.Subset.trans ih ?_
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · sub_tac
        · refine List.Subset.trans hpf ?_; sub_tac

theorem getCont_sites (self : NFrame) (demand : Effect4.Arm)
    (skip : Bool) : popSites (self.getCont demand skip) ⊆ frameSites self := by
  unfold FrameFiber.getCont
  split
  · simp only [popSites, answerSites, List.nil_append, frameSites]
    exact List.Subset.refl _
  · refine List.Subset.trans (popFrom_sites demand skip self.stack _) ?_
    simp only [frameSites, List.flatMap_nil, List.append_nil]
    sub_tac

/-- A pop that answers with a frame: that frame's race sites and the popped fiber's are the
fiber's. -/
theorem getCont_answer_frame_sites (self : NFrame) (demand : Effect4.Arm)
    (skip : Bool) (frame : NCode)
    (h : (self.getCont demand skip).answer = ContAnswer.frame frame) :
    raceSites frame ⊆ frameSites self ∧
      frameSites (self.getCont demand skip).fiber ⊆ frameSites self := by
  have := getCont_sites self demand skip
  simp only [popSites, h, answerSites, List.append_subset] at this
  exact this

theorem armA_sites (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hb : HooksNoRace interp) (frame : NCode) (value : Val) (provided : Option ExitV)
    (next : NCode) (pushed : List NCode)
    (h : frame.armA interp value provided = some (next, pushed)) :
    raceSites next ++ pushed.flatMap raceSites ⊆ raceSites frame := by
  rcases hb with ⟨hA, hE, hS, hL, hC, hI⟩
  cases frame with
  | onSuccess body name | onSuccessAndFailure body name other =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [raceSites, hA]
  | onSuccessConst body saved =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, raceSites]
    exact List.subset_append_right _ _
  | exitFrame body =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [raceSites]
  | onExit body finalizer flag =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [raceSites_ofExit]
  | whileLoop name cursor =>
    simp only [Prim.armA] at h
    have hR := (hL name cursor).2 value
    split at h
    · next stepped body hr =>
      have hbody : raceSites body = [] := by rw [hr] at hR; exact hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [raceSites, hbody]
    · next code hr =>
      have hcode : raceSites code = [] := by rw [hr] at hR; exact hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [raceSites, hcode]
  | iterator name cursor =>
    cases hi : (interp.iterNext name value).2 with
    | done result =>
      simp only [Prim.armA, hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [raceSites]
    | halt cause =>
      simp only [Prim.armA, hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [raceSites]
    | resume code continueAs =>
      have hz := hI name value
      simp only [hi, stepRaceSites] at hz
      simp only [Prim.armA, hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [raceSites, hz]
  | success _ | failure _ | sync _ | suspend _ | withFiber _ | yieldableError _
  | onFailure _ _ | setInterruptible _ | yieldNowWith _ | async _ _ _ | asyncFinalizer _ =>
    simp only [Prim.armA] at h
    cases h

theorem armE_sites (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hb : HooksNoRace interp) (frame : NCode) (cause : CauseV) (provided : Option ExitV)
    (next : NCode) (pushed : List NCode)
    (h : frame.armE interp cause provided = some (next, pushed)) :
    raceSites next ++ pushed.flatMap raceSites ⊆ raceSites frame := by
  rcases hb with ⟨hA, hE, hS, hL, hC, hI⟩
  cases frame with
  | onFailure body name | onSuccessAndFailure body other name =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [raceSites, hE]
  | exitFrame body =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [raceSites]
  | onExit body finalizer flag =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [raceSites_ofExit]
  | asyncFinalizer name =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split <;> simp [raceSites, hC]
  | success _ | failure _ | sync _ | suspend _ | withFiber _ | yieldableError _ | iterator _ _
  | onSuccess _ _ | onSuccessConst _ _ | setInterruptible _ | whileLoop _ _
  | yieldNowWith _ | async _ _ _ =>
    simp only [Prim.armE] at h
    cases h

theorem resumeValue_sites (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hb : HooksNoRace interp) (self : NFrame) (value : Val) (provided : Option ExitV) :
    stepSites (self.resumeValue interp value provided).1 ⊆ frameSites self := by
  have hg := getCont_sites self Effect4.Arm.contA false
  simp only [popSites] at hg
  unfold FrameFiber.resumeValue
  split
  · exact List.nil_subset _
  · next cause heq =>
    rw [heq] at hg
    simp only [answerSites, List.nil_append, frameSites] at hg
    simp only [stepSites, frameSites, raceSites, List.nil_append]
    exact (List.append_subset.mp hg).2
  · next code heq =>
    rw [heq] at hg
    simp only [answerSites, frameSites, List.append_subset] at hg
    simp only [stepSites, frameSites]
    exact List.append_subset.mpr ⟨hg.1, hg.2.2⟩
  · next frame heq =>
    rw [heq] at hg
    simp only [answerSites, frameSites, List.append_subset] at hg
    split
    · next code pushed harm =>
      have ha := armA_sites interp hb frame value provided code pushed harm
      have ha' := List.Subset.trans ha hg.1
      simp only [List.append_subset] at ha'
      simp only [stepSites, frameSites, List.flatMap_append]
      exact List.append_subset.mpr ⟨ha'.1, List.append_subset.mpr ⟨ha'.2, hg.2.2⟩⟩
    · exact List.nil_subset _

theorem resumeCause_sites (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hb : HooksNoRace interp) (self : NFrame) (cause : CauseV) (provided : Option ExitV) :
    stepSites (self.resumeCause interp cause provided).1 ⊆ frameSites self := by
  have hg := getCont_sites self Effect4.Arm.contE true
  simp only [popSites] at hg
  unfold FrameFiber.resumeCause
  split
  · exact List.nil_subset _
  · next cause' heq =>
    rw [heq] at hg
    simp only [answerSites, List.nil_append, frameSites] at hg
    simp only [stepSites, frameSites, raceSites, List.nil_append]
    exact (List.append_subset.mp hg).2
  · next code heq =>
    rw [heq] at hg
    simp only [answerSites, frameSites, List.append_subset] at hg
    simp only [stepSites, frameSites]
    exact List.append_subset.mpr ⟨hg.1, hg.2.2⟩
  · next frame heq =>
    rw [heq] at hg
    simp only [answerSites, frameSites, List.append_subset] at hg
    split
    · next code pushed harm =>
      have ha := armE_sites interp hb frame cause provided code pushed harm
      have ha' := List.Subset.trans ha hg.1
      simp only [List.append_subset] at ha'
      simp only [stepSites, frameSites, List.flatMap_append]
      exact List.append_subset.mpr ⟨ha'.1, List.append_subset.mpr ⟨ha'.2, hg.2.2⟩⟩
    · exact List.nil_subset _

theorem step_sites (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hb : HooksNoRace interp) (self : NFrame) :
    stepSites (self.step interp).1 ⊆ frameSites self := by
  have hS := hb.2.2.1
  have hL := hb.2.2.2.1
  have hsites : frameSites self = raceSites self.current ++ self.stack.flatMap raceSites := rfl
  unfold FrameFiber.step
  split
  · exact resumeValue_sites interp hb self _ _
  · exact resumeCause_sites interp hb self _ _
  · exact resumeValue_sites interp hb self _ _
  · next thunk heq =>
    simp only [stepSites, frameSites, hS, List.nil_append]
    exact List.subset_append_right _ _
  · next thunk heq =>
    simp only [stepSites, frameSites, hS, List.nil_append]
    exact List.subset_append_right _ _
  · simp only [stepSites, frameSites, raceSites, List.nil_append]
    exact List.subset_append_right _ _
  · next generator cursor heq =>
    split
    · next code pushed harm =>
      have ha := armA_sites interp hb (.iterator generator cursor) cursor none code pushed harm
      simp only [raceSites, List.subset_nil] at ha
      simp only [stepSites, frameSites, List.flatMap_append, ← List.append_assoc, ha, List.nil_append]
      exact List.subset_append_right _ _
    · exact List.Subset.refl _
  · next body name heq =>
    rw [hsites, heq]
    simp only [stepSites, frameSites, raceSites, List.flatMap_cons]
    sub_tac
  · next body saved heq =>
    rw [hsites, heq]
    simp only [stepSites, frameSites, raceSites, List.flatMap_cons]
    sub_tac
  · next body name heq =>
    rw [hsites, heq]
    simp only [stepSites, frameSites, raceSites, List.flatMap_cons]
    sub_tac
  · next body onValue onCause heq =>
    rw [hsites, heq]
    simp only [stepSites, frameSites, raceSites, List.flatMap_cons]
    sub_tac
  · next body heq =>
    rw [hsites, heq]
    simp only [stepSites, frameSites, raceSites, List.flatMap_cons]
    sub_tac
  · next body finalizer flag heq =>
    rw [hsites, heq]
    simp only [stepSites, frameSites, raceSites, List.flatMap_cons]
    sub_tac
  · simp only [stepSites, frameSites, raceSites, List.nil_append]
    exact List.subset_append_right _ _
  · simp only [stepSites, frameSites, raceSites, List.nil_append]
    exact List.subset_append_right _ _
  · exact List.Subset.refl _
  · exact List.Subset.refl _
  · next name cursor heq =>
    have hE := (hL name cursor).1
    split
    · next entered body he =>
      have hbody : raceSites body = [] := by rw [he] at hE; exact hE
      simp only [stepSites, frameSites, hbody, List.flatMap_cons, raceSites, List.nil_append]
      exact List.subset_append_right _ _
    · next code he =>
      have hcode : raceSites code = [] := by rw [he] at hE; exact hE
      simp only [stepSites, frameSites, hcode, List.nil_append]
      exact List.subset_append_right _ _

/-- A running frame step introduces no race registration site under the six
native hook premises. There is no reachability or driver premise here. -/
theorem frame_step_sites (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hb : HooksNoRace interp) (frame next : NFrame)
    (h : (frame.step interp).1 = .running next) :
    frameSites next ⊆ frameSites frame := by
  have hs := step_sites interp hb frame
  simpa only [h, stepSites] using hs

end FrameProof

abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def frameSites (f : NFrame) : List Nat := raceSites f.current ++ f.stack.flatMap raceSites

theorem frameCodeOwned_sites {m : NativeMachine} {f : NFiber} (hf : FrameCodeOwned m f) :
    ∀ rid ∈ frameSites f.frame, ∃ race, m.race? rid = some race ∧ race.host = f.id := by
  intro rid hr
  rcases List.mem_append.mp hr with hc | hs
  · exact hf.1 rid hc
  · obtain ⟨code, hc, hr⟩ := List.mem_flatMap.mp hs
    exact hf.2 code hc rid hr

theorem frameCodeOwned_of_sites {m n : NativeMachine} {f g : NFiber}
    (hf : FrameCodeOwned m f) (hm : RaceHostsPreserved m n) (hid : g.id = f.id)
    (hs : frameSites g.frame ⊆ frameSites f.frame) : FrameCodeOwned n g := by
  have owned : ∀ rid ∈ frameSites g.frame, ∃ race, n.race? rid = some race ∧ race.host = g.id := by
    intro rid hr
    obtain ⟨race, hlook, hhost⟩ := frameCodeOwned_sites hf rid (hs hr)
    obtain ⟨next, hn, hh⟩ := hm rid race hlook
    exact ⟨next, hn, hh.trans (hhost.trans hid.symm)⟩
  constructor
  · intro rid hr
    exact owned rid (List.mem_append_left _ hr)
  · intro code hc rid hr
    exact owned rid (List.mem_append_right _ (List.mem_flatMap.mpr ⟨code, hc, hr⟩))

theorem frameCodeOwned_same_races {m n : NativeMachine} {f g : NFiber}
    (hf : FrameCodeOwned m f) (hm : n.races = m.races) (hid : g.id = f.id)
    (hs : frameSites g.frame ⊆ frameSites f.frame) : FrameCodeOwned n g := by
  apply frameCodeOwned_of_sites hf _ hid hs
  intro rid race hr
  exact ⟨race, by simpa only [RunMachine.race?, hm] using hr, rfl⟩

theorem getCont_frameSites (f : NFrame) (demand : Effect4.Arm) (skip : Bool) :
    frameSites (f.getCont demand skip).fiber ⊆ frameSites f := by
  intro rid hr
  exact FrameProof.getCont_sites f demand skip (List.mem_append_right _ hr)

theorem replace_current_sites (f : NFrame) (code : NCode) (hc : raceSites code = []) :
    frameSites { f with current := code } ⊆ frameSites f := by
  simp only [frameSites, hc, List.nil_append]
  exact List.subset_append_right _ _

theorem raceSites_finalizerCode (interp : NInterp) (exit : ExitV) (code : NCode) :
    raceSites (finalizerCode interp exit code) = raceSites code := by
  cases exit <;> rfl

theorem raceSites_finalizerProgram (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (exit : ExitV) (code : NCode)
    (h : (interpAt p completed table).finalizerProgram name exit = some code) :
    raceSites code = [] := by
  cases name <;> simp only [interpAt, interpOf] at h
  all_goals repeat' first | cases h | split at h
  all_goals first | rfl | exact raceSites_resolve _ _ | exact raceSites_finProgram _ _

theorem raceSites_closeScopeUnsafe (scope : Nat) (exit : ExitV) (mask : Bool)
    (state after : Stores) (program : Option Effect4.Machine.Program)
    (h : storesCloseScopeUnsafe scope exit mask state = some (after, program)) :
    ∀ code, program = some code → raceSites (embed code) = [] := by
  unfold storesCloseScopeUnsafe at h
  cases hsn : scopeCloseSnapshot scope exit state with
  | none => simp [hsn] at h
  | some snapshot =>
    rcases snapshot with ⟨s, strategy, order⟩
    simp only [hsn] at h
    cases h
    intro code hc
    cases order with
    | nil => cases hc
    | cons fin rest =>
      cases rest with
      | nil => cases hc; exact raceSites_finProgram _ _
      | cons fin' rest => cases hc; rfl

theorem raceSites_closeScope (scope : Nat) (exit : ExitV) (mask : Bool)
    (state after : Stores) (code : Effect4.Machine.Program)
    (h : storesCloseScope scope exit mask state = some (after, code)) :
    raceSites (embed code) = [] := by
  unfold storesCloseScope at h
  cases hs : storesCloseScopeUnsafe scope exit mask state with
  | none => simp [hs] at h
  | some pair =>
    rcases pair with ⟨s, program⟩
    cases program with
    | none =>
      simp only [hs, Option.map_some, Option.getD_none, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl
    | some c =>
      simp only [hs, Option.map_some, Option.getD_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact raceSites_closeScopeUnsafe scope exit mask state s (some c) hs c rfl

theorem stepFrame_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (hf : FrameCodeOwned m f) :
    FrameCodeOwned (evaluatePrim.stepFrame (interpAt p completed table) m f yielding).machine
      (evaluatePrim.stepFrame (interpAt p completed table) m f yielding).fiber := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step (interpAt p completed table).toPrimInterp with
  | mk step events =>
    cases step with
    | running next =>
      apply frameCodeOwned_same_races hf <;> try rfl
      exact FrameProof.frame_step_sites _ (hooksNoRace_interpAt p completed table)
        f.frame next (congrArg Prod.fst hs)
    | finished exit =>
      apply frameCodeOwned_same_races hf <;> try rfl
      change frameSites (frameExitState f.frame) ⊆ frameSites f.frame
      unfold frameExitState
      split <;> exact getCont_frameSites _ _ _

theorem finalizerOr_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (exit : ExitV)
    (hf : FrameCodeOwned m f) :
    FrameCodeOwned (evaluatePrim.finalizerOr (interpAt p completed table) m f yielding exit).machine
      (evaluatePrim.finalizerOr (interpAt p completed table) m f yielding exit).fiber := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · rename_i code hc
        apply frameCodeOwned_same_races hf <;> try rfl
        apply List.Subset.trans (replace_current_sites _ _ _) (getCont_frameSites _ _ _)
        rw [raceSites_finalizerCode]
        exact raceSites_finalizerProgram _ _ _ _ _ _ hc
      · exact stepFrame_owned _ _ _ _ _ _ hf
    · exact stepFrame_owned _ _ _ _ _ _ hf

def optionRaceSites : Option NCode → List Nat
  | none => []
  | some code => raceSites code

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] optionRaceSites

theorem M1.deferred_register_sites (d : DeferredStore)
    (cell : DeferredKey) (fid : FiberId) (token : Nat) : ProofGraph.Obligation (
    optionRaceSites ((d.register cell fid token).2.map (fun c => embed (completionPrim c))) = []) := ⟨⟩

theorem deferred_register_sites (d : DeferredStore)
    (cell : DeferredKey) (fid : FiberId) (token : Nat) :
    optionRaceSites ((d.register cell fid token).2.map (fun c => embed (completionPrim c))) = [] := by
  cases (d.register cell fid token).2 with
  | none => rfl
  | some completion => exact raceSites_completion completion

theorem prepareExternalAnswer_sites (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) :
    raceSites (prepareExternalAnswer table current answer state).2 = [] := by
  unfold prepareExternalAnswer
  repeat' first | rfl | exact raceSites_completion _ | split

attribute [aesop norm -1 apply (rule_sets := [Effect4.Stores])]
  deferred_register_sites prepareExternalAnswer_sites

theorem M1.registerAsync_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (fid : FiberId) (token : Nat) (state : Stores) : ProofGraph.Obligation (
    optionRaceSites ((interpAt p completed table).registerAsync name fid token state).2 = []) := ⟨⟩

theorem registerAsync_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (fid : FiberId) (token : Nat) (state : Stores) :
    optionRaceSites ((interpAt p completed table).registerAsync name fid token state).2 = [] := by
  cases name <;> simp only [interpAt, interpOf]
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe [deferred_register_sites, prepareExternalAnswer_sites])

attribute [aesop norm -1 apply (rule_sets := [Effect4.Stores])] registerAsync_sites

theorem M1Origin.beginRace_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (entrants : List NCode)
    (_bounds : RaceIdsBelow m) (_hf : FrameCodeOwned m f) (site : Option (List Nat) := none) : ProofGraph.Obligation (FrameCodeOwned (beginRace (interpAt p completed table) m f yielding entrants site).machine
      (beginRace (interpAt p completed table) m f yielding entrants site).fiber) := ⟨⟩

theorem beginRace_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (entrants : List NCode)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) (site : Option (List Nat) := none) :
    FrameCodeOwned (beginRace (interpAt p completed table) m f yielding entrants site).machine
      (beginRace (interpAt p completed table) m f yielding entrants site).fiber := by
  constructor
  · exact raceCodeOwned_beginRace p table m f yielding entrants bounds site
  · intro code hc
    apply raceCodeOwned_transport (raceHostsPreserved_append m _) (hf.2 code hc)

theorem registerRace_owned (m : NativeMachine) (f : NFiber) (yielding : Bool) (rid : Nat)
    (hf : FrameCodeOwned m f) :
    FrameCodeOwned (registerRace m f yielding rid).machine (registerRace m f yielding rid).fiber := by
  unfold registerRace
  cases hr : m.race? rid with
  | none => exact hf
  | some race =>
    apply frameCodeOwned_of_sites hf
    · apply raceHostsPreserved_updateRace (race := race)
      · simpa only [race_id_of_lookup hr] using hr
      · rfl
      · rfl
    · rfl
    · exact List.Subset.refl _

theorem modify_races (m : NativeMachine) (fid : FiberId) (update : NFiber → NFiber) :
    (m.modify fid update).races = m.races := by
  unfold RunMachine.modify
  split <;> rfl

theorem linkScope_races (interp : NInterp) (m : NativeMachine) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    (linkScope interp m mode scope target interruptor extra).1.races = m.races := by
  unfold linkScope
  repeat' first | rfl | split
  all_goals simp only [RunMachine.emit, modify_races]

theorem forkFinalizers_races (interp : NInterp) (m : NativeMachine) (f : NFiber) (codes : List NCode) :
    (forkFinalizers interp m f codes).1.races = m.races := by
  induction codes generalizing m with
  | nil => rfl
  | cons code rest ih =>
    simpa only [forkFinalizers, spawn, RunMachine.emit] using ih (spawn interp m f code ⟨true, true, .inherit⟩).1

theorem closeScope_hook_sites (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (scope : Nat) (exit : ExitV) (mask : Bool) (fid : FiberId) (state after : Stores) (code : NCode)
    (h : (interpAt p completed table).closeScope scope exit mask fid state = some (after, code)) :
    raceSites code = [] := by
  change (storesCloseScope scope exit mask state).map _ = _ at h
  cases hs : storesCloseScope scope exit mask state with
  | none => simp [hs] at h
  | some pair =>
    rcases pair with ⟨s, c⟩
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact raceSites_closeScope scope exit mask state s c hs

theorem M1Hooks.interruptCode_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (target : FiberId) : ProofGraph.Obligation (
    raceSites ((interpAt p completed table).interruptCode target) = []) := ⟨⟩

theorem M1Hooks.interruptAsCode_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (target who : FiberId) : ProofGraph.Obligation (
    raceSites ((interpAt p completed table).interruptAsCode target who) = []) := ⟨⟩

theorem interruptCode_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (target : FiberId) :
    raceSites ((interpAt p completed table).interruptCode target) = [] := by aesop

theorem interruptAsCode_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (target who : FiberId) :
    raceSites ((interpAt p completed table).interruptAsCode target who) = [] := by aesop

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  interruptCode_sites interruptAsCode_sites
attribute [aesop safe forward (rule_sets := [Effect4.Stores])] closeScope_hook_sites

theorem withFiber_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (action : NAction)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) (ha : actionRaceSites action = []) :
    FrameCodeOwned (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).machine
      (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).fiber := by
  cases action <;> simp only [actionRaceSites] at ha
  case raceAll entrants site =>
    exact beginRace_owned p completed table m f yielding entrants bounds hf site
  all_goals simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start,
    countdownPark, RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
    FrameFiber.setFiberInterruptible]
  all_goals repeat' split
  all_goals apply frameCodeOwned_same_races hf
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add norm simp [RunMachine.emit, modify_races, linkScope_races, forkFinalizers_races,
        frameSites, raceSites, Option.getD_none, Option.getD_some, countdownPark.resumePrim,
        List.flatMap_cons, List.nil_append, ha])
      (add safe apply [replace_current_sites, closeScope_hook_sites])

theorem withFiber_hook_sites (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (thunk : EffThunk) (action : NAction)
    (h : (interpAt p completed table).withFiberOf thunk = some action) : actionRaceSites action = [] := by
  have hs := raceSites_withFiberOf p table thunk
  change optionActionRaceSites ((interpAt p completed table).withFiberOf thunk) = [] at hs
  rw [h] at hs
  exact hs

theorem M1.registerAsync_result_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (fid : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (_h : ((interpAt p completed table).registerAsync name fid token state).2 = some code) : ProofGraph.Obligation (
    raceSites code = []) := ⟨⟩

theorem registerAsync_result_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (fid : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (h : ((interpAt p completed table).registerAsync name fid token state).2 = some code) :
    raceSites code = [] := by
  have hs := registerAsync_sites p completed table name fid token state
  rw [h] at hs
  exact hs

theorem countdownPark_owned (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool)
    (hf : FrameCodeOwned m f) :
    FrameCodeOwned (countdownPark interp m f targets resumeWith failFast).1
      (countdownPark interp m f targets resumeWith failFast).2.1 := by
  unfold countdownPark
  dsimp only
  cases hwalk : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
  | mk exits waiting =>
    cases waiting with
    | none =>
      apply frameCodeOwned_same_races hf <;> try rfl
      apply replace_current_sites
      cases resumeWith <;> rfl
    | some pair =>
      rcases pair with ⟨target, remaining⟩
      apply frameCodeOwned_same_races hf
      · simp only [RunMachine.emit, modify_races]
      · rfl
      · simp only [RunFiber.park, frameSites, raceSites, List.flatMap_cons, List.nil_append]
        exact List.Subset.refl _

theorem M1Results.countdownPark_result_owned (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool)
    (after : NativeMachine) (next : NFiber) (parked : Bool)
    (_hf : FrameCodeOwned m f)
    (_h : countdownPark interp m f targets resumeWith failFast = (after, next, parked)) :
    ProofGraph.Obligation (FrameCodeOwned after next) := ⟨⟩

theorem M1Results.closeScopeUnsafe_some_sites (scope : Nat) (exit : ExitV) (mask : Bool)
    (state after : Stores) (code : Effect4.Machine.Program)
    (_h : storesCloseScopeUnsafe scope exit mask state = some (after, some code)) :
    ProofGraph.Obligation (raceSites (embed code) = []) := ⟨⟩

theorem countdownPark_result_owned (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool)
    (after : NativeMachine) (next : NFiber) (parked : Bool)
    (hf : FrameCodeOwned m f)
    (h : countdownPark interp m f targets resumeWith failFast = (after, next, parked)) :
    FrameCodeOwned after next := by
  simpa only [h] using countdownPark_owned interp m f targets resumeWith failFast hf

theorem closeScopeUnsafe_some_sites (scope : Nat) (exit : ExitV) (mask : Bool)
    (state after : Stores) (code : Effect4.Machine.Program)
    (h : storesCloseScopeUnsafe scope exit mask state = some (after, some code)) :
    raceSites (embed code) = [] := by
  exact raceSites_closeScopeUnsafe scope exit mask state after (some code) h code rfl

attribute [aesop safe forward (rule_sets := [Effect4.Stores])]
  countdownPark_result_owned closeScopeUnsafe_some_sites

theorem exitValue_sites (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (exit : ExitV) (mode : Supervision.ObserverMode) :
    raceSites ((interpAt p completed table).exitValue exit mode) = [] := by
  cases mode
  · rfl
  · exact raceSites_ofExit _

theorem M1.evaluatePrim_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (_bounds : RaceIdsBelow m) (_hf : FrameCodeOwned m f) : ProofGraph.Obligation (
    FrameCodeOwned (evaluatePrim (interpAt p completed table) m f yielding).machine
      (evaluatePrim (interpAt p completed table) m f yielding).fiber) := ⟨⟩

theorem evaluatePrim_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) :
    FrameCodeOwned (evaluatePrim (interpAt p completed table) m f yielding).machine
      (evaluatePrim (interpAt p completed table) m f yielding).fiber := by
  unfold evaluatePrim
  repeat' split
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe apply [stepFrame_owned, finalizerOr_owned, registerRace_owned,
        countdownPark_owned, withFiber_owned])
      (add safe forward [withFiber_hook_sites, registerAsync_result_sites])
      (add norm simp [exitValue_sites, RunFiber.park, RunMachine.emit, frameSites,
        raceSites, List.flatMap_cons, List.nil_append])
      (add safe 50 (by apply frameCodeOwned_same_races hf))

theorem M1.exitScoped_owned (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (_bounds : RaceIdsBelow m)
    (_hf : FrameCodeOwned m f) : ProofGraph.Obligation (
    FrameCodeOwned (exitScoped p m f yielding exit).machine (exitScoped p m f yielding exit).fiber) := ⟨⟩

theorem exitScoped_owned (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (bounds : RaceIdsBelow m)
    (hf : FrameCodeOwned m f) :
    FrameCodeOwned (exitScoped p m f yielding exit).machine (exitScoped p m f yielding exit).fiber := by
  have replaced (demand : Effect4.Arm) (skip : Bool) (code : NCode) (sites : raceSites code = []) :
      frameSites { (f.frame.getCont demand skip).fiber with current := code } ⊆
        frameSites f.frame :=
    List.Subset.trans (replace_current_sites _ code sites) (getCont_frameSites f.frame demand skip)
  cases exit <;> simp only [exitScoped]
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe apply [evaluatePrim_owned, getCont_frameSites, replaced])
      (add norm simp [RunMachine.emit, raceSites_ofExit, raceSites_finalizerCode])
      (add safe 50 (by apply frameCodeOwned_same_races hf))

/-- Internal local ownership: the input frame is owned, allocated race ids are
below nextRace, and completion data supplies race-free answers. No public guard premise changes. -/
theorem M1.evaluateNative_frameOwned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (_bounds : RaceIdsBelow m) (_hf : FrameCodeOwned m f) : ProofGraph.Obligation (
    FrameCodeOwned (evaluateNative p m f yielding table).machine
      (evaluateNative p m f yielding table).fiber) := ⟨⟩

theorem evaluateNative_frameOwned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) :
    FrameCodeOwned (evaluateNative p m f yielding table).machine
      (evaluateNative p m f yielding table).fiber := by
  unfold evaluateNative
  repeat' split
  all_goals
    aesop (rule_sets := [Effect4.Stores])
      (add safe apply [evaluatePrim_owned, exitScoped_owned])
      (add norm simp [enterScoped, frameSites, raceSites, raceSites_resolve])
      (add safe 50 (by apply frameCodeOwned_same_races hf))

theorem runloopTop_owned (m : NativeMachine) (f : NFiber) (hf : FrameCodeOwned m f) :
    FrameCodeOwned m (runloopTop f) := by
  unfold runloopTop
  split
  · apply frameCodeOwned_same_races hf <;> try rfl
    exact replace_current_sites _ _ rfl
  · exact hf

theorem injectYield_owned (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (hf : FrameCodeOwned m f) (h : injectYield m f yielding = some it) :
    FrameCodeOwned it.machine it.fiber ∧ it.machine.races = m.races ∧
      it.machine.nextRace = m.nextRace ∧ it.machine.state = m.state := by
  unfold injectYield at h
  split at h
  · cases h
    refine ⟨?_, rfl, rfl, rfl⟩
    apply frameCodeOwned_same_races hf <;> try rfl
    exact List.Subset.refl _
  · cases h

/-- The native iteration version uses the same two internal premises. -/
theorem M1.iteration_frameOwned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (_bounds : RaceIdsBelow m) (_hf : FrameCodeOwned m f) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    FrameCodeOwned (iteration (interpOf p table) m f yielding).machine
      (iteration (interpOf p table) m f yielding).fiber) := ⟨⟩

theorem iteration_frameOwned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) :
    letI := evaluatorFor p table
    FrameCodeOwned (iteration (interpOf p table) m f yielding).machine
      (iteration (interpOf p table) m f yielding).fiber := by
  letI := evaluatorFor p table
  have ht : FrameCodeOwned m (countOp (runloopTop f)) := runloopTop_owned m f hf
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      evaluateNative_frameOwned p table m (countOp (runloopTop f)) yielding bounds ht
  | some it =>
    obtain ⟨hown, hr, hb, _⟩ := injectYield_owned m _ yielding it ht hi
    have bounds' : RaceIdsBelow it.machine := by simpa only [RaceIdsBelow, hr, hb] using bounds
    simpa only [iteration, hi] using
      evaluateNative_frameOwned p table it.machine it.fiber it.yielding bounds' hown

#typed_state_obligations Effect4.Program.Guard.FrameOwned.M1 ceiling 0 using
  aesop (rule_sets := [Effect4.Stores]) (add safe [deferred_register_sites, registerAsync_sites, registerAsync_result_sites, evaluatePrim_owned, exitScoped_owned, evaluateNative_frameOwned, iteration_frameOwned])

#typed_state_obligations Effect4.Program.Guard.FrameOwned.M1Origin ceiling 0 using
  aesop (rule_sets := [Effect4.Stores]) (add safe apply [beginRace_owned])

#typed_state_obligations Effect4.Program.Guard.FrameOwned.M1Hooks ceiling 0 using
  aesop (rule_sets := [Effect4.Stores])

#typed_state_obligations Effect4.Program.Guard.FrameOwned.M1Results ceiling 0 using
  aesop (rule_sets := [Effect4.Stores])

end Effect4.Program.Guard.FrameOwned
