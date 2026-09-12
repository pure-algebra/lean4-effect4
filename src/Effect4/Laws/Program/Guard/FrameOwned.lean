import Effect4.Api
import Effect4.Laws.Machine.Handles

/-! Native returned-frame race ownership under existing internal invariants.
RaceIdsBelow, FrameCodeOwned, and DeferredCodes express allocation bounds,
frame ownership, and safe stored answers. The native evaluation laws use these
three local premises. Settle connects them to the complete GuardState predicate.

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

def RaceCodeOwned (m : NativeMachine) (fiber : FiberId) (code : NCode) : Prop :=
  ∀ raceId ∈ raceSites code, ∃ race, m.race? raceId = some race ∧ race.host = fiber

def RaceIdsBelow (m : NativeMachine) : Prop :=
  ∀ race ∈ m.races, race.id < m.nextRace

def FrameCodeOwned (m : NativeMachine) (f : NFiber) : Prop :=
  RaceCodeOwned m f.id f.frame.current ∧
    ∀ code ∈ f.frame.stack, RaceCodeOwned m f.id code

def stepRaceSites : IterStep EffName EffThunk Val Err Defect FiberId Ann → List Nat
  | .resume next _ => raceSites next
  | _ => []

def HooksNoRace (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  (∀ name value, raceSites (interp.contA name value) = []) ∧
  (∀ name cause, raceSites (interp.contE name cause) = []) ∧
  (∀ thunk, raceSites (interp.suspendBody thunk) = []) ∧
  (∀ name value, raceSites (interp.loopBody name value) = []) ∧
  (∀ name cause, raceSites (interp.cancelThenFail name cause) = []) ∧
  (∀ name value, stepRaceSites (interp.iterNext name value).2 = [])

/- Frozen local proof dependencies; no global GuardState induction is copied. -/
namespace FrameProof
abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NAnswer := ContAnswer EffName EffThunk Val Err Defect FiberId Ann
abbrev NPop := FramePop EffName EffThunk Val Err Defect FiberId Ann
abbrev NStep := FrameStep EffName EffThunk Val Err Defect FiberId Ann

def frameSites (f : NFrame) : List Nat := raceSites f.current ++ f.stack.flatMap raceSites

theorem raceSites_ofExit (exit : ExitV) : raceSites (Prim.ofExit exit) = [] := by
  cases exit <;> rfl

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
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> simp [raceSites, hL]
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
    split
    · simp only [stepSites, frameSites, hL, List.flatMap_cons, raceSites, List.nil_append]
      exact List.subset_append_right _ _
    · simp only [stepSites, frameSites, raceSites, List.nil_append]
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

theorem hooksNoRace_interpOf (root : NativeEff) (table : RowTable) :
    HooksNoRace (interpOf root table).toPrimInterp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact raceSites_contAOf root
  · exact raceSites_contEOf root
  · exact raceSites_suspendBodyAt root
  · intro name value
    cases name <;> first | rfl | exact raceSites_resolve _ _
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
  · intro name value
    cases name <;> first | rfl | exact raceSites_resolve _ _
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

theorem deferred_register_sites (d : DeferredStore) (hd : DeferredCodes d)
    (cell : DeferredKey) (fid : FiberId) (token : Nat) :
    optionRaceSites ((d.register cell fid token).2.map embed) = [] := by
  cases h : (d.register cell fid token).2 with
  | none => rfl
  | some code => exact (deferredCodes_register hd cell fid token).2 code h

theorem prepareExternalAnswer_sites (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) :
    raceSites (prepareExternalAnswer table current answer state).2 = [] := by
  unfold prepareExternalAnswer
  repeat' first | rfl | exact raceSites_completion _ | split

theorem registerAsync_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (fid : FiberId) (token : Nat) (state : Stores)
    (hd : DeferredCodes state.deferreds) :
    optionRaceSites ((interpAt p completed table).registerAsync name fid token state).2 = [] := by
  cases name <;> simp only [interpAt, interpOf]
  all_goals repeat' first
    | rfl
    | exact deferred_register_sites _ hd _ _ _
    | exact prepareExternalAnswer_sites _ _ _ _
    | split

theorem beginRace_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (entrants : List NCode)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) :
    FrameCodeOwned (beginRace (interpAt p completed table) m f yielding entrants).machine
      (beginRace (interpAt p completed table) m f yielding entrants).fiber := by
  constructor
  · exact raceCodeOwned_beginRace p table m f yielding entrants bounds
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

theorem withFiber_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (action : NAction)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) (ha : actionRaceSites action = []) :
    FrameCodeOwned (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).machine
      (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).fiber := by
  cases action <;> simp only [actionRaceSites] at ha
  all_goals simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start,
    countdownPark, RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
    FrameFiber.setFiberInterruptible]
  all_goals repeat' first
    | exact beginRace_owned _ _ _ _ _ _ _ bounds hf
    | exact hf
    | (solve
        | apply frameCodeOwned_same_races hf
          · simp only [RunMachine.emit, modify_races, linkScope_races, forkFinalizers_races]
            try rfl
          · rfl
          · simp only [frameSites, raceSites, Option.getD_none, Option.getD_some, ha, countdownPark.resumePrim,
              List.flatMap_cons, List.nil_append, List.append_nil] <;> sub_tac)
    | split
  all_goals try simp_all only [WithFiberAction.setInterruptible.injEq, Bool.false_eq_true,
    Bool.true_eq_false, reduceCtorEq]
  all_goals repeat' first
    | (solve
        | apply frameCodeOwned_same_races hf
          · simp only [RunMachine.emit, modify_races, linkScope_races, forkFinalizers_races]
            try rfl
          · rfl
          · simp only [frameSites, raceSites, Option.getD_none, Option.getD_some, ha, countdownPark.resumePrim,
              List.flatMap_cons, List.nil_append, List.append_nil] <;> sub_tac)
    | (solve
        | apply frameCodeOwned_same_races hf <;> try rfl
          apply replace_current_sites
          apply closeScope_hook_sites
          assumption)
    | split

theorem withFiber_hook_sites (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (thunk : EffThunk) (action : NAction)
    (h : (interpAt p completed table).withFiberOf thunk = some action) : actionRaceSites action = [] := by
  have hs := raceSites_withFiberOf p table thunk
  change optionActionRaceSites ((interpAt p completed table).withFiberOf thunk) = [] at hs
  rw [h] at hs
  exact hs

theorem registerAsync_result_sites (p : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (fid : FiberId) (token : Nat) (state : Stores)
    (hd : DeferredCodes state.deferreds) (code : NCode)
    (h : ((interpAt p completed table).registerAsync name fid token state).2 = some code) :
    raceSites code = [] := by
  have hs := registerAsync_sites p completed table name fid token state hd
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

theorem exitValue_sites (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (exit : ExitV) (mode : Supervision.ObserverMode) :
    raceSites ((interpAt p completed table).exitValue exit mode) = [] := by
  cases mode
  · rfl
  · exact raceSites_ofExit _

theorem evaluatePrim_owned (p : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) (hd : DeferredCodes m.state.deferreds) :
    FrameCodeOwned (evaluatePrim (interpAt p completed table) m f yielding).machine
      (evaluatePrim (interpAt p completed table) m f yielding).fiber := by
  simp only [evaluatePrim, RunFiber.park]
  repeat' first
    | exact stepFrame_owned _ _ _ _ _ _ hf
    | exact finalizerOr_owned _ _ _ _ _ _ _ hf
    | exact registerRace_owned _ _ _ _ hf
    | exact countdownPark_owned _ _ _ _ _ _ hf
    | (solve
        | apply withFiber_owned p completed table _ _ _ _ bounds hf
          apply withFiber_hook_sites p completed table
          assumption)
    | exact hf
    | (solve
        | apply frameCodeOwned_same_races hf
          · simp only [RunMachine.emit, modify_races]
            try rfl
          · rfl
          · simp only [frameSites, raceSites, countdownPark.resumePrim,
              List.flatMap_cons, List.nil_append, List.append_nil] <;> sub_tac)
    | (solve
        | apply frameCodeOwned_same_races hf <;> try rfl
          apply replace_current_sites
          apply registerAsync_result_sites p completed table _ f.id m.nextToken m.state hd
          assumption)
    | (solve
        | apply frameCodeOwned_same_races hf <;> try rfl
          apply replace_current_sites
          exact exitValue_sites _ _ _ _ _)
    | split
  all_goals try simp_all only [reduceCtorEq]

theorem exitScoped_owned (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (bounds : RaceIdsBelow m)
    (hf : FrameCodeOwned m f) (hd : DeferredCodes m.state.deferreds) :
    FrameCodeOwned (exitScoped p m f yielding exit).machine (exitScoped p m f yielding exit).fiber := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_owned _ _ _ _ _ _ bounds hf hd
    | (solve
        | apply frameCodeOwned_same_races hf <;> try rfl
          exact getCont_frameSites _ _ _)
    | (solve
        | apply frameCodeOwned_same_races hf <;> try rfl
          refine (replace_current_sites _ _ ?_).trans (getCont_frameSites _ _ _)
          first
          | exact raceSites_ofExit _
          | rw [raceSites_finalizerCode]
            apply raceSites_closeScopeUnsafe
            · assumption
            · rfl)
    | split

/-- Internal local ownership: the input frame is owned, allocated race ids are
below nextRace, and completed Deferred code is safe. No public guard premise changes. -/
theorem evaluateNative_frameOwned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) (hd : DeferredCodes m.state.deferreds) :
    FrameCodeOwned (evaluateNative p m f yielding table).machine
      (evaluateNative p m f yielding table).fiber := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_owned _ _ _ _ _ _ bounds hf hd
    | exact exitScoped_owned _ _ _ _ _ bounds hf hd
    | (solve
        | apply frameCodeOwned_same_races hf <;> try rfl
          simp only [enterScoped, frameSites, raceSites, raceSites_resolve,
            List.nil_append]
          sub_tac)
    | split

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

/-- The native iteration version uses the same three internal premises. -/
theorem iteration_frameOwned (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (bounds : RaceIdsBelow m) (hf : FrameCodeOwned m f) (hd : DeferredCodes m.state.deferreds) :
    letI := evaluatorFor p table
    FrameCodeOwned (iteration (interpOf p table) m f yielding).machine
      (iteration (interpOf p table) m f yielding).fiber := by
  letI := evaluatorFor p table
  have ht : FrameCodeOwned m (countOp (runloopTop f)) := runloopTop_owned m f hf
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      evaluateNative_frameOwned p table m (countOp (runloopTop f)) yielding bounds ht hd
  | some it =>
    obtain ⟨hown, hr, hb, hs⟩ := injectYield_owned m _ yielding it ht hi
    have bounds' : RaceIdsBelow it.machine := by simpa only [RaceIdsBelow, hr, hb] using bounds
    have hd' : DeferredCodes it.machine.state.deferreds := by simpa only [hs] using hd
    simpa only [iteration, hi] using
      evaluateNative_frameOwned p table it.machine it.fiber it.yielding bounds' hown hd'



end Effect4.Program.Guard.FrameOwned
