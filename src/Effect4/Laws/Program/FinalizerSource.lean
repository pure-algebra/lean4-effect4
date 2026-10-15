import Effect4.Laws.Program.FinalizerPlacement
import Effect4.Laws.Program.SourceOpportunityFrames
import Effect4.Laws.Machine.PlaceLedger

/-!
Concept: scope-lifetime-finalization, R11.
Question: the joint source and scoped-release budget of `once_placed_outside_census`.
Consumer: its native evaluator debit and command invariant.
Reach: existing native code, captured releases, race programs and pending replies.
A registration transfers its descendant opportunity into custody.
A release-start push transfers custody into its saved continuation.
These local transfers establish no whole-history source bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program
abbrev SourceFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann

/-- A registered release reserves its selected descendant source. -/
def releaseWeight (q path : List Nat) : Nat := SourceScope.Opportunities.below q (path ++ [1])

/-- Release custody owns foreign captures before their actual release-start push. -/
def name (q : List Nat) : EffName → Nat
  | .afterScopeAdd _ _ | .releaseUnder _ _ _ => 0
  | callback => SourceScope.Opportunities.name q callback

/-- Foreign release suspensions remain in custody until the release-start push. -/
def thunk (root : NativeEff) (q : List Nat) : EffThunk → Nat
  | .store (.foreign _ _) => 0
  | .body point => if point.fuel = 0 then 0 else SourceScope.Opportunities.below q point.path
  | suspended => SourceScope.Opportunities.thunk root q suspended

/-- A pushed acquisition template transfers its selected release descendant into custody. -/
def successPush (q : List Nat) : EffName → Nat
  | .afterScopeAdd _ (.foreign capture) => SourceScope.Opportunities.here q capture.path + releaseWeight q capture.path
  | _ => 0

/-- An actual selected onExit push spends its direct source opportunity. -/
def exitPush (q : List Nat) : EffName → Bool → Nat
  | .fin point, _ => SourceScope.Opportunities.here q point.path
  | _, _ => 0

abbrev nativeWeights (root : NativeEff) (q : List Nat) : PrimWeights.Model EffName EffThunk where
  name := name q
  thunk := thunk root q
  successPush := successPush q
  exitPush := exitPush q

/-- The current code counts the selected source and transfers into release custody. -/
abbrev current (root : NativeEff) (q : List Nat) (code : NCode) : Nat :=
  cata_prim (PrimWeights.currentAlgebra (nativeWeights root q)) code

/-- A success push can move an existing release reservation into its saved callback. -/
def savedSuccess (q : List Nat) (base : EffName → Nat) : EffName → Nat
  | .releaseUnder point _ _ => releaseWeight q point.path
  | callback => base callback

/-- The shared paired fold computes the saved source reading. -/
abbrev saved (root : NativeEff) (q : List Nat) (code : NCode) : Nat :=
  (cata_prim (PrimWeights.pairedAlgebra (nativeWeights root q)
    (savedSuccess q (name q))) code).2

/-- The source reservation held by an existing frame excludes its copied active body. -/
def frame (root : NativeEff) (q : List Nat) (fiber : SourceFrame) : Nat :=
  current root q fiber.current + (fiber.stack.map (saved root q)).sum

/-- Pushes consume direct source opportunities or transfer descendants into custody. -/
def consumedFrame (q : List Nat) : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed (.onSuccess _ callback) => successPush q callback
  | .pushed (.onExit _ callback flag) => exitPush q callback flag
  | _ => 0

/-- A recorded release-start push returns its descendant opportunity from custody. -/
def producedFrame (q : List Nat) : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed (.onSuccess _ (.releaseUnder point _ _)) => releaseWeight q point.path
  | _ => 0

/-- The whole machine includes unlaunched race bodies and detached resume programs. -/
def ledger (root : NativeEff) (q : List Nat) :
    PlaceLedger EffName EffThunk Val Err Defect FiberId Ann Ctx Stores where
  fiber := fun fiber => frame root q fiber.frame
  race := fun race => (race.programs.map (current root q)).sum
  state := fun _ => 0
  command := fun | .resume _ _ code => current root q code | _ => 0
  task := fun | .resume _ _ code => current root q code | _ => 0
  consumed := fun | .frame _ event => consumedFrame q event | _ => 0
  produced := fun | .frame _ event => producedFrame q event | _ => 0

/-- Native names retain no more active source opportunity than the original lexical projection. -/
theorem name_le (q : List Nat) (callback : EffName) : name q callback ≤ SourceScope.Opportunities.name q callback := by
  cases callback
  case afterScopeAdd => exact Nat.zero_le _
  case releaseUnder => exact Nat.zero_le _
  all_goals exact Nat.le_refl _

/-- Thunks retain no more active source opportunity than the original lexical projection. -/
theorem thunk_le (root : NativeEff) (q : List Nat) (suspended : EffThunk) :
    thunk root q suspended ≤ SourceScope.Opportunities.thunk root q suspended := by
  cases suspended
  case body point =>
    change (if point.fuel = 0 then 0 else SourceScope.Opportunities.below q point.path) ≤
      SourceScope.Opportunities.below q point.path
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  case store suspended =>
    cases suspended
    case foreign => exact Nat.zero_le _
    all_goals exact Nat.le_refl _
  all_goals exact Nat.le_refl _

/-- The registration template retains its descendant once, across its push and callback slots. -/
theorem callback_le (q : List Nat) (callback : EffName) :
    name q callback + successPush q callback ≤
      SourceScope.Opportunities.name q callback + SourceScope.Opportunities.push q (.onSuccess (.success .unit) callback) := by
  cases callback
  case afterScopeAdd acquired fin =>
    cases fin <;> simp only [name, successPush, SourceScope.Opportunities.name, SourceScope.Opportunities.push, SourceScope.Opportunities.fin, releaseWeight, Nat.zero_add]
    all_goals omega
  case releaseUnder => exact Nat.zero_le _
  all_goals simp only [name, successPush, SourceScope.Opportunities.push, Nat.add_zero]
  all_goals exact Nat.le_refl _

/-- The source-only current weight is bounded by the existing compiler opportunity bound. -/
theorem current_le (root : NativeEff) (q : List Nat) (code : NCode) :
    current root q code ≤ SourceScope.Opportunities.current root q code := by
  induction code with
  | success | failure | yieldableError | setInterruptible | yieldNowWith => exact Nat.le_refl _
  | sync suspended | suspend suspended | withFiber suspended => exact thunk_le root q suspended
  | iterator callback cursor | whileLoop callback cursor | asyncFinalizer callback => exact name_le q callback
  | onSuccess body callback ih =>
    have bounded := callback_le q callback
    change current root q body + name q callback + successPush q callback ≤
      SourceScope.Opportunities.current root q body + SourceScope.Opportunities.name q callback + SourceScope.Opportunities.push q (.onSuccess (.success .unit) callback)
    omega
  | onSuccessConst body next ihBody ihNext => exact Nat.add_le_add ihBody ihNext
  | onFailure body callback ih => exact Nat.add_le_add ih (name_le q callback)
  | onSuccessAndFailure body success failure ih =>
    exact Nat.add_le_add (Nat.add_le_add ih (name_le q success)) (name_le q failure)
  | exitFrame body ih => exact ih
  | onExit body callback flag ih =>
    have bounded := name_le q callback
    have same : exitPush q callback flag = SourceScope.Opportunities.push q (.onExit (.success .unit) callback flag) := by
      cases callback <;> rfl
    change current root q body + name q callback + exitPush q callback flag ≤
      SourceScope.Opportunities.current root q body + SourceScope.Opportunities.name q callback + SourceScope.Opportunities.push q (.onExit (.success .unit) callback flag)
    rw [same]
    omega
  | async register signal cancel =>
    cases cancel with
    | none => exact Nat.le_refl _
    | some callback => exact name_le q callback

/-- Every actual source resolution starts with at most its lexical source opportunity. -/
theorem resolve_le (root : NativeEff) (q : List Nat) (point : Point) :
    current root q (resolve root point) ≤ SourceScope.Opportunities.below q point.path :=
  Nat.le_trans (current_le root q _) (SourceScope.Opportunities.resolve_le root q point)

/-- Administrative hooks add no selected-source reservation to the saved stack. -/
theorem ensure_saved (root : NativeEff) (q : List Nat) (code : NCode) (fiber : SourceFrame) :
    ((code.ensure fiber).1.stack.map (saved root q)).sum =
      (fiber.stack.map (saved root q)).sum := by
  fun_cases Prim.ensure code fiber
  all_goals simp only [saved, List.map_cons, List.sum_cons, Nat.zero_add]

/-- Administrative replacement hooks expose no selected source. -/
theorem ensure_answer_zero (root : NativeEff) (q : List Nat) (code : NCode)
    (fiber : SourceFrame) (next : NCode) (found : (code.ensure fiber).2 = some next) :
    current root q next = 0 := by
  revert found
  fun_cases Prim.ensure code fiber
  all_goals intro found
  all_goals aesop (add norm simp [current, cata_prim])

/-- The existing generic pop model reads the active source and custody-transfer slots. -/
def frameModel (root : NativeEff) (q : List Nat) :
    FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann where
  current := current root q
  saved := saved root q
  ensure_stack := fun code fiber => Nat.le_of_eq (ensure_saved root q code fiber)
  ensure_replacement := ensure_answer_zero root q

/-- Every loaded program starts with at most one selected source reservation. -/
theorem load_funded (root : NativeEff) (q : List Nat) (fuel : Nat) :
    (ledger root q).Funded 1 (Api.load root fuel) [] [] := by
  have bound := SourceScope.Opportunities.compile_le root q root (rootPoint fuel) (by rfl)
  have smaller := current_le root q (compileEff root (rootPoint fuel))
  have compiled := Nat.le_trans smaller bound
  change current root q (compileEff root (rootPoint fuel)) ≤ 1 at compiled
  simpa only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued,
    ledger, FiberSum.total, Api.load, RunMachine.empty, RunFiber.make, FrameFiber.start,
    frame, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add, Nat.add_zero,
    Api.compile, compile] using compiled

/-- An actual selected onExit push exchanges active syntax for its recorded source occurrence. -/
theorem exit_push (root : NativeEff) (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : SourceFrame) (body : NCode) (point : Point) (flag : Bool) :
    frame root q {fiber with current := body, stack := .onExit body (.fin point) flag :: fiber.stack} +
      consumedFrame q (.pushed (.onExit body (.fin point) flag)) =
      frame root q {fiber with current := .onExit body (.fin point) flag} ∧
    ({fiber with current := .onExit body (.fin point) flag}).step interp =
      (.running {fiber with current := body, stack := .onExit body (.fin point) flag :: fiber.stack},
        [.pushed (.onExit body (.fin point) flag)]) := by
  refine ⟨?_, FrameFiber.step_onExit interp fiber body (.fin point) flag⟩
  simp only [frame, current, cata_prim, saved, consumedFrame, exitPush,
    List.map_cons, List.sum_cons]
  omega

/-- Stored finalizer programs carry custody, rather than active descendant source reservations. -/
theorem fin_program_zero (root : NativeEff) (q : List Nat) (fin : FinName) (exit : ExitV) :
    current root q (embed (finProgram fin exit)) = 0 := by
  fun_cases finProgram fin exit
  all_goals aesop (add norm simp [current, cata_prim, thunk, name, successPush, exitPush,
    SourceScope.Opportunities.thunk, SourceScope.Opportunities.name, embed])

/-- Interpreting a stored program keeps its foreign descendants in custody until release starts. -/
theorem stored_program_zero (root : NativeEff) (q : List Nat) (program : ProgName) :
    current root q (embed (progOf program)) = 0 := by
  fun_induction progOf program
  all_goals aesop (add norm simp [current, cata_prim, thunk, name, successPush, exitPush,
    SourceScope.Opportunities.thunk, SourceScope.Opportunities.name, embed, fin_program_zero])

/-- Opening a captured release retains zero active source weight before its recorded start push. -/
theorem foreign_suspension_zero (root : NativeEff) (q : List Nat) (capture : Capture) (exit : ExitV) :
    current root q (suspendBodyAt root (.store (.foreign capture exit))) = 0 := rfl

/-- The saved release-start reservation supplies the release-context callback's actual next code. -/
theorem release_context_le (root : NativeEff) (q : List Nat) (point : Point)
    (context : Ctx) (exit : ExitV) (value : Val) :
    current root q (contAOf root (.releaseUnder point context exit) value) ≤
      releaseWeight q point.path := by
  unfold contAOf
  cases found : Val.context? value with
  | none => exact Nat.zero_le _
  | some previous =>
    change 0 + name q (.releaseBody point exit previous) + 0 ≤ releaseWeight q point.path
    simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.le_refl _

/-- The release-body callback transfers its saved reservation to the actual masked child. -/
theorem release_body_le (root : NativeEff) (q : List Nat) (point : Point)
    (previous : Ctx) (exit : ExitV) (value : Val) :
    current root q (contAOf root (.releaseBody point exit previous) value) ≤
      releaseWeight q point.path := Nat.le_refl _

/-- The acquisition callback constructs the exact source-to-custody transfer template. -/
theorem acquired_le (root : NativeEff) (q : List Nat) (point : Point)
    (context : Ctx) (scope : Nat) (value : Val) :
    current root q (contAOf root (.acquired point context scope) value) =
      SourceScope.Opportunities.here q point.path + releaseWeight q point.path := by
  simp only [contAOf, current, cata_prim, thunk, name, successPush,
    SourceScope.Opportunities.thunk, Point.capture, Nat.zero_add]

/-- Registration answers keep the selected release descendant in custody, including closed-scope answers. -/
theorem after_add_zero (root : NativeEff) (q : List Nat) (value : Val) (fin : FinName) (answer : Val) :
    current root q (contAOf root (.afterScopeAdd value fin) answer) = 0 := by
  unfold contAOf
  split
  · rfl
  · cases found : exitOfVal answer with
    | none => rfl
    | some exit =>
      change current root q (embed (finProgram fin exit)) + 0 + 0 = 0
      rw [fin_program_zero]

/-- Acquisition registration exchanges the source descendant for its recorded custody transfer. -/
theorem registration_push (root : NativeEff) (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : SourceFrame) (body : NCode) (acquired : Val) (capture : Capture) :
    frame root q {fiber with current := body, stack := .onSuccess body (.afterScopeAdd acquired (.foreign capture)) :: fiber.stack} +
      consumedFrame q (.pushed (.onSuccess body (.afterScopeAdd acquired (.foreign capture)))) =
      frame root q {fiber with current := .onSuccess body (.afterScopeAdd acquired (.foreign capture))} ∧
    ({fiber with current := .onSuccess body (.afterScopeAdd acquired (.foreign capture))}).step interp =
      (.running {fiber with current := body, stack := .onSuccess body (.afterScopeAdd acquired (.foreign capture)) :: fiber.stack},
        [.pushed (.onSuccess body (.afterScopeAdd acquired (.foreign capture)))]) := by
  refine ⟨?_, FrameFiber.step_onSuccess interp fiber body _⟩
  simp only [frame, current, cata_prim, saved, savedSuccess, name, consumedFrame, successPush,
    List.map_cons, List.sum_cons, Nat.add_zero, Nat.zero_add]
  omega

/-- A recorded release start exchanges custody for the descendant's actual saved source reservation. -/
theorem release_push (root : NativeEff) (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : SourceFrame) (body : NCode) (point : Point) (context : Ctx) (exit : ExitV) :
    frame root q {fiber with current := body, stack := .onSuccess body (.releaseUnder point context exit) :: fiber.stack} =
      frame root q {fiber with current := .onSuccess body (.releaseUnder point context exit)} +
        producedFrame q (.pushed (.onSuccess body (.releaseUnder point context exit))) ∧
    ({fiber with current := .onSuccess body (.releaseUnder point context exit)}).step interp =
      (.running {fiber with current := body, stack := .onSuccess body (.releaseUnder point context exit) :: fiber.stack},
        [.pushed (.onSuccess body (.releaseUnder point context exit))]) := by
  refine ⟨?_, FrameFiber.step_onSuccess interp fiber body _⟩
  simp only [frame, current, cata_prim, saved, savedSuccess, name, successPush, producedFrame,
    List.map_cons, List.sum_cons, Nat.add_zero]
  omega

end Effect4.Program.FinalizerSource
