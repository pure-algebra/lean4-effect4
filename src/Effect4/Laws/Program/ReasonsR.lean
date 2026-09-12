import Effect4.Laws.Program.RuntimeR
import Effect4.Api.Frontier

/-! P2b: the reference projects to the run-level reason alphabet. The existing
book relation transports host, timer, decision and command-exhaustion reasons.
Compile-fuel equality has its own per-fiber obligation, `CompileBook`. -/
set_option autoImplicit false
namespace Effect4.Program.Sched
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Api

def hasRunnableR (m : RState) : Bool :=
  m.fibers.any fun f => f.exit.isNone && f.parked == .notParked

def externalRequest : NCode → Option (NativeOp × Val)
  | .async (.external op request) _ _ => some (op, request)
  | _ => none

def externalRequestR : RProgram → Option (NativeOp × Val)
  | .vis (.inr (.async (.external op request) _)) _ => some (op, request)
  | _ => none

/-- Keep the actual id lookup, including its behavior on duplicate ids. -/
def requestOfR (m : RState) (fiber : FiberId) (token : Nat) : Option (NativeOp × Val) := do
  let f ← m.fiber? fiber
  guard (f.parked = .withGuard token)
  externalRequestR f.frame.current

def awaitsR (m : RState) : List Await :=
  m.fibers.filterMap fun f =>
    match f.parked with
    | .withGuard token => (requestOfR m f.id token).map fun (op, req) => (f.id, token, op, req)
    | .notParked => none

def hostReasonsR (m : RState) : List FrontierReason :=
  (awaitsR m).map fun (fiber, token, _, _) => .awaitHost ⟨fiber, token⟩

def timerReasonsR (m : RState) : List FrontierReason :=
  m.state.timers.wake.waiters.map fun w => .awaitTimer w.fiber w.payload

/-- The pending-denotation marker's projection, with no invented source-choice reason. -/
def isCompileFrontierR : RProgram → Bool
  | .vis (.inr (.frontier .compileFuel _)) _ => true
  | _ => false

def compileReasonsR (m : RState) : List FrontierReason :=
  m.fibers.filterMap fun f =>
    if isCompileFrontierR f.frame.current then some (.compileFuel f.id) else none

def reasonsR (why : Exhaustion) (m : RState) : List FrontierReason :=
  (match why with | .fuel => [.commandFuel] | .tape => []) ++
    compileReasonsR m ++ hostReasonsR m ++ timerReasonsR m ++
    (match why with
    | .fuel => []
    | .tape => if hasRunnableR m then [.awaitDecision] else [])

def nonCompile : FrontierReason → Bool
  | .compileFuel _ => false
  | _ => true

theorem listRel_any {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : ListRel R xs ys) {f : α → Bool} {g : β → Bool}
    (hf : ∀ x y, R x y → f x = g y) : xs.any f = ys.any g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.any_cons, hf _ _ hab, ih]

theorem listRel_filterMap {α β γ : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : ListRel R xs ys) {f : α → Option γ} {g : β → Option γ}
    (hf : ∀ x y, R x y → f x = g y) : xs.filterMap f = ys.filterMap g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.filterMap_cons, hf _ _ hab, ih]

theorem listRel_filter_map {α β γ : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : ListRel R xs ys) {p : α → Bool} {q : β → Bool} {f : α → γ} {g : β → γ}
    (hp : ∀ x y, R x y → p x = q y) (hf : ∀ x y, R x y → f x = g y) :
    (xs.filter p).map f = (ys.filter q).map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.filter_cons, hp _ _ hab]
    split <;> simp only [List.map_cons, hf _ _ hab, ih]

theorem hasRunnable_eq_ref {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) : hasRunnable m = hasRunnableR r := by
  apply listRel_any h.fibers
  intro f g hfg
  have hf : FMeans e f g := hfg
  rw [hf.exit, hf.parked]

theorem externalRequest_eq_ref {e : NativeEff} {c : NCode} {r : RProgram}
    (h : CodeMeans e c r) : externalRequest c = externalRequestR r := by
  cases h <;> rfl

theorem requestOf_eq_ref {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) (fiber : FiberId) (token : Nat) :
    Program.requestOf m fiber token = requestOfR r fiber token := by
  rcases book_fiber?_cases h fiber with ⟨hm, hr⟩ | ⟨f, g, hm, hr, hfg⟩
  · simp [Program.requestOf, requestOfR, hm, hr]
  · have hf : FMeans e f g := hfg
    change ((m.fiber? fiber).bind fun f => do
      guard (f.parked = .withGuard token)
      externalRequest f.frame.current) = requestOfR r fiber token
    simp only [requestOfR, hm, hr, Option.bind_some, hf.parked,
      externalRequest_eq_ref hf.current]
    rfl

theorem awaits_eq_ref {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) : Program.awaits m = awaitsR r := by
  apply listRel_filterMap h.fibers
  intro f g hfg
  have hf : FMeans e f g := hfg
  rw [hf.parked, hf.id]
  cases g.parked with
  | notParked => rfl
  | withGuard token => simp only [requestOf_eq_ref h]

theorem hostReasons_eq_ref {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) : hostReasons m = hostReasonsR r := by
  simp only [hostReasons, hostReasonsR, awaits_eq_ref h]

theorem timerReasons_eq_ref {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) : timerReasons m = timerReasonsR r := by
  simp only [timerReasons, timerReasonsR, h.state]

theorem filter_compile_map {α : Type} (xs : List α) (id : α → FiberId) :
    (xs.map fun x => FrontierReason.compileFuel (id x)).filter nonCompile = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons, List.filter_cons, nonCompile, Bool.false_eq_true,
      ↓reduceIte] using ih

theorem filter_compileReasons (m : NativeMachine) : (compileReasons m).filter nonCompile = [] := by
  unfold compileReasons
  generalize m.fibers = fs
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases h : isCompileFrontier f.frame.current <;>
      simp [List.filterMap_cons, h, nonCompile, ih]

theorem filter_compileReasonsR (r : RState) : (compileReasonsR r).filter nonCompile = [] := by
  unfold compileReasonsR
  generalize r.fibers = fs
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases h : isCompileFrontierR f.frame.current <;>
      simp [List.filterMap_cons, h, nonCompile, ih]

/-- Ordered list equality; compile reasons alone are explicitly outside this claim. -/
theorem book_reasons_nonCompile {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) (why : Exhaustion) :
    (frontierReasons why m).filter nonCompile = (reasonsR why r).filter nonCompile := by
  simp only [frontierReasons, reasonsR, List.filter_append, filter_compileReasons,
    filter_compileReasonsR, hostReasons_eq_ref h, timerReasons_eq_ref h, hasRunnable_eq_ref h]
  cases why <;> rfl

/-- The raw replay relation supplies equal exhaustion tags as well as the book. -/
theorem frontier_reasons_nonCompile {e : NativeEff} {m : NativeMachine} {r : RState}
    {why whyR : Exhaustion}
    (h : ReplayRel (CodeMeans e) (Means e) (.frontier why m) (.frontier whyR r)) :
    (frontierReasons why m).filter nonCompile = (reasonsR whyR r).filter nonCompile := by
  obtain ⟨htags, hbook⟩ := h
  subst whyR
  exact book_reasons_nonCompile hbook why

def replayReasons : FReplay → List FrontierReason
  | .frontier why m => frontierReasons why m
  | _ => []

def replayReasonsR : RReplay → List FrontierReason
  | .frontier why m => reasonsR why m
  | _ => []

theorem replayRel_reasons_nonCompile {e : NativeEff} {r₁ : FReplay} {r₂ : RReplay}
    (h : ReplayRel (CodeMeans e) (Means e) r₁ r₂) :
    (replayReasons r₁).filter nonCompile = (replayReasonsR r₂).filter nonCompile := by
  cases r₁ <;> cases r₂ <;> first
    | exact (h : False).elim
    | rfl
    | exact frontier_reasons_nonCompile h

theorem replayReasons_eq_ref (e : NativeEff) (compileFuel fuel : Nat)
    (tape : List Api.Decision) (choices : List Bool) :
    letI := evaluatorFor e
    letI := termEvaluatorFor e
    (replayReasons (replayEval (interpOf e) fuel tape (Api.load e compileFuel choices))).filter nonCompile =
      (replayReasonsR (replayR e fuel tape choices compileFuel)).filter nonCompile := by
  letI := evaluatorFor e
  letI := termEvaluatorFor e
  exact replayRel_reasons_nonCompile (replay_rel e compileFuel fuel tape choices)

/-- The remaining per-fiber compile observation obligation, kept separate from BookMeans. -/
def CompileBook (m : NativeMachine) (r : RState) : Prop :=
  ListRel (fun f g => f.id = g.id ∧
    isCompileFrontier f.frame.current = isCompileFrontierR g.frame.current) m.fibers r.fibers

theorem compileReasons_eq_ref {m : NativeMachine} {r : RState} (h : CompileBook m r) :
    compileReasons m = compileReasonsR r := by
  apply listRel_filterMap h
  intro f g hf
  rw [hf.1, hf.2]

theorem book_reasons_eq_ref {e : NativeEff} {m : NativeMachine} {r : RState}
    (h : BookMeans (CodeMeans e) (Means e) m r) (hc : CompileBook m r) (why : Exhaustion) :
    frontierReasons why m = reasonsR why r := by
  simp only [frontierReasons, reasonsR, compileReasons_eq_ref hc,
    hostReasons_eq_ref h, timerReasons_eq_ref h, hasRunnable_eq_ref h]
  cases why <;> rfl

/-- The public replay exposes the driver's reason projection. -/
theorem replay_reasons (e : NativeEff) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool) (compileFuel : Nat) :
    (Api.replay e fuel tape choices [] [] compileFuel).reasons =
      replayReasons (replayEval (evaluator := evaluatorFor e) (interpOf e) fuel tape
        (Api.load e compileFuel choices)) := by
  unfold Api.replay
  split <;> rename_i heq <;> rw [heq] <;> rfl

/-- At the empty table and oracle, the public run and reference agree on every
reason except the separately stated per-fiber compile observation obligation. -/
theorem reasons_eq_ref (e : NativeEff) (compileFuel fuel : Nat)
    (tape : List Api.Decision) (choices : List Bool := []) :
    ((Api.replay e fuel tape choices [] [] compileFuel).reasons).filter nonCompile =
      (replayReasonsR (replayR e fuel tape choices compileFuel)).filter nonCompile := by
  rw [replay_reasons]
  exact replayReasons_eq_ref e compileFuel fuel tape choices

end Effect4.Program.Sched
