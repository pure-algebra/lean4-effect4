import Test.Dogfood.Scenario.Routing.Model
import Effect4.Laws.Api.AuthorBuild


import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Auto.KernelRfl

/-!
# Routing failure propagation

Concept: translation-simulation. Requirement: R10.
Claim: the existing routing scenario's `infrastructure_escapes`.
Reach: the authorized request, its failure script, default budgets, and every nonbusiness tag.
The normal-form and machine helpers serve the original scenario clause `infrastructure_escapes`.
This proof establishes no general script law or runtime agreement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostRouting
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Effect4.Program.Denote Effect4.Program.Agreement
open Test.Dogfood.Scenario Test.Dogfood.Scenario.Routing

/-- A build's program is its elaboration. A step of the routing goals: it reads the program off
the elaboration, which the kernel computes with free leaves, where the build's checker does not. -/
theorem build_program {m : Authoring.Module NativeOp} {b : Api.Built}
    (h : Effect4.Api.Author.build m = .ok b) : Authoring.elaborateModule m = .ok b.program :=
  (Effect4.Api.Author.build_retains h).1

/-- The routing program, read off the elaboration. -/
def progOf (token : String) (id : Nat) (idText : String) : Api.Program :=
  match Authoring.elaborateModule (request token id idText) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

/-- The kernel elaborates the request with a free token, id and id text. -/
theorem elaborate_free (token : String) (id : Nat) (idText : String) :
    Authoring.elaborateModule (request token id idText) = .ok (progOf token id idText) := by
  kernel_rfl

/-- A built request's program and table. -/
theorem built_request {token : String} {id : Nat} {idText : String} {b : Api.Built}
    (hb : Effect4.Api.Author.build (request token id idText) = .ok b) :
    b.program = progOf token id idText ∧ b.table = (request token id idText).table := by
  refine ⟨?_, (Effect4.Program.Authoring.build_table hb).1⟩
  have h := build_program hb
  rw [elaborate_free] at h
  exact (Except.ok.inj h).symm

/-- The routing call-tree bridge consumes row-fragment admission for every request. -/
theorem straight_free (token : String) (id : Nat) (idText : String) :
    StraightRows (request token id idText).table (progOf token id idText) = true := by
  kernel_rfl

/-- A handler's test: `tagIs(literal, e)`. -/
def tagTest (lit : String) : Term :=
  Term.app "tagIs" (Terms.cons (Term.lit (Lit.str lit)) (Terms.cons (Term.var 0) Terms.nil))

/-- A `Response` record of a status and a body term. -/
def responseTerm (status : Nat) (body : Term) : Term :=
  Term.record [("status", false, Ty.nat), ("body", false, Ty.string)] ["status", "body"]
    (Terms.cons (Term.lit (Lit.nat status)) (Terms.cons body Terms.nil))

/-- The token check: `not (eq token config.adminToken)`. -/
def tokenTest (token : String) : Term :=
  Term.app "not"
    (Terms.cons
      (Term.app "eq"
        (Terms.cons (Term.lit (Lit.str token))
          (Terms.cons (Term.field FieldReadMode.required (Term.var 0) "adminToken") Terms.nil)))
      Terms.nil)

/-- The failure of a wrong token. -/
def badToken : NativeEff :=
  Eff.fail
    (Term.app "pair"
      (Terms.cons (Term.lit (Lit.str "Unauthorized"))
        (Terms.cons (Term.lit (Lit.str "bad token")) Terms.nil)))

/-- The authorized path: the caller's lookup, the profile check, the requested lookup. -/
def routeLookups (id : Nat) (idText : String) : NativeEff :=
  ((Eff.perform (NativeOp.external 1) (Term.lit (Lit.nat 1))).bind
        (Eff.select (Term.var 1) Decision.option
          (Eff.fail
            (Term.app "pair"
              (Terms.cons (Term.lit (Lit.str "NotFound"))
                (Terms.cons (Term.lit (Lit.str "1")) Terms.nil))))
          (Eff.succeed (Term.var 2)))).bind
    (Eff.select
      (Term.app "and"
        (Terms.cons
          (Term.app "not"
            (Terms.cons
              (Term.app "eq"
                (Terms.cons (Term.field FieldReadMode.required (Term.var 1) "role")
                  (Terms.cons (Term.lit (Lit.str "admin")) Terms.nil)))
              Terms.nil))
          (Terms.cons
            (Term.app "not"
              (Terms.cons
                (Term.app "eq"
                  (Terms.cons (Term.field FieldReadMode.required (Term.var 1) "id")
                    (Terms.cons (Term.lit (Lit.nat id)) Terms.nil)))
                Terms.nil))
            Terms.nil)))
      Decision.bool
      (Eff.fail
        (Term.app "pair"
          (Terms.cons (Term.lit (Lit.str "Unauthorized"))
            (Terms.cons (Term.lit (Lit.str "not yours")) Terms.nil))))
      ((Eff.perform (NativeOp.external 1) (Term.lit (Lit.nat id))).bind
        (Eff.select (Term.var 2) Decision.option
          (Eff.fail
            (Term.app "pair"
              (Terms.cons (Term.lit (Lit.str "NotFound"))
                (Terms.cons (Term.lit (Lit.str idText)) Terms.nil))))
          (Eff.succeed (Term.var 3)))))

/-- The token check's select. -/
def routeSel (token : String) (id : Nat) (idText : String) : NativeEff :=
  Eff.select (tokenTest token) Decision.bool badToken (routeLookups id idText)

/-- The 200 response. -/
def route200 : NativeEff :=
  Eff.succeed (responseTerm 200 (Term.field FieldReadMode.required (Term.var 0) "name"))

/-- The handled body: the configuration, the token check, the two lookups, the 200 response. -/
def routeBody (token : String) (id : Nat) (idText : String) : NativeEff :=
  ((Eff.perform (NativeOp.external 0) (Term.lit Lit.unit)).bind (routeSel token id idText)).bind
    route200

/-- The 401 handler. -/
def route401 : NativeEff :=
  Eff.succeed (responseTerm 401 (Term.app "snd" (Terms.cons (Term.var 0) Terms.nil)))

/-- The 404 handler. -/
def route404 : NativeEff :=
  Eff.succeed (responseTerm 404 (Term.app "concat" (Terms.cons (Term.lit (Lit.str "no user "))
    (Terms.cons (Term.app "snd" (Terms.cons (Term.var 0) Terms.nil)) Terms.nil))))

/-- The routing program, written out. -/
def routeProg (token : String) (id : Nat) (idText : String) : NativeEff :=
  Eff.catchIf (tagTest "NotFound")
    (Eff.catchIf (tagTest "Unauthorized") (routeBody token id idText) route401) route404

/-- The written-out program is the elaborated one, for every token, id and id text. -/
theorem progOf_eq (token : String) (id : Nat) (idText : String) :
    progOf token id idText = routeProg token id idText := by
  kernel_rfl

/-- A handler's test is false on a tagged failure with another tag: the failure escapes. -/
theorem caught_tagged_none (tag message lit : String) (h : tag ≠ lit) :
    caughtErrorValue? [] (tagTest lit) (Cause.fail (.tagged tag message)) = none := by
  have heval : evalTerm [Val.list [Val.str tag, Val.str message]] (tagTest lit) =
      some (.bool (tag == lit)) := by
    kernel_rfl
  have hfirst : firstErrorValue? (Cause.fail (.tagged tag message) : CauseV) =
      some (Val.list [Val.str tag, Val.str message]) := by
    kernel_rfl
  have hne : (tag == lit) = false := beq_eq_false_iff_ne.mpr h
  unfold caughtErrorValue?
  rw [hfirst]
  show (if evalTerm ([] ++ [Val.list [Val.str tag, Val.str message]]) (tagTest lit) =
      some (.bool true) then some (Val.list [Val.str tag, Val.str message]) else none) = none
  rw [List.nil_append, heval, hne]
  rfl


def p0 : Point := { path := [], env := [], fuel := 1000, tape := [] }
def p1 : Point := { path := [0], env := [], fuel := 999, tape := [] }
def cfgCur : NCode := .async (.external (.external 0) .unit [0,0,0,0]) false none
def repoCur : NCode := .async (.external (.external 1) (.nat 1) [0,0,0,1,1,0,0]) false none
def cfgPart : NCode := .onSuccess cfgCur (.cont {path := [0,0,0], env := [], fuel := 997, tape := []})
def bodyPart : NCode := .onSuccess cfgPart (.cont {path := [0,0], env := [], fuel := 998, tape := []})
def cfgValue : Val := configOf "secret" 20
def firstPart : NCode := .onSuccess repoCur
  (.cont { path := [0,0,0,1,1,0], env := [cfgValue], fuel := 994, tape := [] })
def secondPart : NCode := .onSuccess firstPart
  (.cont { path := [0,0,0,1,1], env := [cfgValue], fuel := 995, tape := [] })
def insideHandler : NCode := .onFailure bodyPart (.caughtError p1)
def K : List NCode := [firstPart, secondPart, bodyPart, insideHandler,
  .onFailure insideHandler (.caughtError p0)]

theorem missU (id : Nat) (idText tag message : String) (h : tag ≠ "Unauthorized") :
    (interpAt (routeProg "secret" id idText) []).contE (.caughtError p1)
      (Cause.fail (.tagged tag message)) = Prim.failure (Cause.fail (.tagged tag message)) := by
  change (match caughtErrorValue? [] (tagTest "Unauthorized") (Cause.fail (.tagged tag message)) with
    | some value => resolve (routeProg "secret" id idText) (p1.childWith 1 value)
    | none => Prim.failure (Cause.fail (.tagged tag message))) = _
  rw [caught_tagged_none tag message "Unauthorized" h]

theorem missNF (id : Nat) (idText tag message : String) (h : tag ≠ "NotFound") :
    (interpAt (routeProg "secret" id idText) []).contE (.caughtError p0)
      (Cause.fail (.tagged tag message)) = Prim.failure (Cause.fail (.tagged tag message)) := by
  change (match caughtErrorValue? [] (tagTest "NotFound") (Cause.fail (.tagged tag message)) with
    | some value => resolve (routeProg "secret" id idText) (p0.childWith 1 value)
    | none => Prim.failure (Cause.fail (.tagged tag message))) = _
  rw [caught_tagged_none tag message "NotFound" h]

theorem tailStep1 (id : Nat) (idText tag message : String) (h : tag ≠ "Unauthorized") :
    localStep (routeProg "secret" id idText)
      (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) K true) Stores.empty =
      .running (fiberOf (Prim.failure (Cause.fail (.tagged tag message)))
        [Prim.onFailure insideHandler (.caughtError p0)] true) Stores.empty := by
  unfold K firstPart secondPart bodyPart cfgPart insideHandler
  rw [step_failure_pass_onSuccess, step_failure_pass_onSuccess,
    step_failure_pass_onSuccess, step_failure_onFailure, missU id idText tag message h]

theorem tailStep2 (id : Nat) (idText tag message : String) (h : tag ≠ "NotFound") :
    localStep (routeProg "secret" id idText)
      (fiberOf (Prim.failure (Cause.fail (.tagged tag message)))
        [Prim.onFailure insideHandler (.caughtError p0)] true) Stores.empty =
      .running (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true) Stores.empty := by
  rw [step_failure_onFailure, missNF id idText tag message h]

theorem failureTail (id : Nat) (idText tag message : String)
    (hNF : tag ≠ "NotFound") (hU : tag ≠ "Unauthorized") (tr : NTrace) (nt : Nat) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor (routeProg "secret" id idText)
        (request "secret" id idText).table) (interpOf (routeProg "secret" id idText)
        (request "secret" id idText).table) (n + 6)
      (M (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) K true) Stores.empty 0 tr nt)
      [Cmd.loop Api.root false, Cmd.drainDue] =
      (Mexit (routeProg "secret" id idText) (.failure (Cause.fail (.tagged tag message)))
        (frameExitState (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true))
        Stores.empty 3 tr' nt, []) := by
  let root := routeProg "secret" id idText
  let table := (request "secret" id idText).table
  let c : CauseV := Cause.fail (.tagged tag message)
  have hs : ∀ t, Prim.failure c ≠ (Prim.sync t : NCode) := fun _ h => by cases h
  have hK : PlainStack K := by simp only [K, PlainStack, List.mem_cons]; intros; aesop
  have hK2 : PlainStack [Prim.onFailure insideHandler (.caughtError p0)] := by simp only [PlainStack, List.mem_singleton]; intros; aesop
  obtain ⟨tr1, h1⟩ := drive_loop_running (table := table) root (Prim.failure c) K true
    Stores.empty 0 tr nt [Cmd.drainDue] (Prim.failure c)
    [Prim.onFailure insideHandler (.caughtError p0)] true rfl hK hs rfl (by decide)
    (tailStep1 id idText tag message hU)
  obtain ⟨tr2, h2⟩ := drive_loop_running (table := table) root (Prim.failure c)
    [Prim.onFailure insideHandler (.caughtError p0)] true Stores.empty 1 tr1 nt
    [Cmd.drainDue] (Prim.failure c) [] true rfl hK2 hs rfl (by decide)
    (tailStep2 id idText tag message hNF)
  obtain ⟨tr3, h3⟩ := drive_loop_finish (table := table) root (Prim.failure c) [] true
    Stores.empty 2 tr2 nt [Cmd.drainDue] (.failure c) rfl hs (by decide)
    (step_exit_empty root (.failure c) true Stores.empty)
  obtain ⟨tr4, h4⟩ := drive_finish_M (table := table) root (.failure c)
    (frameExitState (fiberOf (Prim.failure c) [] true)) Stores.empty 3 tr3 nt [Cmd.drainDue]
  refine ⟨tr4, fun n => ?_⟩
  rw [show n + 6 = (n + 5) + 1 by omega, h1,
    show n + 5 = (n + 4) + 1 by omega, h2,
    show n + 4 = (n + 3) + 1 by omega, h3,
    show n + 3 = (n + 2) + 1 by omega, h4,
    drive_drainDue root (n + 1) _ _ rfl Quiet.empty,
    drive_drainDue root n _ _ rfl Quiet.empty, Agreement.drive_nil]

def beforeApply (tag message : String) : List Move :=
  script [[.start], answer cfg (ok (configOf "secret" 20)), [.receive repo (failed tag message)]]

theorem machineShape (id : Nat) (idText tag message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b) :
    (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).machine =
      Mcall (fiberOf repoCur K true) Stores.empty 5
        (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).machine.trace 1 := by
  obtain ⟨hprog, htable⟩ := built_request hb
  obtain ⟨table, program, admitted, rowNames⟩ := b
  have hp : program = progOf "secret" id idText := hprog
  have ht : table = (request "secret" id idText).table := htable
  subst hp
  subst ht
  kernel_rfl

theorem lastRow (id : Nat) (idText tag message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b) :
    Test.Dogfood.Scenario.play (opened b) (failing tag message) =
      (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).step
        (.apply ⟨Api.root, 1⟩) := by
  obtain ⟨hprog, htable⟩ := built_request hb
  obtain ⟨table, program, admitted, rowNames⟩ := b
  have hp : program = progOf "secret" id idText := hprog
  have ht : table = (request "secret" id idText).table := htable
  subst hp
  subst ht
  kernel_rfl

theorem rawFinish (id : Nat) (idText tag message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b)
    (hNF : tag ≠ "NotFound") (hU : tag ≠ "Unauthorized") :
    ∃ tr, stepDecisionState (evaluator := evaluatorFor (routeProg "secret" id idText)
        (request "secret" id idText).table) (interpOf (routeProg "secret" id idText)
        (request "secret" id idText).table) 1000
      (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).machine
      (.answerAsync Api.root 1 (.ofExit (.failure (Cause.fail (.tagged tag message))))) =
      (Mexit (routeProg "secret" id idText) (.failure (Cause.fail (.tagged tag message)))
        (frameExitState (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true))
        Stores.empty 3 tr 2, true) := by
  let root := routeProg "secret" id idText
  let table := (request "secret" id idText).table
  let c : CauseV := Cause.fail (.tagged tag message)
  rw [machineShape id idText tag message b hb]
  obtain ⟨tr0, h0⟩ := answer_Mcall (table := table) root repoCur K true Stores.empty 5
    (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).machine.trace 1
    (.failure c) (s' := Stores.empty) (code := Prim.failure c) rfl
  obtain ⟨tr1, h1⟩ := failureTail id idText tag message hNF hU tr0 2
  refine ⟨tr1, ?_⟩
  rw [show 1000 = 998 + 2 by decide, h0, show 998 = 992 + 6 by decide, h1]
  rfl

def replyOf (tag message : String) : Api.HostSession.Reply :=
  ⟨Api.HostSession.version, "routing", 1, ⟨Api.root, 1⟩, failed tag message⟩

def boundOf (id : Nat) (idText : String) : Api.HostSession.BoundCall :=
  ⟨⟨Api.HostSession.version, "routing", (request "secret" id idText).table, 1,
      Api.root, .external 1, .nat 1⟩, 1⟩

theorem lookupFacts (id : Nat) (idText tag message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b) :
    ((Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).session.active.find?
      (fun bound => bound.key == (⟨Api.root, 1⟩ : Api.HostSession.Key)),
      Api.HostSession.readReply
        (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).session.pending ⟨Api.root, 1⟩,
      Api.HostSession.preflight
        (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).session (replyOf tag message)) =
      (some (boundOf id idText), some (replyOf tag message),
        .ok (.answerAsync Api.root 1 (failed tag message))) := by
  obtain ⟨hprog, htable⟩ := built_request hb
  obtain ⟨table, program, admitted, rowNames⟩ := b
  have hp : program = progOf "secret" id idText := hprog
  have ht : table = (request "secret" id idText).table := htable
  subst hp
  subst ht
  kernel_rfl

theorem applyFinishes (s : Run) (id : Nat) (idText tag message : String) (tr : NTrace)
    (hshape : s.machine = Mcall (fiberOf repoCur K true) Stores.empty 5 s.machine.trace 1)
    (hbound : s.session.active.find? (fun bound => bound.key == (⟨Api.root, 1⟩ : Api.HostSession.Key)) =
      some (boundOf id idText))
    (hreply : Api.HostSession.readReply s.session.pending ⟨Api.root, 1⟩ = some (replyOf tag message))
    (hpre : Api.HostSession.preflight s.session (replyOf tag message) =
      .ok (.answerAsync Api.root 1 (failed tag message)))
    (hm : Program.steppedBy s.built.program 1000 s.built.table s.machine
      (.answerAsync Api.root 1 (failed tag message)) =
      Mexit (routeProg "secret" id idText) (.failure (Cause.fail (.tagged tag message)))
        (frameExitState (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true))
        Stores.empty 3 tr 2) :
    (Api.HostSession.applyReply s.session ⟨Api.root, 1⟩ 1000).session.machine =
      Mexit (routeProg "secret" id idText) (.failure (Cause.fail (.tagged tag message)))
        (frameExitState (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true))
        Stores.empty 3 tr 2 := by
  simp only [Api.HostSession.applyReply, hbound, hreply, hpre]
  change Program.steppedBy s.built.program (999 + 1) s.built.table s.session.machine
    (.answerAsync Api.root 1 (failed tag message)) = _ at hm
  unfold Program.steppedBy at hm
  rw [hm]
  change s.session.machine = _ at hshape
  rw [hshape]
  kernel_rfl

theorem appliedExit (s : Run) (id : Nat) (idText tag message : String) (tr : NTrace)
    (hfuel : s.budget.fuel = 1000)
    (happly : (Api.HostSession.applyReply s.session ⟨Api.root, 1⟩ 1000).session.machine =
      Mexit (routeProg "secret" id idText) (.failure (Cause.fail (.tagged tag message)))
        (frameExitState (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true))
        Stores.empty 3 tr 2) :
    (s.step (.apply ⟨Api.root, 1⟩)).exit = some (.failure (Cause.fail (.tagged tag message))) := by
  unfold Run.exit Run.inspect
  rw [Run.step_session_apply, hfuel]
  unfold Api.HostSession.inspect
  rw [happly]
  kernel_rfl



end Test.Dogfood.Proofs.HostRouting
