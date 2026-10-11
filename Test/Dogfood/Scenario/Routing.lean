import Test.Dogfood.Scenario.Routing.Model
import Test.Dogfood.Proofs.HostRouting
import Test.Dogfood.Scenario.Routing.Calls
import Test.Dogfood.Scenario
import Test.Dogfood.P2HandlerLayers
import Test.Audit.ScenarioGate

/-!
# The routing scenario: exact handlers, and the call that must not happen

Decisions row 254. The scenario extends the consumer of `Test/Dogfood/P2HandlerLayers.lean`: its
admitted `handle` program over the two host rows. It composes four features: two nested handlers
selected by a tag, a branch on a host answer, host calls in sequence, and a typed failure that a
host answer carries.

* **Program.** `request`: p2's handler on fixed arguments. `handleOn` writes the same handler
  over any repository row and any two handler tests, so a red control changes one part. The
  instance at p2's row and tests elaborates to p2's own program (a control pins it).
* **Script.** The host answers the configuration, then each repository lookup. A script offers a
  repository answer even where the program must not ask for one. `runsOf` lists each script
  once, as a named run.
* **Observation.** `Observation`, three fields: the exact response or the failure that escapes,
  the repository's calls, and the refused rows with the session's reason.
* **Claim.** `routing` assembles three clauses. The handler's test is exact on the pair spelling
  (`tagIs_pair`, proved). Two are planned goals: `infrastructure_escapes` and
  `unauthorized_calls_nothing`. One law stands beside them as an associated law: a stored
  successful reply fits its row (`submit_success_prepared_fits`, a theorem of the law graph). It
  has controls, and the claim's proof does not use it.
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  control names the runs that its comparison reads.
* **Lowered runs.** The program prints and reads back (`Test/Dogfood/Scenario/Faces.lean`). The
  host lane and the engine's lane take their scripts from `runsOf`: the keyed lane performs each
  named run that a host can perform, and `Test/Dogfood/Scenario/Tape.lean` names the runs of the
  engine's fixture.

Two findings stand in the controls. The repository row's error column is a pair of strings, so a
host failure that wears a business tag is routed as that business failure. With the exact column,
the session refuses that reply. Each run is a finite probe: one script on the Lean machine.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Routing

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Proofs.HostRouting
open Effect4.Run.CallTree Test.Dogfood.Scenario.Routing.Calls
open Effect4.Program.Agreement Effect4.Program.Denote
open Test.Dogfood.P2HandlerLayers (getConfig findById response userTy recordVal user caseModule)

/-! ## 4. The claim -/

/-- **The handler's test is exact on the pair spelling.** `tagIs` answers true on a failure
`[tag', message]` exactly when `tag'` is the handler's tag. Reach: every tag and every pair value
(DB-15's spelling of a tagged failure). It does not establish what `catchIf` does with the
answer: the handler's routing on the machine is shown by the finite runs. A record payload is
`NativeAtom.tagHit_record`'s (`src/Effect4/Laws/Program/RecordTag.lean`). Consumer: the routing
scenario's clause "exact". -/
@[semantics "residual-program-typing" (requirement := R10)]
theorem tagIs_pair (tag other : String) (message : Val) :
    NativeAtom.eval .tagIs [.str tag, .list [.str other, message]] =
      some (.bool (other == tag)) := rfl

/-- **An infrastructure failure escapes the business handlers.** On the authorized path, a
repository failure whose tag is neither business tag reaches the root unchanged. Reach: p2's
handler, the script `failing`, every user id, every tag but `NotFound` and `Unauthorized`, every
message, the default budgets. It does not establish the same for another script. It does not
hold for a failure that wears a business tag: the row's error column admits one, and the handler
then routes it as the business failure (a red control). Concept `translation-simulation`: the
statement is the handler form's behaviour, R10's "one behaviour law" for `catchTag`, on one
program. Consumer: the routing scenario. Its controls are finite runs. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem infrastructure_escapes : InfrastructureEscapes := by
  intro id idText tag message b hb hNF hU
  simp only [observe]
  obtain ⟨hprog, htable⟩ := built_request hb
  generalize hs : Test.Dogfood.Scenario.play (opened b) (beforeApply tag message) = s
  have hsbuild : s.built = b := by
    rw [← hs]
    exact (Test.Dogfood.Scenario.play_opened (opened b) (beforeApply tag message)).1
  have hbudget := (Test.Dogfood.Scenario.play_opened (opened b) (beforeApply tag message)).2.2.1
  rw [hs] at hbudget
  have hsfuel : s.budget.fuel = 1000 := congrArg Api.Budget.fuel hbudget
  obtain ⟨tr, hraw⟩ := rawFinish id idText tag message b hb hNF hU
  rw [hs] at hraw
  let ended := Mexit (routeProg "secret" id idText) (.failure (Cause.fail (.tagged tag message)))
    (frameExitState (fiberOf (Prim.failure (Cause.fail (.tagged tag message))) [] true))
    Stores.empty 3 tr 2
  have hm : Program.steppedBy s.built.program 1000 s.built.table s.machine
      (.answerAsync Api.root 1 (failed tag message)) = ended := by
    rw [hsbuild, hprog, htable, progOf_eq]
    exact congrArg Prod.fst hraw
  have hlook := lookupFacts id idText tag message b hb
  rw [hs] at hlook
  have hbound := congrArg (fun x => x.1) hlook
  have hreply := congrArg (fun x => x.2.1) hlook
  have hpre := congrArg (fun x => x.2.2) hlook
  change s.session.active.find? (fun bound => bound.key == (⟨Api.root, 1⟩ : Api.HostSession.Key)) =
    some (boundOf id idText) at hbound
  change Api.HostSession.readReply s.session.pending ⟨Api.root, 1⟩ = some (replyOf tag message) at hreply
  change Api.HostSession.preflight s.session (replyOf tag message) =
    .ok (.answerAsync Api.root 1 (failed tag message)) at hpre
  have hshape := machineShape id idText tag message b hb
  rw [hs] at hshape
  have hmachine := applyFinishes s id idText tag message tr hshape hbound hreply hpre hm
  have hlast := lastRow id idText tag message b hb
  have hstep : (Test.Dogfood.Scenario.play (opened b) (beforeApply tag message)).step
      (.apply ⟨Api.root, 1⟩) = s.step (.apply ⟨Api.root, 1⟩) :=
    congrArg (fun q : Run => q.step (.apply ⟨Api.root, 1⟩)) hs
  have hfinish := appliedExit s id idText tag message tr hsfuel hmachine
  have htotal := (congrArg Run.exit hlast).trans ((congrArg Run.exit hstep).trans hfinish)
  exact htotal

/-- **An unauthorized request makes no call of the repository.** Under every script, if no reply
in the journal carries a configuration whose token is the request's, the host holds no
repository call. Reach: p2's handler, every request, every script of the driver's alphabet, the
default budgets. It does not establish what an authorized request calls, and it says nothing of
a handler that looks the caller up first (a red control). Concept `context-requirements`: the
repository is the service the handler may use only after the check, R5. Consumer: the routing
scenario. Its controls are finite runs, and a bounded search over every script of 14 moves up to
length 5 found no repository call without the token: a finite probe, in the seat's receipt. -/
@[semantics "context-requirements" (requirement := R5)]
theorem unauthorized_calls_nothing : UnauthorizedCallsNothing := by
  intro token id idText b moves hb hnone
  obtain ⟨hprog, htable⟩ := built_request hb
  have hreach : Run.Reached (Test.Dogfood.Scenario.play (opened b) moves) :=
    Test.Dogfood.Scenario.reached_play _ _ (Run.Reached.opened _ _ _ _)
  have hbuilt : (Test.Dogfood.Scenario.play (opened b) moves).built = b :=
    (Test.Dogfood.Scenario.play_opened (opened b) moves).1
  cases hcalls : (observe (Test.Dogfood.Scenario.play (opened b) moves)).repositoryCalls with
  | nil => rfl
  | cons v rest =>
    exfalso
    have hmem : v ∈ Test.Dogfood.Scenario.requestsOn (Test.Dogfood.Scenario.play (opened b) moves)
        "UserRepo.findById" := by
      have : v ∈ (observe (Test.Dogfood.Scenario.play (opened b) moves)).repositoryCalls := by
        rw [hcalls]
        exact List.mem_cons_self
      exact this
    obtain ⟨seen, hseenf, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨hseen, hrowname⟩ := List.mem_filter.mp hseenf
    have hfrag : StraightRows (Test.Dogfood.Scenario.play (opened b) moves).built.table
        (Test.Dogfood.Scenario.play (opened b) moves).built.program = true := by
      rw [hbuilt, hprog, htable]
      exact straight_free token id idText
    have hcause : NoCauseHandler (Test.Dogfood.Scenario.play (opened b) moves).built.program =
        true := by
      rw [hbuilt, hprog]
      exact noCauseHandler_free token id idText
    have hclock : NoClockRead (Test.Dogfood.Scenario.play (opened b) moves).built.program =
        true := by
      rw [hbuilt, hprog]
      exact noClockRead_free token id idText
    obtain ⟨i, row, T, hrow, hspell, hjournal, hwait⟩ :=
      held_in_tree _ hreach hfrag hcause hclock seen hseen
    rw [hbuilt, hprog, htable] at hwait
    rw [hbuilt, htable] at hrow
    have hi : i = 1 := repo_position token id idText i row hrow
      (hspell.trans (beq_iff_eq.mp hrowname))
    subst hi
    obtain ⟨pageSize, rest', hT⟩ := tree_needs_token token id idText T seen.request hwait
    obtain ⟨reply, hsub, hcomp⟩ := hjournal _ (by rw [hT]; exact List.mem_cons_self)
    exact hnone reply pageSize hsub hcomp

/-- **The routing scenario's claim.** The handler's test is exact on the pair spelling. An
infrastructure failure escapes the business handlers. An unauthorized request makes no call of
the repository. The first is proved, and the other two are planned goals, so this theorem is
proved modulo them. The record's associated law is a theorem of the law graph: a stored
successful reply fits its row (`Effect4.Api.HostSession.submit_success_prepared_fits`). This
theorem does not use that law. It does not establish a code-valued service, a layer's lowering,
or reply admission beyond that law. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem routing :
    (∀ (tag other : String) (message : Val),
      NativeAtom.eval .tagIs [.str tag, .list [.str other, message]] =
        some (.bool (other == tag))) ∧
    InfrastructureEscapes ∧ UnauthorizedCallsNothing :=
  ⟨tagIs_pair, infrastructure_escapes, unauthorized_calls_nothing⟩

/-! ## 5. The runs and the controls -/

/-- A `Response` value, and a tagged failure at the root. -/
def responded (status : Nat) (body : String) : Option ExitV :=
  some (.success (recordVal ["status", "body"] [.nat status, .str body]))
def escaped (tag message : String) : Option ExitV :=
  some (.failure (Cause.fail (.tagged tag message)))

/-- A user row with a column the type does not name, as a row decoder hands a wider row on. -/
def wide : Val :=
  .some (recordVal ["id", "name", "role", "createdAt"] [.nat 1, .str "ada", .str "admin", .nat 0])

/-- Whether a run shows an observation. -/
def shows (s : Run) (expected : Observation) : Bool := observe s == expected

/-- The scenario's named runs: each script of a control, once, from one build of each program.
The first six are on the scenario's own program `request`. The others are on the variants of the
red controls. The host lane performs them in this order. -/
def runsOf (bob missing denied misnamed catchAll eager exact : Api.Built) : List NamedRun :=
  [ ⟨"200", opened bob, lookups 2⟩
  , ⟨"404", opened missing, lookups 9⟩
  , ⟨"401", opened denied, lookups 2⟩
  , ⟨"escape", opened bob, failing "SqlError" "connection lost"⟩
  , ⟨"business-tag", opened bob, failing "NotFound" "db"⟩
  , ⟨"wide", opened bob,
      script [[.start], answer cfg (ok (configOf "secret" 20)), answer repo (ok wide)]⟩
  , ⟨"misnamed", opened misnamed, lookups 2⟩
  , ⟨"catch-all", opened catchAll, failing "SqlError" "connection lost"⟩
  , ⟨"eager", opened eager, lookups 2⟩
  , ⟨"exact-business-tag", opened exact, failing "NotFound" "db"⟩
  , ⟨"exact-escape", opened exact, failing "SqlError" "connection lost"⟩ ]

/-- The controls. Each names the runs of `runsOf` that its comparison reads, and the gate hands
them over as played. -/
def controlsOf : List Control :=
  [ -- each handler catches only its named failure
    green "exact" "the three requests of run-p2.ts get rc.112's three responses"
      ["200", "404", "401"] fun
      | [served, missing, denied] =>
        shows served ⟨responded 200 "bob", [.nat 1, .nat 2], []⟩ &&
          shows missing ⟨responded 404 "no user 9", [.nat 1, .nat 9], []⟩ &&
          shows denied ⟨responded 401 "bad token", [], []⟩
      | _ => false
  , red "exact" "a handler that names another tag lets the business failure escape"
      ["misnamed"] fun
      | [misnamed] => shows misnamed ⟨escaped "Unauthorized" "bad token", [], []⟩
      | _ => false
  , red "exact" "a handler that catches every failure answers 401 to an infrastructure failure"
      ["catch-all"] fun
      | [caught] => shows caught ⟨responded 401 "connection lost", [.nat 1], []⟩
      | _ => false
    -- an infrastructure failure escapes the business handlers
  , green "escape" "a repository failure with another tag reaches the root unchanged"
      ["escape"] fun
      | [escaping] => shows escaping ⟨escaped "SqlError" "connection lost", [.nat 1], []⟩
      | _ => false
  , red "escape" "a repository failure that wears a business tag is routed as that failure"
      ["business-tag"] fun
      | [tagged] => shows tagged ⟨responded 404 "no user db", [.nat 1], []⟩
      | _ => false
  , red "escape" "with the exact error column the session refuses the business tag"
      ["exact-business-tag", "exact-escape"] fun
      | [tagged, escaping] =>
        shows tagged ⟨none, [.nat 1], [("submit", .envelope), ("apply", .noCall)]⟩ &&
          shows escaping ⟨escaped "SqlError" "connection lost", [.nat 1], []⟩
      | _ => false
    -- an unauthorized request makes no call of the repository
  , green "no call" "a request with a wrong token holds no repository call, though offered"
      ["401"] fun
      | [denied] => shows denied ⟨responded 401 "bad token", [], []⟩
      | _ => false
  , red "no call" "a handler that looks the caller up first calls the repository" ["eager"] fun
      | [eager] =>
        shows eager
          ⟨responded 401 "bad token", [.nat 1], [("submit", .noCall), ("apply", .noCall)]⟩
      | _ => false
    -- a stored successful reply fits its row
  , green "admission" "the exact records are stored and applied: no row is refused" ["200"] fun
      | [served] => shows served ⟨responded 200 "bob", [.nat 1, .nat 2], []⟩
      | _ => false
  , red "admission" "a wider record is refused at the reply receipt, and the root does not move"
      ["wide"] fun
      | [widened] => shows widened ⟨none, [.nat 1], [("submit", .envelope), ("apply", .noCall)]⟩
      | _ => false ]

/-- The scenario's runs and its controls, from one build of each program. The first control pins
that the scenario's program is p2's own. A program that does not build leaves no run and one
failing control. -/
def runsAndControls : List NamedRun × List Control :=
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  match build (request "secret" 2 "2"), build (request "secret" 9 "9"), build (request "wrong" 2 "2"),
    build (routed false findById (named "NotFound") (named "Unauthorised") "wrong" 2 "2"),
    build (routed false findById (named "NotFound") (fun _ => bool true) "secret" 2 "2"),
    build (routed true findById (named "NotFound") (named "Unauthorized") "wrong" 2 "2"),
    build (routed false findByIdExact (named "NotFound") (named "Unauthorized") "secret" 2 "2"),
    build (caseModule "secret" 2 "2") with
  | some bob, some missing, some denied, some misnamed, some catchAll, some eager, some exact,
      some p2 =>
    (runsOf bob missing denied misnamed catchAll eager exact,
      green "exact" "the scenario's program is p2's own handler" []
        (fun _ => decide (bob.program = p2.program)) :: controlsOf)
  | _, _, _, _, _, _, _, _ =>
    ([], [green "exact" "the handler and its variants build" [] fun _ => false])

/-! ## 6. The record -/

/-- The routing scenario. The claim assembles the three clauses. The session's law of a stored
successful reply is an associated law: the record claims no dependency of `routing` on it. The
registry places it by its module, a default module of `host-session-protocol`. -/
def scenario : Scenario :=
  { name := "routing"
    program := ``request
    observation := ``observe
    claim := ``routing
    clauses :=
      [ ⟨"exact", ``tagIs_pair⟩
      , ⟨"escape", ``infrastructure_escapes⟩
      , ⟨"no call", ``unauthorized_calls_nothing⟩ ]
    laws := [⟨"admission", ``Effect4.Api.HostSession.submit_success_prepared_fits⟩]
    runs := runsAndControls.1
    controls := runsAndControls.2 }

#scenario_gate scenario

end Test.Dogfood.Scenario.Routing
