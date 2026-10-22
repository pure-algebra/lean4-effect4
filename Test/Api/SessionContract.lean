import Test.Api.SessionFixtures
import Effect4.Laws.Api.Session
import Effect4.Laws.Run.Runner

/-! Finite evaluations and refusal controls for the checked session constructor.
These executions do not establish a transformation theorem or physical host behaviour. -/

set_option autoImplicit false
namespace Test.Api.SessionContract
open Effect4 Effect4.Program Effect4.Machine
open Effect4.Api (Built SessionRefusal)
open Test.Api.SessionFixtures

-- Finite evaluation: the ordinary service answers every request and ends.
#guard todoRun.map (fun (run, state) =>
  (run.exit, state.1, (replies run).map (·.2), state.2.1)) ==
  some (some (.success .unit), [], todoExpected, (3, [(2, "café 日本 🙂", false)]))
#guard todoRun.map (fun (_, state) => state.2.2) =
  some ["TodoRepo.insert", "TodoRepo.insert", "TodoRepo.all", "TodoRepo.setDone",
    "TodoRepo.all", "TodoRepo.delete", "TodoRepo.all"]

-- Finite evaluation: one cached lifetime asks the repository once for two lists.
#guard cachedSession.map (fun b =>
  let (run, state) := runTodo b twoLists stocked
  (run.exit, (replies run).map (·.2), state.2.2)) =
  some (some (.success .unit),
    [success (.list [Test.Dogfood.Scenario.Todo.todo 1 "milk" false]),
     success (.list [Test.Dogfood.Scenario.Todo.todo 1 "milk" false])],
    ["TodoRepo.all"])

-- Control: opening two cached consumers loses that cache between requests.
#guard (Test.Dogfood.Scenario.Todo.Cached.consumerBuiltAt "list" []).map (fun b =>
  let (_, first) := Run.runWith b recordedRepository (stocked, [])
  (Run.runWith b recordedRepository first).2.2) =
  some ["TodoRepo.all", "TodoRepo.all"]

-- Control: duplicate definition names do not change the selected method position.
#guard shadowed.map (fun o => o.open.isOk && o.services.isOk) = some true
#guard (shadowed.bind fun o => (o.open.toOption.bind fun b =>
  (b.session "TodoApp").toOption)).map (fun b =>
    let (run, state) := runTodo b [.list [.str "list", .unit]] stocked
    (run.exit, (replies run).map (·.2), state.2.2)) =
  some (some (.success .unit), [success (.list [Test.Dogfood.Scenario.Todo.todo 1 "milk" false])],
    ["TodoRepo.all"])

-- Control: the exact protocol key collides; another Session operation is harmless.
#guard todoBuilt.map (fun b => (withRow (Object.ofBuilt b) "Session.next").open.isOk) = some true
#guard todoBuilt.map (fun b => sessionObject (withRow (Object.ofBuilt b) "Session.next") "TodoApp") =
  some (.error (.admission (.signature (.duplicateRow ("Session.next", [])))))
#guard todoBuilt.map (fun b =>
  sessionObject (withRow (Object.ofBuilt b) "Session.reply_list") "TodoApp") =
  some (.error (.admission (.signature (.duplicateRow ("Session.reply_list", [])))))
#guard (todoBuilt.bind fun b => (sessionObject (withRow (Object.ofBuilt b) "Session.health")
  "TodoApp").toOption).map (fun o => o.app.rows.map (·.spelling)) =
  some ["TodoRepo.insert", "TodoRepo.all", "TodoRepo.setDone", "TodoRepo.delete", "Session.health",
    "Session.next", "Session.reply_add", "Session.reply_list", "Session.reply_complete", "Session.reply_remove"]

-- Control: selection reports the requested service, including a block-free program.
#guard todoBuilt.map (fun b => (b.session "Absent").map Object.ofBuilt) =
  some (.error (.missingService "Absent"))
#guard sessionObject ⟨{}, unitProgram⟩ "Absent" = .error (.missingService "Absent")

-- Controls: source admission permits these declarations; session construction keeps each owner.
-- A required key stays the host's: the session provides nothing, and admission refuses a read of a
-- key the signature does not type, so `foreign` is empty on every admitted lifetime.
#guard [parameterized, remaining, nonunit, incomingHandle, outgoingHandle, unusedParameterized,
  twoArguments].all (fun o => o.open.isOk && o.services.isOk)
#guard sessionObject parameterized "Simple" =
  .error (.admission (.illTyped ⟨[1, 1, 0, 1, 1, 0, 0, 0], .outsideDomain "method"⟩))
#guard (sessionObject nonunit "Simple").bind (fun o => o.open.mapError .admission |>.map (·.requires)) =
  .ok [natKey]
#guard (sessionObject remaining "Simple").bind (fun o => o.open.mapError .admission |>.map (·.requires)) =
  .ok [unitKey]
#guard foreignRemaining.open.isOk = false
#guard sessionObject incomingHandle "Simple" =
  .error (.admission (.signature (.row 0 (.internalHandle "answer"))))
#guard (sessionObject outgoingHandle "Simple").map (fun o => o.app.rows.map (·.request)) =
  .ok [.unit, .exitOf (.refOf .nat) .never]
#guard (sessionObject unusedParameterized "Simple").map (fun o => o.program.defsOf.length) = .ok 3

-- Finite evaluation: multiple ordinary arguments retain their values and order.
#guard ((twoArguments.open.toOption).bind fun b => (b.session "Simple").toOption).map (fun b =>
  let (run, _) := runExample b [.list [.str "m", .list [.nat 9, .str "value"]]]
  (run.exit, (replies run).map (·.2))) =
  some (some (.success .unit), [success (.list [.nat 9, .str "value"])])

-- Finite evaluation: program names are data, with no target identifier restriction.
#guard ["", "delete", "x.y", "café 日本", "_%name"].all (fun name =>
  match sessionObject (named name) "Simple" with
  | .error _ => false
  | .ok object =>
    (object.app.rows.map (·.spelling)) == ["Session.next", "Session.reply_" ++ name] &&
    object.app.rows[0]?.map (·.answer) == some (.option (.prod (.lit name) .unit)))

-- Finite evaluation: unusual tags also dispatch at runtime, without name resolution.
#guard ["", "delete", "x.y", "café 日本", "_%name"].all (fun name =>
  match (named name).open.toOption.bind (fun b => (b.session "Simple").toOption) with
  | none => false
  | some built =>
    let (run, _) := runExample built [.list [.str name, .unit]]
    run.exit == some (.success .unit) &&
      replies run == [("Session.reply_" ++ name, success .unit)])

-- Finite evaluation: the body's module-layer reference still selects its stored layer.
#guard moduleLayer.open.isOk
#guard (sessionObject moduleLayer "Simple").map (fun o => o.program.refSites []) =
  .ok [([0, 1, 0, 0], [2, 0])]
#guard (moduleLayer.open.toOption.bind fun b => (b.session "Simple").toOption).map (fun b =>
  let (run, _) := runExample b [.list [.str "m", .unit]]
  (run.exit, replies run)) =
  some (some (.success .unit), [("Session.reply_m", success (.nat 23))])

-- Finite evaluation: a typed failure is replied to; later requests update the same cell.
#guard exampleRun.map (fun (run, state) => (run.exit, state.1, replies run)) =
  some (some (.success .unit), [],
    exampleExpected.map ("Session.reply_check", ·))

-- Control: initialization failure produces neither a request call nor a reply.
#guard ((initialFailure.open.toOption).bind fun b => (b.session "Simple").toOption).map (fun b =>
  let (run, state) := runExample b [.list [.str "m", .unit]]
  (run.exit, state.1, replies run,
    (Run.rows run).filterMap fun
      | (.bind call _, .bound) => some call.op
      | _ => none)) ==
  some (some (.failure (.fail (.tag 13))), [.list [.str "m", .unit]], [], [])

-- Finite agreement: the queue and the handled client observe the same seven method exits.
#guard todoRun.map (fun (run, _) =>
  some (.success (((replies run).map (·.2)).foldr (fun head tail => .list [head, tail]) .unit) : ExitV)) =
  clientRun.map (fun (run, _) => run.exit)

-- Finite agreement: the queue and the handled client leave the same repository.
#guard todoRun.map (fun (_, state) => state.2.1) = clientRun.map (fun (_, state) => state.1)

-- Control: a malformed queued request is refused at reply admission and remains live.
#guard todoSession.map (fun b =>
  let (run, state) := runTodo b [.nat 0] (1, [])
  (run.exit, run.phases, (Run.live run).map (·.row), replies run, state.2.1)) ==
  some (none, [.progressed, .bound, .refused .envelope, .refused .noCall],
    ["Session.next"], [], (1, []))

-- Control: `next` reads the pending request and keeps it; the reply consumes it. So a repeated
-- `next` repeats its request, as the general client equations say of an unanswered call.
#guard todoSession.map (fun b => b.app.rows[4]?.bind fun row => do
  let (_, remaining) ← Run.Reactor.queue row .unit todoRequests
  Run.Reactor.queue row .unit remaining) =
  some (some (.ofExit (.success (.some (.list [.str "add", .str "milk"]))), todoRequests))
#guard todoSession.map (fun b => b.app.rows[5]?.bind fun row =>
  Run.Reactor.queue row .unit todoRequests) =
  some (some (.ofExit (.success .unit), todoRequests.tail))
-- Control: a reply with no pending call is declined, a live frontier, not an answer.
#guard todoSession.map (fun b => b.app.rows[5]?.map fun row => Run.Reactor.queue row .unit []) =
  some (some none)

-- Control: overlapping reactors choose the left answer; disjointness is a separate premise.
#guard todoSession.map (fun b => b.app.rows[4]?.bind fun row =>
  Run.Reactor.tensor Run.Reactor.queue Run.Reactor.queue row .unit
    (todoRequests, twoLists)) =
  some (some (.ofExit (.success (.some (.list [.str "add", .str "milk"]))),
    (todoRequests, twoLists)))

-- Control: a reply prefix names the protocol even without a selected service method.
#guard Run.Reactor.queue
    (Effect4.Program.Authoring.Row.host (Effect4.Api.ServiceSession.replyPrefix ++ "absent") .unit .unit).row .unit
    todoRequests = some (.ofExit (.success .unit), todoRequests.tail)

-- Law reader: the queue answers next without changing the recorded repository, or its own list.
example (row : Row) (state : Test.Dogfood.Scenario.Todo.Repo × List String)
    (atNext : row.spelling = Effect4.Api.ServiceSession.nextName) :
    Run.Reactor.tensor Run.Reactor.queue recordedRepository row .unit
      (todoRequests, state) =
      some (.ofExit (.success (.some (.list [.str "add", .str "milk"]))),
        (todoRequests, state)) :=
  Run.Reactor.tensor_left Run.Reactor.queue recordedRepository row .unit
    todoRequests state _ _ (Run.Reactor.queue_spec.1 row .unit todoRequests atNext)

-- Law reader: the repository handles its list row while the queue stays unchanged.
example (remaining : List Val) (state : Test.Dogfood.Scenario.Todo.Repo × List String) :
    Run.Reactor.tensor Run.Reactor.queue recordedRepository
      Examples.Todo.TodoRepo.row.all.row .unit (remaining, state) =
      (recordedRepository Examples.Todo.TodoRepo.row.all.row .unit state).map
        (fun (answer, next) => (answer, (remaining, next))) :=
  Run.Reactor.tensor_right Run.Reactor.queue recordedRepository
    Examples.Todo.TodoRepo.row.all.row .unit remaining state rfl

-- Law reader: the checked lifetime of the concrete Example fixture requires only typed keys.
example (before after : Built) (_source : exampleBuilt = some before)
    (built : before.session "Example" = .ok after) : Effect4.Api.ServiceSession.foreign after = [] := by
  obtain ⟨_, _, _, closed⟩ := (Built.session_ok_iff before "Example" after).mp built
  exact closed

-- Law reader: an admission refusal keeps its full payload at the generated collision candidate.
example (before : Built)
    (_source : (todoBuilt.bind fun b =>
      (withRow (Object.ofBuilt b) "Session.next").open.toOption) = some before) (candidate : Object)
    (_made : Object.session (Object.ofBuilt before) "TodoApp" = .ok candidate)
    (why : AdmitRefusal) (refused : candidate.open = .error why) :
    Effect4.Api.ServiceSession.finish candidate = .error (.admission why) :=
  (Effect4.Api.ServiceSession.finish_admission_error_iff candidate why).mpr refused

end Test.Api.SessionContract
