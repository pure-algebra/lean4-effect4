import Tools.Session
import Effect4.Api.Codegen

/-!
# The session tool: the controls

`tools/Tools/Session.lean` holds an edit session between its lines. `tools/Drivers/Session.lean`
prints `Tools.Session.answerLine` for each line of its input.

* **Red (tested): a request with no answer.** An edit before an open; bytes that do not decode;
  an undo with an empty journal; a natural that binary64 would round (Codex's JSON-01).
* **Control: the boundary.** 2^53, the last natural binary64 holds with its successor rounded,
  opens.
-/

set_option autoImplicit false

namespace Test.Program.SessionToolControls

open Tools.Session

-- red (tested): an edit before an open has no answer
#guard !(answer {} { op := "fill", path := [0] }).2.ok
-- red (tested): an open whose program's bytes do not decode
#guard !(answer {} { op := "open", program := some "00" }).2.ok
-- red (tested): an undo with an empty journal, after the transcript's open
#guard (match Tools.Query.fixtureLines (include_str "../fixtures/session/requests.jsonl") with
  | openLine :: _ => !(answer (answerLine {} openLine).1 { op := "undo" }).2.ok
  | [] => false)

-- An open of `succeed` of a natural, as the JSON an agent writes, answers ok or not. The text
-- stays inside each guard: a battery definition over rendered text reaches `Classical.choice`.

-- red (tested): 2^53 + 1, which binary64 rounds to 2^53, is refused, not changed (JSON-01)
#guard ((answerLine {} ("{\"op\":\"open\",\"programJson\":{\"_tag\":\"succeed\",\"value\":" ++
  "{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":9007199254740993}}}}")).2.splitOn
  "\"ok\":true").length == 1
-- control: 2^53 itself opens, and so does 2^53 + 2, which binary64 holds
#guard ((answerLine {} ("{\"op\":\"open\",\"programJson\":{\"_tag\":\"succeed\",\"value\":" ++
  "{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":9007199254740992}}}}")).2.splitOn
  "\"ok\":true").length == 2
#guard ((answerLine {} ("{\"op\":\"open\",\"programJson\":{\"_tag\":\"succeed\",\"value\":" ++
  "{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":9007199254740994}}}}")).2.splitOn
  "\"ok\":true").length == 2

-- tested: `run` on a closed program answers the exit, `syncExit` and `Live.reached`
#guard
  let r0 := answer {}
    { op := "open", program := some (Tools.JsonBridge.toHex
        (Effect4.Program.Eff.succeed (.lit (.nat 42)) : Effect4.Program.NativeEff)) }
  let ans := (answer r0.1 { op := "run" }).2
  ans.ok && ans.laws == [``Effect4.Live.reached] &&
    ans.result.getObjValD "exit" ==
      Tools.JsonBridge.printJson (.success (.nat 42) : Effect4.Machine.ExitV) &&
    ans.result.getObjValD "syncExit" ==
      Tools.JsonBridge.printJson (.success (.nat 42) : Effect4.Machine.ExitV)

-- tested: `run` on a host program feeds the scripted host answers through `Live.feedAll`
#guard
  let row : Effect4.Program.Row :=
    (Effect4.Program.Authoring.Row.host "Todos.add" .string .nat .never "test").row
  let prog : Effect4.Program.NativeEff := .perform (.external 0) (.lit (.str "milk"))
  let ans0 : Effect4.Api.HostSession.Answer := .ofExit (.success (.nat 1))
  let r0 := answer {}
    { op := "open", program := some (Tools.JsonBridge.toHex prog),
      rows := some (Tools.JsonBridge.toHex [row]) }
  let ans := (answer r0.1
    { op := "run", answers := some (Tools.JsonBridge.toHex [("Todos.add", ans0)]) }).2
  ans.ok && ans.laws == [``Effect4.Live.reached] &&
    ans.result.getObjValD "exit" ==
      Tools.JsonBridge.printJson (.success (.nat 1) : Effect4.Machine.ExitV)

-- tested: a refusal inside a definition's body and an invoked parameter names both (`Eff.defAt`,
-- `Eff.paramAt`, `PrintRefusal.locate`)
#guard
  let decl0 : Effect4.Program.DefDecl :=
    { name := "listCacheGet", request := .unit, answer := .nat, error := .never, requires := [],
      params := [{ name := "load", request := .unit, answer := .nat, error := .never }] }
  let decl1 : Effect4.Program.DefDecl :=
    { name := "TodoApp_list", request := .unit, answer := .nat, error := .never, requires := [] }
  let root : Effect4.Program.NativeEff :=
    .defs [decl0, decl1]
      (.cons (.succeed (.lit (.nat 0)))
        (.cons (.invoke 0 (.lit .unit) (.cons (.succeed (.var 9)) .nil)) .nil))
      (.succeed (.lit (.nat 0))) .nil
  let path : List Nat := [0, 1, 0, 0, 0]
  root.defAt path == some "TodoApp_list" &&
    root.paramAt (Effect4.Program.nativeSignature []) path == some ("listCacheGet", "load") &&
    Effect4.Codegen.PrintRefusal.locate (Effect4.Program.nativeSignature []) root
      (.callbackRequirement [0, 1, 0]) ==
      some (some "TodoApp_list", some ("listCacheGet", "load"))

end Test.Program.SessionToolControls

