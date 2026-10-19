import Effect4.Tool.Wire
import Tools.WireText
import Effect4.Api.Codegen
import Effect4.Program.Authoring

/-!
# The authoring tool: the controls

`Effect4.Tool.serve` answers one request against the tool's state; `tools/Drivers/Workspace.lean`
reads one request envelope a line (`Tools.WireText`) and prints its reply.

* **Red (tested): a request the tool refuses, with the state unchanged.** An edit before an open;
  a revert of an entry the history does not hold.
* **Red (tested): a line the wire refuses.** A natural that binary64 would round (Codex's
  JSON-01) does not read.
* **Control: the boundary.** 2^53, the last natural binary64 holds with its successor rounded,
  reads; so does 2^53 + 2.
* **Tested: runs.** A closed program starts and finishes; a host program plays its scripted
  answer through `Live.feed`.
-/

set_option autoImplicit false

namespace Test.Program.ToolControls

open Effect4 Effect4.Program Effect4.Program.Check Effect4.Tool

def serve1 (s : State) (r : Request) : State × Reply := (serve Oracle.uncached s r).value

-- red (tested): an edit before an open is refused, and the state stays empty
#guard
  let (s, reply) := serve1 empty (.act (.edit ⟨⟨"none", 0⟩, 0⟩ (.draft (.fill [0] (.succeed (.lit .unit))))))
  s.transcript.isEmpty && match reply.result with | .error .noDocument => true | _ => false

def opened (program : NativeEff) (app : SigApp := {}) : State × Reply :=
  serve1 empty (.act (.open_ "n" app ⟨program, []⟩))

-- red (tested): a revert of an entry the history does not hold is refused
#guard
  let (s, _) := opened (.succeed (.lit (.nat 1)))
  let (s', reply) := serve1 s (.act (.edit ⟨⟨"n", 0⟩, 0⟩ (.revert 0)))
  s'.transcript.length == s.transcript.length &&
    match reply.result with | .error (.doc (.noEntry 0)) => true | _ => false

-- An open of `succeed` of a natural, as the JSON line an agent writes, reads or not. The text
-- stays inside each guard: a battery definition over rendered text reaches `Classical.choice`.

-- red (tested): 2^53 + 1, which binary64 rounds to 2^53, does not read, so it is not changed
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
  "\"value\":{\"_tag\":\"nat\",\"value\":9007199254740993}}}}}}}")).toOption.isNone
-- red (tested): 2^53 and 2^53 + 2 are exact in binary64 but past the profile's bound
-- (`CodecProfile.natLimit`, 2^53 - 1), so they do not read either; 2^53 - 1 reads
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
  "\"value\":{\"_tag\":\"nat\",\"value\":9007199254740992}}}}}}}")).toOption.isNone
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
  "\"value\":{\"_tag\":\"nat\",\"value\":9007199254740994}}}}}}}")).toOption.isNone
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
  "\"value\":{\"_tag\":\"nat\",\"value\":9007199254740991}}}}}}}")).toOption.isSome

-- tested: a closed program starts and finishes with its exit
#guard
  let (s, _) := opened (.succeed (.lit (.nat 42)))
  let (_, reply) := serve1 s (.act (.start ⟨⟨"n", 0⟩, 0⟩ {}))
  match reply.result with
  | .ok (.acted (.started _ _ view)) => view.exit == some (.success (.nat 42))
  | _ => false

-- tested: a host program plays its scripted answer through `Live.feed`
#guard
  let row : Row := (Authoring.Row.host "Todos.add" .string .nat .never "test").row
  let (s, _) := opened (.perform (.external 0) (.lit (.str "milk"))) (.ofTable [row])
  let (s, _) := serve1 s (.act (.start ⟨⟨"n", 0⟩, 0⟩ {}))
  let answer : Api.HostSession.Answer := .ofExit (.success (.nat 1))
  let (_, reply) := serve1 s (.act (.play ⟨0⟩
    [.receive (.row "Todos.add") answer, .apply (.row "Todos.add"), .flush]))
  match reply.result with
  | .ok (.acted (.played _ _ view)) => view.exit == some (.success (.nat 1))
  | _ => false

-- tested: a refusal inside a definition's body and an invoked parameter names both (`Eff.defAt`,
-- `Eff.paramAt`, `PrintRefusal.locate`)
#guard
  let decl0 : DefDecl :=
    { name := "listCacheGet", request := .unit, answer := .nat, error := .never, requires := [],
      params := [{ name := "load", request := .unit, answer := .nat, error := .never }] }
  let decl1 : DefDecl :=
    { name := "TodoApp_list", request := .unit, answer := .nat, error := .never, requires := [] }
  let root : NativeEff :=
    .defs [decl0, decl1]
      (.cons (.succeed (.lit (.nat 0)))
        (.cons (.invoke 0 (.lit .unit) (.cons (.succeed (.var 9)) .nil)) .nil))
      (.succeed (.lit (.nat 0))) .nil
  let path : List Nat := [0, 1, 0, 0, 0]
  root.defAt path == some "TodoApp_list" &&
    root.paramAt (nativeSignature []) path == some ("listCacheGet", "load") &&
    Codegen.PrintRefusal.locate (nativeSignature []) root
      (.callbackRequirement [0, 1, 0]) ==
      some (some "TodoApp_list", some ("listCacheGet", "load"))

end Test.Program.ToolControls
