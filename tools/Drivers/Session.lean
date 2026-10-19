import Effect4.Tool.Native

/-!
# The session driver

It reads one JSON envelope for each line of standard input, serves it, and prints one JSON reply
for each. A request is an `Envelope Request`: the method's name, its version (1), and the request,
in the Tool group's generated JSON (`Tool/ToolDerived.lean`). A blank line is skipped.

It is the native shell's loop (`ocaml/engine/kit/kit_tool.ml`) in Lean, over the same code:
- the profile's text grammar reads the line (`NatJson.parse`, `Store/Domain/JsonText.lean`);
- the session reads the tree under the request envelope's shape, serves it through the checker
  memo, and prints the reply envelope (`Tool.Native.serveTree`);
- the reply is the tree's compact text (`NatJson.render`), written as its bytes.

So both drivers read one text by one grammar and answer it by one function. The memo changes
cost, never an answer (`Tool.serve_transparent`). A line that does not read prints
`{"refused":"JSON text at byte N: expected …"}` (`NatJson.refusalText`), and a wire refusal
prints `{"refused": …}` with the refusal's tree (`Tool.Native.refusalTree`). Neither changes the
session.

    lake env lean --run tools/Drivers/Session.lean < requests.jsonl
-/

open Effect4 Effect4.Tool

/-- Write a tree's compact text, its bytes as they are, and a line feed. -/
def printTree (out : IO.FS.Stream) (t : NatJson) : IO Unit := do
  out.write (ByteArray.mk ((NatJson.render t).map UInt8.ofNat).toArray)
  out.write (ByteArray.mk #[10])
  out.flush

/-- A refusal line's tree: `{"refused": why}`. -/
def refusedTree (why : NatJson) : NatJson := .obj [("refused", why)]

/-- Answer each line of standard input, holding the session between lines. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut session : Native.Session := Native.start
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let text := line.trimAscii.toString
    if text.isEmpty then
      continue
    match NatJson.parse (NatJson.codes text) with
    | .error why => printTree stdout (refusedTree (.str (NatJson.refusalText why)))
    | .ok request =>
      match Native.serveTree session request with
      | .ok (reply, next) =>
        session := next
        printTree stdout reply
      | .error why => printTree stdout (refusedTree (Native.refusalTree why))
