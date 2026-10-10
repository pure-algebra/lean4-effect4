import Compare
import Tools.View.Output

open Effect4 Tools.View

def main (args : List String) : IO Unit := do
  let out := System.FilePath.mk (args.head?.getD "host.svg")
  match Api.Author.Internal.finishBuild hostProgram [hostRow] [("read", 0)] with
  | .error _ => throw (IO.userError "host rendering control was refused")
  | .ok b =>
    let pages := Tools.View.Run.framesBuilt "host" b 32
    let some page := pages.getLast? | throw (IO.userError "host rendering control has no page")
    let (w, h) := pageSize 1280 page
    let text := svg {} w.toNat h.toNat 1 (lowerAll 1 (pageCalls {} 1280 page))
    IO.FS.writeFile out (text ++ "\n")
    IO.println s!"host frames={pages.length}; source lines={page.lines.size}; code retained at live frontier"
