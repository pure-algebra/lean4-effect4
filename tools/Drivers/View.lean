import Tools.View.Build
import Effect4.Store.Domain.ProgramWire

/-!
# The view driver: frames of a program built by edits

    lake env lean --run tools/Drivers/View.lean build NAME OUT      a corpus program, built top-down
    lake env lean --run tools/Drivers/View.lean session FILE OUT    the frames of a request file

`NAME` is a program of the wire corpus (`Effect4.Program.Wire.Corpus.all`). `FILE` holds one
session request a line, as `tools/Drivers/Session.lean` reads them. For each frame the driver
writes three outputs of one list of calls (`docs/research/2026-10-09-visual-pipeline.md`):

- `NNN.draw`, the device calls at the ratio 2, which `tools/view/draw` replays to pixels;
- `NNN.svg`, the same calls at the ratio 1;
- `frames.txt`, every frame as characters.

`build` also writes `requests.jsonl`, the requests it ran, so the session driver replays them.
-/

open Tools.View

/-- A page's width, in logical pixels. -/
def width : Int := 1280

/-- A frame's number, in three digits. -/
def frameName (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

/-- Write each page's three outputs into `out`. -/
def writeFrames (out : System.FilePath) (pages : List Page) : IO Unit := do
  IO.FS.createDirAll out
  let mut text : Array String := #[]
  for (g, i) in pages.zipIdx do
    let calls := pageCalls width g
    let (W, H) := pageSize width g
    let name := frameName (i + 1)
    IO.FS.writeFile (out / s!"{name}.draw")
      ("\n".intercalate (stream W.toNat H.toNat 2 (lowerAll 2 calls)) ++ "\n")
    IO.FS.writeFile (out / s!"{name}.svg") (svg W.toNat H.toNat 1 (lowerAll 1 calls) ++ "\n")
    text := text ++ (pageText g).toArray ++ #[""]
  IO.FS.writeFile (out / "frames.txt") ("\n".intercalate text.toList)
  IO.println s!"view: {pages.length} frames in {out}"

/-- Read a request file: one JSON object a line; a blank line is skipped. -/
def readRequests (file : System.FilePath) : IO (List Tools.Session.Request) := do
  let lines ← IO.FS.lines file
  let mut out : Array Tools.Session.Request := #[]
  for line in lines do
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    match Lean.Json.parse line >>= Tools.Session.Request.fromJson? with
    | .ok r => out := out.push r
    | .error e => throw (IO.userError s!"view: a request does not read: {e}")
  return out.toList

def main (args : List String) : IO UInt32 := do
  match args with
  | ["build", name, out] =>
    match List.lookup name Effect4.Program.Wire.Corpus.all with
    | none =>
      IO.eprintln s!"view: no corpus program {name}; the programs are {Effect4.Program.Wire.Corpus.all.map (·.1)}"
      return 2
    | some p =>
      match Build.requests p with
      | none =>
        IO.eprintln s!"view: a sub-program of {name} has no type, so it has no hole row"
        return 1
      | some reqs =>
        IO.FS.createDirAll out
        IO.FS.writeFile (System.FilePath.mk out / "requests.jsonl")
          ("\n".intercalate (reqs.map fun r => r.toJson.compress) ++ "\n")
        writeFrames out (Build.frames name reqs)
        return 0
  | ["session", file, out] =>
    writeFrames out (Build.frames file (← readRequests file))
    return 0
  | _ =>
    IO.eprintln "usage: view (build NAME | session FILE) OUT"
    return 2
