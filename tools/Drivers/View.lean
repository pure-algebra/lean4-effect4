import Tools.View.Build
import Effect4.Store.Domain.ProgramWire

/-!
# The view driver: frames of a program built by edits

    lake env lean --run tools/Drivers/View.lean [--motion N] build NAME OUT    a corpus program, built top-down
    lake env lean --run tools/Drivers/View.lean [--motion N] session FILE OUT  the frames of a request file

`NAME` is a program of the wire corpus (`Effect4.Program.Wire.Corpus.all`). `FILE` holds one
session request a line, as `tools/Drivers/Session.lean` reads them. For each frame the driver
writes three outputs of one list of calls (`docs/research/2026-10-09-visual-pipeline.md`):

- `NNN.draw`, the device calls at the ratio 2, which `tools/view/draw` replays to pixels;
- `NNN.svg`, the same calls at the ratio 1;
- `frames.txt`, every frame as characters.

Between two frames it writes `N - 1` frames of motion (`Tools.View.tween`), named after the frame
they lead to: `002-001.draw` comes before `002.draw` in a sorted listing. It reports the splice
check of each spliced edit: the lines outside the edited subtree keep their text, type and note.

`build` also writes `requests.jsonl`, the requests it ran, so the session driver replays them.
-/

open Tools.View Tools.View.Build

/-- A page's width, in logical pixels. -/
def width : Int := 1280

/-- A frame's number, in three digits. -/
def frameName (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

/-- Write one picture's stream (ratio 2) and SVG (ratio 1). -/
def writePicture (out : System.FilePath) (name : String) (W H : Int) (calls : List (Keyed Call)) :
    IO Unit := do
  IO.FS.writeFile (out / s!"{name}.draw")
    ("\n".intercalate (stream W.toNat H.toNat 2 (lowerAll 2 calls)) ++ "\n")
  IO.FS.writeFile (out / s!"{name}.svg") (svg W.toNat H.toNat 1 (lowerAll 1 calls) ++ "\n")

/-- Write each frame's outputs into `out`, with `motion - 1` frames before each frame after the
first that move its lines from the frame before (`tween`). Report the splice check: the lines
outside each spliced edit's subtree keep their text, type and note (`keptUnchanged`). -/
def writeFrames (out : System.FilePath) (frames : List Build.Frame) (motion : Nat) : IO Unit := do
  IO.FS.createDirAll out
  let mut text : Array String := #[]
  let mut prev : Option Page := none
  let mut kept := 0
  let mut same := 0
  let mut spliced := 0
  for (f, i) in frames.zipIdx do
    let g := f.page
    let name := frameName (i + 1)
    if let some g0 := prev then
      for t in List.range' 1 (motion - 1) do
        let (W, H) := tweenSize width g0 g
        writePicture out s!"{name}-{frameName t}" W H (tween width g0 g t motion)
      if f.spliced then
        if let some a := f.edit then
          let (n, k) := keptUnchanged g0 g (Program.bracket a)
          kept := kept + n
          same := same + k
          spliced := spliced + 1
    let (W, H) := pageSize width g
    writePicture out name W H (pageCalls width g)
    text := text ++ (pageText g).toArray ++ #[""]
    prev := some g
  IO.FS.writeFile (out / "frames.txt") ("\n".intercalate text.toList)
  IO.println s!"view: {frames.length} frames in {out}, {motion - 1} between each two"
  IO.println s!"C\tkept-lines-unchanged\t{spliced} spliced edits\t{same} of {kept} lines"

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

/-- The frames of motion between two frames, from `--motion N` (default 6; 1 draws none). -/
def motionOf : List String → Nat × List String
  | "--motion" :: n :: rest => (n.toNat?.getD 6, rest)
  | rest => (6, rest)

def main (args : List String) : IO UInt32 := do
  let (motion, args) := motionOf args
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
        writeFrames out (Build.frames name reqs) motion
        return 0
  | ["session", file, out] =>
    writeFrames out (Build.frames file (← readRequests file)) motion
    return 0
  | _ =>
    IO.eprintln "usage: view [--motion N] (build NAME | session FILE) OUT"
    return 2
