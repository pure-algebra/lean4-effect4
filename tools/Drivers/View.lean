import Tools.View.Build
import Tools.View.Run
import Tools.View.Specimen
import Effect4.Store.Domain.ProgramWire

/-!
# The view driver: frames of a program built by edits

    lake env lean --run tools/Drivers/View.lean [--motion N] [--plain] build NAME OUT    a corpus program, built top-down
    lake env lean --run tools/Drivers/View.lean [--motion N] [--plain] run NAME OUT    a corpus program, run step by step
    lake env lean --run tools/Drivers/View.lean [--motion N] [--plain] session FILE OUT  the frames of a request file
    lake env lean --run tools/Drivers/View.lean [--motion N] specimen OUT                a graph built one edge at a time

`NAME` is a program of the wire corpus (`Effect4.Program.Wire.Corpus.all`). `FILE` holds one
session request a line, as `tools/Drivers/Session.lean` reads them. For each frame the driver
writes three outputs of one list of calls (`docs/research/2026-10-09-visual-pipeline.md`):

- `NNN.draw`, the device calls at the ratio 2, which `tools/view/draw` replays to pixels;
- `NNN.svg`, the same calls at the ratio 1;
- `frames.txt`, every frame as characters.

Between two frames it writes `N - 1` pictures of motion (`Tools.View.sample`), named after the frame
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

/-- Write each frame's outputs into `out`, with `motion - 1` pictures before each frame after the
first: the moments of the step from the frame before (`sample`). Each step's moment at its end is
the next frame by `sample_end`, so no check repeats it. Report the splice check: the lines
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
      for k in List.range' 1 (motion - 1) do
        let moment := sample {} g0 g (k * 1000 / motion)
        let (W, H) := pageSize width moment
        writePicture out s!"{name}-{frameName k}" W H (pageCalls width moment)
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
  let graphs := frames.filterMap fun f => f.page.graph.map (·.2)
  IO.println s!"view: {frames.length} frames in {out}, {motion - 1} between each two"
  IO.println s!"C\tkept-lines-unchanged\t{spliced} spliced edits\t{same} of {kept} lines"
  IO.println s!"C\tgraph-boxes-apart\t{graphs.length} graphs\t{(graphs.filter Laid.boxesApart).length} apart"

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

/-- The settings of a run: the pictures of motion between two frames (`--motion N`, default 20;
1 draws none), and whether the marks are drawn (`--plain` draws none). -/
structure Settings where
  motion : Nat := 20
  marks : Bool := true

/-- Read the flags before the command. -/
def settingsOf : List String → Settings × List String
  | "--motion" :: n :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with motion := n.toNat?.getD 20 }, rest)
  | "--plain" :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with marks := false }, rest)
  | rest => ({}, rest)

/-- The frames, with the settings' marks. -/
def withMarks (st : Settings) (frames : List Build.Frame) : List Build.Frame :=
  frames.map fun f => { f with page := { f.page with marks := st.marks } }

def main (args : List String) : IO UInt32 := do
  let (st, args) := settingsOf args
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
        writeFrames out (withMarks st (Build.frames name reqs)) st.motion
        return 0
  | ["run", name, out] =>
    match List.lookup name Effect4.Program.Wire.Corpus.all with
    | none =>
      IO.eprintln s!"view: no corpus program {name}; the programs are {Effect4.Program.Wire.Corpus.all.map (·.1)}"
      return 2
    | some p =>
      match Tools.View.Run.frames name p with
      | none =>
        IO.eprintln s!"view: {name} is not admitted, so it does not run"
        return 1
      | some pages =>
        writeFrames out (withMarks st (pages.map fun page => ({ page } : Build.Frame))) st.motion
        return 0
  | ["specimen", out] =>
    writeFrames out (Tools.View.Specimen.frames.map fun page => ({ page } : Build.Frame)) st.motion
    return 0
  | ["session", file, out] =>
    writeFrames out (withMarks st (Build.frames file (← readRequests file))) st.motion
    return 0
  | _ =>
    IO.eprintln "usage: view [--motion N] [--plain] (build NAME | run NAME | session FILE | specimen) OUT"
    return 2
