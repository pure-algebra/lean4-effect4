import Tools.View.Build
import Tools.View.Run
import Tools.View.Specimen
import Tools.View.FlowSpecimen
import Tools.View.Tokens
import Tools.View.Output
import Effect4.Store.Domain.ProgramWire

/-!
# The view driver: frames of a program built by edits

    lake env lean --run tools/Drivers/View.lean [FLAGS] build NAME OUT      a corpus program, built top-down
    lake env lean --run tools/Drivers/View.lean [FLAGS] run NAME OUT        a corpus program, run step by step
    lake env lean --run tools/Drivers/View.lean [FLAGS] session FILE OUT    the frames of a request file
    lake env lean --run tools/Drivers/View.lean [FLAGS] specimen OUT        a graph built one edge at a time
    lake env lean --run tools/Drivers/View.lean [FLAGS] flows OUT           the program graph's cases, one program a page
    lake env lean --run tools/Drivers/View.lean looks DIR OUT               every look of DIR, side by side

The flags: `--motion N`, the pictures of motion between two frames (default 20; 1 draws none);
`--plain`, no marks; `--look LOOK`, the look (`Tools.View.Look`): a token file, or the name of
one in `tools/view/looks/` (default: the dark look, the base of every other).

`NAME` is a program of the wire corpus (`Effect4.Program.Wire.Corpus.all`). `FILE` holds one
session request a line, as `tools/Drivers/Session.lean` reads them. For each frame the driver
writes three outputs of one list of calls (`docs/research/2026-10-09-visual-pipeline.md`):

- `NNN.draw`, the device calls at the ratio 2 in the look, which `tools/view/draw` replays to
  pixels;
- `NNN.svg`, the same calls at the ratio 1, with the look's classes and values;
- `frames.txt`, every frame as characters.

`looks` reads every token file of `DIR` over the dark look. For each look, and for the dark look
itself, it writes `OUT/NAME/`: the look's whole token file and its CSS, and two pages in the look,
the graph specimen's last frame and pFork's last frame built, as `.draw` and `.svg`. `OUT/index.html`
shows the looks side by side, and `OUT/looks.css` holds every look's custom properties and the
class rules. It reports whether each look comes back from its own written token file.

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

/-- Write one picture's stream (ratio 2) and SVG (ratio 1), in a look. -/
def writePicture (L : Look) (out : System.FilePath) (name : String) (W H : Int) (calls : List (Keyed Call)) :
    IO Unit := do
  IO.FS.writeFile (out / s!"{name}.draw")
    ("\n".intercalate (stream L W.toNat H.toNat 2 (lowerAll 2 calls)) ++ "\n")
  IO.FS.writeFile (out / s!"{name}.svg") (svg L W.toNat H.toNat 1 (lowerAll 1 calls) ++ "\n")

/-- Write one page, in a look. -/
def writePage (L : Look) (out : System.FilePath) (name : String) (g : Page) : IO Unit := do
  let (W, H) := pageSize width g
  writePicture L out name W H (pageCalls L width g)

/-- Write each frame's outputs into `out`, with `motion - 1` pictures before each frame after the
first: the moments of the step from the frame before (`sample`). Each step's moment at its end is
the next frame by `sample_end`, so no check repeats it. Report the splice check: the lines
outside each spliced edit's subtree keep their text, type and note (`keptUnchanged`). -/
def writeFrames (L : Look) (out : System.FilePath) (frames : List Build.Frame) (motion : Nat) : IO Unit := do
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
        writePage L out s!"{name}-{frameName k}" (sample L.motion g0 g (k * 1000 / motion))
      if f.spliced then
        if let some a := f.edit then
          let (n, k) := keptUnchanged g0 g (Program.bracket a)
          kept := kept + n
          same := same + k
          spliced := spliced + 1
    writePage L out name g
    text := text ++ (pageText g).toArray ++ #[""]
    prev := some g
  IO.FS.writeFile (out / "frames.txt") ("\n".intercalate text.toList)
  let graphs := frames.filterMap fun f => f.page.graph.map (·.laid)
  IO.println s!"view: {frames.length} frames in {out}, {motion - 1} between each two"
  IO.println s!"C\tkept-lines-unchanged\t{spliced} spliced edits\t{same} of {kept} lines"
  IO.println s!"C\tgraph-boxes-apart\t{graphs.length} graphs\t{(graphs.filter Laid.boxesApart).length} apart"
  IO.println s!"C\tgraph-edges-descend\t{graphs.length} graphs\t{(graphs.filter Laid.edgesDescend).length} descend"
  IO.println s!"C\tgraph-dims-valid\t{graphs.length} graphs\t{(graphs.filter Laid.dimsValid).length} valid"

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
1 draws none), whether the marks are drawn (`--plain` draws none), and the look (`--look`). -/
structure Settings where
  motion : Nat := 20
  marks : Bool := true
  look : Option String := none

/-- Read the flags before the command. -/
def settingsOf : List String → Settings × List String
  | "--motion" :: n :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with motion := n.toNat?.getD 20 }, rest)
  | "--plain" :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with marks := false }, rest)
  | "--look" :: l :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with look := some l }, rest)
  | rest => ({}, rest)

/-- The frames, with the settings' marks. -/
def withMarks (st : Settings) (frames : List Build.Frame) : List Build.Frame :=
  frames.map fun f => { f with page := { f.page with marks := st.marks } }

/-- The folder of the looks. -/
def looksDir : System.FilePath := "tools/view/looks"

/-- A look's name: its file's name without `.tokens.json`. -/
def lookName (path : System.FilePath) : String := (path.fileName.getD "look").replace ".tokens.json" ""

/-- A look's token file read over the dark look; a refusal names the token and the reason. -/
def readLookFile (path : System.FilePath) : IO Look := do
  match Tokens.parseLook {} (lookName path) (← IO.FS.readFile path) with
  | .ok L => pure L
  | .error why => throw (IO.userError s!"view: the look {path} is refused at {why}")

/-- The look a `--look` names: the dark look by default or by name, a file of `tools/view/looks/`
by its name, or a token file by its path. -/
def lookOf : Option String → IO Look
  | none | some "dark" => pure {}
  | some l => readLookFile (if l.endsWith ".json" then l else looksDir / s!"{l}.tokens.json")

/-- The token files of a folder, in order of name. -/
def lookFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let entries ← dir.readDir
  let files := entries.toList.filter (·.fileName.endsWith ".tokens.json") |>.map (·.path)
  pure (files.mergeSort fun a b => decide (a.toString ≤ b.toString))

/-- The page of the looks side by side, in the dark look's own properties. -/
def looksIndex (looks : List Look) : String :=
  let figure (L : Look) : String :=
    s!"<section><h2>{escape L.name}</h2><p>{escape L.description}</p>" ++
    s!"<p class=\"files\"><a href=\"{L.name}/{L.name}.tokens.json\">tokens</a> · <a href=\"{L.name}/{L.name}.css\">css</a></p>" ++
    s!"<div class=\"pair\"><img src=\"{L.name}/specimen.svg\" alt=\"the graph specimen in {escape L.name}\"><img src=\"{L.name}/program.svg\" alt=\"pFork built, in {escape L.name}\"></div></section>\n"
  "<!doctype html>\n<html lang=\"en\" data-look=\"dark\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>Looks</title>\n" ++
  "<link rel=\"stylesheet\" href=\"looks.css\">\n<style>\n" ++
  "body { margin: 0; padding: 24px 16px 48px; background: var(--e4-color-ground); color: var(--e4-color-ink); font-family: var(--e4-font-name-family); }\n" ++
  "h1 { font-family: var(--e4-font-title-family); font-weight: var(--e4-font-title-weight); margin: 0 0 4px; }\n" ++
  "h2 { font-family: var(--e4-font-data-family); font-size: 15px; margin: 32px 0 2px; }\n" ++
  "p { margin: 0 0 6px; max-width: 72ch; font-style: var(--e4-font-label-style); }\n" ++
  ".files a { color: var(--e4-color-ink); font-family: var(--e4-font-data-family); font-size: 13px; font-style: normal; }\n" ++
  ".pair { display: grid; grid-template-columns: repeat(auto-fit, minmax(320px, 1fr)); gap: 12px; align-items: start; }\n" ++
  ".pair img { width: 100%; height: auto; border: 1px solid var(--e4-color-rule); }\n" ++
  "</style>\n</head>\n<body>\n<h1>Looks</h1>\n" ++
  "<p>Each look is a token file of the W3C design-token format, read over the dark look. The same two pages are drawn in each.</p>\n" ++
  String.join (looks.map figure) ++ "</body>\n</html>\n"

/-- Write every look of `dir`, and the dark look, side by side into `out`. -/
def writeLooks (dir out : System.FilePath) : IO UInt32 := do
  let files ← lookFiles dir
  let looks := ({} : Look) :: (← files.mapM readLookFile)
  let some specimen := Tools.View.Specimen.frames.getLast? | throw (IO.userError "view: the specimen has no frame")
  let some program := (List.lookup "pFork" Effect4.Program.Wire.Corpus.all >>= Build.requests).bind
      fun reqs => (Build.frames "pFork" reqs).getLast?.map (·.page)
    | throw (IO.userError "view: pFork has no frame built")
  IO.FS.createDirAll out
  for L in looks do
    let dirL := out / L.name
    IO.FS.createDirAll dirL
    IO.FS.writeFile (dirL / s!"{L.name}.tokens.json") (Tokens.render L)
    IO.FS.writeFile (dirL / s!"{L.name}.css") (Tokens.css L)
    writePage L dirL "specimen" specimen
    writePage L dirL "program" program
  IO.FS.writeFile (out / "looks.css") (String.join (looks.map Tokens.css) ++ Tokens.rules)
  IO.FS.writeFile (out / "index.html") (looksIndex looks)
  let back := looks.filter (Tokens.roundTrips {})
  IO.println s!"view: {looks.length} looks in {out}"
  IO.println s!"C\tlook-round-trip\t{looks.length} looks\t{back.length} come back from their token files"
  return if back.length == looks.length then 0 else 1

def main (args : List String) : IO UInt32 := do
  let (st, args) := settingsOf args
  if let ["looks", dir, out] := args then return ← writeLooks dir out
  let L ← lookOf st.look
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
        writeFrames L out (withMarks st (Build.frames name reqs)) st.motion
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
        writeFrames L out (withMarks st (pages.map fun page => ({ page } : Build.Frame))) st.motion
        return 0
  | ["specimen", out] =>
    writeFrames L out (Tools.View.Specimen.frames.map fun page => ({ page } : Build.Frame)) st.motion
    return 0
  | ["flows", out] =>
    writeFrames L out (Tools.View.FlowSpecimen.frames.map fun page => ({ page } : Build.Frame)) st.motion
    return 0
  | ["session", file, out] =>
    writeFrames L out (withMarks st (Build.frames file (← readRequests file))) st.motion
    return 0
  | _ =>
    IO.eprintln "usage: view [--motion N] [--plain] [--look LOOK] (build NAME | run NAME | session FILE | specimen | flows) OUT\n       view looks DIR OUT"
    return 2
