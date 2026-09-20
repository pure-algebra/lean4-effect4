import Lean
import Tools.GeneratedStamp
import Tools.ArchitectureRoles

/-!
# Tools.Architecture — the architecture map, measured from the tree

    lake env lean -M6144 --run tools/Tools/Architecture.lean [--check] [--out <path>]

Writes `docs/core/architecture-map.html`: the roots and their measured import direction, the
typed-state proof stack with its planned modules, the file map by role, the generated groups,
the pinned packages, and an audit of what the tree says against what the role register
declares. `make gen-architecture` runs it; `--check` regenerates in memory and fails on drift,
for a landing that wants the receipt. It is not in `make check`: the map is a report.

What is measured, and how:

- every `.lean` file under `src/`, `tools/` and `Test/`, its line count, and its imports through
  `Lean.Elab.parseImports`, the parser the compiler uses on the same header;
- the roots of `Tools.Architecture.roots`, loaded with `importModules`, for the theorems,
  definitions and inductives each module declares (auxiliary declarations skipped by name);
- every estate outside the Lean roots by file walk, lines counted for text extensions;
- the generated groups from `docs/GENERATED.md`'s table and the pinned packages from
  `lakefile.toml`, read as text so the map cannot disagree with either.

What is declared, in `Tools.ArchitectureRoles`: the areas and their roles, the column and
height of each, the layering rule, the accepted exceptions, the milestone's modules. The
register is total: a Lean file under no area, or an area whose path does not exist, stops the
run with the name. Nothing else stops it.

A tool (`lakefile.toml`, the `Tools` library): outside the axiom gate, imported by nothing.
-/

open Lean System

namespace Tools.Architecture

/-! ## Measuring -/

/-- One Lean source file, as the map sees it. -/
structure LeanFile where
  path : String
  module : Name
  lines : Nat
  imports : Array Name
  driver : Bool
  built : Bool
deriving Inhabited

/-- What a module declares, by kind, auxiliaries excluded. -/
structure Counts where
  theorems : Nat := 0
  defs : Nat := 0
  inductives : Nat := 0
deriving Inhabited

def Counts.add (a b : Counts) : Counts :=
  ⟨a.theorems + b.theorems, a.defs + b.defs, a.inductives + b.inductives⟩

/-- Newlines, which is what `wc -l` counts. -/
def countLines (s : String) : Nat :=
  s.foldl (fun n c => if c == '\n' then n + 1 else n) 0

/-- Prefix and suffix removal as `String`s: the toolchain's `drop` answers a slice. -/
def dropStr (s : String) (n : Nat) : String := (s.toSubstring.drop n).toString
def dropRightStr (s : String) (n : Nat) : String := (s.toSubstring.dropRight n).toString

/-- Directories the walk never enters: hidden ones, installs, build trees. -/
def skipDir (p : FilePath) : Bool :=
  let name := p.fileName.getD ""
  name.startsWith "." || name == "node_modules" || name == "_build"

/-- Every file under `root`, in walk order, with the skipped directories left out. -/
def files (root : FilePath) : IO (Array FilePath) := do
  unless ← root.pathExists do return #[]
  if !(← root.isDir) then return #[root]
  let entries ← root.walkDir fun d => pure (!skipDir d)
  entries.filterM fun p => do return !(← p.isDir)

/-- The module a source path names: under `src/` or `tools/` the remaining components, under
`Test/` all of them, the extension dropped. -/
def moduleOf (path : String) : Name :=
  let rel := if path.startsWith "src/" then dropStr path 4
    else if path.startsWith "tools/" then dropStr path 6 else path
  let rel := if rel.endsWith ".lean" then dropRightStr rel 5 else rel
  (rel.splitOn "/").foldl (fun n c => Name.str n c) .anonymous

def nameOfString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => Name.str n c) .anonymous

/-- A file declares `main` when a line starts with `def main`, with or without `unsafe`
or `partial`: the shape every driver of this tree has. -/
def declaresMain (source : String) : Bool :=
  (source.splitOn "\n").any fun line =>
    line.startsWith "def main" || line.startsWith "unsafe def main" ||
      line.startsWith "partial def main"

def readLeanFile (p : FilePath) : IO LeanFile := do
  let path := p.toString
  let source ← IO.FS.readFile p
  let (imports, _, _) ← Lean.Elab.parseImports source (some path)
  let module := moduleOf path
  let olean := Lean.modToFilePath ".lake/build/lib/lean" module "olean"
  return { path, module, lines := countLines source, imports := imports.map (·.module),
           driver := declaresMain source, built := ← olean.pathExists }

/-- Does `a` cover `p`: the area itself, its file, or anything beneath it. -/
def Area.covers (a : Area) (p : String) : Bool :=
  p == a.path || p == a.path ++ ".lean" || p.startsWith (a.path ++ "/")

/-- The longest area covering `p`, and its enclosing non-detail area. -/
def areaOf (p : String) : Option Area :=
  (areas.filter (·.covers p)).foldl (init := none) fun best a =>
    match best with
    | none => some a
    | some b => if a.path.length > b.path.length then some a else some b

def rollupOf (p : String) : Option Area :=
  (areas.filter fun a => !a.detail && a.covers p).foldl (init := none) fun best a =>
    match best with
    | none => some a
    | some b => if a.path.length > b.path.length then some a else some b

/-- The external package a module outside the tree belongs to, by its first component. -/
def externalOf (m : Name) : String :=
  match m.components.head? with
  | some (.str _ s) =>
    if s == "Lean" || s == "Init" || s == "Std" || s == "Lake" then "Lean" else s
  | _ => "?"

/-- One aggregated import edge between two areas, or from an area to an external package. -/
structure Edge where
  src : String
  dst : String
  count : Nat
deriving Inhabited

/-- One import against the declared direction, with the reason a document accepts it, if any. -/
structure Against where
  file : String
  module : Name
  src : String
  dst : String
  accepted : Option String
deriving Inhabited

/-- Auxiliary declarations the compiler and the deriving handlers mint: not the module's
own count. -/
def isNoise (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes || n.components.any fun c =>
    match c with
    | .str _ s =>
      s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        s == "rec" || s == "recOn" || s == "casesOn" || s == "below" || s == "brecOn" ||
        s == "binductionOn" || s == "ibelow" || s == "noConfusion" || s == "noConfusionType" ||
        s == "inj" || s == "injEq" || s == "sizeOf_spec" || s.startsWith "instSizeOf" ||
        s == "ctorIdx" || s == "ctorElim"
    | _ => true

/-- Load the declared roots and count what every loaded module declares. -/
def loadCounts : IO (Std.HashMap Name Counts) := do
  initSearchPath (← findSysroot)
  let imports := roots.toArray.map fun r => ({ module := nameOfString r } : Import)
  let env ← importModules imports {} 0
  let mods := env.header.moduleNames
  return env.constants.fold (init := {}) fun acc name ci =>
    if isNoise name then acc else
    match env.getModuleIdxFor? name with
    | none => acc
    | some idx =>
      let modName := mods[idx.toNat]!
      let old := acc.getD modName {}
      let new := match ci with
        | .thmInfo _ => { old with theorems := old.theorems + 1 }
        | .defnInfo _ | .opaqueInfo _ => { old with defs := old.defs + 1 }
        | .inductInfo _ => { old with inductives := old.inductives + 1 }
        | _ => old
      acc.insert modName new

/-- A measured estate outside the Lean roots. -/
structure Estate where
  area : Area
  fileCount : Nat
  lines : Nat
  byExt : List (String × Nat × Nat)
deriving Inhabited

def textExts : List String :=
  ["ml", "mli", "ts", "tsx", "js", "py", "sh", "md", "json", "tsv", "txt", "toml", "hex", "lean", "yml", "yaml"]

def measureEstate (a : Area) : IO Estate := do
  if !a.measure then return ⟨a, 0, 0, []⟩
  let fs ← files a.path
  let mut byExt : Std.HashMap String (Nat × Nat) := {}
  let mut total := 0
  for f in fs do
    let ext := f.extension.getD "(none)"
    let n ← if textExts.contains ext then do
        let s ← IO.FS.readFile f
        pure (countLines s)
      else pure 0
    total := total + n
    let (c, l) := byExt.getD ext (0, 0)
    byExt := byExt.insert ext (c + 1, l + n)
  let listed := byExt.fold (init := ([] : List (String × Nat × Nat))) fun acc e (c, l) => (e, c, l) :: acc
  let sorted := listed.toArray.qsort (fun x y => x.2.2 > y.2.2 || (x.2.2 == y.2.2 && x.2.1 > y.2.1))
  return ⟨a, fs.size, total, sorted.toList⟩

/-- One row of `docs/GENERATED.md`'s groups table. -/
structure Group where
  name : String
  producer : String
  inputs : String
  consumers : String
  check : String
  evidence : String
deriving Inhabited

def cells (line : String) : List String :=
  let parts := (line.splitOn "|").map String.trim
  let parts := if parts.head? == some "" then parts.drop 1 else parts
  if parts.getLast? == some "" then parts.dropLast else parts

/-- The table under `## The groups`: every row after the header and its rule. -/
def readGroups : IO (List Group) := do
  let text ← IO.FS.readFile "docs/GENERATED.md"
  let lines := text.splitOn "\n"
  let after := lines.dropWhile (fun l => l.trim != "## The groups")
  let table := (after.drop 1).dropWhile (fun l => !l.startsWith "|") |>.takeWhile (·.startsWith "|")
  let rows := table.drop 2
  return rows.filterMap fun l =>
    match cells l with
    | [n, p, i, c, k, e] => some ⟨n, p, i, c, k, e⟩
    | n :: p :: i :: c :: k :: e :: _ => some ⟨n, p, i, c, k, e⟩
    | _ => none

/-- One `[[require]]` of `lakefile.toml`. -/
structure Pin where
  name : String
  git : String
  rev : String
deriving Inhabited

def tomlValue (line : String) : String :=
  match line.splitOn "=" with
  | _ :: rest => ((String.intercalate "=" rest).trim.splitOn "\"").getD 1 ""
  | _ => ""

def readPins : IO (List Pin) := do
  let text ← IO.FS.readFile "lakefile.toml"
  let mut pins : Array Pin := #[]
  let mut cur : Option Pin := none
  for raw in text.splitOn "\n" do
    let line := raw.trim
    if line == "[[require]]" then
      if let some p := cur then pins := pins.push p
      cur := some ⟨"", "", ""⟩
    else if line.startsWith "[[" then
      if let some p := cur then pins := pins.push p
      cur := none
    else if let some p := cur then
      if line.startsWith "name" then cur := some { p with name := tomlValue line }
      else if line.startsWith "git" then cur := some { p with git := tomlValue line }
      else if line.startsWith "rev" then cur := some { p with rev := tomlValue line }
  if let some p := cur then pins := pins.push p
  return pins.toList

/-! ## The facts, assembled -/

structure Facts where
  leanFiles : Array LeanFile
  counts : Std.HashMap Name Counts
  edges : Array Edge
  against : Array Against
  estates : Array Estate
  groups : List Group
  pins : List Pin
  emptyDirs : Array String
  missing : Array String
  uncovered : Array String
deriving Inhabited

/-- Files of an area (its own, by longest prefix). -/
def Facts.own (f : Facts) (a : Area) : Array LeanFile :=
  f.leanFiles.filter fun x => (areaOf x.path).map (·.path) == some a.path

/-- Files of an area and every detail area beneath it. -/
def Facts.rolled (f : Facts) (a : Area) : Array LeanFile :=
  f.leanFiles.filter fun x => (rollupOf x.path).map (·.path) == some a.path

def Facts.countsOf (f : Facts) (xs : Array LeanFile) : Counts :=
  xs.foldl (fun acc x => acc.add (f.counts.getD x.module {})) {}

def linesOf (xs : Array LeanFile) : Nat := xs.foldl (fun n x => n + x.lines) 0

def measure : IO Facts := do
  let mut leanFiles : Array LeanFile := #[]
  let mut dirs : Array String := #[]
  for root in ["src", "tools", "Test"] do
    let entries ← (root : FilePath).walkDir fun d => pure (!skipDir d)
    for e in entries do
      if ← e.isDir then dirs := dirs.push e.toString
      else if e.extension == some "lean" then
        unless notModules.any (fun n => e.toString.startsWith (n ++ "/")) do
          leanFiles := leanFiles.push (← readLeanFile e)
  leanFiles := leanFiles.qsort (·.path < ·.path)
  let counts ← loadCounts
  -- totality of the register, both ways
  let uncovered := (leanFiles.filter fun x => (areaOf x.path).isNone).map (·.path)
  let mut missing : Array String := #[]
  for a in areas do
    unless ← (a.path : FilePath).pathExists do missing := missing.push a.path
  -- the edges
  let byModule : Std.HashMap Name String :=
    leanFiles.foldl (fun m x => m.insert x.module x.path) {}
  let mut edgeCounts : Std.HashMap (String × String) Nat := {}
  let mut against : Array Against := #[]
  for x in leanFiles do
    let some a := rollupOf x.path | continue
    for m in x.imports do
      match byModule.get? m with
      | some target =>
        let some b := rollupOf target | continue
        if a.path == b.path then continue
        edgeCounts := edgeCounts.insert (a.path, b.path) (edgeCounts.getD (a.path, b.path) 0 + 1)
        unless allowed a b do
          let why := accepted.find? fun acc =>
            x.path.startsWith acc.fromPath && m.toString.startsWith acc.toModule
          against := against.push ⟨x.path, m, a.path, b.path, why.map (·.reason)⟩
      | none =>
        let key := (a.path, "ext:" ++ externalOf m)
        edgeCounts := edgeCounts.insert key (edgeCounts.getD key 0 + 1)
  let edges := (edgeCounts.fold (init := (#[] : Array Edge)) fun acc (s, d) n => acc.push ⟨s, d, n⟩)
    |>.qsort fun e f => e.src < f.src || (e.src == f.src && e.dst < f.dst)
  -- the estates
  let mut estates : Array Estate := #[]
  for a in areas do
    if !a.column.isLean && !a.detail then estates := estates.push (← measureEstate a)
  -- directories of the library roots with no Lean file beneath them (leftovers)
  let emptyDirs := dirs.filter fun d =>
    (d.startsWith "src/" || d.startsWith "tools/") && !leanFiles.any fun x => x.path.startsWith (d ++ "/")
  return { leanFiles, counts, edges, against, estates, groups := ← readGroups, pins := ← readPins,
           emptyDirs := emptyDirs.qsort (· < ·), missing, uncovered }

/-! ## Rendering -/

def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | c => acc.push c

/-- Escaped, with backtick spans as `<code>`. -/
def md (s : String) : String := Id.run do
  let parts := s.splitOn "`"
  let mut out := ""
  let mut code := false
  for p in parts do
    out := out ++ (if code then "<code>" ++ esc p ++ "</code>" else esc p)
    code := !code
  return out

def fmt (n : Nat) : String := Id.run do
  let s := toString n
  let len := s.length
  let mut out := ""
  let mut i := 0
  for c in s.toList do
    if i > 0 && (len - i) % 3 == 0 then out := out ++ ","
    out := out.push c
    i := i + 1
  return out

/-- The path as the diagram prints it: the root's prefix dropped. -/
def short (p : String) : String :=
  if p.startsWith "src/Effect4/Laws/" then dropStr p 12
  else if p.startsWith "src/Effect4/" then dropStr p 12
  else if p == "src/Effect4.lean" then "Effect4.lean"
  else p

def css : String := "
:root {
  --paper: #f6f4ee; --ink: #1d2230; --ink-2: #4a5060; --ink-3: #7d8391; --rule: #d8d4ca; --panel: #fbfaf6;
  --runtime: #2f5d8a; --laws: #4b6b3c; --tools: #a3671b; --tests: #6b5b95; --estate: #55606e;
  --bad: #b3261e; --bad-bg: #f7e5e3; --ok-bg: #e9efe6; --accent: #2f5d8a;
  --mono: 'IBM Plex Mono', ui-monospace, SFMono-Regular, Menlo, monospace;
  --sans: 'IBM Plex Sans', system-ui, -apple-system, 'Segoe UI', sans-serif;
}
@media (prefers-color-scheme: dark) { :root:not([data-theme='light']) {
  --paper: #171a21; --ink: #e8e6df; --ink-2: #b5b3ab; --ink-3: #8a8983; --rule: #343945; --panel: #1f232c;
  --runtime: #7fb0e0; --laws: #9cc487; --tools: #e0a85a; --tests: #b5a6dc; --estate: #9aa4b3;
  --bad: #f28b82; --bad-bg: #3a2220; --ok-bg: #22301f; --accent: #7fb0e0; } }
:root[data-theme='dark'] {
  --paper: #171a21; --ink: #e8e6df; --ink-2: #b5b3ab; --ink-3: #8a8983; --rule: #343945; --panel: #1f232c;
  --runtime: #7fb0e0; --laws: #9cc487; --tools: #e0a85a; --tests: #b5a6dc; --estate: #9aa4b3;
  --bad: #f28b82; --bad-bg: #3a2220; --ok-bg: #22301f; --accent: #7fb0e0; }
* { box-sizing: border-box; }
html { color-scheme: light dark; }
body { margin: 0; background: var(--paper); color: var(--ink); font: 15px/1.5 var(--sans); }
.wrap { max-width: 1180px; margin: 0 auto; padding-block: 28px 56px; padding-inline: 20px; }
header h1 { font-size: 30px; margin: 0 0 6px; letter-spacing: -0.01em; text-wrap: balance; }
header p { max-width: 68ch; margin: 0 0 8px; color: var(--ink-2); }
.stamp { font: 12px/1.5 var(--mono); color: var(--ink-3); }
nav { display: flex; flex-wrap: wrap; gap: 8px 16px; margin: 18px 0 8px; font-size: 13px; }
nav a { color: var(--accent); text-decoration: none; border-bottom: 1px solid var(--rule); }
.legend { display: flex; flex-wrap: wrap; gap: 8px 18px; font-size: 12px; color: var(--ink-2); margin: 10px 0 0; }
.legend span::before { content: ''; display: inline-block; width: 12px; height: 12px; border-radius: 2px; margin-right: 6px; vertical-align: -1px; }
.legend .runtime::before { background: var(--runtime); } .legend .laws::before { background: var(--laws); }
.legend .tools::before { background: var(--tools); } .legend .tests::before { background: var(--tests); }
.legend .planned::before { background: transparent; border: 1.5px dashed var(--ink-3); }
.legend .bad::before { background: var(--bad); }
section { margin-top: 44px; }
h2 { font-size: 21px; margin: 0 0 4px; letter-spacing: -0.005em; }
h3 { font-size: 15px; margin: 26px 0 6px; text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-2); }
.lede { color: var(--ink-2); max-width: 72ch; margin: 0 0 14px; }
figure { margin: 14px 0 0; }
.scroll { overflow-x: auto; border: 1px solid var(--rule); border-radius: 6px; background: var(--panel); }
svg { display: block; max-width: 100%; height: auto; font-family: var(--sans); }
figcaption { font-size: 13px; color: var(--ink-2); margin-top: 8px; max-width: 72ch; }
table { border-collapse: collapse; width: 100%; font-size: 13px; }
th, td { text-align: left; vertical-align: top; padding: 6px 10px; border-bottom: 1px solid var(--rule); }
th { font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-3); font-weight: 600; }
td.n, th.n { text-align: right; font-variant-numeric: tabular-nums; font-family: var(--mono); font-size: 12px; white-space: nowrap; }
code, .path { font-family: var(--mono); font-size: 12px; }
.path { color: var(--ink-2); white-space: nowrap; }
tr.detail td:first-child { padding-left: 26px; }
tr.detail td { color: var(--ink-2); }
tr.planned td { color: var(--ink-3); }
tr.planned td:first-child { border-left: 2px dashed var(--ink-3); }
.tag { display: inline-block; font: 600 10px/1.4 var(--sans); letter-spacing: 0.06em; text-transform: uppercase; padding: 1px 6px; border-radius: 3px; border: 1px solid var(--rule); color: var(--ink-2); margin-left: 6px; }
.tag.bad { color: var(--bad); border-color: var(--bad); }
.tag.ok { background: var(--ok-bg); }
.matrix td, .matrix th { padding: 3px 6px; font-size: 11px; }
.matrix td.n { font-size: 11px; }
.matrix th.row { position: sticky; left: 0; background: var(--panel); white-space: nowrap; font-family: var(--mono); text-transform: none; letter-spacing: 0; font-size: 11px; }
.matrix th.col { writing-mode: vertical-rl; transform: rotate(180deg); white-space: nowrap; font-family: var(--mono); text-transform: none; letter-spacing: 0; height: 150px; padding: 6px 2px; }
.matrix td.bad { background: var(--bad-bg); color: var(--bad); font-weight: 600; }
.matrix td.dot { color: var(--rule); text-align: center; }
.cols { display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 12px 28px; }
.kv { font-size: 13px; }
.kv b { font-weight: 600; }
ul.plain { padding-left: 18px; margin: 6px 0; }
.small { font-size: 12px; color: var(--ink-3); }
footer { margin-top: 56px; font-size: 12px; color: var(--ink-3); border-top: 1px solid var(--rule); padding-top: 14px; }
@media (prefers-reduced-motion: reduce) { * { transition: none !important; } }
"

/-- The colour token of a column. -/
def tone : Column → String
  | .runtime => "var(--runtime)" | .laws => "var(--laws)" | .tools => "var(--tools)"
  | .tests => "var(--tests)" | _ => "var(--estate)"

/-- The diagram of the four Lean roots: one column each, height by declared layer, the
imports between columns aggregated at the top, and a mark on every area with an import
against the direction. -/
def renderStack (f : Facts) : String := Id.run do
  let cols : List Column := [.runtime, .laws, .tools, .tests]
  let colX (c : Column) : Nat := 30 + c.order * 270
  let colW := 240
  let maxLayer := areas.foldl (fun m a => if a.column.isLean && !a.detail then max m a.layer else m) 0
  let top := 64
  let rowH := 78
  let yOf (layer : Nat) : Nat := top + (maxLayer - layer) * rowH
  let height := top + (maxLayer + 1) * rowH + 12
  let width := 30 + 4 * 270
  let mut out := #[s!"<svg viewBox=\"0 0 {width} {height}\" role=\"img\" aria-label=\"The four Lean roots as columns, every area at its declared height, with the measured imports between the columns\">"]
  out := out.push "<defs><marker id=\"arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M0,0 L10,5 L0,10 z\" fill=\"currentColor\"/></marker></defs>"
  -- against-the-direction counts per area (outgoing)
  let badOf (p : String) : Nat := (f.against.filter fun v => v.src == p && v.accepted.isNone).size
  for c in cols do
    let members := areas.filter fun a => a.column == c && !a.detail
    let x := colX c
    let total := linesOf (members.foldl (fun acc a => acc ++ f.rolled a) #[])
    let label := match c with
      | .runtime => "runtime · src/Effect4" | .laws => "proofs · src/Effect4/Laws"
      | .tools => "tools · tools/ and src/OCaml5" | .tests => "batteries · Test/" | _ => ""
    out := out.push s!"<text x=\"{x}\" y=\"20\" font-size=\"12\" font-weight=\"600\" fill=\"{tone c}\">{esc label}</text>"
    out := out.push s!"<text x=\"{x}\" y=\"36\" font-size=\"11\" fill=\"var(--ink-3)\">{fmt total} lines</text>"
    for layer in [0:maxLayer+1] do
      let here := members.filter (·.layer == layer)
      let k := here.length
      if k == 0 then continue
      let w := (colW - (k - 1) * 8) / k
      let mut i := 0
      for a in here do
        let bx := x + i * (w + 8)
        let yy := yOf layer
        let own := f.rolled a
        let cnt := f.countsOf own
        let bad := badOf a.path
        out := out.push s!"<rect x=\"{bx}\" y=\"{yy}\" width=\"{w}\" height=\"66\" rx=\"4\" fill=\"var(--panel)\" stroke=\"{tone c}\" stroke-width=\"1.5\"/>"
        out := out.push s!"<text x=\"{bx + 8}\" y=\"{yy + 17}\" font-size=\"12\" font-weight=\"600\" fill=\"var(--ink)\">{esc a.title}</text>"
        out := out.push s!"<text x=\"{bx + 8}\" y=\"{yy + 31}\" font-size=\"9.5\" font-family=\"var(--mono)\" fill=\"var(--ink-2)\">{esc (short a.path)}</text>"
        out := out.push s!"<text x=\"{bx + 8}\" y=\"{yy + 45}\" font-size=\"9.5\" fill=\"var(--ink-3)\">{own.size} files · {fmt (linesOf own)} lines</text>"
        out := out.push s!"<text x=\"{bx + 8}\" y=\"{yy + 58}\" font-size=\"9.5\" fill=\"var(--ink-3)\">{fmt cnt.theorems} thm · {fmt cnt.defs} def · {cnt.inductives} ind</text>"
        if bad > 0 then
          out := out.push s!"<rect x=\"{bx + w - 30}\" y=\"{yy + 6}\" width=\"24\" height=\"14\" rx=\"7\" fill=\"var(--bad)\"/>"
          out := out.push s!"<text x=\"{bx + w - 18}\" y=\"{yy + 16}\" font-size=\"9.5\" font-weight=\"600\" text-anchor=\"middle\" fill=\"var(--paper)\">↑{bad}</text>"
        i := i + 1
  -- the aggregated column arrows, at the top band
  let colTotal (src dst : Column) : Nat :=
    f.edges.foldl (init := 0) fun n e =>
      match areaOf e.src, areaOf e.dst with
      | some a, some b => if a.column == src && b.column == dst then n + e.count else n
      | _, _ => n
  let arrow (fromC toC : Column) (y : Nat) (label : String) : String :=
    let x1 := colX fromC
    let x2 := colX toC + colW + 4
    s!"<path d=\"M{x1 - 4},{y} L{x2},{y}\" stroke=\"currentColor\" stroke-width=\"1\" fill=\"none\" marker-end=\"url(#arrow)\"/><text x=\"{(x1 + x2) / 2}\" y=\"{y - 4}\" font-size=\"10\" text-anchor=\"middle\" fill=\"var(--ink-2)\">{esc label}</text>"
  out := out.push (arrow .laws .runtime 54 s!"imports runtime: {colTotal .laws .runtime}")
  out := out.push (arrow .tools .laws 54 s!"imports laws {colTotal .tools .laws} · runtime {colTotal .tools .runtime}")
  out := out.push (arrow .tests .tools 54 s!"imports tools {colTotal .tests .tools} · laws {colTotal .tests .laws} · runtime {colTotal .tests .runtime}")
  out := out.push "</svg>"
  return String.intercalate "\n" out.toList

/-- The file or directory a module name denotes, in whichever root holds it, and whether it
exists; a module not yet written resolves under `src/` for `Effect4.*` and `tools/` otherwise. -/
def pathOfModule (m : String) : IO (String × Bool) := do
  let rel := String.intercalate "/" (m.splitOn ".")
  for root in ["src/", "tools/", ""] do
    let file := root ++ rel ++ ".lean"
    if ← (file : FilePath).pathExists then return (file, true)
    if ← (root ++ rel : FilePath).isDir then return (root ++ rel, true)
  let root := if m.startsWith "Effect4." then "src/" else "tools/"
  return (root ++ rel ++ ".lean", false)

/-- The typed-state proof stack: one row per slice, its modules solid once they exist. -/
def renderMilestone : IO String := do
  let rowH := 60
  let labelW := 150
  let width := 1080
  let height := 24 + milestone.length * rowH
  let mut out := #[s!"<svg viewBox=\"0 0 {width} {height}\" role=\"img\" aria-label=\"The typed-state proof stack by slice, landed modules solid and planned modules dashed\">"]
  let mut r := 0
  for s in milestone do
    let y := 14 + r * rowH
    out := out.push s!"<text x=\"0\" y=\"{y + 18}\" font-size=\"12\" font-weight=\"600\" fill=\"var(--ink)\">{esc s.name}</text>"
    out := out.push s!"<text x=\"0\" y=\"{y + 33}\" font-size=\"10\" fill=\"var(--ink-3)\">{esc s.what}</text>"
    let k := s.modules.length
    let avail := width - labelW
    let w := min 250 ((avail - (k - 1) * 8) / k)
    let mut i := 0
    for mod in s.modules do
      let (m, landed) ← pathOfModule mod
      let bx := labelW + i * (w + 8)
      let stroke := if landed then "var(--laws)" else "var(--ink-3)"
      let dash := if landed then "" else " stroke-dasharray=\"5 4\""
      let fill := if landed then "var(--panel)" else "transparent"
      out := out.push s!"<rect x=\"{bx}\" y=\"{y}\" width=\"{w}\" height=\"42\" rx=\"4\" fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"1.5\"{dash}/>"
      let name := (m.splitOn "/").getLast?.getD m
      let dir := if m.startsWith "src/Effect4/Laws/" then dropRightStr (dropStr m 17) (name.length + 1)
        else if m.startsWith "tools/" then dropRightStr (dropStr m 6) (name.length + 1) else m
      out := out.push s!"<text x=\"{bx + 8}\" y=\"{y + 17}\" font-size=\"11\" font-weight=\"600\" fill=\"{if landed then "var(--ink)" else "var(--ink-3)"}\">{esc name}</text>"
      out := out.push s!"<text x=\"{bx + 8}\" y=\"{y + 32}\" font-size=\"9.5\" font-family=\"var(--mono)\" fill=\"var(--ink-3)\">{esc dir}{if landed then "" else " · planned"}</text>"
      i := i + 1
    r := r + 1
  out := out.push "</svg>"
  return String.intercalate "\n" out.toList

/-- The import matrix over the non-detail Lean areas and the external packages. -/
def renderMatrix (f : Facts) : String := Id.run do
  let lean := (areas.filter fun a => a.column.isLean && !a.detail).toArray.qsort fun a b =>
    a.column.order < b.column.order || (a.column.order == b.column.order && (a.layer > b.layer || (a.layer == b.layer && a.path < b.path)))
  let exts := (f.edges.filter (·.dst.startsWith "ext:")).map (·.dst) |>.toList.eraseDups.toArray.qsort (· < ·)
  let count (s d : String) : Nat := (f.edges.find? fun e => e.src == s && e.dst == d).map (·.count) |>.getD 0
  let mut out := #["<table class=\"matrix\"><thead><tr><th class=\"row\">imports ↓ from →</th>"]
  for b in lean do out := out.push s!"<th class=\"col\">{esc (short b.path)}</th>"
  for e in exts do out := out.push s!"<th class=\"col\">{esc (dropStr e 4)}</th>"
  out := out.push "</tr></thead><tbody>"
  for a in lean do
    out := out.push s!"<tr><th class=\"row\" style=\"color:{tone a.column}\">{esc (short a.path)}</th>"
    for b in lean do
      let n := count a.path b.path
      if n == 0 then out := out.push "<td class=\"dot\">·</td>"
      else if allowed a b then out := out.push s!"<td class=\"n\">{n}</td>"
      else out := out.push s!"<td class=\"n bad\">{n}</td>"
    for e in exts do
      let n := count a.path e
      out := out.push (if n == 0 then "<td class=\"dot\">·</td>" else s!"<td class=\"n\">{n}</td>")
    out := out.push "</tr>"
  out := out.push "</tbody></table>"
  return String.intercalate "" out.toList

def renderAgainst (f : Facts) : String := Id.run do
  if f.against.isEmpty then return "<p class=\"small\">No import runs against the declared direction.</p>"
  let sorted := f.against.qsort fun a b => a.src < b.src || (a.src == b.src && a.file < b.file)
  let mut out := #["<table><thead><tr><th>importing file</th><th>imports</th><th>from → to</th><th>standing</th></tr></thead><tbody>"]
  for v in sorted do
    let standing := match v.accepted with
      | some why => s!"<span class=\"tag ok\">accepted</span> {md why}"
      | none => "<span class=\"tag bad\">against the direction</span>"
    out := out.push s!"<tr><td class=\"path\">{esc v.file}</td><td><code>{esc v.module.toString}</code></td><td class=\"path\">{esc (short v.src)} → {esc (short v.dst)}</td><td>{standing}</td></tr>"
  out := out.push "</tbody></table>"
  return String.intercalate "" out.toList

/-- The file map of one Lean column. -/
def renderLeanColumn (f : Facts) (c : Column) : String := Id.run do
  let members := (areas.filter (·.column == c)).toArray.qsort fun a b =>
    a.layer > b.layer || (a.layer == b.layer && a.path < b.path)
  let mut out := #[s!"<h3>{esc c.title}</h3>", "<div class=\"scroll\"><table><thead><tr><th>area</th><th>path</th><th class=\"n\">files</th><th class=\"n\">lines</th><th class=\"n\">thm</th><th class=\"n\">def</th><th class=\"n\">ind</th><th>role</th></tr></thead><tbody>"]
  for a in members do
    let own := f.own a
    let cnt := f.countsOf own
    let cls := if a.detail then " class=\"detail\"" else ""
    let drivers := own.filter (·.driver) |>.size
    let unbuilt := own.filter (fun x => !x.built) |>.size
    let tags := (if drivers > 0 then s!"<span class=\"tag\">{drivers} driver{if drivers == 1 then "" else "s"}</span>" else "") ++
      (if unbuilt > 0 then s!"<span class=\"tag\">{unbuilt} not built</span>" else "")
    out := out.push s!"<tr{cls}><td><b>{esc a.title}</b>{tags}</td><td class=\"path\">{esc a.path}</td><td class=\"n\">{own.size}</td><td class=\"n\">{fmt (linesOf own)}</td><td class=\"n\">{fmt cnt.theorems}</td><td class=\"n\">{fmt cnt.defs}</td><td class=\"n\">{cnt.inductives}</td><td>{md a.role}</td></tr>"
  out := out.push "</tbody></table></div>"
  return String.intercalate "" out.toList

def renderEstates (f : Facts) (c : Column) : String := Id.run do
  let members := f.estates.filter (·.area.column == c)
  if members.isEmpty then return ""
  let mut out := #[s!"<h3>{esc c.title}</h3>", "<div class=\"scroll\"><table><thead><tr><th>area</th><th>path</th><th class=\"n\">files</th><th class=\"n\">lines</th><th>by extension</th><th>role</th></tr></thead><tbody>"]
  for e in members do
    let ext := if !e.area.measure then "not walked" else
      String.intercalate " · " (e.byExt.take 5 |>.map fun (x, c, l) => if l > 0 then s!"{x} {c} ({fmt l})" else s!"{x} {c}")
    let count := if e.area.measure then fmt e.fileCount else "—"
    let lines := if e.area.measure then fmt e.lines else "—"
    out := out.push s!"<tr><td><b>{esc e.area.title}</b></td><td class=\"path\">{esc e.area.path}</td><td class=\"n\">{count}</td><td class=\"n\">{lines}</td><td class=\"small\">{esc ext}</td><td>{md e.area.role}</td></tr>"
  out := out.push "</tbody></table></div>"
  return String.intercalate "" out.toList

def renderGroups (f : Facts) : String := Id.run do
  let mut out := #["<div class=\"scroll\"><table><thead><tr><th>group</th><th>producer</th><th>consumers</th><th>check</th><th>evidence</th></tr></thead><tbody>"]
  for g in f.groups do
    out := out.push s!"<tr><td><b>{esc g.name}</b></td><td>{md g.producer}</td><td>{md g.consumers}</td><td>{md g.check}</td><td>{md g.evidence}</td></tr>"
  out := out.push "</tbody></table></div>"
  return String.intercalate "" out.toList

def renderPins (f : Facts) : String := Id.run do
  let mut out := #["<div class=\"scroll\"><table><thead><tr><th>package</th><th>source</th><th>revision</th></tr></thead><tbody>"]
  for p in f.pins do
    out := out.push s!"<tr><td><b>{esc p.name}</b></td><td class=\"path\">{esc p.git}</td><td class=\"path\">{esc p.rev}</td></tr>"
  for a in areas do
    if a.column == .vendor then
      out := out.push s!"<tr><td><b>{esc a.title}</b></td><td class=\"path\">{esc a.path}</td><td>{md a.role}</td></tr>"
  out := out.push "</tbody></table></div>"
  return String.intercalate "" out.toList

def renderAudit (f : Facts) : String := Id.run do
  let againstCount := (f.against.filter (·.accepted.isNone)).size
  let acceptedCount := f.against.size - againstCount
  let unbuilt := f.leanFiles.filter fun x => !x.built && !x.driver
  let largest := (f.leanFiles.qsort fun a b => a.lines > b.lines).extract 0 12
  let cycles := f.edges.filter fun e => !e.dst.startsWith "ext:" && e.src < e.dst &&
    f.edges.any fun r => r.src == e.dst && r.dst == e.src
  let mut out := #[]
  out := out.push "<div class=\"cols\">"
  out := out.push s!"<div class=\"kv\"><b>Imports against the direction:</b> {againstCount}, and {acceptedCount} accepted by a document. Every one is listed above.</div>"
  out := out.push s!"<div class=\"kv\"><b>Area pairs that import each other:</b> {cycles.size}. {String.intercalate "; " (cycles.toList.map fun e => esc (short e.src) ++ " ↔ " ++ esc (short e.dst))}</div>"
  out := out.push s!"<div class=\"kv\"><b>Modules with no built olean, drivers aside:</b> {unbuilt.size}. {String.intercalate ", " (unbuilt.toList.map fun x => "<code>" ++ esc x.path ++ "</code>")}</div>"
  out := out.push s!"<div class=\"kv\"><b>Directories under src/ and tools/ with no Lean file:</b> {f.emptyDirs.size}. {String.intercalate ", " (f.emptyDirs.toList.map fun d => "<code>" ++ esc d ++ "</code>")}</div>"
  out := out.push "</div>"
  out := out.push "<h3>The twelve largest modules</h3><div class=\"scroll\"><table><thead><tr><th>module</th><th class=\"n\">lines</th><th class=\"n\">thm</th><th class=\"n\">def</th><th>area</th></tr></thead><tbody>"
  for x in largest do
    let cnt := f.counts.getD x.module {}
    let area := (areaOf x.path).map (·.title) |>.getD "?"
    out := out.push s!"<tr><td class=\"path\">{esc x.path}</td><td class=\"n\">{fmt x.lines}</td><td class=\"n\">{fmt cnt.theorems}</td><td class=\"n\">{fmt cnt.defs}</td><td>{esc area}</td></tr>"
  out := out.push "</tbody></table></div>"
  return String.intercalate "" out.toList

def page (f : Facts) : IO String := do
  let leanLines := linesOf f.leanFiles
  let loaded := (f.leanFiles.filter fun x => f.counts.contains x.module).size
  let thms := (f.countsOf f.leanFiles).theorems
  let milestoneSvg ← renderMilestone
  let head := "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1, viewport-fit=cover\">\n<title>Effect4 Architecture Map</title>\n<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600&display=swap\">\n<style>" ++ css ++ "</style>\n</head>\n<body>\n<!-- " ++ Tools.GeneratedStamp.note "tools/Tools/Architecture.lean (make gen-architecture)" ++ " -->\n<div class=\"wrap\">\n"
  let header := s!"<header><h1>Effect4 Architecture Map</h1><p>The tree as it is: the four Lean roots and the direction their imports run, the estates around them, the typed-state proof stack as it lands, and what the tree says against what the role register declares. Measured by <code>tools/Tools/Architecture.lean</code>; the roles and the layering are declared in <code>tools/Tools/ArchitectureRoles.lean</code>.</p><div class=\"stamp\">{f.leanFiles.size} Lean modules · {fmt leanLines} lines · {loaded} loaded for counts · {fmt thms} theorems · regenerate with <code>make gen-architecture</code></div>" ++
    "<nav><a href=\"#roots\">The roots</a><a href=\"#matrix\">The import matrix</a><a href=\"#against\">Against the direction</a><a href=\"#stack\">The typed-state stack</a><a href=\"#map\">The file map</a><a href=\"#faces\">Faces and generated groups</a><a href=\"#pins\">Pinned references</a><a href=\"#audit\">Audit</a></nav>" ++
    "<div class=\"legend\"><span class=\"runtime\">runtime</span><span class=\"laws\">proofs</span><span class=\"tools\">tools</span><span class=\"tests\">batteries</span><span class=\"planned\">planned, not yet a file</span><span class=\"bad\">imports against the declared direction</span></div></header>"
  let roots := "<section id=\"roots\"><h2>The roots and their direction</h2><p class=\"lede\">Each column is a lake root; each box an area at the height the register declares. Inside a column an import may point at the same height or lower; the runtime imports only itself; the proof graph imports the runtime and <code>ProofGraph</code>; the tool roots import the runtime, the proof graph and lower tools; the batteries import everything. A red count on a box is the number of that area's imports that break one of those rules.</p><figure><div class=\"scroll\">" ++ renderStack f ++ "</div><figcaption>Arrows at the top aggregate the import statements between columns. Counts on the boxes are the area with its detail directories; theorems, definitions and inductives are counted from the loaded environment, auxiliaries excluded.</figcaption></figure></section>"
  let matrix := "<section id=\"matrix\"><h2>The import matrix</h2><p class=\"lede\">Rows import columns. A red cell is an import against the direction; a dot is none. The external columns are the packages the tree imports, by first component.</p><div class=\"scroll\">" ++ renderMatrix f ++ "</div></section>"
  let against := "<section id=\"against\"><h2>Against the direction</h2><p class=\"lede\">Every import statement the register does not allow, by file. An accepted row names the document that accepts it; the rest are the organization questions the map exists to surface.</p><div class=\"scroll\">" ++ renderAgainst f ++ "</div></section>"
  let stack := "<section id=\"stack\"><h2>The typed-state stack</h2><p class=\"lede\">The milestone's modules by slice of the plan's §14. A box is solid once its file exists and dashed until then, so this figure updates itself as slices land.</p><figure><div class=\"scroll\">" ++ milestoneSvg ++ "</div><figcaption>Layer 0 and slices T1 to T4 are landed; M2 to M7 and P2 are the milestone's remaining slices.</figcaption></figure></section>"
  let map := "<section id=\"map\"><h2>The file map</h2><p class=\"lede\">Every area by column, top of the column first, with its detail directories indented. Files and lines are the area's own; a tag counts its <code>--run</code> drivers and any module without a built olean.</p>" ++
    renderLeanColumn f .runtime ++ renderLeanColumn f .laws ++ renderLeanColumn f .tools ++ renderLeanColumn f .tests ++
    renderEstates f .ocaml ++ renderEstates f .ts ++ renderEstates f .host ++ renderEstates f .docs ++ "</section>"
  let faces := "<section id=\"faces\"><h2>Faces and generated groups</h2><p class=\"lede\">How a Lean definition becomes an OCaml or TypeScript face: the groups of <code>docs/GENERATED.md</code>, read from that table so the two cannot disagree.</p>" ++ renderGroups f ++ "</section>"
  let pins := "<section id=\"pins\"><h2>Pinned references</h2><p class=\"lede\">The packages <code>lakefile.toml</code> requires, at their exact revisions, and the vendored behavioral reference.</p>" ++ renderPins f ++ "</section>"
  let audit := "<section id=\"audit\"><h2>Audit</h2><p class=\"lede\">What the tree says about itself at this measurement. None of it fails a build; all of it is a question for the next slice.</p>" ++ renderAudit f ++ "</section>"
  let footer := "<footer>Generated by <code>tools/Tools/Architecture.lean</code> from the tree: import headers through <code>Lean.Elab.parseImports</code>, declaration counts from the loaded roots, sizes by file walk, the groups from <code>docs/GENERATED.md</code>, the pins from <code>lakefile.toml</code>. The role register <code>tools/Tools/ArchitectureRoles.lean</code> is the one hand input and is checked for totality on every run. No commit or date is embedded; the map changes when the tree does.</footer>"
  return head ++ header ++ roots ++ matrix ++ against ++ stack ++ map ++ faces ++ pins ++ audit ++ footer ++ "\n</div>\n</body>\n</html>\n"

end Tools.Architecture

open Tools.Architecture in
def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let out := match args.dropWhile (· != "--out") with
    | _ :: p :: _ => p
    | _ => "docs/core/architecture-map.html"
  let facts ← measure
  unless facts.uncovered.isEmpty do
    IO.eprintln s!"architecture: {facts.uncovered.size} Lean file(s) under no declared area (tools/Tools/ArchitectureRoles.lean):"
    for p in facts.uncovered do IO.eprintln s!"  {p}"
  unless facts.missing.isEmpty do
    IO.eprintln s!"architecture: {facts.missing.size} declared area(s) with no such path:"
    for p in facts.missing do IO.eprintln s!"  {p}"
  unless facts.uncovered.isEmpty && facts.missing.isEmpty do return 1
  let html ← page facts
  let against := (facts.against.filter (·.accepted.isNone)).size
  if check then
    let current ← IO.FS.readFile out
    if current == html then
      IO.println s!"architecture: {out} is current ({facts.leanFiles.size} Lean files, {against} imports against the direction)"
      return 0
    IO.eprintln s!"architecture: {out} is stale; run make gen-architecture"
    return 1
  IO.FS.writeFile out html
  let loaded := (facts.leanFiles.filter fun x => facts.counts.contains x.module).size
  IO.println s!"architecture: wrote {out}: {facts.leanFiles.size} Lean modules, {fmt (linesOf facts.leanFiles)} lines, {loaded} loaded for counts, {against} imports against the direction, {facts.edges.size} area edges"
  return 0
