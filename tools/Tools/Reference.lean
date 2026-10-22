import Tools.Site
import Tools.ProfileJson
import Tools.View.Glyph
import Effect4.Codegen.Forms
import Effect4.Ingest.Taxonomy
import Effect4.Codegen.Refusal

/-!
# Tools.Reference — the reference pages, folded from the tree's data

Each page is a `Tools.Document.Document` built from data the tree already holds, and the set is a
`Tools.Site.Site`: the Markdown, JSON and HTML of every page are the folds of `Tools.Document` and
the shell of `Tools.Site`, as for the documentation site. A page holds its subject's name, its
tables and its figures. A sentence stands only where a table cannot carry the fact, as a template
over a row's fields (`Template`, listed in `templates`).

* `forms`: the 26 rows of `Effect4.Program.arms`, the constructors of `LayerTerm` with the
  combinator and the line their docstrings cite, and the derived forms of
  `Effect4.Codegen.Forms.all`;
* `native`: the row of every operation that `NativeOp.spelled` lists, as the native signature
  gives it (`nativeSignature`);
* `marks`: the marks of `Tools.View.Glyph`, their kinds, the constructors each one draws, and the
  three forms of a figure's node (`Tools.Form`), drawn once as a figure;
* `refusals`: the ingest's closed alphabet (`Effect4.Ingest.Code`) and the three alphabets of
  `Effect4.Program` in `src/Effect4/Codegen/Refusal.lean`, the meaning of each from its docstring;
* `dictionary`: every tree anchor of the dictionary (`docs/core/controlled-english.md` §3) and
  what its file holds for it (`Finding`);
* `semantics`: the semantics report's own document (`Tools.SemanticsDocument`), read back from its
  JSON (`Tools.Document.Json.Document.ofJson`), in the set that the build writes under
  `.lake/gen/reference/` alone (`builtSemantics`): rewritten at each report, it is never committed;
* the index, at the root of the set.

A pin is a cited line of the vendored rc.112 sources. Its link leaves the set for the repository:
from a page one folder below the set's root it climbs to `vendor/`: three folders from
`generated/reference/`, four from `.lake/gen/reference/` (the set's `root`). The site's check reads
such a link at the set's root, where the URL parser's walk stops, so the driver lists each pinned
file as a file of the site after checking that the file holds the line (`Pin`).
-/

namespace Tools.Reference

open Lean Tools.Document Tools.Site

/-! ## Constructors with their docstrings -/

open Elab Term Meta in
/-- **The constructors of an inductive type with their docstrings**, read from the environment
where the term is elaborated: each constructor's last name, the names of its explicit fields after
the type's parameters, and its docstring, trimmed (empty for none). A constructor added to the type
is on the page at the next build. -/
elab "ctor_docs% " i:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let .inductInfo info ← getConstInfo n | throwError "{n} is not an inductive type"
  let env ← getEnv
  let rows ← info.ctors.mapM fun c => do
    let ci ← getConstInfo c
    let fields ← forallTelescope ci.type fun xs _ => do
      let mut out : Array String := #[]
      for x in xs.extract info.numParams xs.size do
        let d ← x.fvarId!.getDecl
        if d.binderInfo.isExplicit then out := out.push d.userName.toString
      return out.toList
    let doc := ((← findDocString? env c).getD "").trimAscii.toString
    return (c.getString!, fields, doc)
  return toExpr rows

/-- A docstring as one line: its lines joined by a space, its backtick spans as code. -/
def docLine (doc : String) : Line :=
  proseLine (" ".intercalate ((doc.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)))

/-- The backtick spans of a text, in order. -/
def spans (s : String) : List String :=
  (s.splitOn "`").zipIdx.filterMap fun (run, i) => if i % 2 == 1 then some run else none

/-! ## Pins -/

/-- The folder of the vendored rc.112 sources, from the repository's root. -/
def vendorSrc : String := "vendor/effect-4.0.0-rc.112/src/"

/-- **A pinned line** of the vendored sources: the file under `vendorSrc`, its first line and the
last line of its range. -/
structure Pin where
  file : String
  first : Nat
  last : Nat
  deriving BEq, Repr

/-- The pin a citation names, when it names a TypeScript file and a line: `internal/effect.ts:1275`,
`Ref.ts:496-501`, a path under `vendorSrc`, or a list whose first item is one
(`internal/effect.ts:5291, :5304`). -/
def Pin.of? (cite : String) : Option Pin := do
  let cite := (cite.dropPrefix vendorSrc).toString
  let head := ((cite.splitOn ",").headD "").trimAscii.toString
  let [file, lines] := head.splitOn ":" | none
  unless file.endsWith ".ts" && !file.startsWith "git" do none
  match lines.splitOn "-" with
  | [a] => let n ← a.toNat?; return { file, first := n, last := n }
  | [a, b] => return { file, first := ← a.toNat?, last := ← b.toNat? }
  | _ => none

/-- The pin's link from a page at `depth` folders below the repository's root, with GitHub's line
fragment. -/
def Pin.href (p : Pin) (depth : Nat) : String :=
  String.join (List.replicate depth "../") ++ vendorSrc ++ p.file ++ "#L" ++ toString p.first ++
    (if p.last == p.first then "" else "-L" ++ toString p.last)

/-- A citation's cell: a link to its pin, labelled as the citation is written under `vendorSrc`, or
the citation as code when it names no pinned line. -/
def citeCell (depth : Nat) (cite : String) : Line :=
  match Pin.of? cite with
  | some p => [.link (p.href depth) (cite.dropPrefix vendorSrc).toString]
  | none => [.code cite]

/-! ## Words for small alphabets -/

/-- A word as the JSON fold of its owner writes it. -/
def word : Json → String
  | .str s => s
  | j => j.compress

open Effect4.Codegen.Forms in
def arityWord : Arity → String
  | .value => "value"
  | .call n => s!"call {n}"
  | .dual n => s!"dual {n}"

open Effect4.Codegen.Forms in
def argWord : ArgClass → String
  | .effect => "effect" | .continuation => "continuation" | .thunk => "thunk"
  | .literal => "literal" | .term => "term" | .termArm => "termArm" | .key => "key"
  | .releaseOne => "releaseOne" | .handlers => "handlers"

/-- The common head of a page's producer lines: the generated file's mark and the command. -/
def producer (inputs : List String) : List String :=
  ["GENERATED by tools/Drivers/Reference.lean (make gen-reference); do not edit",
   "inputs: " ++ ", ".intercalate inputs]

/-- A dash for an empty cell. -/
def orDash (l : Line) : Line := if l.isEmpty then [.text "—"] else l

/-! ## forms -/

/-- The constructors of `LayerTerm`, with their docstrings. -/
def layerDocs : List (String × List String × String) := ctor_docs% Effect4.Program.LayerTerm

/-- **The page `forms`**: each constructor of `Eff` with the Effect TypeScript it prints as, the
primitive it compiles to and its pin (`arms`); each constructor of `LayerTerm` with the combinator
and the pin its docstring cites, the first span of each; each derived form with its head, arity,
argument classes and pin. -/
def forms (root : Nat := 2) : Document where
  title := "forms"
  producer := producer ["src/Effect4/Program/Eff.lean", "src/Effect4/Codegen/Forms.lean"]
  body := [
    .part "eff" "Eff" [
      .table ["constructor", "combinator", "primitive", "cite"]
        (Effect4.Program.arms.map fun a =>
          [[.code ("Eff." ++ a.constructor)], [.code a.combinator], [.code a.primitive], citeCell (root + 1) a.cite])],
    .part "layer-term" "LayerTerm" [
      .table ["constructor", "combinator", "cite"]
        (layerDocs.map fun (name, _, doc) =>
          let ss := spans doc
          [[.code ("LayerTerm." ++ name)], orDash ((ss.head?.map fun s => [Inline.code s]).getD []),
           orDash (((ss.find? (·.contains ".ts:")).map (citeCell (root + 1))).getD [])])],
    .part "derived" "Forms.all" [
      .table ["id", "head", "arity", "arguments", "citation"]
        (Effect4.Codegen.Forms.all.map fun f =>
          [[.code f.id], [.code f.head], [.text (arityWord f.arity)],
           orDash (", ".intercalate (f.arguments.map argWord) |> fun s => if s.isEmpty then [] else [.text s]),
           citeCell (root + 1) f.citation])]]

/-! ## native -/

/-- The rows the page lists: the native signature's row of each spelled operation. -/
def nativeRows : List Effect4.Program.Row :=
  Effect4.Program.NativeOp.spelled.map Effect4.Program.nativeSignature.rowOf

/-- **The page `native`**: the row of every spelled native operation, its columns the fields of
`Row`: the spelling an operation prints as, its shape, its kind, its request, answer and error
types (`Ty.render`), its trailing arguments and its pin. -/
def native (root : Nat := 2) : Document where
  title := "native"
  producer := producer ["src/Effect4/Program/Native.lean", "src/Effect4/Program/Eff.lean"]
  body := [
    .table ["name", "spelling", "shape", "kind", "request", "answer", "error", "trailing", "cite"]
      (nativeRows.map fun r =>
        [[.code r.name], [.code r.spelling], [.text (word (Tools.ProfileJson.shapeJson r.shape))],
         [.text (word (Tools.ProfileJson.kindJson r.kind))],
         [.code r.request.render], [.code r.answer.render], [.code r.error.render],
         orDash (r.trailing.map fun
           | .name s => Inline.code s
           | .str v => Inline.code v.quote),
         citeCell (root + 1) r.cite])]

/-! ## marks -/

open Tools.View.Glyph in
/-- The sort that declares a constructor, by the name `sorts` gives it. -/
def sortOf (c : Name) : String :=
  ((sorts.find? (·.ctors.contains c)).map (·.name)).getD "—"

open Tools.View.Glyph in
/-- A constructor by its type and its own name: `Eff.succeed`. -/
def ctorName (c : Name) : String :=
  match c with
  | .str (.str _ t) n => t ++ "." ++ n
  | _ => c.toString

/-- A constructor's own name, as its `Repr` writes it. -/
def reprName {α : Type} [Repr α] (a : α) : String := ((reprStr a).splitOn ".").getLast?.getD ""

open Tools.View.Glyph in
/-- The marks, each with its name, in the order of their constructors (`shapeNames`, checked
below). -/
def shapes : List (String × Shape) :=
  [Shape.box, .value, .series, .parallel, .block, .alternative, .loop, .region, .bracket, .openBracket,
   .rail, .arrow, .blockedArrow, .spider, .rest, .hollowBox, .filledBox, .hollowDot, .filledDot,
   .port, .probe, .call, .library, .cross, .hash, .reasons, .exitBar, .hole, .enter, .barLine,
   .fermata, .caesura, .panel, .cells, .slot, .tag, .atom].map fun s => (reprName s, s)

#guard shapes.map (·.1) == Tools.View.Glyph.shapeNames.map (·.getString!)

open Tools.View.Glyph in
/-- The kinds, each with its name, in the order of their constructors (checked below). -/
def kinds : List (String × Kind) :=
  [Kind.body, .vessel, .container, .wire, .bond, .force, .cadence].map fun k => (reprName k, k)

open Tools.View.Glyph in
#guard kinds.map (·.1) == (ctors_of% Tools.View.Glyph.Kind).map (·.getString!)

/-- The three forms of a figure's node, each with its word. -/
def nodeForms : List Form := [.box, .wire, .port]

/-- How the Markdown fold writes a form's node in Mermaid (`Tools.Document.mermaid`). -/
def mermaidShape (f : Form) : String :=
  match (mermaid [{ key := "n", label := "…", form := f }] []).splitOn "\n" with
  | _ :: _ :: node :: _ => (node.trimAscii.drop 2).toString
  | _ => ""

open Tools.View.Glyph in
/-- **The page `marks`**: each mark with its glyph, kind, meaning and the number of constructors it
draws; each kind with its motion; each constructor the pictures fold with its mark; and the three
forms of a node, drawn once as a figure. -/
def marks : Document where
  title := "marks"
  producer := producer ["tools/Tools/View/Glyph.lean", "tools/Tools/Form.lean"]
  body := [
    .part "shapes" "Shape" [
      .table ["shape", "glyph", "kind", "means", "rows"]
        (shapes.map fun (name, s) =>
          [[.code name], [.code s.glyph],
           (let k := reprName s.kind; [.ref ("kind:" ++ k) k]),
           [.text s.means], [.text (toString (table.filter (·.shape == s)).length)]])],
    .part "kinds" "Kind" (
      [.table ["kind", "means", "enter", "change", "leave"]
        (kinds.map fun (name, k) =>
          let g := k.grammar
          [[.code name], [.text k.means], [.text g.enter.how], [.text g.change.how], [.text g.leave.how]])] ++
      kinds.map fun (name, k) => .part ("kind:" ++ name) name
        [.items ((shapes.filter (·.2.kind == k)).map fun (n, s) => [Inline.code s.glyph, .text " ", .code n])]),
    .part "rows" "Glyph.table" [
      .table ["constructor", "sort", "shape", "variant", "word", "means"]
        (table.map fun r =>
          [[.code (ctorName r.ctor)], [.text (sortOf r.ctor)],
           [.code (((shapes.find? (·.2 == r.shape)).map (·.1)).getD "")],
           orDash (if r.variant.isEmpty then [] else [.text r.variant]), [.text r.word], [.text r.means]])],
    .part "node-forms" "Form" [
      .graph "fig:forms" "Form"
        (nodeForms.map fun f => { key := f.word, label := f.word, form := f }) [],
      .table ["form", "mermaid"]
        (nodeForms.map fun f => [[.code f.word], [.code (mermaidShape f)]])]]

/-! ## refusals -/

/-- The three refusal alphabets of `src/Effect4/Codegen/Refusal.lean`, with their docstrings. -/
def readDocs : List (String × List String × String) := ctor_docs% Effect4.Program.ReadRefusal
def printDocs : List (String × List String × String) := ctor_docs% Effect4.Program.PrintRefusal
def classDocs : List (String × List String × String) := ctor_docs% Effect4.Program.ClassRefusal

/-- An alphabet's table: each constructor, its fields and its docstring. -/
def alphabet (type : String) (docs : List (String × List String × String)) : Block :=
  .table ["constructor", "fields", "meaning"]
    (docs.map fun (name, fields, doc) =>
      [[.code (type ++ "." ++ name)], orDash (if fields.isEmpty then [] else [.code (" ".intercalate fields)]),
       orDash (docLine doc)])

/-- **The page `refusals`**: each code of the ingest's alphabet with its spectrum, status and detail
template, and each constructor of the reader's, the printer's and the class table's alphabets with
its fields and meaning. -/
def refusals : Document where
  title := "refusals"
  producer := producer ["src/Effect4/Ingest/Taxonomy.lean", "src/Effect4/Codegen/Refusal.lean"]
  body := [
    .part "ingest" "Ingest.Code" [
      .table ["code", "spectrum", "status", "detail"]
        (Effect4.Ingest.Code.all.map fun c =>
          [[.code c.wire], [.text c.spectrum.wire], [.text c.status.wire], [.code c.detailTemplate]])],
    .part "read" "ReadRefusal" [alphabet "ReadRefusal" readDocs],
    .part "print" "PrintRefusal" [alphabet "PrintRefusal" printDocs],
    .part "class" "ClassRefusal" [alphabet "ClassRefusal" classDocs]]

/-! ## dictionary -/

/-- A tree anchor of the dictionary: a declaration's name with the file that holds it, or a file
alone. -/
structure Anchor where
  name : Option String
  path : String
  deriving BEq, Repr

/-- One entry of the dictionary: its part of §3, its term and its anchors. -/
structure Entry where
  part : String
  term : String
  anchors : List Anchor
  deriving Repr

/-- The cells of a table row: split at each `|` that no backslash escapes and no code span holds. -/
def cells (row : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut inCode := false
  let mut prev := ' '
  for c in row.toList do
    if c == '`' then inCode := !inCode
    if c == '|' && !inCode && prev != '\\' then
      out := out.push cur.trimAscii.toString; cur := ""
    else cur := cur.push c
    prev := c
  out := out.push cur.trimAscii.toString
  -- the empty cells before the first bar and after the last
  return (out.toList.drop 1).dropLast

/-- The anchors of a cell, as the language check reads them (`anchors`, `scripts/lib/language.py`):
a code span that holds a `/` and stands in parentheses is a path, and it anchors the names written
before it, back to the previous path; a span with no `/` and no space is a name. Two readings
more: a path in parentheses with no name before it, or a span that holds a `/` and no space
outside parentheses, is an anchor of the file alone; a `git:` citation is no anchor. -/
def anchorsOf (cell : String) : List Anchor := Id.run do
  let runs := cell.splitOn "`"
  let mut out : Array Anchor := #[]
  let mut names : Array String := #[]
  for i in [0:runs.length] do
    if i % 2 == 0 then continue
    let content := runs[i]!.trimAscii.toString
    let before := runs[i - 1]!.trimAscii.toString
    let after := (runs[i + 1]?.getD "").trimAscii.toString
    if content.startsWith "git:" || content.contains ' ' then continue
    if content.contains '/' then
      let inParens := before.endsWith "(" && (after.startsWith ")" || after.startsWith "," || after.startsWith ";")
      if inParens && !names.isEmpty then
        out := out ++ names.map fun n => { name := some n, path := content }
        names := #[]
      else if names.isEmpty then out := out.push { name := none, path := content }
    else names := names.push content
  return out.toList

/-- **The dictionary's entries**, from the text of `docs/core/controlled-english.md`: every row of
every table of §3 whose header names a tree anchor (`Tree anchor`) or a site (`Tree name (site)`),
the term its first cell with the bold taken off. -/
def entries (text : String) : List Entry := Id.run do
  let mut out : Array Entry := #[]
  let mut inDictionary := false
  let mut heading := ""
  let mut column : Option Nat := none
  for line in text.splitOn "\n" do
    if line.startsWith "## " then inDictionary := line.startsWith "## 3."; column := none
    else if inDictionary && line.startsWith "### " then heading := (line.drop 4).toString; column := none
    else if inDictionary && line.startsWith "|" then
      let cs := cells line
      if cs.all (·.all (fun c => c == '-' || c == ' ')) then continue
      match column with
      | none => column := cs.findIdx? fun c => c == "Tree anchor" || c == "Tree name (site)"
      | some k =>
        let term := ((cs.headD "").replace "**" "").trimAscii.toString
        out := out.push { part := heading, term, anchors := anchorsOf (cs.getD k "") }
    else if !line.startsWith "|" then column := none
  return out.toList

/-- What an anchor's file holds for it. -/
inductive Finding where
  /-- a line of the file declares the name: a declaration keyword, a constructor's bar or a field,
  then the name's last component -/
  | declaration
  /-- the file holds the name's last component as a word, and no line declares it -/
  | word
  /-- the file is there, with no name to look for -/
  | file
  /-- the file does not hold the name's last component -/
  | missing
  /-- no file stands at the path -/
  | noFile
  deriving BEq, Repr

def Finding.text : Finding → String
  | .declaration => "declaration"
  | .word => "word"
  | .file => "file"
  | .missing => "missing"
  | .noFile => "no file"

/-- The word a file must hold for a name, as the language check takes it: the last component,
with a leading `.` or `#` and a trailing `%` taken off. -/
def declaredWord (name : String) : String :=
  let w := ((name.dropWhile (fun c => c == '.' || c == '#')).dropEndWhile (· == '%')).toString
  ((w.splitOn ".").getLast?).getD w

/-- The keywords that open a declaration of a name: Lean's, and OCaml's `val` and `type` for an
interface file. -/
def keywords : List String :=
  ["def", "theorem", "lemma", "abbrev", "structure", "inductive", "class", "instance", "opaque",
   "axiom", "proof_goal", "elab", "macro", "syntax", "initialize", "builtin_initialize", "val", "type"]

/-- The modifiers a declaration's keyword may follow. -/
def modifiers : List String :=
  ["private", "protected", "noncomputable", "partial", "unsafe", "public", "nonrec", "scoped", "local"]

/-- A character of a Lean identifier. -/
def identChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Whether a line declares the name `n`, whose word is `w` (`declaredWord`): after its attributes
and modifiers, a keyword then a name whose last component is `w`; a constructor `| w`; a field
`w :`; or a `syntax`, `elab` or `macro` line that spells `n` in quotes (a command, `#plan_status`),
or a line that opens with that spelling (a syntax written over two lines). -/
def declares (n w : String) (line : String) : Bool :=
  let toks := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  let toks := toks.dropWhile fun t => t.startsWith "@[" || t.endsWith "]" || modifiers.contains t
  let last (t : String) := ((t.takeWhile fun c => identChar c || c == '.').toString.splitOn ".").getLast?.getD ""
  match toks with
  | k :: m :: _ =>
    (keywords.contains k && last m == w) || (k == "|" && last m == w) || (k == w && m == ":") ||
      (["syntax", "elab", "macro"].contains k && (line.splitOn ("\"" ++ n)).length > 1) ||
      k.startsWith ("\"" ++ n)
  | _ => false

/-- Whether `text` holds `w` as a word: no identifier character on either side. -/
def holdsWord (w : String) (text : String) : Bool :=
  let parts := text.splitOn w
  (parts.zip parts.tail).any fun (a, b) =>
    !((a.back?.map identChar).getD false) && !((b.front?.map identChar).getD false)

/-- **What an anchor's file holds for it**, given the file's text (none when no file stands at
the path). -/
def find (a : Anchor) (text : Option String) : Finding :=
  match text, a.name with
  | none, _ => .noFile
  | some _, none => .file
  | some t, some n =>
    let w := declaredWord n
    if (t.splitOn "\n").any (declares n w) then .declaration
    else if holdsWord w t then .word else .missing

/-- **The page `dictionary`**: the count of each finding, then each section's anchors, a row each:
the term on its first anchor's row, the name, the path and what the path's file holds for it.
`read` gives the text of a file of the repository, by its path. -/
def dictionary (es : List Entry) (read : String → Option String) : Document :=
  let found := es.map fun e => (e, e.anchors.map fun a => (a, find a (read a.path)))
  let all := found.flatMap (·.2.map (·.2))
  let count (f : Finding) := toString (all.filter (· == f)).length
  let sections := es.map (·.part) |>.eraseDups
  { title := "dictionary"
    producer := producer ["docs/core/controlled-english.md", "the files its anchors name"]
    body :=
      [.fields ([("entries", [.text (toString es.length)]), ("anchors", [.text (toString all.length)])] ++
        [Finding.declaration, .word, .file, .missing, .noFile].map fun f => (f.text, [.text (count f)]))] ++
      sections.zipIdx.map fun (s, i) =>
        .part s!"section-{i + 1}" s [
          .table ["term", "name", "path", "finding"]
            ((found.filter (·.1.part == s)).flatMap fun (e, as) =>
              if as.isEmpty then [[[.code e.term], [.text "—"], [.text "—"], [.text "—"]]] else
              as.zipIdx.map fun ((a, f), j) =>
                [if j == 0 then [.code e.term] else [], orDash ((a.name.map fun n => [Inline.code n]).getD []),
                 [.code a.path], [.text f.text]])]}

/-! ## The set -/

/-- The page of the set at the root: each page by its link, with its subject's declarations and its
rows (a dash for a page this set does not hold). -/
def index (pages : List (String × String × List String × Option Nat)) : Document where
  title := "reference"
  producer := producer ["the pages below"]
  body := [
    .table ["page", "source", "rows"]
      (pages.map fun (href, path, sources, rows) =>
        [[.link href path], sources.map Inline.code |>.intersperse (.text ", "),
         [.text ((rows.map toString).getD "—")]])]

/-- The rows of a document's tables, at every depth. -/
def rows (d : Document) : Nat :=
  (Block.collect { Algebra.collect (fun _ => ([] : List Unit)) with
    table := fun _ rs => rs.map fun _ => () } d.body).length

/-- The semantics page of the build's set, from the committed set's root (`generated/reference/`):
the build writes the set with the semantics page under `.lake/gen/reference/`, never committed. -/
def builtSemantics : String := "../../.lake/gen/reference/semantics/index.html"

/-- **The set**, its root `root` folders below the repository's: the index at the root, then each
page one folder down. With the semantics report's document, the set holds it as its last page,
titled by its subject's name like every page; its Markdown is `generated/semantics.md`, so it
writes none of its own. Without it, the index links the build's semantics page
(`builtSemantics`), which the site's check reads as a file at the set's root. -/
def site (dictionaryPage : Document) (semantics : Option Document) (pinned : List String)
    (root : Nat := 2) : Site :=
  let pages : List (String × List String × Document) := [
    ("forms", ["Effect4.Program.arms", "LayerTerm", "Effect4.Codegen.Forms.all"], forms root),
    ("native", ["Effect4.Program.NativeOp.spelled", "nativeSignature"], native root),
    ("marks", ["Tools.View.Glyph", "Tools.Form"], marks),
    ("refusals", ["Effect4.Ingest.Code", "ReadRefusal", "PrintRefusal", "ClassRefusal"], refusals),
    ("dictionary", ["docs/core/controlled-english.md"], dictionaryPage)] ++
    (semantics.map fun d =>
      ("semantics", ["Tools.SemanticsDocument", "generated/semantics.md"], { d with title := "semantics" })).toList
  let semanticsRow := match semantics with
    | some _ => []
    | none => [(builtSemantics, "semantics", ["Tools.SemanticsDocument", "generated/semantics.md"], none)]
  { pages :=
      { path := [], space := "index",
        doc := index (pages.map (fun (p, s, d) => (p ++ "/", p, s, some (rows d))) ++ semanticsRow) } ::
      pages.map fun (p, _, d) => { path := [p], space := p, doc := d, markdown := p != "semantics" }
    files := ["page.css", "looks.css", "site.json"] ++ pinned ++
      (if semantics.isNone then [builtSemantics.replace "../" ""] else [])
    contents := [] }

/-- The pins of the set's pages: every link that climbs to `vendorSrc`, as its file under the
repository's root, each once. -/
def pinnedFiles (docs : List Document) : List String :=
  (docs.flatMap fun d => Block.collect (Algebra.collect fun l => l.filterMap fun
    | .link href _ =>
      let path := ((href.splitOn "#").headD "").replace "../" ""
      if path.startsWith vendorSrc then some path else none
    | _ => none) d.body).eraseDups

/-- The pins of the set's pages, with their lines. -/
def pins (docs : List Document) : List Pin :=
  (docs.flatMap fun d => Block.collect (Algebra.collect fun l => l.filterMap fun
    | .link _ label => Pin.of? label
    | _ => none) d.body).eraseDups

/-- The templates the pages use: none. Every fact stands in a table cell or a figure. -/
def templates : List String := []

end Tools.Reference
