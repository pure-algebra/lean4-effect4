import Std.Data.HashSet
import Tools.Form

/-!
# Tools.Document — a generated document as data, and its Markdown

A generator builds one `Document` and every output format is a fold of it: Markdown here, HTML in
`Tools.Document.Html`. The value holds no markup, no closure and no format choice:

* a part's heading level is its nesting, so no level is out of range;
* text and code are literal, and each format escapes them;
* a reference names a part of the same document by its key, and a link another page or file of
  the same site by its path from this page;
* a status is a word that a format may mark;
* a figure is a graph as data, its nodes and edges, which each format draws its own way: the HTML
  fold through the view's layout, the Markdown fold as a Mermaid diagram (decisions row 365).

Every fold that reads lines (the check, the site's links and keys) is one monoid fold,
`Algebra.collect`, with a field overridden where a block holds more than lines.
`Document.check` refuses a duplicate key, a reference to no part, a table row of the wrong width
and a figure's edge to no node, before any output is written. The design and its review, against Codex's docgen probe, are
`docs/research/2026-10-11-docgen/README.md`.
-/

namespace Tools.Document

/-- Inline content. -/
inductive Inline where
  | text (s : String)
  | code (s : String)
  /-- a reference to the part `key` of the same document, shown as `label` -/
  | ref (key label : String)
  /-- a link to another page or file, by its path from this page (`../semantics/`), shown as
  `label` -/
  | link (href label : String)
  /-- a status word (`proved`, `modulo`, `goal`, `open`, …) -/
  | status (word : String)
  deriving Inhabited, BEq, Repr

/-- A run of inline content. -/
abbrev Line := List Inline

/-- A node of a figure's graph: its key (unique in the figure), its label, its status word (empty for
none), a detail drawn after the status, the part it opens, by key, and its form (`Tools.Form`): a
box computes, a wire names, a port is a row of the host. -/
structure GraphNode where
  key : String
  label : String
  status : String := ""
  detail : String := ""
  ref : Option String := none
  form : Form := .box
  deriving Inhabited, BEq, Repr

/-- A node as a line: a reference to the part it opens, shown as its label, or its label. -/
def GraphNode.line (n : GraphNode) : Line :=
  match n.ref with
  | some r => [.ref r n.label]
  | none => [.text n.label]

/-- Block content. A part's blocks are its only recursive position. -/
inductive Block where
  | para (line : Line)
  /-- labelled values: a definition list -/
  | fields (rows : List (String × Line))
  /-- an unordered list -/
  | items (lines : List Line)
  /-- a code block in the syntax `language` (`lean`, `mermaid`, `text`) -/
  | code (language body : String)
  | table (headers : List String) (rows : List (List Line))
  /-- a figure of a directed graph: its key (unique among the document's keys), its caption, its
  nodes in the order the drawing ranks them, and its edges by node key -/
  | graph (key caption : String) (nodes : List GraphNode) (edges : List (String × String))
  /-- a part: its key (unique in its document), its title and its blocks -/
  | part (key title : String) (body : List Block)
  deriving Inhabited, Repr

/-- A document: its title, the lines that name its producer, and its blocks. -/
structure Document where
  title : String
  /-- the producer and the command that writes the document; a format that has comments prints them -/
  producer : List String := []
  body : List Block
  deriving Inhabited

/-- An algebra of the block signature: one field per constructor, a part receiving its blocks
already folded. -/
structure Algebra (α : Type) where
  para : Line → α
  fields : List (String × Line) → α
  items : List Line → α
  code : String → String → α
  table : List String → List (List Line) → α
  graph : String → String → List GraphNode → List (String × String) → α
  part : String → String → List α → α

mutual
  /-- The fold of a block into an algebra. -/
  def Block.fold {α : Type} (a : Algebra α) : Block → α
    | .para l => a.para l
    | .fields rs => a.fields rs
    | .items ls => a.items ls
    | .code lang body => a.code lang body
    | .table hs rs => a.table hs rs
    | .graph k c ns es => a.graph k c ns es
    | .part k t body => a.part k t (Block.foldList a body)
  /-- The fold of each block of a list. -/
  def Block.foldList {α : Type} (a : Algebra α) : List Block → List α
    | [] => []
    | b :: bs => b.fold a :: Block.foldList a bs
end

/-- **A monoid fold** into lists: each line a block holds, mapped by `line` and joined in order (a
paragraph's line, each field's value, each item, each table cell, each figure node as
`GraphNode.line`), and at a part its body's results, combined by `part`. A fold that reads more
than lines overrides a field: `{ Algebra.collect f with table := … }`. -/
def Algebra.collect {β : Type} (line : Line → List β)
    (part : String → String → List β → List β := fun _ _ body => body) : Algebra (List β) where
  para l := line l
  fields rs := rs.flatMap (line ·.2)
  items ls := ls.flatMap line
  code _ _ := []
  table _ rs := rs.flatMap (·.flatMap line)
  graph _ _ ns _ := ns.flatMap (line ·.line)
  part k t body := part k t body.flatten

/-- The results of a monoid fold over a list of blocks, joined. -/
def Block.collect {β : Type} (a : Algebra (List β)) (bs : List Block) : List β :=
  (Block.foldList a bs).flatten

/-! ## Checks -/

/-- What `check` reads from a block, one finding at a time. -/
inductive Finding where
  /-- a key the block declares: a part's or a figure's -/
  | key (k : String)
  | ref (k : String)
  | link (href : String)
  /-- a malformed block, in words -/
  | malformed (why : String)

private def lineFindings (l : Line) : List Finding :=
  l.filterMap fun
    | .ref k _ => some (.ref k)
    | .link h _ => some (.link h)
    | _ => none

/-- The census: the monoid fold of the lines' references and links and the parts' keys, with a
table's width and a figure's key, node keys and edges read too. -/
private def censusAlgebra : Algebra (List Finding) :=
  { Algebra.collect lineFindings (fun k _ body => .key k :: body) with
    table := fun hs rs => rs.flatMap (·.flatMap lineFindings) ++
      (if rs.all (·.length == hs.length) then [] else
        [.malformed s!"table [{", ".intercalate hs}]: a row's width differs from its header"])
    graph := fun k _ ns es =>
      let keys := ns.map (·.key)
      .key k :: ns.flatMap (lineFindings ·.line) ++
        (if keys.eraseDups.length == keys.length then [] else [.malformed s!"figure {k}: a node key twice"]) ++
        es.filterMap fun (a, b) =>
          if keys.contains a && keys.contains b then none else some (.malformed s!"figure {k}: the edge {a} → {b} names no node") }

/-- Refuse a blank or duplicate key, a reference to no part, a blank link or one with a space, a
table row of the wrong width and a figure's malformed graph, each by name. A reference may name a key that `outside`
holds: a part of another page split from the same document (`Tools.Site`). -/
def Document.check (d : Document) (outside : String → Bool := fun _ => false) : Except (List String) Unit := Id.run do
  let fs := Block.collect censusAlgebra d.body
  let mut errors := fs.filterMap fun | .malformed why => some why | _ => none
  let mut seen : Std.HashSet String := {}
  for f in fs do
    if let .key k := f then
      if k.isEmpty || k.any Char.isWhitespace then errors := errors ++ [s!"key {k.quote}: blank or with a space"]
      if seen.contains k then errors := errors ++ [s!"key {k}: duplicate"]
      seen := seen.insert k
  for f in fs do
    match f with
    | .ref r => unless seen.contains r || outside r do errors := errors ++ [s!"reference {r}: no part has this key"]
    | .link h => if h.isEmpty || h.any Char.isWhitespace then errors := errors ++ [s!"link {h.quote}: blank or with a space"]
    | _ => pure ()
  return if errors.isEmpty then .ok () else .error errors

/-! ## Prose: a docstring as blocks

A declaration's docstring is the author's explanation, and a page shows it (the understanding
note, `docs/research/2026-10-12-understanding-docs/README.md`, section 4.1). `prose` reads the
small part of Markdown that docstrings use: paragraphs, lists whose items open with `* ` or `- `,
and fenced code. In a line a backtick span is code and `**` is dropped; every other character is
text, so nothing in a docstring becomes markup by accident. -/

/-- A line's inline content: its backtick spans as code, the rest as text, `**` dropped. -/
def proseLine (s : String) : Line :=
  let runs := (s.replace "**" "").splitOn "`"
  (runs.zipIdx.filterMap fun (run, i) =>
    if run.isEmpty then none else some (if i % 2 == 1 then Inline.code run else .text run))

/-- The open block of `prose`: a paragraph's lines, a list's items (each item's lines), or a fence's
language and lines. -/
private inductive Open where
  | none
  | para (lines : Array String)
  | items (items : Array (Array String))
  | fence (language : String) (lines : Array String)

private def Open.close : Open → List Block
  | .none => []
  | .para ls => [.para (proseLine (" ".intercalate ls.toList))]
  | .items is => [.items (is.toList.map fun i => proseLine (" ".intercalate i.toList))]
  | .fence lang ls => [.code (if lang.isEmpty then "text" else lang) ("\n".intercalate ls.toList)]

/-- **A docstring as blocks.** -/
def prose (doc : String) : List Block := Id.run do
  let mut out : Array Block := #[]
  let mut cur : Open := .none
  for raw in doc.splitOn "\n" do
    let line := raw.trimAscii.toString
    match cur with
    | .fence lang ls =>
      if line.startsWith "```" then out := out ++ (Open.fence lang ls).close.toArray; cur := .none
      else cur := .fence lang (ls.push raw)
    | _ =>
      if line.startsWith "```" then
        out := out ++ cur.close.toArray; cur := .fence (line.drop 3).toString #[]
      else if line.isEmpty then
        out := out ++ cur.close.toArray; cur := .none
      else if line.startsWith "* " || line.startsWith "- " then
        let item := #[(line.drop 2).toString]
        match cur with
        | .items is => cur := .items (is.push item)
        | c => out := out ++ c.close.toArray; cur := .items #[item]
      else
        match cur with
        | .para ls => cur := .para (ls.push line)
        | .items is => cur := .items (is.modify (is.size - 1) (·.push line))
        | c => out := out ++ c.close.toArray; cur := .para #[line]
  return (out ++ cur.close.toArray).toList

/-! ## Markdown (CommonMark with GitHub's tables)

A reference prints as code, its label: a Markdown reader makes its own heading anchors, so a link
to a key would not resolve. A status prints as its word. -/

/-- A backtick run longer than every run inside `s`, and at least `least` long. -/
def fence (least : Nat) (s : String) : String :=
  let (_, longest) := s.foldl (fun (run, longest) c =>
    let run := if c == '`' then run + 1 else 0
    (run, max longest run)) (0, 0)
  String.ofList (List.replicate (max least (longest + 1)) '`')

/-- Literal text, escaped where CommonMark would read it as markup: the punctuation that opens a
span, a link, raw HTML or a table cell, and an underscore that is not inside a word. -/
def markdownText (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  for i in [0:cs.size] do
    let c := cs[i]!
    let inWord := i > 0 && (cs[i-1]!).isAlphanum && (cs[i+1]?.map Char.isAlphanum).getD false
    if c == '\n' then out := out ++ " "
    else if "\\`*[]<>|".contains c || (c == '_' && !inWord) then out := (out.push '\\').push c
    else out := out.push c
  return out

/-- Literal code as a code span; a line break becomes a space. In a table cell a pipe is escaped
too, which GitHub's tables read before the span; elsewhere an escape inside a span would print. -/
def markdownCode (inTable : Bool) (s : String) : String :=
  let s := s.replace "\n" " "
  let s := if inTable then s.replace "|" "\\|" else s
  let f := fence 1 s
  let pad := if s.startsWith "`" || s.endsWith "`" then " " else ""
  f ++ pad ++ s ++ pad ++ f

def markdownInline (inTable : Bool) : Inline → String
  | .text s => markdownText s
  | .code s => markdownCode inTable s
  | .ref _ label => markdownCode inTable label
  | .link href label => "[" ++ markdownText label ++ "](" ++ href ++ ")"
  | .status w => markdownText w

def markdownLine (l : Line) (inTable := false) : String :=
  String.join (l.map (markdownInline inTable))

private def row (cells : List String) : String := "| " ++ " | ".intercalate cells ++ " |\n"

/-- A figure as a Mermaid flowchart, top to bottom, which GitHub draws: each node by its place,
labelled with its label and its status and detail on a second line, in the shape of its form: a box
`[…]`, a wire as a stadium `([…])`, a port as a subroutine `[[…]]`. -/
def mermaid (ns : List GraphNode) (es : List (String × String)) : String :=
  let id (k : String) : String := "n" ++ toString (ns.findIdx (·.key == k))
  let second (n : GraphNode) : String :=
    " · ".intercalate ([n.status, n.detail].filter (!·.isEmpty))
  let label (n : GraphNode) : String :=
    ((n.label ++ (if (second n).isEmpty then "" else "<br/>" ++ second n)).replace "\"" "#quot;")
  let shaped (n : GraphNode) : String :=
    match n.form with
    | .box => s!"[\"{label n}\"]"
    | .wire => s!"([\"{label n}\"])"
    | .port => s!"[[\"{label n}\"]]"
  "```mermaid\nflowchart TB\n" ++ String.join (ns.map fun n => s!"  {id n.key}{shaped n}\n") ++
    String.join (es.map fun (a, b) => s!"  {id a} --> {id b}\n") ++ "```\n\n"

/-- The Markdown algebra. Its carrier takes the nesting depth, which fixes a part's heading
level: a part at the top of the document is `##`, under the title's `#`, and levels stop at six. -/
def markdownAlgebra : Algebra (Nat → String) where
  para l _ := markdownLine l ++ "\n\n"
  fields rs _ := " · ".intercalate (rs.map fun (k, v) => markdownText k ++ ": " ++ markdownLine v) ++ "\n\n"
  items ls _ := String.join (ls.map fun l => "- " ++ markdownLine l ++ "\n") ++ "\n"
  code lang body _ :=
    let f := fence 3 body
    f ++ lang ++ "\n" ++ body ++ (if body.endsWith "\n" then "" else "\n") ++ f ++ "\n\n"
  table hs rs _ :=
    if rs.isEmpty then "" else
      row (hs.map markdownText) ++ row (hs.map fun _ => "---") ++
        String.join (rs.map fun r => row (r.map (markdownLine (inTable := true)))) ++ "\n"
  graph _ caption ns es _ := markdownText caption ++ "\n\n" ++ mermaid ns es
  part _ t body depth :=
    String.ofList (List.replicate (min 6 depth) '#') ++ " " ++ markdownText t ++ "\n\n" ++
      String.join (body.map (· (depth + 1)))

/-- The document as Markdown: its producer as a leading comment, its title, then its blocks. -/
def Document.markdown (d : Document) : String :=
  let producer := if d.producer.isEmpty then "" else
    "<!-- " ++ "\n".intercalate d.producer ++ "\n-->\n"
  producer ++ "# " ++ markdownText d.title ++ "\n\n" ++
    String.join ((Block.foldList markdownAlgebra d.body).map (· 2))

end Tools.Document
