/-!
# Typed Markdown for human surfaces and ledgers

The human-facing outputs — ledgers, briefings, reports, and manifest docs —
are gate surfaces: byte-compared, and required to render well-formed Markdown
for every admitted input. This module is the owned typed emitter behind them
(design prior art: `predictable-machines/lean4-markdown`).

Design rules:
- **Escaping is the default path.** Inline text is escaped by the declared
  policy below; there is no raw-text constructor.
- **Tables are arity-checked**: headers are `Vector String n` and rows are
  `Vector Cell n`, so a row with a missing column does not elaborate.
- **Every human surface is `render` over typed blocks**; no surface is
  assembled by ad-hoc string concatenation.
-/

namespace Cas.Values.Markdown

/-- Inline content. There is deliberately no raw-text constructor: `text`,
`bold`, and table cells all pass through the escape policy at render
time. -/
inductive Inline where
  | text (s : String)
  | bold (s : String)
  | code (s : String)
  deriving Inhabited, Repr

/-- One table cell: escaped inline content. -/
structure Cell where
  content : List Inline
  deriving Inhabited, Repr

/-- An arity-checked table: a row with the wrong number of columns does not
elaborate. -/
structure Table (n : Nat) where
  headers : Vector String n
  rows : List (Vector Cell n)

/-- Block-level content. Bullets are inline lists. -/
inductive Block where
  | h1 (s : String)
  | h2 (s : String)
  | h3 (s : String)
  | p (items : List Inline)
  | ul (items : List (List Inline))
  | table (t : Table n)
  | codeBlock (lang : String) (code : String)

/-- Backslash-escape the declared character set; newlines become spaces. -/
def escape (s : String) : String :=
  String.join <| s.toList.map fun c =>
    if c = '\n' then " "
    else if c ∈ ['\\', '`', '*', '_', '~', '|', '[', ']', '<', '>', '#'] then
      String.singleton '\\' ++ String.singleton c
    else String.singleton c

def renderInline : Inline → String
  | .text s => escape s
  | .bold s => "**" ++ escape s ++ "**"
  | .code s => "`" ++ s ++ "`"

def renderInlines (items : List Inline) : String :=
  String.join (items.map renderInline)

def renderCell (c : Cell) : String :=
  renderInlines c.content

def renderHeaderRow {n : Nat} (headers : Vector String n) : String :=
  let cells := headers.toList.map escape
  "| " ++ String.intercalate " | " cells ++ " |\n| "
    ++ String.intercalate " | " (headers.toList.map fun _ => "---") ++ " |"

def renderRow {n : Nat} (row : Vector Cell n) : String :=
  "| " ++ String.intercalate " | " (row.toList.map renderCell) ++ " |"

def renderTable {n : Nat} (t : Table n) : String :=
  String.intercalate "\n" (renderHeaderRow t.headers :: t.rows.map renderRow)

def renderBlock : Block → String
  | .h1 s => "# " ++ escape s
  | .h2 s => "## " ++ escape s
  | .h3 s => "### " ++ escape s
  | .p items => renderInlines items
  | .ul items => String.intercalate "\n" (items.map fun i => "- " ++ renderInlines i)
  | .table t => renderTable t
  | .codeBlock lang code => "```" ++ lang ++ "\n" ++ code ++ "\n```"

/-- Render a document: blocks joined by blank lines, trailing newline. -/
def render (bs : List Block) : String :=
  String.intercalate "\n\n" (bs.map renderBlock) ++ "\n"

#guard escape "cursor | trace" == "cursor \\| trace"
#guard escape "never `live`" == "never \\`live\\`"
#guard renderInline (.text "a*b") == "a\\*b"
#guard render [.h2 "RPL-003", .p [.text "exactly one"]] == "## RPL-003\n\nexactly one\n"

end Cas.Values.Markdown
