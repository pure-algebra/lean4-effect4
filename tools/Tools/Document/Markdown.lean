import Tools.Document

/-!
# Tools.Document.Markdown — the site's written copy, read as a document

The copy that a writer adds to the documentation site (`docs/site/`, decisions row 366, point 8)
is Markdown in a small subset, read here into a `Tools.Document`, so it takes the same checks and
folds as every page. The writer never touches Lean: `make site` reads the files at every build.

The subset:

* `# Title`, on the first line that holds text, is the document's title;
* `## Heading` opens a part, and `###` to `######` a part inside it. A heading may end in
  `{#key}`, its key; otherwise its key is its words, lowercased and joined by `-`. Every key takes
  the reader's prefix, so copy's keys never meet a key of the page it joins;
* a paragraph is a run of lines; a list is a run of items that open with `- ` or `* `, a line
  that does not open an item continuing the one above;
* a fence of three backticks with a language opens code, and the next fence closes it;
* in a line, a backtick span is code, `[label](#key)` is a reference to a part,
  `[label](href)` a link to a page or a file, and a status word in braces (`{proved}`,
  `{modulo}`, `{goal}`, `{open}`, `{refuted}`, `{absent}`, `{assumed}`) the status with its mark.

Anything else is refused at its line, with the reason: a table, a quotation, raw HTML, an image,
emphasis with `*` or `_` around words, a heading that skips a level, an unclosed span or fence.
The copy is plain text with no markup that the subset does not name.
-/

namespace Tools.Document.Markdown

/-- A refusal: the line, from one, and the reason. -/
abbrev Read := Except String

/-- A heading's words as a key: lowercased, each run of other characters one `-`. -/
def slug (s : String) : String :=
  let cs := s.toList.map fun c => if c.isAlphanum then c.toLower else '-'
  let joined := String.ofList cs
  "-".intercalate ((joined.splitOn "-").filter (!·.isEmpty))

/-- The status words a brace may hold. -/
def statusWords : List String := ["proved", "modulo", "goal", "open", "refuted", "absent", "assumed"]

/-- A line's inline content: code spans, references, links, statuses and text. -/
def readLine (n : Nat) (line : String) : Read Line := do
  let cs := line.toList.toArray
  let mut out : Array Inline := #[]
  let mut text := ""
  let mut i := 0
  let fail (why : String) : Read Line := .error s!"line {n}: {why}"
  while i < cs.size do
    let c := cs[i]!
    if c == '`' then
      let close := (List.range (cs.size - (i + 1))).find? fun k => cs[i + 1 + k]! == '`'
      let some k := close | return ← fail "a code span with no closing backtick"
      unless text.isEmpty do out := out.push (.text text); text := ""
      out := out.push (.code (String.ofList (cs.extract (i + 1) (i + 1 + k)).toList))
      i := i + k + 2
    else if c == '[' then
      let close := (List.range (cs.size - (i + 1))).find? fun k => cs[i + 1 + k]! == ']'
      let some k := close | return ← fail "a `[` with no `]`"
      let label := String.ofList (cs.extract (i + 1) (i + 1 + k)).toList
      let j := i + k + 2
      unless j < cs.size && cs[j]! == '(' do return ← fail s!"`[{label}]` is not followed by `(href)`"
      let shut := (List.range (cs.size - (j + 1))).find? fun m => cs[j + 1 + m]! == ')'
      let some m := shut | return ← fail "a link with no closing `)`"
      let href := String.ofList (cs.extract (j + 1) (j + 1 + m)).toList
      unless text.isEmpty do out := out.push (.text text); text := ""
      out := out.push (if href.startsWith "#" then .ref (href.drop 1).toString label else .link href label)
      i := j + m + 2
    else if c == '{' then
      let close := (List.range (cs.size - (i + 1))).find? fun k => cs[i + 1 + k]! == '}'
      let word := (close.map fun k => String.ofList (cs.extract (i + 1) (i + 1 + k)).toList).getD ""
      if statusWords.contains word then
        unless text.isEmpty do out := out.push (.text text); text := ""
        out := out.push (.status word)
        i := i + word.length + 2
      else
        text := text.push c
        i := i + 1
    else if c == '*' then
      return ← fail "emphasis with `*` is not part of the subset: write the words plainly"
    else if c == '_' && (i == 0 || !(cs[i - 1]!).isAlphanum) && i + 1 < cs.size && (cs[i + 1]!).isAlpha then
      return ← fail "emphasis with `_` is not part of the subset: put a name in a code span"
    else if c == '!' && i + 1 < cs.size && cs[i + 1]! == '[' then
      return ← fail "an image is not part of the subset"
    else
      text := text.push c
      i := i + 1
  unless text.isEmpty do out := out.push (.text text)
  return out.toList

/-- A part being read: its depth, key, title and blocks so far. -/
private structure Open where
  depth : Nat
  key : String
  title : String
  blocks : Array Block
  deriving Inhabited

/-- What a run of lines builds: a paragraph's lines, a list's items, or a fence's language and
lines. -/
private inductive Run where
  | none
  | para (lines : Array String) (start : Nat)
  | items (items : Array (Array String)) (start : Nat)
  | fence (language : String) (lines : Array String) (start : Nat)

/-- **A file of copy as a document**: its title, and its blocks, each key prefixed by `keyPrefix`.
`file` names the file in a refusal. -/
def read (file keyPrefix : String) (text : String) : Read Document := do
  let fail (n : Nat) (why : String) : Read Document := .error s!"{file}:{n}: {why}"
  let mut title : Option String := none
  let mut stack : Array Open := #[{ depth := 1, key := "", title := "", blocks := #[] }]
  let mut run : Run := .none
  let lines := text.splitOn "\n"
  -- the end of a run: its block, pushed onto the innermost open part
  let flush (stack : Array Open) (run : Run) : Read (Array Open) := do
    let block? : Option Block ← match run with
      | .none => pure none
      | .para ls n => pure (some (.para (← (readLine n (" ".intercalate ls.toList)).mapError (s!"{file}:" ++ ·))))
      | .items is n => pure (some (.items (← is.toList.mapM fun i =>
          (readLine n (" ".intercalate i.toList)).mapError (s!"{file}:" ++ ·))))
      | .fence lang ls _ => pure (some (.code (if lang.isEmpty then "text" else lang) ("\n".intercalate ls.toList)))
    match block?, stack.back? with
    | some b, some top => return stack.pop.push { top with blocks := top.blocks.push b }
    | _, _ => return stack
  -- close the parts at `depth` and deeper into their parents
  let close (stack : Array Open) (depth : Nat) : Array Open := Id.run do
    let mut st := stack
    for _ in [0:st.size] do
      match st.back? with
      | some top =>
        if top.depth ≥ depth && st.size > 1 then
          let st' := st.pop
          let parent := st'.back!
          st := st'.pop.push { parent with blocks := parent.blocks.push (.part top.key top.title top.blocks.toList) }
        else break
      | none => break
    return st
  for (raw, i) in lines.zipIdx do
    let n := i + 1
    let line := raw.trimAscii.toString
    if let .fence lang ls start := run then
      if line.startsWith "```" then stack ← flush stack (.fence lang ls start); run := .none
      else run := .fence lang (ls.push raw) start
      continue
    if line.startsWith "```" then
      stack ← flush stack run; run := .fence (line.drop 3).toString #[] n
    else if line.isEmpty then
      stack ← flush stack run; run := .none
    else if line.startsWith "#" then
      stack ← flush stack run; run := .none
      let hashes := (line.takeWhile (· == '#')).toString.length
      let rest := (line.drop hashes).trimAscii.toString
      if hashes == 1 then
        if title.isSome then return ← fail n "a second `#` title"
        title := some rest
      else
        let depth := stack.back!.depth
        if hashes > depth + 1 then return ← fail n s!"a heading of level {hashes} under one of level {depth}"
        let (words, key) := match rest.splitOn "{#" with
          | [w, k] => (w.trimAscii.toString, (k.dropEnd 1).toString)
          | _ => (rest, slug rest)
        stack := close stack hashes
        stack := stack.push { depth := hashes, key := keyPrefix ++ key, title := words, blocks := #[] }
    else if line.startsWith "|" then return ← fail n "a table is not part of the subset: write a list"
    else if line.startsWith ">" then return ← fail n "a quotation is not part of the subset"
    else if line.startsWith "<" then return ← fail n "raw HTML is not part of the subset"
    else if line.startsWith "- " || line.startsWith "* " then
      let item := #[(line.drop 2).toString]
      match run with
      | .items is start => run := .items (is.push item) start
      | r => stack ← flush stack r; run := .items #[item] n
    else
      match run with
      | .para ls start => run := .para (ls.push line) start
      | .items is start => run := .items (is.modify (is.size - 1) (·.push line)) start
      | r => stack ← flush stack r; run := .para #[line] n
  if let .fence _ _ start := run then return ← fail start "a fence that never closes"
  stack ← flush stack run
  stack := close stack 2
  let some t := title | return ← fail 1 "no `#` title on the first line of text"
  return { title := t, producer := [file], body := stack.back!.blocks.toList }

end Tools.Document.Markdown
