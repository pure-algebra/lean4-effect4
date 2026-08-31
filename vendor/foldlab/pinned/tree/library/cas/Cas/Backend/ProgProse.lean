import Cas.Lang.Defun
import Cas.Grammar.Manifest
import Cas.Codec.Hex

/-!
# The effect envelope, verbalized — `Envelope → Prose`

The plain-language capability's first projection. `Cas.Lang.Envelope`
is what a straight-line table can do, computed from the table alone
(`Cas/Lang/Defun.lean`): the literal addresses it reads, the shapes it
puts in program order, and the answer-index dataflow. That is
stratum-1 data, so verbalizing it is a total function on first-order
content — a PROJECTION, not a generation, and the byte gate over the
generated programs checks it for free.

Layering is why this module exists rather than a definition in
`Cas/Lang/Defun.lean`. `Prose = List Inline` and `Ty.sortName` live in
`Cas/Grammar/Manifest.lean`, which is not below `Cas/Lang/Defun.lean`;
`Cas.Backend` already sits above both (`Cas/Backend/Mcp.lean` imports
`Cas.Lang.Defun`), so the bridge is homed here, beside the emitter that
consumes it.

What the envelope CANNOT say is visible in the prose and is stated
rather than papered over:

- `Envelope.puts` is a `filterMap` over the table, so a put does not
  know which LINE it sits on. Puts are numbered as puts and dataflow
  edges are numbered as lines; on a table that is all puts the two
  numberings coincide, and the prose does not claim that they do.
- `Envelope.reads` is a flat list over the whole table and `dataflow`
  is a list of index pairs, so an individual reference's operand — a
  literal or an earlier answer — is not recoverable. The put sentence
  therefore states the expected KINDS of a line's references, and the
  dataflow sentence states the answers a line consumes, without
  pairing them.

The lowering `Tree.table` below is a second walk beside
`Cas.Backend.EmitProg.lowerTree`, not a replacement for it: routing the
emitter itself through `PProg` is its own slice
(`Cas/Backend/Mcp.lean`'s note), and is not taken here. The two walks
are the same children-first recursion, and the gated docstrings are
what would go red if they parted.
-/

namespace Cas.Backend.ProgProse

open Cas.Grammar Cas.Values.Markdown

/-! ## Small spellings

Counting words rather than digits is what makes the output read as
prose; the indices and the byte widths stay numerals, because they are
measurements. -/

/-- English for the small counts a table's prose actually uses. Zero is
`no`, because every sentence that counts here reads better negated than
zeroed ("no references", not "0 references"). -/
def numeral : Nat → String
  | 0 => "no"
  | 1 => "one"
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | 6 => "six"
  | 7 => "seven"
  | 8 => "eight"
  | 9 => "nine"
  | 10 => "ten"
  | 11 => "eleven"
  | 12 => "twelve"
  | n => toString n

/-- `one put`, `six puts` — the singular is the only special case. -/
def counted (n : Nat) (singular plural : String) : String :=
  numeral n ++ " " ++ (if n = 1 then singular else plural)

/-- The indefinite article a sort name takes. The grammar's sort names
are ASCII words, so the vowel test is the whole rule. -/
def article (s : String) : String :=
  match s.toList with
  | c :: _ => if c ∈ ['a', 'e', 'i', 'o', 'u'] then "an" else "a"
  | [] => "a"

/-- A kind tag, spelled as the registry spells it. An unratified tag has
no sort name, so it is named as the number it is rather than guessed
at. -/
def sortSpan (tag : UInt8) : List Inline :=
  match Ty.ofTag tag with
  | some t => [Inline.code t.sortName]
  | none => [Inline.text s!"unratified tag {tag.toNat}"]

/-- A kind tag with its article: ``a `chunk```, ``an `entry```. -/
def sortPhrase (tag : UInt8) : List Inline :=
  match Ty.ofTag tag with
  | some t => [Inline.text (article t.sortName ++ " "), Inline.code t.sortName]
  | none => [Inline.text s!"a node at unratified tag {tag.toNat}"]

/-- ``a `tree`, a `tree` and a `chunk` `` — the expected kinds of one
line's references, in the order the line writes them. -/
def sortList : List UInt8 → List Inline
  | [] => []
  | [t] => sortPhrase t
  | [t, u] => sortPhrase t ++ [Inline.text " and "] ++ sortPhrase u
  | t :: rest => sortPhrase t ++ [Inline.text ", "] ++ sortList rest

/-- `0`, `0 and 1`, `0, 1 and 3` — a line-index list. -/
def indexList : List Nat → String
  | [] => ""
  | [i] => toString i
  | [i, j] => toString i ++ " and " ++ toString j
  | i :: rest => toString i ++ ", " ++ indexList rest

/-- A comma-and list of addresses, each as a code span. -/
def addrSpans : List Addr32 → List Inline
  | [] => []
  | [a] => [Inline.code (hexS a.val)]
  | a :: rest => Inline.code (hexS a.val) :: Inline.text ", " :: addrSpans rest

/-- The dataflow edges of one consuming line, gathered: `Line 4 reads
the answers of lines 1 and 3.` -/
def dataflowSentence (i : Nat) (srcs : List Nat) : Prose :=
  match srcs with
  | [j] => [Inline.text ("Line " ++ toString i ++ " reads line " ++ toString j ++
      "'s answer.")]
  | js => [Inline.text ("Line " ++ toString i ++ " reads the answers of lines " ++
      indexList js ++ ".")]

/-- Group the dataflow by consuming line, keeping both the line order
and each line's operand order. Written as a fold rather than a sort, so
the grouping is the table's own order and nothing else. -/
def groupDataflow : List (Nat × Nat) → List (Nat × List Nat)
  | [] => []
  | (i, j) :: rest =>
    match groupDataflow rest with
    | (i', js) :: more =>
      if i = i' then (i, j :: js) :: more else (i, [j]) :: (i', js) :: more
    | [] => [(i, [j])]

/-- Sentences into one paragraph. -/
def joinSentences : List Prose → Prose
  | [] => []
  | [p] => p
  | p :: rest => p ++ [Inline.text " "] ++ joinSentences rest

end Cas.Backend.ProgProse

namespace Cas.Lang

open Cas.Grammar Cas.Values.Markdown Cas.Backend.ProgProse

/-- One put's sentence: the sort it writes, the width of its payload,
and the kinds its references must have. The scheme version appears only
when it is not the grammar's (`Cas.Grammar.schemeVersion`), because a
sentence that repeats the constant on every line stops being read. -/
def PutShape.sentence (k : Nat) (s : PutShape) : Prose :=
  [Inline.text ("Put " ++ toString k ++ " writes ")] ++ sortPhrase s.tag ++
  [Inline.text (" node with " ++
    (match s.payload.length with
      | 0 => "an empty payload"
      | 1 => "a payload of 1 byte"
      | n => "a payload of " ++ toString n ++ " bytes") ++
    (if s.version = Cas.Grammar.schemeVersion then ""
     else " at scheme version " ++ toString s.version.toNat))] ++
  (match s.refKinds with
    | [] => [Inline.text " and no references"]
    | ks => [Inline.text (" and " ++ counted ks.length "reference" "references" ++
        ", expecting ")] ++ sortList ks) ++
  [Inline.text "."]

/-- The summary sentence over `Envelope.putCount`. -/
def Envelope.putCountSentence (e : Envelope) : Prose :=
  [Inline.text ("The table performs " ++ counted e.putCount "put" "puts" ++ ".")]

/-- The literal addresses the table names outright. These are the whole
of its dependence on content it did not write, so they are spelled in
full rather than counted. -/
def Envelope.readsSentence (e : Envelope) : Prose :=
  match e.reads with
  | [] => [Inline.text "It names no literal address."]
  | as =>
    [Inline.text ("It names " ++
      counted as.length "literal address" "literal addresses" ++ ": ")] ++
    addrSpans as ++ [Inline.text "."]

/-- The summary sentence over `Envelope.dataflowClosed` — the refusal
class the envelope decides without running. -/
def Envelope.closureSentence (e : Envelope) : Prose :=
  if e.dataflow.isEmpty then
    [Inline.text "No line reads another line's answer, so the dataflow is closed."]
  else if e.dataflowClosed then
    [Inline.text
      "Every reference names a strictly earlier line, so the dataflow is closed."]
  else
    [Inline.text
      "Some reference does not name a strictly earlier line, so the dataflow is not closed."]

/-- THE VERBALIZATION, sentence by sentence: the put count, the literal
reads, one sentence per put shape in program order, one sentence per
consuming line of dataflow, and the closure verdict. Every field of the
envelope is spoken for, and nothing else is. -/
def Envelope.proseLines (e : Envelope) : List Prose :=
  [e.putCountSentence, e.readsSentence] ++
  (e.puts.zipIdx.map fun (s, k) => PutShape.sentence k s) ++
  ((groupDataflow e.dataflow).map fun (i, js) => dataflowSentence i js) ++
  [e.closureSentence]

/-- The whole verbalization as one paragraph — `Prose`, so it renders
through the house Markdown emitter and flattens through `Prose.plain`
for the surfaces that take a string. -/
def Envelope.toProse (e : Envelope) : Prose :=
  joinSentences e.proseLines

end Cas.Lang

namespace Cas.Backend

open Cas.Grammar Cas.Lang

/-! ## A grammar term's table

`Cas.Backend.EmitProg.lowerTree` lowers a `Tree` straight to host
statements over variable NAMES; this is the same children-first walk
landing on `PProg`, so a grammar term has an envelope to verbalize.
The two walks agreeing is prose, not a theorem — see the module note. -/

private def putLine (tag : UInt8) (payload : Bytes)
    (refs : List (Nat × UInt8)) : StateM (Array PLine × Nat) Nat := do
  let (lines, n) ← get
  set (lines.push
    (.put Cas.Grammar.schemeVersion tag payload
      (refs.map fun (i, expected) => (expected, PIn.ans i))), n + 1)
  return n

/-- The children-first walk: one `put` line per node in `flatten` order,
each later line's references naming the answer indices of the lines that
wrote its children. -/
def lowerTable : Tree t → StateM (Array PLine × Nat) Nat
  | .value p => putLine Ty.value.wireTag p.val []
  | .chunk p => putLine Ty.chunk.wireTag p.val []
  | .leaf i l d => do
    let cd ← lowerTable d
    putLine Ty.tree.wireTag (nat32 i.toNat ++ nat32 l.toNat)
      [(cd, Ty.chunk.wireTag)]
  | .parent l r => do
    let la ← lowerTable l
    let ra ← lowerTable r
    putLine Ty.tree.wireTag [] [(la, Ty.tree.wireTag), (ra, Ty.tree.wireTag)]
  | .manifest re tot le root => do
    let ra ← lowerTable root
    putLine Ty.manifest.wireTag
      (nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat)
      [(ra, Ty.tree.wireTag)]
  | .file name mt c => do
    let ca ← lowerTable c
    putLine Ty.file.wireTag (frame name.val ++ frame mt.val)
      [(ca, Ty.manifest.wireTag)]
  | .genesis => putLine Ty.entry.wireTag [] []
  | .entry note item prev => do
    let ia ← lowerTable item
    let pa ← lowerTable prev
    putLine Ty.entry.wireTag note.val
      [(ia, Ty.file.wireTag), (pa, Ty.entry.wireTag)]
  | .schema p => putLine Ty.schema.wireTag p.val []
  | .git obj => putLine Ty.git.wireTag obj.val []

/-- The defunctionalized table of a grammar term. -/
def _root_.Cas.Grammar.Tree.table (tr : Tree t) : PProg :=
  ((lowerTable tr).run (#[], 0)).2.1.toList

/-- The effect envelope of a grammar term — what its store program can
do, computed from the term alone. -/
def _root_.Cas.Grammar.Tree.envelope (tr : Tree t) : Cas.Lang.Envelope :=
  PProg.envelope tr.table

/-- A grammar term's verbalization, as the doc lines a generated
declaration carries. -/
def _root_.Cas.Grammar.Tree.docLines (tr : Tree t) : List String :=
  tr.envelope.proseLines.map Prose.plain

/-! ## Witnesses

The verbalizer is pinned on terms, not described. The first guard reads
the put shapes off the grammar's OWN `flatten` order, so this module's
walk cannot part from `Cas/Grammar/Tree.lean`'s without a red build —
the one thing a second walk owes. The second guard is the sentences
themselves, so a change of wording is a visible edit rather than a
silent one. -/

private def noAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

private def noH : Bytes → Addr32 := fun _ => noAddr

private def wChunk : Tree .chunk := .chunk (Payload.ofBytes [1, 2, 3])

private def wLeaf : Tree .tree := .leaf 0 3 wChunk

#guard PProg.puts wLeaf.table ==
  ((wLeaf.flatten noH).map fun b => PutShape.ofNode b.node)

#guard wLeaf.docLines == [
  "The table performs two puts.",
  "It names no literal address.",
  "Put 0 writes a chunk node with a payload of 3 bytes and no references.",
  "Put 1 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.",
  "Line 1 reads line 0's answer.",
  "Every reference names a strictly earlier line, so the dataflow is closed."
]

#guard wChunk.docLines == [
  "The table performs one put.",
  "It names no literal address.",
  "Put 0 writes a chunk node with a payload of 3 bytes and no references.",
  "No line reads another line's answer, so the dataflow is closed."
]

end Cas.Backend
