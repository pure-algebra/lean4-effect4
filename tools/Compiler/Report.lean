import Compiler.Emit
import Tools.Document.Json

/-!
# Compiler.Report — a command's run as a value, and the terminal as one fold of it

Every command of `Compiler.Main` returns a `Report` and prints nothing itself
(`docs/research/2026-10-21-cli-report/README.md`). A report is the command's name, its arguments
as given, the output root its paths are under, and its events in order:

- a fold started or finished (`started`, `finished`): "folding the program", "printing for ts";
- a measure, a word and a count (`measure`): definitions, rows, nodes, calls, requests;
- an artifact written (`artifact`): its role, form and kind in the artifact layout note's words
  (`docs/research/2026-10-21-artifact-layout/README.md`, §3 and §4.1), its path under the output
  root, its byte count and its SHA-256, read from the bytes the command wrote, never from the
  clock or the output path;
- a reading given (`reading`): what a command answers in words, the certificate, a manifest, one
  line of `run`, with the same reading through its carrier's public JSON where it has one;
- a refusal (`refusal`), the located refusal the command already has, in its words; and a usage
  error (`usage`), the command line's.

**The formats are folds of the report.** `piecesWith t styled r` is the one fold over a text `t`:
with `styled := false` it writes text alone, the `plain` format; with `styled := true` it adds
ANSI escapes and the line in progress, the `tty` format, and `strip_pieces` proves the tty fold
with its escapes removed is the plain fold at every text (concept 7, `initial-algebras-folds`;
the text is a parameter the proof never inspects). `Report.json r` is the report's own lossless JSON, read back by `Report.ofJson`
(`Report.ofJson_json`): the `json` format. `document r` folds the report to a `Tools.Document`,
the readable view, and `md` is its Markdown fold.

The marks are the design language's (`Tools.View.Page`, `Tools.View.Glyph`): `□` a fold started
and not finished, `┄┄` the wait while a fold is in progress, `■` a fold finished or an artifact
kept, `─▶` before each artifact under the fold that wrote it.

**The log** (`Log`) is the one IO: a command writes its events to it, and the live sink runs the
same step function as each event arrives, so a terminal shows a fold in progress and the final
text is the batch fold's by construction (`Report.step`, `Report.close`).
-/

namespace Compiler

namespace Report

open Tools.Document (Document Block Inline Line)

/-! ## The vocabulary of the artifact layout note -/

/-- Who a file is for (the layout note, §3). -/
inductive Role where
  | program
  | host
  | run
  deriving DecidableEq, Repr

def Role.word : Role → String
  | .program => "program"
  | .host => "host"
  | .run => "run"

/-- What a file is (the layout note, §4.1): a canonical object, a print for one target, a record
of one run, or the index. -/
inductive Form where
  | object
  | print (target : String)
  | record
  | index
  deriving DecidableEq, Repr

def Form.word : Form → String
  | .object => "object"
  | .print target => "print " ++ target
  | .record => "record"
  | .index => "index"

/-- The layout note's kinds where a command writes one today, and four it does not name: the
copied prelude, an inspection document, a figure and a table (the report note, §8). -/
inductive Kind where
  | object
  | certificate
  | program
  | module
  | surface
  | recipe
  | closure
  | manifest
  | prelude
  | document
  | figure
  | table
  deriving DecidableEq, Repr

def Kind.word : Kind → String
  | .object => "object"
  | .certificate => "certificate"
  | .program => "program"
  | .module => "module"
  | .surface => "surface"
  | .recipe => "recipe"
  | .closure => "closure"
  | .manifest => "manifest"
  | .prelude => "prelude"
  | .document => "document"
  | .figure => "figure"
  | .table => "table"

/-- The report's kind of a file the emission writes, by the manifest's kind (`Compiler.Kind`) and
the file's path: the canonical bytes are the object, and their tagged print the program. -/
def Kind.ofEmitted (kind : Compiler.Kind) (path : String) : Kind :=
  match kind with
  | .canonical => if path.endsWith ".json" then .program else .object
  | .module => .module
  | .recipe => .recipe
  | .closure => .closure
  | .prelude => .prelude
  | .surface => .surface
  | .certificate => .certificate
  | .manifest => .manifest

/-- The form of a file the emission writes: the canonical bytes are the object, the manifest the
index, and every other file a print for the target. -/
def Form.ofEmitted (kind : Compiler.Kind) (path : String) (target : String) : Form :=
  match kind with
  | .canonical => if path.endsWith ".json" then .print target else .object
  | .manifest => .index
  | _ => .print target

/-- **One file a command wrote**: its role, form and kind, its path under the output root, its
byte count and its SHA-256. -/
structure Written where
  role : Role
  form : Form
  kind : Kind
  path : String
  size : Nat
  sha256 : String
  deriving DecidableEq, Repr

/-- A written file, its count and digest read from the bytes. -/
def Written.of (role : Role) (form : Form) (kind : Kind) (path : String) (bytes : ByteArray) :
    Written :=
  { role, form, kind, path, size := bytes.size, sha256 := sha256Hex bytes }

/-- A file of an emission (`Compiler.Artifact`), written for `target`, as the report records it. -/
def Written.ofEmitted (target : String) (a : Artifact) : Written :=
  Written.of .program (Form.ofEmitted a.kind a.path target) (Kind.ofEmitted a.kind a.path) a.path a.bytes

/-! ## The events -/

/-- **One event of a command's run.** -/
inductive Event where
  /-- a fold began -/
  | started (what : String)
  /-- the same fold ended -/
  | finished (what : String)
  /-- a count, by its word; between a fold's start and its finish it belongs to that fold -/
  | measure (word : String) (count : Nat)
  /-- a file written, after the fold that produced it -/
  | artifact (file : Written)
  /-- what the command answers, in words, and the same through its carrier's public JSON -/
  | reading (what : String) (text : String) (json : Option String)
  /-- the located refusal the command already has, at the step it stopped, in its words -/
  | refusal (step : String) (why : String)
  /-- a usage error: the command, and why -/
  | usage (command : String) (why : String)
  deriving DecidableEq, Repr

end Report

/-- **A command's run as a value**: the command's name, its arguments as given, the output root
its artifacts' paths are under, and its events in order. The events are a function of the object,
the target and the pins; the root is a place and no part of them. -/
structure Report where
  command : String
  arguments : List String
  out : Option String := none
  events : List Report.Event
  deriving DecidableEq, Repr

namespace Report

open Tools.Document (Document Block Inline Line)
open Lean (Json)

/-- The exit code: `2` at a usage error, `1` at a refusal, `0` otherwise. -/
def exit (r : Report) : UInt32 :=
  if r.events.any (fun | .usage .. => true | _ => false) then 2
  else if r.events.any (fun | .refusal .. => true | _ => false) then 1
  else 0

/-- The files the command wrote, in order. -/
def artifacts (r : Report) : List Written :=
  r.events.filterMap fun | .artifact w => some w | _ => none

/-- The refusals and usage errors, in their words. -/
def refusals (r : Report) : List String :=
  r.events.filterMap fun
    | .refusal _ why => some why
    | .usage command why => some (if command.isEmpty then why else s!"{command}: {why}")
    | _ => none

/-! ## The text: one fold, two formats

The fold (`piecesWith`) takes its text as a parameter (`Text`): every string it writes comes from
one of the text's functions, and the fold itself only joins pieces, styles them and keeps the
state of the fold in progress. So the law `strip_pieces` is proved for every text and inspects no
string, which keeps it off `Classical.choice`, where Lean's string functions lead. The one text the
formats use is `Text.standard`. -/

/-- A piece of the terminal's text: text every terminal keeps; an ANSI escape, which a terminal
shows and no reader keeps; or text a carriage return overwrites. -/
inductive Piece where
  | text (s : String)
  | escape (s : String)
  | ephemeral (s : String)
  deriving DecidableEq, Repr

/-- Whether a piece is kept text. -/
def Piece.isText : Piece → Bool
  | .text _ => true
  | _ => false

/-- What a terminal receives: every piece. -/
def Piece.shown : Piece → String
  | .text s | .escape s | .ephemeral s => s

/-- **The text with its escapes removed**: the pieces a reader keeps. -/
def strip (ps : List Piece) : List Piece := ps.filter Piece.isText

/-- The terminal's text of pieces, as sent. -/
def shown (ps : List Piece) : String := String.join (ps.map Piece.shown)

/-- The text a reader keeps: the kept pieces, joined. -/
def kept (ps : List Piece) : String := shown (strip ps)

/-- The three styles the tty format uses. -/
inductive Style where
  | bold
  | dim
  | red
  deriving DecidableEq, Repr

/-- A style's ANSI escape (SGR). -/
def Style.code : Style → String
  | .bold => "\x1b[1m"
  | .dim => "\x1b[2m"
  | .red => "\x1b[31m"

/-- The escape that ends every style. -/
def reset : String := "\x1b[0m"

/-- Text pieces. -/
def texts (ss : List String) : List Piece := ss.map Piece.text

/-- Text in a style: with its escapes when `styled`, the text alone otherwise. -/
def styledText (styled : Bool) (style : Style) (s : String) : List Piece :=
  if styled then [.escape style.code, .text s, .escape reset] else [.text s]

/-- The carriage return that rewrites the line in progress, then the erase to the end of the line
(CSI `K`), in the tty format alone. No cursor moves beyond the carriage return. -/
def rewrite (styled : Bool) : List Piece :=
  if styled then [.escape "\r\x1b[K"] else []

/-- Text shown until the line is rewritten, in the tty format alone. -/
def ephemeral (styled : Bool) (s : String) : List Piece :=
  if styled then [.ephemeral s] else []

/-- The fold whose line is in progress: its words, and the measures it has gathered. -/
structure Open where
  what : String
  measures : List (String × Nat)
  deriving DecidableEq, Repr

/-- The state of the fold: the fold in progress, if any. -/
abbrev State := Option Open

/-- **The text of the fold, as functions**: what the fold writes at each place. The fold never
inspects a string, so a theorem over it holds for every text. -/
structure Text where
  /-- the title: the command line -/
  title : Report → String
  /-- a mark at the start of a fold's line: `  ■ ` -/
  mark : String → String
  /-- the line in progress: `  □ words ┄┄` -/
  waiting : String → String
  /-- a fold's words, padded to the measures' column when it has measures -/
  words : Open → String
  /-- the measures of a fold: `5 definitions · 9 rows` -/
  measures : List (String × Nat) → String
  /-- a measure outside a fold, as its own line -/
  measureLine : String → Nat → String
  /-- an artifact's `─▶ role/path`, padded -/
  artifactPath : Written → String
  /-- an artifact's byte count and the start of its digest -/
  artifactDetail : Written → String
  /-- a reading's lines, each indented and ended -/
  reading : String → List String
  /-- a refusal's words, indented -/
  refusal : String → String
  /-- a usage error's words -/
  usage : String → String → String
  /-- the artifacts counted: `11 artifacts` -/
  counted : Nat → String

/-- The measures after a fold's words, when any. -/
def measuresPart (t : Text) (styled : Bool) (ms : List (String × Nat)) : List Piece :=
  if ms.isEmpty then [] else texts ["  "] ++ styledText styled .dim (t.measures ms)

/-- A fold's line, under its mark: rewritten over the line in progress, the mark, its words bold,
its measures dim. -/
def foldLine (t : Text) (styled : Bool) (mark : String) (o : Open) : List Piece :=
  rewrite styled ++ texts [t.mark mark] ++ styledText styled .bold (t.words o) ++
    measuresPart t styled o.measures ++ texts ["\n"]

/-- The line of the fold in progress, closed as unfinished (`□`), when there is one. -/
def close (t : Text) (styled : Bool) : State → List Piece
  | none => []
  | some o => foldLine t styled "□" o

/-- An artifact's line: `─▶ role/path`, its byte count and the start of its digest, dim. -/
def artifactLine (t : Text) (styled : Bool) (w : Written) : List Piece :=
  texts [t.artifactPath w] ++ styledText styled .dim (t.artifactDetail w) ++ texts ["\n"]

/-- A refusal's words, red. -/
def refusalLine (t : Text) (styled : Bool) (why : String) : List Piece :=
  texts ["    "] ++ styledText styled .red (t.refusal why) ++ texts ["\n"]

/-- A usage error's words, red. -/
def usageLine (t : Text) (styled : Bool) (command why : String) : List Piece :=
  texts ["  "] ++ styledText styled .red (t.usage command why) ++ texts ["\n"]

/-- **One step of the fold**: the state after an event, and the pieces it writes. A measure joins
the fold in progress, or stands on its own line. A finish writes its fold's line (`■`). Any other
event first closes a fold in progress as unfinished (`□`); a start then shows the wait. -/
def step (t : Text) (styled : Bool) : State → Event → State × List Piece
  | s, .started what => (some ⟨what, []⟩, close t styled s ++ ephemeral styled (t.waiting what))
  | some o, .finished _ => (none, foldLine t styled "■" o)
  | none, .finished what => (none, foldLine t styled "■" ⟨what, []⟩)
  | some o, .measure word n => (some ⟨o.what, o.measures ++ [(word, n)]⟩, [])
  | none, .measure word n => (none, texts [t.measureLine word n])
  | s, .artifact w => (none, close t styled s ++ artifactLine t styled w)
  | s, .reading _ text _ => (none, close t styled s ++ texts (t.reading text))
  | s, .refusal _ why => (none, close t styled s ++ refusalLine t styled why)
  | s, .usage command why => (none, close t styled s ++ usageLine t styled command why)

/-- The events from a state: each step's pieces, then the fold in progress closed. -/
def run (t : Text) (styled : Bool) (s : State) : List Event → List Piece
  | [] => close t styled s
  | e :: es => (step t styled s e).2 ++ run t styled (step t styled s e).1 es

/-- The title: the command line, bold. -/
def title (t : Text) (styled : Bool) (r : Report) : List Piece :=
  styledText styled .bold (t.title r) ++ texts ["\n"]

/-- The last line: the artifacts counted, and the root they are under. -/
def summary (t : Text) (styled : Bool) (r : Report) : List Piece :=
  match r.artifacts.length, r.out with
  | 0, _ => []
  | n, some root =>
    texts ["  ■ "] ++ styledText styled .bold (t.counted n) ++ texts [" in "] ++
      styledText styled .dim root ++ texts ["\n"]
  | n, none => texts ["  ■ "] ++ styledText styled .bold (t.counted n) ++ texts ["\n"]

/-- **The one fold**, over a text: the title, the events, the summary. -/
def piecesWith (t : Text) (styled : Bool) (r : Report) : List Piece :=
  title t styled r ++ run t styled none r.events ++ summary t styled r

/-! ### The standard text -/

/-- A text padded with spaces to `width` columns. -/
def pad (s : String) (width : Nat) : String := s.pushn ' ' (width - s.length)

/-- A text padded with spaces on its left to `width` columns. -/
def padLeft (s : String) (width : Nat) : String := "".pushn ' ' (width - s.length) ++ s

/-- The digits of a count, from the least significant, in threes. -/
def threes : List Char → List (List Char)
  | a :: b :: c :: rest => [a, b, c] :: threes rest
  | [] => []
  | rest => [rest]

/-- A count with a thousands separator: `12,440`. -/
def grouped (n : Nat) : String :=
  ",".intercalate (((threes (toString n).toList.reverse).map fun ds => String.ofList ds.reverse).reverse)

/-- The lines of a text; a last line break ends the text and opens no line. -/
def lines (text : String) : List String :=
  let ls := text.splitOn "\n"
  if ls.getLast? == some "" then ls.dropLast else ls

/-- The column the measures of a fold's line start at. -/
def foldWidth : Nat := 28

/-- The column an artifact's byte count starts at. -/
def pathWidth : Nat := 44

/-- Measures joined: `5 definitions · 9 rows`. -/
def measuresText (ms : List (String × Nat)) : String :=
  " · ".intercalate (ms.map fun (word, n) => s!"{grouped n} {word}")

/-- The first four hexadecimal digits of a digest, then `…`. -/
def short (sha256 : String) : String := (sha256.take 4).toString ++ "…"

/-- **The standard text**: the title is the command line; a fold's words are padded to the
measures' column when it has measures; an artifact's path is padded to the count's column, the
count carries a thousands separator and the digest its first four digits; a reading's lines and a
refusal's stand four columns in, a usage error two. -/
def Text.standard : Text where
  title r := " ".intercalate ("effect4" :: r.arguments)
  mark m := s!"  {m} "
  waiting what := s!"  □ {what} ┄┄"
  words o := if o.measures.isEmpty then o.what else pad o.what foldWidth
  measures := measuresText
  measureLine word n := s!"  {grouped n} {word}\n"
  artifactPath w := "    ─▶ " ++ pad (w.role.word ++ "/" ++ w.path) pathWidth
  artifactDetail w := padLeft (grouped w.size ++ " B") 12 ++ "  " ++ short w.sha256
  reading text := (lines text).map fun l => "    " ++ l ++ "\n"
  refusal why := "\n    ".intercalate (lines why)
  usage command why := if command.isEmpty then why else s!"{command}: {why}"
  counted n := s!"{n} {if n == 1 then "artifact" else "artifacts"}"

/-- **The one fold** at the standard text. -/
def pieces (styled : Bool) (r : Report) : List Piece := piecesWith .standard styled r

/-- **The plain format**: the fold without styles, as text. -/
def plain (r : Report) : String := shown (pieces false r)

/-- **The tty format**: the fold with its styles and its line in progress, as text. -/
def tty (r : Report) : String := shown (pieces true r)

/-! ## Law (a): the tty fold with its escapes removed is the plain fold -/

theorem strip_append (a b : List Piece) : strip (a ++ b) = strip a ++ strip b :=
  List.filter_append ..

theorem strip_texts (ss : List String) : strip (texts ss) = texts ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [texts, List.map_cons] at ih ⊢
    exact congrArg (Piece.text s :: ·) ih

theorem strip_styledText (styled : Bool) (style : Style) (s : String) :
    strip (styledText styled style s) = [.text s] := by
  cases styled <;> rfl

theorem strip_rewrite (styled : Bool) : strip (rewrite styled) = [] := by
  cases styled <;> rfl

theorem strip_ephemeral (styled : Bool) (s : String) : strip (ephemeral styled s) = [] := by
  cases styled <;> rfl

theorem strip_measuresPart (t : Text) (styled : Bool) (ms : List (String × Nat)) :
    strip (measuresPart t styled ms) = measuresPart t false ms := by
  unfold measuresPart
  split
  · rfl
  · rw [strip_append, strip_texts, strip_styledText]
    rfl

theorem strip_foldLine (t : Text) (styled : Bool) (mark : String) (o : Open) :
    strip (foldLine t styled mark o) = foldLine t false mark o := by
  unfold foldLine
  rw [strip_append, strip_append, strip_append, strip_append, strip_rewrite,
    strip_texts, strip_styledText, strip_measuresPart, strip_texts]
  rfl

theorem strip_close (t : Text) (styled : Bool) (s : State) :
    strip (close t styled s) = close t false s := by
  cases s with
  | none => rfl
  | some o => exact strip_foldLine t styled "□" o

theorem strip_artifactLine (t : Text) (styled : Bool) (w : Written) :
    strip (artifactLine t styled w) = artifactLine t false w := by
  unfold artifactLine
  rw [strip_append, strip_append, strip_texts, strip_styledText, strip_texts]
  rfl

theorem strip_refusalLine (t : Text) (styled : Bool) (why : String) :
    strip (refusalLine t styled why) = refusalLine t false why := by
  unfold refusalLine
  rw [strip_append, strip_append, strip_texts, strip_styledText, strip_texts]
  rfl

theorem strip_usageLine (t : Text) (styled : Bool) (command why : String) :
    strip (usageLine t styled command why) = usageLine t false command why := by
  unfold usageLine
  rw [strip_append, strip_append, strip_texts, strip_styledText, strip_texts]
  rfl

/-- Step of `strip_pieces`: the state after a step does not depend on the style, and the pieces
stripped are the plain step's. -/
theorem strip_step (t : Text) (styled : Bool) (s : State) (e : Event) :
    (step t styled s e).1 = (step t false s e).1 ∧
      strip (step t styled s e).2 = (step t false s e).2 := by
  cases e with
  | started what =>
    refine ⟨rfl, ?_⟩
    simp only [step]
    rw [strip_append, strip_close, strip_ephemeral]
    rfl
  | finished what =>
    cases s with
    | none => exact ⟨rfl, strip_foldLine t styled "■" ⟨what, []⟩⟩
    | some o => exact ⟨rfl, strip_foldLine t styled "■" o⟩
  | measure word n =>
    cases s with
    | none => exact ⟨rfl, strip_texts _⟩
    | some o => exact ⟨rfl, rfl⟩
  | artifact w =>
    refine ⟨rfl, ?_⟩
    simp only [step]
    rw [strip_append, strip_close, strip_artifactLine]
  | reading what text json =>
    refine ⟨rfl, ?_⟩
    simp only [step]
    rw [strip_append, strip_close, strip_texts]
  | refusal where_ why =>
    refine ⟨rfl, ?_⟩
    simp only [step]
    rw [strip_append, strip_close, strip_refusalLine]
  | usage command why =>
    refine ⟨rfl, ?_⟩
    simp only [step]
    rw [strip_append, strip_close, strip_usageLine]

theorem strip_run (t : Text) (styled : Bool) (es : List Event) (s : State) :
    strip (run t styled s es) = run t false s es := by
  induction es generalizing s with
  | nil => exact strip_close t styled s
  | cons e es ih =>
    simp only [run]
    rw [strip_append, (strip_step t styled s e).2, (strip_step t styled s e).1, ih]

theorem strip_title (t : Text) (styled : Bool) (r : Report) :
    strip (title t styled r) = title t false r := by
  unfold title
  rw [strip_append, strip_styledText, strip_texts]
  rfl

theorem strip_summary (t : Text) (styled : Bool) (r : Report) :
    strip (summary t styled r) = summary t false r := by
  unfold summary
  split
  · rfl
  · rw [strip_append, strip_append, strip_append, strip_append, strip_texts, strip_styledText,
      strip_texts, strip_styledText, strip_texts]
    rfl
  · rw [strip_append, strip_append, strip_texts, strip_styledText, strip_texts]
    rfl

/-- **Law (a)**: the tty fold with its escapes and its lines in progress removed is the plain
fold, at every text. Placement: concept `initial-algebras-folds`, claim `cli-report-strip`
(proposed, the report note §10). Consumer: the live sink, which prints what the batch fold
prints. The text is a parameter: no string is inspected, and the theorem rests on
`[propext, Quot.sound]` alone; its image at `Text.standard` is the battery's finite evaluation
(`Test/Codegen/CompilerReport.lean`). -/
theorem strip_pieces (t : Text) (r : Report) :
    strip (piecesWith t true r) = piecesWith t false r := by
  unfold piecesWith
  rw [strip_append, strip_append, strip_title, strip_run, strip_summary]

/-! ## The document: the json and md formats -/

/-- A fold's line of the document's list: its mark, its words, its measures. -/
def foldItem (mark : String) (o : Open) : Line :=
  [.text s!"{mark} {o.what}"] ++
    (if o.measures.isEmpty then [] else [.text (" · " ++ measuresText o.measures)])

/-- **The events as the document's list**, folded as the text is (`step`): a fold finished is one
line with its measures, a fold refused is `□`, a measure outside a fold is its own line, and a
refusal its words. Artifacts stand in the table and readings in their parts, so they close a fold
and add no line. -/
def eventLines (s : State) : List Event → List Line
  | [] => (match s with | none => [] | some o => [foldItem "□" o])
  | .started what :: es => (match s with | none => [] | some o => [foldItem "□" o]) ++ eventLines (some ⟨what, []⟩) es
  | .finished what :: es => foldItem "■" ((s.getD ⟨what, []⟩)) :: eventLines none es
  | .measure word n :: es =>
    (match s with
      | some o => eventLines (some ⟨o.what, o.measures ++ [(word, n)]⟩) es
      | none => [.text s!"{n} {word}"] :: eventLines none es)
  | .artifact _ :: es | .reading .. :: es =>
    (match s with | none => [] | some o => [foldItem "□" o]) ++ eventLines none es
  | .refusal step why :: es =>
    (match s with | none => [] | some o => [foldItem "□" o]) ++ [.text s!"refused at {step}: {why}"] :: eventLines none es
  | .usage command why :: es =>
    (match s with | none => [] | some o => [foldItem "□" o]) ++ [.text (if command.isEmpty then why else s!"{command}: {why}")] :: eventLines none es

/-- An artifact as a row of the document's table. -/
def artifactRow (w : Written) : List Line :=
  [[.text w.role.word], [.text w.form.word], [.text w.kind.word], [.code w.path],
   [.text (toString w.size)], [.code w.sha256]]

/-- A reading as a part of the document: its text, and its JSON when it has one. -/
def readingPart (i : Nat) (what text : String) (json : Option String) : Block :=
  .part s!"reading-{i}" what ([.code "text" text] ++ match json with
    | some j => [.code "json" j]
    | none => [])

/-- **The report as a document**: its command line as the title; the command, its arguments, its
root and its exit code as fields; the events as a list (`eventLines`); the artifacts as a table;
each reading as a part. -/
def document (r : Report) : Document :=
  let readings := r.events.filterMap fun
    | .reading what text json => some (what, text, json)
    | _ => none
  { title := " ".intercalate ("effect4" :: r.arguments)
    body := [.fields [("command", [.code r.command]),
      ("arguments", [.code (" ".intercalate r.arguments)]),
      ("out", match r.out with | some root => [.code root] | none => [.text "no output root"]),
      ("exit", [.text (toString r.exit)])],
      .items (eventLines none r.events),
      .table ["role", "form", "kind", "path", "bytes", "sha256"] (r.artifacts.map artifactRow)] ++
      readings.zipIdx.map fun ((what, text, json), i) => readingPart i what text json }

/-- **The md format**: the document's Markdown. -/
def md (r : Report) : String := (document r).markdown

/-! ## The transport: the report as JSON, read back

`Report.json` is the report's own lossless JSON, the protocol another CLI folds: the format word,
the command, the arguments as a list, the output root as a string or `null`, and the events in
order, each tagged by its `event` word with every field, a reading's text and its JSON both.
`Report.ofJson` reads it back and refuses a field it does not know; `Report.ofJson_json` is the
retraction (concept 7, `initial-algebras-folds`, claim `cli-report-transport`). The document
(`Report.document`) stays the readable view. -/

/-- The version of the transport, on every report. -/
def format : String := "effect4-report/1"

/-- An object's fields, in the order of their names. -/
private def entries (what : String) : Json → Except String (List (String × Json))
  | .obj kvs => .ok kvs.toList
  | _ => .error s!"{what}: not an object"

/-- An object's fields, refused when it holds a field not in `names`. -/
private def fields (what : String) (names : List String) (j : Json) : Except String (List (String × Json)) := do
  let fs ← entries what j
  if let some (k, _) := fs.find? (fun (k, _) => !names.contains k) then throw s!"{what}: unknown field {k}"
  return fs

private def field (what key : String) (fs : List (String × Json)) : Except String Json :=
  match fs.lookup key with
  | some v => .ok v
  | none => .error s!"{what}: no field {key}"

private def str (what : String) : Json → Except String String
  | .str s => .ok s
  | _ => .error s!"{what}: not a string"

private def nat (what : String) : Json → Except String Nat
  | .num ⟨.ofNat n, 0⟩ => .ok n
  | _ => .error s!"{what}: not a natural number"

private def arr (what : String) : Json → Except String (List Json)
  | .arr xs => .ok xs.toList
  | _ => .error s!"{what}: not an array"

/-- An optional text: the text, or `null`. -/
def optJson : Option String → Json
  | none => .null
  | some s => .str s

private def readOpt (what : String) : Json → Except String (Option String)
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error s!"{what}: not a string or null"

def Role.all : List Role := [.program, .host, .run]

def readRole (j : Json) : Except String Role := do
  let w ← str "role" j
  match Role.all.find? (·.word == w) with
  | some r => return r
  | none => throw s!"role {w}: not a role"

/-- A form as JSON: its word, and a print's target. -/
def formJson : Form → Json
  | .object => Json.mkObj [("form", "object")]
  | .print target => Json.mkObj [("form", "print"), ("target", target)]
  | .record => Json.mkObj [("form", "record")]
  | .index => Json.mkObj [("form", "index")]

def readForm (j : Json) : Except String Form := do
  let fs ← fields "form" ["form", "target"] j
  match ← str "form" (← field "form" "form" fs) with
  | "object" => return .object
  | "print" => return .print (← str "target" (← field "form" "target" fs))
  | "record" => return .record
  | "index" => return .index
  | w => throw s!"form {w}: not a form"

def Kind.all : List Kind :=
  [.object, .certificate, .program, .module, .surface, .recipe, .closure, .manifest, .prelude,
   .document, .figure, .table]

def readKind (j : Json) : Except String Kind := do
  let w ← str "kind" j
  match Kind.all.find? (·.word == w) with
  | some k => return k
  | none => throw s!"kind {w}: not a kind"

/-- A written file as JSON: every field. -/
def writtenJson (w : Written) : Json :=
  Json.mkObj [("role", w.role.word), ("form", formJson w.form), ("kind", w.kind.word),
    ("path", w.path), ("size", w.size), ("sha256", w.sha256)]

def readWritten (j : Json) : Except String Written := do
  let fs ← fields "file" ["role", "form", "kind", "path", "size", "sha256"] j
  return { role := ← readRole (← field "file" "role" fs), form := ← readForm (← field "file" "form" fs)
           kind := ← readKind (← field "file" "kind" fs), path := ← str "path" (← field "file" "path" fs)
           size := ← nat "size" (← field "file" "size" fs), sha256 := ← str "sha256" (← field "file" "sha256" fs) }

/-- An event as JSON, tagged by its `event` word, every field present. -/
def eventJson : Event → Json
  | .started what => Json.mkObj [("event", "started"), ("what", what)]
  | .finished what => Json.mkObj [("event", "finished"), ("what", what)]
  | .measure word n => Json.mkObj [("event", "measure"), ("word", word), ("count", n)]
  | .artifact w => Json.mkObj [("event", "artifact"), ("file", writtenJson w)]
  | .reading what text json =>
    Json.mkObj [("event", "reading"), ("what", what), ("text", text), ("json", optJson json)]
  | .refusal step why => Json.mkObj [("event", "refusal"), ("step", step), ("why", why)]
  | .usage command why => Json.mkObj [("event", "usage"), ("command", command), ("why", why)]

def readEvent (j : Json) : Except String Event := do
  let tag ← str "event" (← field "event" "event" (← entries "event" j))
  let fs ← fields s!"event {tag}" (match tag with
    | "started" | "finished" => ["event", "what"]
    | "measure" => ["event", "word", "count"]
    | "artifact" => ["event", "file"]
    | "reading" => ["event", "what", "text", "json"]
    | "refusal" => ["event", "step", "why"]
    | "usage" => ["event", "command", "why"]
    | _ => ["event"]) j
  let get (k : String) := field s!"event {tag}" k fs
  match tag with
  | "started" => return .started (← str "what" (← get "what"))
  | "finished" => return .finished (← str "what" (← get "what"))
  | "measure" => return .measure (← str "word" (← get "word")) (← nat "count" (← get "count"))
  | "artifact" => return .artifact (← readWritten (← get "file"))
  | "reading" =>
    return .reading (← str "what" (← get "what")) (← str "text" (← get "text")) (← readOpt "json" (← get "json"))
  | "refusal" => return .refusal (← str "step" (← get "step")) (← str "why" (← get "why"))
  | "usage" => return .usage (← str "command" (← get "command")) (← str "why" (← get "why"))
  | t => throw s!"event: no event {t}"

/-- **The report as JSON**, lossless: the format, the command, the arguments, the root or `null`,
and the events in order. -/
def Report.json (r : Report) : Json :=
  Json.mkObj [("format", format), ("command", r.command),
    ("arguments", .arr (r.arguments.map Json.str).toArray), ("out", optJson r.out),
    ("events", .arr (r.events.map eventJson).toArray)]

/-- **The report read from its JSON**, in the format `format` alone. -/
def Report.ofJson (j : Json) : Except String Report := do
  let fs ← fields "report" ["format", "command", "arguments", "out", "events"] j
  let f ← str "format" (← field "report" "format" fs)
  unless f == format do throw s!"report: format {f}, not {format}"
  let command ← str "command" (← field "report" "command" fs)
  let arguments ← (← arr "arguments" (← field "report" "arguments" fs)).mapM (str "argument")
  let out ← readOpt "out" (← field "report" "out" fs)
  let events ← (← arr "events" (← field "report" "events" fs)).mapM readEvent
  return { command, arguments, out, events }

/-- Step of `cli-report-transport`: a list lifts its element retraction. -/
private theorem mapM_retraction {α β : Type} (write : α → β) (read : β → Except String α)
    (law : ∀ x, read (write x) = .ok x) (xs : List α) :
    (xs.map write).mapM read = .ok xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons, law, ih]
    rfl

private theorem readRole_word (r : Role) : readRole (.str r.word) = .ok r := by
  cases r <;> rfl

private theorem readForm_formJson (f : Form) : readForm (formJson f) = .ok f := by
  cases f <;> rfl

private theorem readKind_word (k : Kind) : readKind (.str k.word) = .ok k := by
  cases k <;> rfl

/-- Step of `cli-report-transport`, consumed by its artifact case. -/
private theorem readWritten_writtenJson (w : Written) : readWritten (writtenJson w) = .ok w := by
  cases w with
  | mk role form kind path size sha256 =>
    change (do
      let role ← readRole (.str role.word)
      let form ← readForm (formJson form)
      let kind ← readKind (.str kind.word)
      pure (Written.mk role form kind path size sha256)) = .ok (Written.mk role form kind path size sha256)
    rw [readRole_word, readForm_formJson, readKind_word]
    rfl

/-- Step of `cli-report-transport`, consumed by `Report.ofJson_json`. -/
private theorem readEvent_eventJson (e : Event) : readEvent (eventJson e) = .ok e := by
  cases e with
  | artifact w =>
    change (do let f ← readWritten (writtenJson w); pure (Event.artifact f)) = .ok (Event.artifact w)
    rw [readWritten_writtenJson]
    rfl
  | reading what text json => cases json <;> rfl
  | _ => rfl

private theorem readOpt_optJson (what : String) (o : Option String) : readOpt what (optJson o) = .ok o := by
  cases o <;> rfl

/-- **The transport's retraction**: the report read from its own JSON is the report. Placement:
concept `initial-algebras-folds`, claim `cli-report-transport` (proposed, the report note §10).
Consumer: the OCaml shell's reader, and the battery's finite check through `Lean.Json.parse`. It
states equality of report values; it makes no claim about another language's JSON parser. -/
theorem Report.ofJson_json (r : Report) : Report.ofJson (Report.json r) = .ok r := by
  cases r with
  | mk command arguments out events =>
    change (do
      let arguments ← (arguments.map Json.str).mapM (str "argument")
      let out ← readOpt "out" (optJson out)
      let events ← (events.map eventJson).mapM readEvent
      pure (Report.mk command arguments out events)) = .ok (Report.mk command arguments out events)
    rw [mapM_retraction Json.str (str "argument") (fun _ => rfl), readOpt_optJson,
      mapM_retraction eventJson readEvent readEvent_eventJson]
    rfl

/-- **The json format**: the report's own JSON (`Report.json`), laid out, then a line break. -/
def jsonText (r : Report) : String := (Report.json r).pretty ++ "\n"

/-! ## The formats, named -/

/-- The four formats `--format` names. -/
inductive Format where
  | tty
  | plain
  | json
  | md
  deriving DecidableEq, Repr

def Format.all : List Format := [.tty, .plain, .json, .md]

def Format.name : Format → String
  | .tty => "tty"
  | .plain => "plain"
  | .json => "json"
  | .md => "md"

def Format.parse (word : String) : Option Format := Format.all.find? (·.name == word)

/-- A report in a format, as text. -/
def Format.text : Format → Report → String
  | .tty => Report.tty
  | .plain => Report.plain
  | .json => Report.jsonText
  | .md => Report.md

/-! ## The log: the one IO -/

/-- **A command's log**: its events so far, the output root it set, and the live sink that shows
each event as it arrives. -/
structure Log where
  events : IO.Ref (Array Event)
  root : IO.Ref (Option String)
  live : Event → IO Unit

/-- Write one event. -/
def Log.event (l : Log) (e : Event) : IO Unit := do
  l.events.modify (·.push e)
  l.live e

/-- Set the output root the artifacts' paths are under. -/
def Log.setOut (l : Log) (root : String) : IO Unit := l.root.set (some root)

/-- Whether an event from `from` on is a refusal or a usage error. -/
def Log.refusedSince (l : Log) (from_ : Nat) : IO Bool := do
  return ((← l.events.get).toList.drop from_).any fun
    | .refusal .. | .usage .. => true
    | _ => false

/-- **A fold**: `started what`, the body, then `finished what` unless the body refused. -/
def Log.folding {α : Type} (l : Log) (what : String) (body : IO α) : IO α := do
  let from_ := (← l.events.get).size
  l.event (.started what)
  let a ← body
  unless ← l.refusedSince from_ do l.event (.finished what)
  return a

/-- **One file written under the root**: its folder made, its bytes written, then the artifact
recorded; an error is a refusal at `step`, and no artifact is recorded. Whether it was written. -/
def Log.write (l : Log) (step : String) (root : System.FilePath) (w : Written) (bytes : ByteArray) :
    IO Bool := do
  try
    let file := root / w.path
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeBinFile file bytes
    l.event (.artifact w)
    return true
  catch e =>
    l.event (.refusal step s!"{w.path}: {e}")
    return false

/-- The report of a log. -/
def Log.report (l : Log) (command : String) (arguments : List String) : IO Report := do
  return { command, arguments, out := ← l.root.get, events := (← l.events.get).toList }

/-- The live sink of a text format: the step function run on each event, its pieces sent; and
the state it leaves, which the close reads. -/
def liveSink (styled : Bool) (out : IO.FS.Stream) : IO ((Event → IO Unit) × IO.Ref State) := do
  let state ← IO.mkRef (none : State)
  return (fun e => do
    let (next, ps) := step .standard styled (← state.get) e
    state.set next
    out.putStr (shown ps)
    out.flush, state)

/-- **A command run and shown** (decisions row 444 (7)): the `tty` and `plain` formats are for
a person and go to the error stream, the title and the events as they arrive, then the close and
the summary; the `json` and `md` formats are the requested result and go to the standard output,
a failed report included; under `quiet` the refusals' words alone, on the error stream. The exit
code is the report's. -/
def print (format : Format) (quiet : Bool) (command : String) (arguments : List String)
    (body : Log → IO Unit) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  let styled := format == .tty
  let (live, state) ← match quiet, format with
    | false, .tty | false, .plain => liveSink styled err
    | _, _ => do pure (fun _ => pure (), ← IO.mkRef none)
  let log : Log := { events := ← IO.mkRef #[], root := ← IO.mkRef none, live }
  unless quiet do
    match format with
    | .tty | .plain => err.putStr (shown (title .standard styled { command, arguments, events := [] }))
    | _ => pure ()
  try body log catch e => log.event (.refusal command (toString e))
  let r ← log.report command arguments
  if quiet then
    for why in r.refusals do err.putStrLn why
  else
    match format with
    | .tty | .plain => err.putStr (shown (close .standard styled (← state.get) ++ summary .standard styled r))
    | .json | .md => out.putStr (format.text r)
  out.flush
  err.flush
  return r.exit

end Report
end Compiler
