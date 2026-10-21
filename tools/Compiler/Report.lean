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
the text is a parameter the proof never inspects). `document r` folds the report to a `Tools.Document`: `json` is `Document.json` of
it, which `Document.ofJson` reads back (`Document.ofJson_json`), and `md` its Markdown fold.

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
    | .usage command why => some s!"{command}: {why}"
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

/-- A reading as a part of the document: its JSON when it has one, its text otherwise. -/
def readingPart (i : Nat) (what text : String) (json : Option String) : Block :=
  .part s!"reading-{i}" what [match json with
    | some j => .code "json" j
    | none => .code "text" text]

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
      ("out", [.text (r.out.getD "none")]),
      ("exit", [.text (toString r.exit)])],
      .items (eventLines none r.events),
      .table ["role", "form", "kind", "path", "bytes", "sha256"] (r.artifacts.map artifactRow)] ++
      readings.zipIdx.map fun ((what, text, json), i) => readingPart i what text json }

/-- **The json format**: the document's JSON, laid out, then a line break. -/
def json (r : Report) : String := (Tools.Document.Json.Document.json (document r)).pretty ++ "\n"

/-- **The md format**: the document's Markdown. -/
def md (r : Report) : String := (document r).markdown

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
  | .json => Report.json
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

/-- **A command run and shown**: the title, the events as they arrive, then the close and the
summary, for a text format; the document at the end, for `json` and `md`; the refusals' words
alone on the error stream under `quiet`. The exit code is the report's. -/
def print (format : Format) (quiet : Bool) (command : String) (arguments : List String)
    (body : Log → IO Unit) : IO UInt32 := do
  let out ← IO.getStdout
  let styled := format == .tty
  let (live, state) ← match quiet, format with
    | false, .tty | false, .plain => liveSink styled out
    | _, _ => do pure (fun _ => pure (), ← IO.mkRef none)
  let log : Log := { events := ← IO.mkRef #[], root := ← IO.mkRef none, live }
  unless quiet do
    match format with
    | .tty | .plain => out.putStr (shown (title .standard styled { command, arguments, events := [] }))
    | _ => pure ()
  try body log catch e => log.event (.refusal command (toString e))
  let r ← log.report command arguments
  if quiet then
    for why in r.refusals do (← IO.getStderr).putStrLn why
  else
    match format with
    | .tty | .plain => out.putStr (shown (close .standard styled (← state.get) ++ summary .standard styled r))
    | .json | .md => out.putStr (format.text r)
  out.flush
  return r.exit

end Report
end Compiler
