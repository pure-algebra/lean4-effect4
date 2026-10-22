import Compiler.Main
import Test.Codegen.CompilerEmit

/-!
# The command-line report, read: the one fold, its formats and its laws

Readers, controls and finite evaluations over `Compiler.Report` (`tools/Compiler/Report.lean`;
the report note, `docs/research/2026-10-21-cli-report/README.md`). A battery reads no file and
runs no command: the reports here are built from the pure emission of the wire corpus's first
program (`Test.Codegen.CompilerEmit`) as `emit` records it (`reportOf`), or written by hand. A
battery `def` over rendered text reaches `Classical.choice`, so every digest, every emission and
the terminal's reader stand inside a `#guard`.

- **Law (a), its string image**: `Report.strip_pieces` is proved over the pieces at every text;
  here a reader of a terminal's text (every control sequence dropped, a line before a carriage
  return overwritten) takes the tty format of a real report to its plain format, a finite
  evaluation at the standard text.
- **Law (b)**: the report's own JSON read back, `Report.ofJson_json` applied at the real report,
  the finite check through `Lean.Json.parse` of the `json` format's text, and the controls: an
  unknown field, a wrong format word and a foreign event word are refused. The document view keeps
  both fields of a reading and reads back too (`Document.ofJson_json`).
- **Law (c), where it stands**: two emissions into two folders differ at exactly the three
  artifacts whose bytes record the command, the module, the surface and the manifest (the layout
  note §4.3), and agree everywhere else; one command twice gives equal events. The control shows
  where the law stops until the layout note's repair lands.
- **The look**: the plain text of a small report, byte for byte; the thousands separator; the
  exit code; the lines of a reading; the vocabulary's words; the document's event lines.
- **The flags**: `takeFlags` reads `--format`, `--format=F`, `--quiet`, `--help`, `--version`
  and the alias `--json` from anywhere, stops at `--`, refuses a format it does not know, and keeps
  the flags read before the one that reads wrong.
- **The publication of an inspection** (`inspectPlan`, `publicationOf`, `Publication.apply`): a
  session that does not exist refuses the plan before any file, so a folder as data stays as it
  was; a good plan writes its files and removes the programs' stale files of the form, and twice
  gives the same folder. A fold whose program is refused stands hollow (`eventLines`).

Every check is a `#guard`, so the rendered bytes stay inside them.
-/

namespace Test.Codegen.CompilerReport

open Compiler Compiler.Report Test.Codegen.CompilerEmit

/-- **A report of `emit` over the files of a pure emission**, as `emitCommand` records it: the
folds and measures, then each file as an artifact. The files' `Written` values are made inside
each `#guard`, since a digest is rendered text. -/
def reportOf (command : List String) (files : List Written) (out : String) : Report :=
  { command := "emit", arguments := command, out := some out
    events := [.started "folding the program p42", .measure "definitions" 0, .measure "rows" 0,
      .finished "folding the program p42", .started "printing for ts",
      .measure "files" files.length, .finished "printing for ts"] ++
      files.map Event.artifact }

/-- The spec of `p42`'s emission recorded under `emit --out DIR`. -/
def specOut (dir : String) : Spec := { specOf first.1 with command := ["emit", "--out", dir] }

/-! ## Law (a): the tty text read by a terminal is the plain text -/

-- finite evaluation: the string image of `strip_pieces` on the real report of an emission, and
-- on a report with a refused fold, a usage error and a reading. The tty text carries the escapes.
-- The terminal's reading (`stripAnsi`): each control sequence (`ESC [`, its parameters, its final
-- byte) dropped, and at a carriage return the line so far overwritten, as the erase that follows
-- it leaves nothing of it.
#guard match emitProgram (specOut "o") first.2 with
  | .ok e =>
    let stripAnsi : String → String := fun s => Id.run do
      let mut out := ""
      let mut line := ""
      let mut escape : Nat := 0
      for c in s.toList do
        if escape == 1 then escape := if c == '[' then 2 else 0
        else if escape == 2 then
          if c.toNat ≥ 0x40 && c.toNat ≤ 0x7e then escape := 0
        else if c == '\x1b' then escape := 1
        else if c == '\r' then line := ""
        else if c == '\n' then out := out ++ line ++ "\n"; line := ""
        else line := line.push c
      return out ++ line
    let r := reportOf ["emit", "--out", "o"] ((e.files Kind.selectable).map (Written.ofEmitted "ts")) "o"
    let refused : Report :=
      { command := "check", arguments := ["check"]
        events := [.started "folding the program x", .measure "rows" 2,
          .refusal "check" "refused: the entry add", .reading "certificate" "a\nb" none,
          .usage "check" "--bogus is no option"] }
    stripAnsi (tty r) == plain r && stripAnsi (tty refused) == plain refused &&
      (tty r).startsWith "\x1b[1meffect4 emit" && !((plain r).any (· == '\x1b')) &&
      kept (pieces true r) == plain r
  | .error _ => false

-- reader: the law at the standard text, as the live sink relies on it.
example (r : Report) : strip (pieces true r) = pieces false r := strip_pieces .standard r

/-! ## Law (b): the report reads back -/

-- reader: `Report.ofJson_json` at the real report; finite evaluations: the `json` format's text
-- parses and reads back to the report, and the document view checks and reads back.
#guard match emitProgram (specOut "o") first.2 with
  | .ok e =>
    let r := reportOf ["emit", "--out", "o"]
      ((e.files Kind.selectable).map (Written.ofEmitted "ts")) "o"
    let r := { r with events := r.events ++ [.reading "manifest" "{}" (some "{}"),
      .refusal "emit" "why", .usage "emit" "bogus"] }
    Report.ofJson (Report.json r) == .ok r &&
      ((Lean.Json.parse (jsonText r)).bind Report.ofJson) == .ok r &&
      (Tools.Document.Json.Document.reads (Tools.Document.Json.Document.json (document r))).toOption.isSome &&
      (document r).check.toOption.isSome
  | .error _ => false

example (r : Report) : Report.ofJson (Report.json r) = .ok r := Report.ofJson_json r

example (r : Report) :
    Tools.Document.Json.Document.ofJson (Tools.Document.Json.Document.json (document r)) =
      .ok (document r) :=
  Tools.Document.Json.Document.ofJson_json (document r)

-- controls: a report with an unknown field, with another format word, and with an event of a
-- word the transport lacks, are refused; the root `null` reads as none, and the string "none" as
-- a root named so.
#guard (Report.ofJson (Lean.Json.mkObj [("format", "effect4-report/1"), ("command", "check"),
    ("arguments", .arr #[]), ("out", .null), ("events", .arr #[]), ("extra", "x")])).toOption.isNone &&
  (Report.ofJson (Lean.Json.mkObj [("format", "effect4-report/2"), ("command", "check"),
    ("arguments", .arr #[]), ("out", .null), ("events", .arr #[])])).toOption.isNone &&
  (Report.ofJson (Lean.Json.mkObj [("format", "effect4-report/1"), ("command", "check"),
    ("arguments", .arr #[]), ("out", .null),
    ("events", .arr #[Lean.Json.mkObj [("event", "exploded")]])])).toOption.isNone &&
  (Report.ofJson (Lean.Json.mkObj [("format", "effect4-report/1"), ("command", "check"),
    ("arguments", .arr #["check", "--out", "a b"]), ("out", "none"), ("events", .arr #[])])) ==
    .ok { command := "check", arguments := ["check", "--out", "a b"], out := some "none", events := [] }

/-! ## Law (c): where determinism stands -/

-- control: two emissions into two folders give reports whose events differ at exactly the three
-- artifacts whose bytes record the command (the layout note §4.3: the module, the surface and
-- the manifest), and agree everywhere else. `p42` declares no data service, so it has no surface,
-- and the module and the manifest alone differ. One command twice gives equal events.
#guard match emitProgram (specOut "a") first.2, emitProgram (specOut "b") first.2 with
  | .ok ea, .ok eb =>
    let fa := (ea.files Kind.selectable).map (Written.ofEmitted "ts")
    let fb := (eb.files Kind.selectable).map (Written.ofEmitted "ts")
    let ra := (reportOf ["emit", "--out", "a"] fa "a").events
    let rb := (reportOf ["emit", "--out", "b"] fb "b").events
    let differing := (ra.zip rb).filterMap fun (x, y) =>
      if x == y then none else match x with
        | .artifact w => some w.kind
        | _ => some .object
    ra.length == rb.length && differing == [.module, .manifest] &&
      ra == (reportOf ["emit", "--out", "a"] fa "a").events
  | _, _ => false

-- reader: an artifact's digest and count are the bytes', and the prelude's files are equal
-- between the two folders, as every file that records no command is.
#guard match emitProgram (specOut "a") first.2, emitProgram (specOut "b") first.2 with
  | .ok ea, .ok eb =>
    let wa := (ea.files Kind.selectable).map (Written.ofEmitted "ts")
    let wb := (eb.files Kind.selectable).map (Written.ofEmitted "ts")
    wa.length == wb.length &&
      (wa.zip wb).all (fun (x, y) => x.kind == .module || x.kind == .manifest || x == y) &&
      (wa.all fun w => w.sha256.length == 64) &&
      (match (ea.files Kind.selectable).find? (·.kind == .canonical) with
        | some a => (wa.find? (·.path == a.path)).map (·.size) == some a.bytes.size
        | none => false)
  | _, _ => false

/-! ## The vocabulary -/

-- reader: the emission's kinds in the layout note's words: the canonical bytes are the object,
-- their tagged print the program, the manifest the index, and every other file a print.
#guard Kind.ofEmitted .canonical "p.eff" == .object && Kind.ofEmitted .canonical "p.eff.json" == .program &&
  Kind.ofEmitted .manifest "manifest.json" == .manifest && Kind.ofEmitted .prelude "prelude/x.ts" == .prelude &&
  Form.ofEmitted .canonical "p.eff" "ts" == .object && Form.ofEmitted .canonical "p.eff.json" "ts" == .print "ts" &&
  Form.ofEmitted .manifest "manifest.json" "ts" == .index && Form.ofEmitted .module "p.gen.ts" "ts" == .print "ts" &&
  (Form.print "ts").word == "print ts" && Role.program.word == "program" && Kind.figure.word == "figure"

/-! ## The look -/

-- finite evaluation: the plain text of a small report, byte for byte: the title, a fold with its
-- measures at the column, an artifact under it, and the summary naming the root.
#guard plain
    { command := "emit", arguments := ["emit", "--group", "todo"], out := some "o"
      events := [.started "folding the program todo", .measure "definitions" 5, .measure "rows" 9,
        .finished "folding the program todo", .started "printing for ts", .finished "printing for ts",
        .artifact ⟨.program, .print "ts", .module, "todo.gen.ts", 12440, "8c02ab00"⟩] } ==
  "effect4 emit --group todo\n" ++
  "  ■ folding the program todo      5 definitions · 9 rows\n" ++
  "  ■ printing for ts\n" ++
  "    ─▶ program/todo.gen.ts                             12,440 B  8c02…\n" ++
  "  ■ 1 artifact in o\n"

-- finite evaluation: a fold refused is `□` with the refusal's words under it; a usage error
-- stands two columns in; a reading's lines four; a measure outside a fold is its own line.
#guard plain
    { command := "check", arguments := ["check"]
      events := [.started "folding the program x", .refusal "check" "refused: the entry add",
        .usage "check" "--bogus is no option", .reading "certificate" "a\nb\n" none,
        .measure "rows" 2] } ==
  "effect4 check\n  □ folding the program x\n    refused: the entry add\n" ++
  "  check: --bogus is no option\n    a\n    b\n  2 rows\n"

-- reader: the thousands separator, the lines of a text, and the exit code of the events.
#guard grouped 0 == "0" && grouped 999 == "999" && grouped 1000 == "1,000" && grouped 12440 == "12,440" &&
  grouped 1234567 == "1,234,567" &&
  lines "a\nb\n" == ["a", "b"] && lines "a\nb" == ["a", "b"] && lines "" == [] &&
  Report.exit { command := "", arguments := [], events := [] } == 0 &&
  Report.exit { command := "", arguments := [], events := [.refusal "check" "x"] } == 1 &&
  Report.exit { command := "", arguments := [], events := [.refusal "check" "x", .usage "check" "y"] } == 2

-- reader: the document's event lines fold as the text does: one line a finished fold with its
-- measures, `□` for a refused one, and a refusal's words.
#guard eventLines none [.started "a", .measure "rows" 2, .finished "a", .started "b",
    .refusal "check" "why", .artifact ⟨.program, .object, .object, "p.obj", 1, "00"⟩] ==
  [[.text "■ a", .text " · 2 rows"], [.text "□ b"], [.text "refused at check: why"]]

/-! ## The flags -/

-- reader: the report's flags are read from anywhere, `--json` is the alias of `--format json`,
-- `--format=F` is `--format F`, `--` ends the flags, and the line without them is what the
-- command reads. red: a format the table lacks, and `--format` with no word, are refused, and the
-- flags read before the bad one hold.
#guard (takeFlags ["emit", "--group", "todo", "--format", "md", "--quiet"] {}) ==
    ({ format := some .md, quiet := true }, .ok ["emit", "--group", "todo"]) &&
  (takeFlags ["--json", "check"] {}) == ({ format := some .json }, .ok ["check"]) &&
  (takeFlags ["--format=json", "check", "--help"] {}) == ({ format := some .json, help := true }, .ok ["check"]) &&
  (takeFlags ["--version"] {}) == ({ version := true }, .ok []) &&
  (takeFlags ["check", "--", "--format", "md"] {}) == ({}, .ok ["check", "--format", "md"]) &&
  (takeFlags ["check"] {}) == ({}, .ok ["check"]) &&
  (match takeFlags ["--quiet", "check", "--format", "xml"] {} with
    | (f, .error _) => f == { quiet := true }
    | _ => false) &&
  (match takeFlags ["--format", "md", "check", "--format"] {} with
    | (f, .error _) => f == { format := some .md }
    | _ => false) &&
  Format.all.all (fun f => Format.parse f.name == some f) &&
  commandOf ["--group", "todo", "emit"] == "emit" && commandOf ["check", "--group", "todo"] == "check"

/-! ## The publication of an inspection -/

-- control: a session that does not exist refuses the plan, before any file; the good plan gives
-- the to-do's documents, one file in Markdown.
#guard match check Test.Dogfood.Scenario.Todo.application with
  | .ok b =>
    (inspectPlan [("todo", b)] (some "Nope") .md "relations").toOption.isNone &&
      ((inspectPlan [("todo", b)] (some "TodoApp") .md "relations").toOption.map (·.map (·.1))) ==
        some ["todo.gen.md"]
  | .error _ => false

-- finite evaluation: a publication of TSV files into a folder as data removes the program's
-- stale files of the form, keeps every other file, writes its own; applied twice it gives the
-- same folder; and a Markdown publication removes nothing.
#guard
  let folder := [("todo.old.gen.tsv", "stale"), ("todo.gen.md", "md"), ("other.x.gen.tsv", "other"),
    ("todo.calls-nodes.gen.tsv", "before")]
  let outputs := [("todo.calls-nodes.gen.tsv", "after"), ("todo.calls-edges.gen.tsv", "edges")]
  let p := publicationOf .tsv ["todo"] (folder.map (·.1)) outputs
  let once := p.apply folder
  p.removals == ["todo.old.gen.tsv"] &&
    once == [("todo.gen.md", "md"), ("other.x.gen.tsv", "other"), ("todo.calls-nodes.gen.tsv", "after"),
      ("todo.calls-edges.gen.tsv", "edges")] &&
    (publicationOf .tsv ["todo"] (once.map (·.1)) outputs).apply once == once &&
    (publicationOf .md ["todo"] (folder.map (·.1)) [("todo.gen.md", "new")]).removals == []

-- reader: a fold whose program is refused is hollow, and the readings after it follow it.
#guard eventLines none [.started "folding the group corpus", .measure "programs" 2,
    .refusal "check" "the entry add is refused", .reading "certificate" "line" none] ==
  [[.text "□ folding the group corpus", .text " · 2 programs"], [.text "refused at check: the entry add is refused"]]

end Test.Codegen.CompilerReport
