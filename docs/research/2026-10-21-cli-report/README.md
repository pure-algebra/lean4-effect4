# 2026-10-21 The command-line report: a command's run is a value, and the terminal shows one fold of it

Status: a design note written before the code, finished after it as the receipt (§9). It rules nothing; it proposes decisions rows in §10.
The evidence words are those of `docs/core/controlled-english.md` §3.8.
Base `ff59aa6f7`, branch `cli-report`.

## 1. The one thing to know

Every command of `Compiler.Main` now returns a `Report` (`tools/Compiler/Report.lean`) and prints nothing itself.
A report is the command's name, its arguments as given, and its events in order. An event is a fold started or finished, a measure, an artifact written, a reading given, or a refusal.
The terminal output is one fold of that value (`Report.pieces`), in four formats: `tty`, `plain`, `json` and `md`.
The `json` format is the report folded to a `Tools.Document` and written by `Document.json`. So `Document.ofJson` reads it back, and the OCaml shell folds the same value later.
What changed for a caller: the output is a report in every format, and `--json` is now an alias of `--format json`. A refusal stands inside the report on the standard output.

## 2. Today

Each command prints ad hoc strings, JSON under `--json`, and nothing shared says what a run produced (`out/today.txt` beside this note).

| Command | Today's output | Where |
| --- | --- | --- |
| `check` | the certificate as a header block, or one line of JSON | `IO.println` |
| `check --out FILE.obj` | the object file, unannounced | `IO.FS.writeBinFile` |
| `emit` | one line: `emit: 11 files to DIR: module 1, prelude 5, …` | `IO.println` |
| `describe` | the manifest, one line or indented | `IO.println` |
| `inspect --what types` | the reading's text, or one line of JSON | `IO.println` |
| `inspect --form md` | the document on the standard output, or files under `--out DIR`, unannounced | `putStr`, `writeFile` |
| `run` | one line a request | `IO.println` |
| a refusal | words on the error stream, or JSON on the standard output | `IO.eprintln` |
| a usage error | words on the error stream | `IO.eprintln` |

## 3. The model, derived

### 3.1 The vocabulary

The words come from the artifact layout note (`docs/research/2026-10-21-artifact-layout/README.md`, §3 and §4.1), whose Lean is not yet in the tree. `Compiler.Report` defines them and names the note.

- A **role** is who a file is for: `program`, `host`, `run`.
- A **form** is what a file is: a canonical `object`, a `print` for one target, a `record` of one run, the `index`.
- A **kind** is the layout note's list where a command writes one today: `object`, `certificate`, `program`, `module`, `surface`, `recipe`, `closure`, `manifest`. Four kinds that the note does not name are added. They are `prelude` (the copied prelude files), `document` (an inspection document in Markdown or JSON), `figure` (an SVG figure) and `table` (a TSV relation). §8 asks the owner about them.

The compiler's own `Compiler.Kind` (`tools/Compiler/Emit.lean`) is the manifest's. `Kind.ofEmitted` maps it to the report's kind by the file's path, so the manifest's bytes do not change.

### 3.2 The events

```lean
inductive Event where
  | started (what : String)                -- a fold began
  | finished (what : String)               -- the same fold ended
  | measure (word : String) (count : Nat)  -- definitions, rows, nodes, calls, requests, files
  | artifact (file : Written)              -- role, form, kind, path, byte count, SHA-256
  | reading (what : String) (text : String) (json : Option String)
  | refusal (step : String) (why : String) -- the located refusal the command already has, in its words
  | usage (command : String) (why : String)
```

A `Written` file's byte count and SHA-256 are computed from the bytes the command wrote (`Written.of`), never from the clock or from the output path. Its path is relative to the output root.
A reading is what a command answers in words: the certificate, a manifest, a `--what` reading, one line of `run`. Its JSON is the same reading through its carrier's public JSON where it has one.
A measure between a fold's start and its finish belongs to that fold's line. An artifact stands after the fold that produced it.
A fold that starts and does not finish was refused: the refusal event follows it.

```lean
structure Report where
  command : String
  arguments : List String   -- as given
  out : Option String       -- the output root the paths are under; a place, not part of the events
  events : List Event
```

The exit code is a fold of the events (`Report.exit`): 2 at a usage event, 1 at a refusal, 0 otherwise.

### 3.3 The log, the one IO

A command writes its events to a `Log`, an `IO.Ref` of events with a live sink. The live sink is the format's step function run as each event arrives. So the terminal shows a fold in progress, and the final text is the batch fold's by construction: both call `Report.step`.
`Log.folding what k` writes `started what`, runs `k`, and writes `finished what` unless `k` refused.

## 4. The formats as folds

### 4.1 One fold, pieces

`Report.piecesWith (t : Text) (styled : Bool) (r : Report) : List Piece` is the one fold. Its text is a parameter: a `Text` is the functions that give each string the fold writes, and the fold inspects none of them. `Text.standard` is the one text the formats use, and `pieces` is the fold at it. A piece is one of three things. `text s` is kept by every terminal. `escape s` is an ANSI sequence, shown by a terminal and kept by none. `ephemeral s` is text that a carriage return overwrites.
With `styled := false` the fold writes `text` pieces alone: the `plain` format. With `styled := true` it adds the escapes and the in-progress line: the `tty` format.
The marks are the design language's, from `Tools.View.Page` and `Tools.View.Glyph`. `□` is a fold started and not finished. `┄┄` is the wait, in the tty format while a fold is in progress. `■` is a fold finished or an artifact kept. `─▶` stands before an artifact, under the fold that wrote it.

### 4.2 The look, derived

```text
effect4 emit --group todo
  ■ folding the program        todo · 5 definitions · 4 rows · 71 nodes · 14 calls
  ■ printing for ts            11 files
    ─▶ program/todo.gen.ts                      5,055 B  3c8f…
    ─▶ program/prelude/prelude.ts              16,064 B  a1d2…
    ─▶ program/todo.eff                         5,713 B  ebf3…
    ─▶ program/manifest.json                   92,895 B  0b1e…
  ■ 11 artifacts in .lake/effect4/todo/ts
```

- The title line is the command with its arguments as given.
- A fold's line: two spaces, `■`, its words, padded to a column when it has measures, then its measures joined by ` · `.
- An artifact's line: four spaces, `─▶`, `role/path` padded, then the byte count with a thousands separator and ` B`. Two spaces, then the first four hexadecimal digits of the SHA-256 and `…`.
- A reading's text stands under its fold, each line four spaces in.
- A refusal: the fold it stopped is `□`, and the refusal's words stand under it, four spaces in. A usage error is its words, two spaces in.
- The last line counts the artifacts and names the output root, when any was written.

The `tty` format: the title and each `■` line's words bold, the measures and the artifact details dim, a refusal red. The current fold's line is written as `□ words ┄┄`. As it finishes, a carriage return and an erase to the end of the line (CSI `K`) rewrite it in place. No cursor movement beyond the carriage return.

### 4.3 The document

`Report.document r : Tools.Document.Document` is the report as a document. Its title is the command line. A `fields` block gives the command, its arguments, the output root and the exit code. An `items` block lists the events in order, one line each with its mark. A `table` lists the artifacts (role, form, kind, path, bytes, sha256). Each reading is a `code` block, its JSON when it has one, its text otherwise.
`json` is `Document.json` of it, one document, pretty-printed; `md` is `Document.markdown` of it.

## 5. The laws, placed under concept 7, `initial-algebras-folds`

| Law | Statement | Evidence |
| --- | --- | --- |
| (a) strip | `Report.strip (piecesWith t true r) = piecesWith t false r` at every text `t`: the tty fold with its escapes and its lines in progress removed is the plain fold. The text is a parameter the proof never inspects, so the theorem rests on `[propext, Quot.sound]` alone (§9, the audit). | `Report.strip_pieces` (`tools/Compiler/Report.lean`), proved; its string image at the standard text, a terminal's reading of `tty r` equal to `plain r`, a finite evaluation in `Test/Codegen/CompilerReport.lean` |
| (b) read-back | `Document.ofJson (Document.json (Report.document r)) = .ok (Report.document r)` | `Document.ofJson_json` applied at the report's document, and `Document.reads` on the JSON of a real report: a reader and a finite evaluation in `Test/Codegen/CompilerReport.lean` |
| (c) determinism | the events of a command are a function of the object, the target and the pins, never of the clock or the output root | by construction where the bytes written are; see §5.1 |

Consumer of (a): the live sink prints what the batch fold prints. Consumer of (b): the OCaml shell's reader. Consumer of (c): a gate that compares two runs.

### 5.1 Where (c) stands today

The report's digests are of the bytes written, and nothing else. The layout note (§4.3, tested) found that `emit` writes the `--out` path into the module header, the surface header and the manifest. So two emissions into two folders give reports that differ at exactly those three artifacts, and agree everywhere else. The battery's control pins that boundary.
The repair is the layout note's slice 1 (its proposed row 442: no artifact carries the command, and the manifest records the command without `--out`). This landing does not touch the emission's bytes.
`inspect --out` writes documents that carry no path, so its two runs give equal events: a finite probe, `landing/determinism.log`.

## 6. The flags, one table

| Flag | Where | Meaning |
| --- | --- | --- |
| `--format tty\|plain\|json\|md` | every command | the format; the default is `tty` when the standard output is a terminal and `NO_COLOR` is unset, else `plain` |
| `--quiet` | every command | the refusal's words alone, on the error stream; nothing on success |
| `--json` | every command | an alias of `--format json` for one release; the docstring of `Compiler.Main` says so |
| `--group NAME` | `lake exe effect4` | the source, as before |

The three are read before the command, in any position (`takeFormat`), so no command's own reader sees them. `check --json`, `inspect --json` and `run --json` therefore mean the report in JSON. `run`'s line modes are `--text` and `--typed`; the value-tree line of every request is the reading's JSON, in the json and md formats. `inspect --what relations --form json` keeps its meaning: the document form.

## 7. What changes, by file

| File | Change |
| --- | --- |
| `tools/Compiler/Report.lean` (new) | the vocabulary, the events, the report, the one fold and its formats, the document, the laws, the log |
| `tools/Compiler/Main.lean` | every command returns `IO Unit` over a log; the printing is `Compiler.print`, one place; the flag table |
| `tools/Compiler/Run.lean` | `RunOptions.read` no longer reads `--json` |
| `Test/Codegen/CompilerEmit.lean` | the option readers' lines follow the flags |
| `Test/Codegen/CompilerReport.lean` (new) | the laws (b) and (c) as battery lines, the finite image of (a), the readers of the fold |
| `Test/All.lean` | the new battery, after `Test.Codegen.CompilerEmit` |

The committed `generated/graphs` regenerates byte for byte: `inspect --form md|json|tsv --out DIR` writes the same files, and the report describes them.

## 8. Questions for the owner

1. The layout note names no kind for an inspection document, a figure or a table, nor for the copied prelude. The report uses `document`, `figure`, `table` and `prelude`. Keep them, or fold the documents into the note's `program` kind?
2. A mark for "every promise kept" at the last line would be a check mark. The vocabulary has none, so the last line uses `■`.
3. A reading's JSON stands in the document as a `code` block whose body is JSON text. A JSON-tree block in `Tools.Document` would carry it as data; that is a change to the document's contract and its read-back theorem.

## 9. The receipt

### The one thing the coordinator must know

Every command prints through one place, `Report.print` (`tools/Compiler/Report.lean`), in the format the flags choose. The old outputs moved, and three of them changed meaning:

- `--json` now prints the report as a document. The certificate, the manifest, a `--what` reading and a `run` line stand inside it as `code` blocks of JSON text (§8, question 3).
- A refusal stands in the report on the standard output, with exit code `1`; `--quiet` prints its words alone on the error stream.
- `run --json` no longer chooses the value-tree line: that line is every request's reading in the `json` and `md` formats.

`generated/graphs` regenerated byte for byte, twice. The emission's bytes did not change.

### The look, as landed

`emit`, plain, verbatim (`out/emit.plain.txt`; the json is `out/emit.json`, the tty `out/emit.tty.txt` as `cat -v` shows it):

```text
effect4 emit --group todo --out .lake/effect4/todo/ts --format plain
  ■ folding the program todo      5 definitions · 4 rows · 35 nodes · 4 calls
  ■ printing for ts               11 files
    ─▶ program/todo.gen.ts                              4,929 B  1281…
    ─▶ program/prelude/control.ts                       3,227 B  471f…
    ─▶ program/prelude/prelude-atoms.gen.ts            15,457 B  9814…
    ─▶ program/prelude/prelude.ts                      29,661 B  7001…
    ─▶ program/prelude/records.ts                       2,644 B  6844…
    ─▶ program/prelude/tuples.ts                          344 B  35c5…
    ─▶ program/todo.surface.gen.ts                      2,863 B  3a69…
    ─▶ program/todo.eff                                 5,713 B  ebf3…
    ─▶ program/todo.eff.json                            5,213 B  1cc3…
    ─▶ program/certificate.json                         4,589 B  f524…
    ─▶ program/manifest.json                           92,854 B  6cff…
  ■ 11 artifacts in .lake/effect4/todo/ts
exit 0
```

`check`, plain, verbatim (`out/check.plain.txt`; `out/check.json`, `out/check.tty.txt`):

```text
✔ [1813/1814] Built Compiler.Report:c.o (982ms)
✔ [1814/1814] Built effect4:exe (2.5s)
effect4 check --group todo --format plain
  ■ folding the program todo      5 definitions · 4 rows · 35 nodes · 4 calls
    todo: checked; the service TodoApp
    
    program   sha256 ebf361e27f030719b4b55c2078fae00c89187057882b66967aa451ceb749108d
    type      void
    rows      TodoRepo.insert(string) { readonly done: boolean; readonly id: number; readonly title: string } ! readonly ["SqlError", string] needs k30_6
              TodoRepo.all(void) ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }> ! readonly ["SqlError", string] needs k30_6
              TodoRepo.setDone(readonly [number, boolean]) Option.Option<{ readonly done: boolean; readonly id: number; readonly title: string }> ! readonly ["SqlError", string] needs k30_6
              TodoRepo.delete(number) boolean ! readonly ["SqlError", string] needs k30_6
    services  TodoRepo k30_6 (Test.Dogfood.Scenario.Todo.todoRepoKey)
    defines   TodoAppContext(void) Context.Context<"k30_6"> needs k30_6
              TodoApp_add(readonly [Context.Context<"k30_6">, string]) { readonly done: boolean; readonly id: number; readonly title: string } ! readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"]
              TodoApp_list(Context.Context<"k30_6">) ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }> ! readonly ["SqlError", string]
              TodoApp_complete(readonly [Context.Context<"k30_6">, number]) { readonly done: boolean; readonly id: number; readonly title: string } ! readonly ["SqlError", string] | { readonly _tag: "NotFound"; readonly id: number }
              TodoApp_remove(readonly [Context.Context<"k30_6">, number]) void ! readonly ["SqlError", string] | { readonly _tag: "NotFound"; readonly id: number }
exit 0
```

`inspect`, plain, verbatim (`out/inspect.plain.txt`; `out/inspect.json`, `out/inspect.tty.txt`):

```text
effect4 inspect --group todo --session TodoApp --what relations --form tsv --out .lake/effect4/todo/graphs --format plain
  ■ folding the program todo      5 definitions · 4 rows · 35 nodes · 4 calls
  ■ reading the relations as tsv  11 files
    ─▶ program/todo.relation-nodes.gen.tsv              3,932 B  342d…
    ─▶ program/todo.relation-defs.gen.tsv                 252 B  fcf7…
    ─▶ program/todo.relation-rows.gen.tsv               1,298 B  8b93…
    ─▶ program/todo.relation-calls.gen.tsv              1,099 B  34f8…
    ─▶ program/todo.mapping.gen.tsv                       610 B  9d56…
    ─▶ program/todo.boundary-nodes.gen.tsv                262 B  ea32…
    ─▶ program/todo.boundary-edges.gen.tsv                199 B  bcba…
    ─▶ program/todo.boundary-boxes-nodes.gen.tsv          149 B  ebd7…
    ─▶ program/todo.boundary-boxes-edges.gen.tsv           83 B  309f…
    ─▶ program/todo.calls-nodes.gen.tsv                   562 B  c430…
    ─▶ program/todo.calls-edges.gen.tsv                   172 B  3e4d…
  ■ 11 artifacts in .lake/effect4/todo/graphs
exit 0
```

A usage error and `--quiet` (`out/usage.plain.txt`, `out/quiet.txt`):

```text
effect4 check --group todo --bogus --format plain
  check: --bogus is no option; usage: check [--out FILE.obj]
exit 2
run: the group corpus is programs with no host to answer a row; run takes an application and its host
exit 2
```

The tty format differs from the plain one in its escapes alone. The title and each fold's words are bold (`ESC[1m` … `ESC[0m`), the measures and the artifact details dim (`ESC[2m`), a refusal red (`ESC[31m`). While a fold runs its line reads `□ words ┄┄`; at its finish a carriage return and `ESC[K` erase it, and the `■` line takes its place. `out/*.tty.txt` show each escape as `cat -v` prints it.

The head of `emit`'s json (`out/emit.json`):

```json
{"title": "effect4 emit --group todo --out .lake/effect4/todo/ts --format json",
 "producer": [],
 "format": "effect4-document/1",
 "body":
 [{"rows":
   [{"line": [{"code": "emit"}], "label": "command"},
    {"line":
     [{"code": "emit --group todo --out .lake/effect4/todo/ts --format json"}],
     "label": "arguments"},
    {"line": [{"text": ".lake/effect4/todo/ts"}], "label": "out"},
    {"line": [{"text": "0"}], "label": "exit"}],
   "kind": "fields"},
  {"lines":
   [[{"text": "■ folding the program todo"},
     {"text": " · 5 definitions · 4 rows · 35 nodes · 4 calls"}],
    [{"text": "■ printing for ts"}, {"text": " · 11 files"}]],
   "kind": "items"},
  {"rows":
   [[[{"text": "program"}],
     [{"text": "print ts"}],
     [{"text": "module"}],
     [{"code": "todo.gen.ts"}],
```

### Base, head and files

Base `ff59aa6f7b7584ab31772b02e2d4920938b3a7c3`, branch `cli-report`. The head is the one commit that holds this note and the code.

| File | Change |
| --- | --- |
| `tools/Compiler/Report.lean` (new) | the vocabulary, the events, the report, the fold over a text and its four formats, the document, law (a), the log and the printing |
| `tools/Compiler/Main.lean` | every command writes a log and returns nothing; `dispatch`, `reported`, the flag table, `measured` |
| `tools/Compiler/Run.lean` | `Served`, `serve` and `served` give the outcome; `runFrom` derives the lines; `--json` left `RunOptions.read` |
| `Test/Codegen/CompilerEmit.lean` | the readers of `inspect`'s options follow the flags; two comments |
| `Test/Codegen/CompilerReport.lean` (new) | laws (a), (b) and (c) as battery lines; the look; the vocabulary; the flags |
| `Test/All.lean` | the new battery after `Test.Codegen.CompilerEmit` |
| this folder | the note, `out/` (the captures), `landing/` (the audit, the batteries, the determinism probe, the generate logs) |

### Commands and results

Run from the worktree on 2026-10-21, one `lake` at a time with `LEAN_NUM_THREADS=3`.

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build Compiler.Report Compiler.Run Compiler.Main Compiler.Exe Test.Codegen.CompilerEmit Test.Codegen.CompilerReport` | Pass; 1,357 jobs | the build log |
| `lake env lean -DwarningAsError=true docs/research/2026-10-21-cli-report/landing/audit.lean` | Exit 1: #axiom_audit: 68 of 1185 declarations reach axioms outside [propext, Quot.sound]: | `landing/audit.log` |
| `make batteries-touched BASE=ff59aa6f7` | Pass; 2 batteries, 1,355 jobs | `landing/batteries.log` |
| `python3 scripts/generate.py --only graphs`, twice | Pass; `git status generated/` clean after each | `landing/generate-1.log`, `landing/generate-2.log` |
| `python3 scripts/check-language.py --strict docs/research/2026-10-21-cli-report/README.md` | Pass | the note |
| the three formats of `check`, `emit` and `inspect` on the to-do | captured | `out/` |
| `inspect --form json --out A` and `--out B`, the reports compared | equal | `landing/determinism.log` |
| `emit --out A` and `--out B`, the reports compared | three digests differ: `todo.gen.ts`, `todo.surface.gen.ts`, `manifest.json` | `landing/determinism.log` |

### The axiom output

The audit names 68 declarations that reach `Classical.choice` (Compiler (Main, Run): 40, Compiler.Report: 28). None is a theorem. The generic fold and its laws (`strip_pieces`, `strip_step`, `strip_run`, `strip_title`, `strip_summary`, their steps) rest on `[propext, Quot.sound]`, and so does every declaration of the battery. The named declarations are of four kinds. The standard text: `pad`, `grouped`, `lines`, `measuresText`, `short`, `Text.standard`. What folds at it: `pieces`, `plain`, `tty`, `document`, `json`, `md`. The kind and form of an emitted file (`String.endsWith`). The option readers of `Main` and the log's IO. They reach it through Lean's string functions, as the rendering paths do (the view-graph note §9). No exception was added.

### Open obligations

- Law (c) holds for `emit` once the layout note's slice 1 lands; until then the control in the battery pins the three artifacts.
- The `json` format carries a reading as JSON text in a `code` block (§8, question 3).
- The report's claim `cli-report-strip` is proposed below and not yet in the registry; the theorem names it in its docstring.
- A live `tty` is checked by reading, not by a test. The sink and the batch fold call the same `step` and `close`, and the terminal shows one line in progress.

## 10. Proposed decisions rows

1. **The report.** A command of `Compiler.Main` returns a `Report` and prints nothing; the printing is `Report.print`, one place, in one of four formats. The events' vocabulary is `Compiler.Report.Event`.
2. **The flags.** `--format tty|plain|json|md`, `--quiet`, and `--json` as an alias of `--format json` for one release; read before the command, from anywhere on the line.
3. **The law.** `cli-report-strip` under concept 7, `initial-algebras-folds`: `strip (piecesWith t true r) = piecesWith t false r` at every text, proved (`Report.strip_pieces`). The read-back of the report's document is an instance of `document-json-fold-retraction`.
4. **The kinds.** The report's `Kind` takes the layout note's words and adds `prelude`, `document`, `figure` and `table` until the note names them (§8, question 1).
