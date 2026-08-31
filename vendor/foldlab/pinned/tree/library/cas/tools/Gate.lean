import Cas.Values.Json

/-!
# The gate driver — `tools/Gate.lean`

One skeleton for every emitter in `tools/`. A tool is its registry plus
the `List Fixture` that registry renders; everything else — writing,
byte-checking, the verdict vocabulary, the argument grammar, the usage
line — lives here and is therefore the same for all of them.

A `Fixture` is one committed artifact: where it lives, the bytes the
model says it holds, and a short label naming what it carries. The
fixture list is produced in `IO` because some tools must execute the
model to know their content (the environment walk in `Surface`, the
payload-bound witness in `EmitPrograms`, the computed verdicts in
`Verdicts`); the action is forced only AFTER arguments parse, so a
typo'd flag never pays for the document.

## The verdict vocabulary

Four words, the same in prose and in `--json`:

- `wrote` — the artifact was regenerated from the model;
- `ok` — the committed bytes equal the regeneration;
- `missing` — no committed artifact at that path;
- `differs` — the committed bytes are not the regeneration, reported
  with the first differing byte offset and the line it falls on.

`--check` visits EVERY fixture and reports each one before failing
once at the end: a red gate with three stale fixtures is one run, not
three. `--json` prints one object per fixture on its own line
(`{tool, fixture, verdict, bytes, ms, renderMs, hint}`) instead of the
prose line; the failure is still an error, so stdout stays parseable.

## Self-timing

`ms` and `renderMs` make the gate loop's cost auditable from the gate
itself rather than from a stopwatch outside it. They are wall times on
the host that ran them, so they are TELEMETRY, never fixture bytes: no
gate compares them, and nothing built from them may be committed. The
prose line stays untimed — a human reading a red gate wants the
diagnosis, not the milliseconds.

## The emitted header

`Emitted` is the one header every generated artifact carries, so a
document found on disk says who wrote it without anyone having to
grep for the emitter. Four fields and not a fifth: the artifact's own
`schemaVersion`, the `emitter` that writes it, the `module` that
declares it, and the `toolchain` that compiled that module.

There is deliberately no timestamp and no input fingerprint. Both
would make the header a function of WHEN the run happened rather than
of what the model says, and the byte gate is the estate's freshness
relation — a header that changed on every run would defeat it. Every
field here is a constant of the build, so a regeneration that changes
nothing changes no byte.

`Lean.versionString` is the toolchain source. It comes from the
compiler that built the emitter, which is exactly the thing a
signature-printing artifact can drift on; a toolchain bump therefore
reprints every artifact, and the gate says so once, loudly, instead of
letting a re-pretty-printed signature look like a content change.
-/

namespace Gate

/-! ## The emitted header -/

/-- The provenance every generated artifact carries at its head.
`toolchain` is not a field: it is `Lean.versionString`, read from the
running emitter, so no caller can spell it wrong. -/
structure Emitted where
  /-- The ARTIFACT's version, not the header's. It starts at the
  version the artifact already declared where it declared one
  (`manifestVersion`, `revision`, `mapVersion`) and at 1 where it
  declared none; the old field stays for one release so a consumer
  reading the old name is not broken by the new one. -/
  schemaVersion : Nat
  /-- The executable that writes it — the `lake exe` name, bare. -/
  emitter : String
  /-- The tool source that declares it, repository-relative. -/
  module : String

/-- The header's own value: the four fields, in the order
`Meta.emittedShape` declares them. Both canonical printers sort keys at
render time, so this order is the reading order and never the bytes. -/
def Emitted.value (e : Emitted) : Cas.Json.Value :=
  .obj [("schemaVersion", .nat e.schemaVersion),
        ("emitter", .str e.emitter),
        ("module", .str e.module),
        ("toolchain", .str Lean.versionString)]

/-- The header as ONE field, ready to prepend to a document's top-level
object. -/
def Emitted.field (e : Emitted) : String × Cas.Json.Value :=
  ("emitted", e.value)

/-- A JSON document's top-level object, headed. This is the insertion
every JSON emitter makes: `.obj [...]` becomes `e.obj [...]`, and the
header cannot then be forgotten halfway down a field list. -/
def Emitted.obj (e : Emitted) (fields : List (String × Cas.Json.Value)) :
    Cas.Json.Value :=
  .obj (e.field :: fields)

/-- The header prepended to a value BUILT ELSEWHERE — the three
documents whose top-level object is a projection of a library value
(`Cas.Grammar.manifestV0.toValue`, `Cas.Backend.Mcp.manifest`) rather
than a field list the tool spells. A non-object passes through
unchanged, which is unreachable at every call site and pinned there by
a `#guard`: a document that is not an object has nowhere to put a
header, and inventing one would be the emitter deciding the shape. -/
def Emitted.onto (e : Emitted) : Cas.Json.Value → Cas.Json.Value
  | .obj fields => e.obj fields
  | v => v

/-- The header as the closing lines of a generated TypeScript module's
doc block — the same four facts, in the register that file is read in.
A comment rather than a value: a generated module's consumers import
its declarations, and a provenance constant nobody reads would be one
more export to keep. -/
def Emitted.headerLines (e : Emitted) : List String :=
  ["",
   s!"emitted — schemaVersion {e.schemaVersion}, emitter `{e.emitter}`,",
   s!"module `{e.module}`, toolchain Lean {Lean.versionString}."]

/-- One committed artifact: its path, the bytes the model renders, and
a short label naming what it carries (shown in the prose line and in
the `hint` field of a `wrote`/`ok` JSON row). -/
structure Fixture where
  path : System.FilePath
  content : String
  label : String

/-- The verdict vocabulary — the only four words a gate answers. -/
inductive Verdict where
  | wrote
  | ok
  | missing
  | differs
deriving DecidableEq

def Verdict.word : Verdict → String
  | .wrote => "wrote"
  | .ok => "ok"
  | .missing => "missing"
  | .differs => "differs"

/-- A verdict that fails the gate. -/
def Verdict.stale : Verdict → Bool
  | .missing | .differs => true
  | _ => false

/-- One fixture's outcome. `hint` is the label for `wrote`/`ok` and the
diagnosis (with the fix) for `missing`/`differs`.

`ms` and `renderMs` are the self-timing, filled in by `run` and zero
until it does: `ms` is THIS fixture's own emit-or-check wall time, and
`renderMs` is the run's SHARED cost of producing the fixture list —
the model execution (`importModules` for the environment walks, the
computed verdicts, the payload-bound witness) that happens once before
any fixture is written. The split matters because for the two
`supportInterpreter` tools `renderMs` is nearly the whole run and `ms`
is a rounding error, and a single number would hide which. `renderMs`
repeats on every row of one run; it is a property of the run, printed
per row so a row stands alone. -/
structure Report where
  fixture : Fixture
  verdict : Verdict
  hint : String
  ms : Nat := 0
  renderMs : Nat := 0

/-! ## Where the bytes part company -/

/-- The first byte offset at which two renderings differ, or `none`
when they are equal. A pure prefix answers the length of the shorter
side — the offset at which the shorter one ran out. -/
private def firstDiffOffset (expected actual : ByteArray) : Option Nat := Id.run do
  let n := min expected.size actual.size
  for i in [0:n] do
    if expected[i]! != actual[i]! then return some i
  if expected.size == actual.size then return none else return some n

/-- The 1-based line and byte column an offset falls on. Columns count
bytes, not codepoints — the gate is a byte gate. -/
private def lineColOf (bytes : ByteArray) (offset : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  for i in [0:offset] do
    if bytes[i]! == 10 then
      line := line + 1
      col := 1
    else
      col := col + 1
  return (line, col)

/-- The character index a 1-based byte column falls on within a line. -/
private def charColOf (line : String) (byteCol : Nat) : Nat := Id.run do
  let mut b := 1
  let mut i := 0
  for c in line.toList do
    if b >= byteCol then return i
    b := b + c.utf8Size
    i := i + 1
  return i

/-- Sixty characters of a line, centred on where it went wrong: the
one-line JSON artifacts are whole documents on line 1, so the line
alone would say nothing. -/
private def window (line : String) (charCol : Nat) : String :=
  let chars := line.toList
  let start := if charCol > 20 then charCol - 20 else 0
  (if start > 0 then "…" else "") ++
    String.ofList ((chars.drop start).take 60) ++
    (if chars.length > start + 60 then "…" else "")

/-- The `differs` diagnosis: the first differing byte offset, the line
and byte column it falls on, and the regeneration's text there. -/
private def diffHint (expected actual : String) : String :=
  match firstDiffOffset expected.toUTF8 actual.toUTF8 with
  | none => "byte-equal (the comparison disagrees — report this)"
  | some offset =>
    let (line, col) := lineColOf expected.toUTF8 offset
    let text := ((expected.splitOn "\n")[line - 1]?).getD ""
    s!"first differs at byte {offset} (line {line}, column {col}), \
regeneration has «{window text (charColOf text col)}»"

/-! ## Emitting and checking one fixture -/

def emitOne (f : Fixture) : IO Report := do
  if let some parent := f.path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile f.path f.content
  return { fixture := f, verdict := .wrote, hint := f.label }

def checkOne (regen : String) (f : Fixture) : IO Report := do
  let actual? ← try pure (some (← IO.FS.readFile f.path)) catch _ => pure none
  match actual? with
  | none =>
    return { fixture := f, verdict := .missing,
             hint := s!"no such file; run `{regen}`" }
  | some actual =>
    if actual == f.content then
      return { fixture := f, verdict := .ok, hint := f.label }
    else
      return { fixture := f, verdict := .differs,
               hint := s!"{diffHint f.content actual}; run `{regen}`" }

/-! ## Reporting -/

private def hex4 (n : Nat) : String :=
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  String.ofList [digit (n / 4096 % 16), digit (n / 256 % 16),
                 digit (n / 16 % 16), digit (n % 16)]

/-- JSON string escaping for the `--json` report line. Kept local: the
report is telemetry about a run, not a document of the value plane, and
building it through `Cas.Json` would put the gate's own diagnostics
under the canonical printer's key sort. -/
private def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => if c.val < 0x20 then "\\u" ++ hex4 c.val.toNat else c.toString

def proseLine (r : Report) : String :=
  s!"{r.verdict.word} {r.fixture.path} \
({r.fixture.content.toUTF8.size} bytes) — {r.hint}"

def jsonLine (tool : String) (r : Report) : String :=
  "{\"tool\":\"" ++ escape tool ++
  "\",\"fixture\":\"" ++ escape r.fixture.path.toString ++
  "\",\"verdict\":\"" ++ r.verdict.word ++
  "\",\"bytes\":" ++ toString r.fixture.content.toUTF8.size ++
  ",\"ms\":" ++ toString r.ms ++
  ",\"renderMs\":" ++ toString r.renderMs ++
  ",\"hint\":\"" ++ escape r.hint ++ "\"}"

/-! ## The argument grammar -/

structure Options where
  check : Bool := false
  json : Bool := false
  help : Bool := false
  /-- `--all`, accepted only by the selecting entry point: the explicit
  spelling of the default, so a caller can say "every fixture" out
  loud instead of by omission. -/
  all : Bool := false
  /-- The positional word. A PATH for `mainAt` (a re-pointed artifact)
  and a fixture NAME for `mainSelect`; the grammar is the same either
  way, and only the entry point knows which it means. -/
  target : Option System.FilePath := none

private def parseArgs (allowTarget allowAll : Bool) :
    List String → Options → Option Options
  | [], o => some o
  | "--check" :: rest, o => if o.check then none else parseArgs allowTarget allowAll rest { o with check := true }
  | "--json" :: rest, o => if o.json then none else parseArgs allowTarget allowAll rest { o with json := true }
  | "--all" :: rest, o =>
    if !allowAll || o.all || o.target.isSome then none
    else parseArgs allowTarget allowAll rest { o with all := true }
  | "--help" :: _, o => some { o with help := true }
  | "-h" :: _, o => some { o with help := true }
  | a :: rest, o =>
    if allowTarget && !a.startsWith "-" && o.target.isNone && !o.all then
      parseArgs allowTarget allowAll rest { o with target := some ⟨a⟩ }
    else none

/-- The usage line, in the order the parser actually accepts: flags
first, the optional target last. -/
def usage (regen : String) (allowTarget : Bool) : String :=
  s!"usage: {regen} [--check] [--json]" ++
    (if allowTarget then " [<path>]" else "")

/-- The selecting tool's usage line: `--all` and a bare fixture name are
alternatives, and omitting both means `--all`. -/
def usageSelect (regen : String) : String :=
  s!"usage: {regen} [--check] [--json] [--all | <fixture>]"

/-- The tool's own name — the last word of the regeneration command,
which is what `{tool}` reports in `--json`. -/
def toolOf (regen : String) : String :=
  (regen.splitOn " ").getLastD regen

/-! ## The driver -/

def run (regen : String) (fixtures : IO (List Fixture)) (o : Options) :
    IO Unit := do
  let renderStart ← IO.monoMsNow
  let fs ← fixtures
  let renderMs := (← IO.monoMsNow) - renderStart
  let reports ← fs.mapM fun f => do
    let start ← IO.monoMsNow
    let r ← if o.check then checkOne regen f else emitOne f
    return { r with ms := (← IO.monoMsNow) - start, renderMs }
  for r in reports do
    IO.println (if o.json then jsonLine (toolOf regen) r else proseLine r)
  let stale := reports.filter (·.verdict.stale)
  unless stale.isEmpty do
    throw (IO.userError
      s!"{stale.length} of {reports.length} fixtures stale — run `{regen}`")

/-- The entry point of a tool whose target is fixed. `regen` is the
regeneration command every message names as the fix. -/
def main (regen : String) (fixtures : IO (List Fixture))
    (args : List String) : IO Unit := do
  match parseArgs false false args {} with
  | none => throw (IO.userError (usage regen false))
  | some o =>
    if o.help then IO.println (usage regen false) else run regen fixtures o

/-- The entry point of a tool that bakes in a canonical target but lets
a caller re-point it: the positional path is an OVERRIDE, never a
requirement. -/
def mainAt (regen : String)
    (fixtures : Option System.FilePath → IO (List Fixture))
    (args : List String) : IO Unit := do
  match parseArgs true false args {} with
  | none => throw (IO.userError (usage regen true))
  | some o =>
    if o.help then IO.println (usage regen true)
    else run regen (fixtures o.target) o

/-- The entry point of a tool whose fixtures are a REGISTRY: the
positional word selects one registered name, and `--all` (or nothing at
all) is every one of them. `none` is handed to the fixture action for
the whole registry, `some name` for the single selection; the action
owns the refusal when the name is no row. -/
def mainSelect (regen : String)
    (fixtures : Option String → IO (List Fixture))
    (args : List String) : IO Unit := do
  match parseArgs true true args {} with
  | none => throw (IO.userError (usageSelect regen))
  | some o =>
    if o.help then IO.println (usageSelect regen)
    else run regen (fixtures (o.target.map (·.toString))) o

end Gate
