import Lean
import Cas.Values.Json
import Cas.Grammar.Manifest
import Gate
import Walk

/-!
# The obligation harvester — `tools/Obl.lean`

The scan the obligation ledger runs, promoted out of `Obligations` so a
second projection can read it. `Obligations` was the only reader until
the debt lane needed the same rows; the promotion is a MOVE, not a
redesign — the keyword set, the boundary rules, the excerpt shape and
the document are the ones that were there, and the tool root keeps its
ledger, its counters and its bytes.

Two exe roots cannot import one another (each must declare `main`), so
a projection shared between them lives in a module of its own — the
same reason `Walk` exists.

## What it reads

Declaration docstrings (`findDocString?`) and module docstring blocks
(`getModuleDoc?`), over `Walk`'s shared environment walk. Rows sort by
module then declaration — `Walk.collect`'s own total order — so a diff
is a change of content, never of traversal.

## Every row says where it is

A row carries `file` and, where the environment has one, `line`. The
file is `Walk.sourceOf` of the module — Lake's own name-to-path rule,
not a search — and the line is the declaration's range
(`Lean.findDeclarationRanges?`) or, for a module block, the block's own
range. Nothing here opens a source file: both anchors are read off what
the oleans already carry.

The point is operational. An obligation is a request to do work, and a
row a reader cannot open is a request nobody acts on. `line` is
optional because the environment carries no range for a few generated
declarations; a row with none says so rather than inventing a zero.

## The keyword set is closed

`owed`, `obligation`, `parked`, `un-parked`, `discharged`,
`pin pending`, `sub-obligation`. An ad-hoc synonym is silently
invisible, which is the price of a closed set and the reason it is
written here rather than inferred. Matching is case-insensitive and
requires a non-letter before the match, so `borrowed` is not `owed`;
`un-parked` and `sub-obligation` are matched as themselves and not
double-counted as `parked` and `obligation`.

## The structured form

A marker may NAME the debt it marks:

```
owed(judge-stable): the definition is not written yet
discharges(judge-stable): STABLE is defined here
```

The id is short-kebab and follows the keyword with no space. That is
the whole convention: a marker written this way carries its id into the
row, and two docstrings in different modules can then talk about one
obligation. A bare `owed` still marks a debt and carries no id — the
estate has forty of those and none of them moves.

`discharges` is admitted ONLY in the structured form. It is ordinary
prose in a dozen docstrings (*"the grammar discharges that premise"*),
so counting it bare would invent a discharge wherever the word appears;
counting it only when it names an id costs nothing and invents nothing.

One row per keyword class per docstring is still the rule, PLUS one row
for every marker that names an id. So a docstring that owes two named
things reports both, which is the point of naming them, while a
docstring that says `owed` twice reports what it always reported.
-/

open Lean

namespace Obl

/-! ## The closed keyword set -/

/-- One keyword class. `spellings` are the literal forms the estate
writes; `notAfter` are the prefixes that mean a hit belongs to a
LONGER keyword and must not be counted here; `idOnly` are the spellings
that count as a marker only when they NAME an id. -/
structure Keyword where
  state : String
  spellings : List String
  notAfter : List String := []
  /-- Spellings admitted only in the structured `keyword(id)` form.
  `discharges` is here because it is a common verb in this library's
  prose and a rare marker: bare, it would report a discharge every time
  a docstring said one theorem discharges another's premise. -/
  idOnly : List String := []

/-- The closed set, in the order rows sort within one docstring. -/
def keywords : List Keyword := [
  { state := "owed", spellings := ["owed"] },
  { state := "obligation", spellings := ["obligation"],
    notAfter := ["sub-"] },
  { state := "parked", spellings := ["parked"], notAfter := ["un-"] },
  { state := "un-parked", spellings := ["un-parked"] },
  { state := "discharged", spellings := ["discharged"],
    idOnly := ["discharges"] },
  { state := "pin-pending", spellings := ["pin pending", "pin-pending"] },
  { state := "sub-obligation", spellings := ["sub-obligation"] }]

/-! ## Matching

Every offset below is a CHARACTER index. `String.toLower` is
character-wise and ASCII-only on this toolchain, so a match found in
the lowered text sits at the same index in the original — which is why
the keyword and the excerpt can be quoted verbatim from the source
prose while the search runs case-blind. -/

private def offsetsGo (width : Nat) : List String → Nat → List Nat
  | [], _ => []
  | [_], _ => []
  | p :: rest, acc =>
    let here := acc + p.length
    here :: offsetsGo width rest (here + width)

/-- The character offsets at which `needle` occurs in `hay`,
left to right and non-overlapping. -/
def offsetsOf (hay needle : String) : List Nat :=
  if needle.isEmpty then []
  else offsetsGo needle.length (hay.splitOn needle) 0

/-- The letter test that keeps `borrowed` from being `owed`: a match
must start at a non-letter boundary. The END is deliberately free, so
`obligations` and `parked)` still match. -/
def boundaryOk (chars : Array Char) (offset : Nat) : Bool :=
  offset == 0 || !(chars[offset - 1]!).isAlpha

/-- Does the text immediately before `offset` spell `s`? This is how
`un-parked` keeps its `parked` and `sub-obligation` its `obligation`. -/
def precededBy (chars : Array Char) (offset : Nat) (s : String) : Bool :=
  let sc := s.toList
  sc.length ≤ offset &&
    (List.range sc.length).all fun i =>
      (chars[offset - sc.length + i]!).toLower == (sc[i]!).toLower

/-- Every valid hit of the given spellings, as (offset, matched width),
in spelling order and then left to right. The two rules a hit must pass
are the boundary test and the longer-keyword test. -/
def candidates (chars : Array Char) (lowered : String) (k : Keyword)
    (spellings : List String) : List (Nat × Nat) :=
  spellings.flatMap fun sp =>
    (offsetsOf lowered sp.toLower).filterMap fun off =>
      if !boundaryOk chars off then none
      else if k.notAfter.any (precededBy chars off) then none
      else some (off, sp.length)

/-- The first valid hit for one keyword class: the earliest offset over
all its ALWAYS-valid spellings, with the earlier spelling winning a
tie. Answers the offset and the matched length. The `idOnly` spellings
are deliberately absent — this is the hit the ledger has always
reported, and a new spelling may not move it. -/
def firstHit (chars : Array Char) (lowered : String) (k : Keyword) :
    Option (Nat × Nat) :=
  (candidates chars lowered k k.spellings).foldl
    (init := (none : Option (Nat × Nat))) fun acc c =>
      match acc with
      | none => some c
      | some a => if c.1 < a.1 then some c else acc

/-! ## The named form -/

/-- A short-kebab id: lowercase letters, digits and inner hyphens.
Anything else is prose, and prose is not an id. -/
def kebabOk (s : String) : Bool :=
  !s.isEmpty && !s.startsWith "-" && !s.endsWith "-" &&
    s.all fun c => c.isDigit || c.isLower || c == '-'

/-- The id a marker names, read from the characters that follow it:
`(`, a short-kebab id, `)`, with no space anywhere. `none` means the
marker is bare — which is the common case and not a defect. -/
def idAt (chars : Array Char) (after : Nat) : Option String :=
  if chars[after]? != some '(' then none
  else
    let rest := (chars.toList.drop (after + 1))
    let body := rest.takeWhile (· != ')')
    if body.length == rest.length then none
    else
      let id := String.ofList body
      if kebabOk id then some id else none

/-! ## The rows -/

/-- Whitespace runs collapse to one space and the ends are trimmed:
docstrings are hard-wrapped prose, and an excerpt that carried the
wrapping would diff on a re-flow that changed nothing. -/
private def squashGo : List Char → Bool → List Char → List Char
  | [], _, acc => acc.reverse
  | c :: rest, prevWs, acc =>
    if c.isWhitespace then squashGo rest true acc
    else squashGo rest false
      (c :: (if prevWs && !acc.isEmpty then ' ' :: acc else acc))

def squash (cs : List Char) : String := String.ofList (squashGo cs false [])

/-- Forty characters of lead-in, the keyword, sixty of follow-on. -/
def excerptAt (chars : Array Char) (offset width : Nat) : String :=
  let start := if offset > 40 then offset - 40 else 0
  let stop := min chars.size (offset + width + 60)
  let body := squash (((chars.toList).drop start).take (stop - start))
  (if start > 0 then "…" else "") ++ body ++
    (if stop < chars.size then "…" else "")

/-- One docstring the scan reads: a declaration's, or one `/-! -/`
block of a module's. -/
structure Entry where
  module : String
  /-- The module's source, repository-relative (`Walk.sourceOf`). -/
  file : String
  /-- `none` for a module docstring block. -/
  declaration : Option String
  /-- The 1-based line the docstring opens on: the declaration's own
  range for a declaration docstring, the block's range for a module
  one. `none` where the environment carries no range. -/
  line : Option Nat := none
  doc : String

/-- One obligation hit. `state` is the machine bucket; `keyword` is the
estate's own spelling of it, verbatim, because `OBLIGATION`,
`obligation` and `PIN PENDING` are the prose the register is made of;
`id` is the debt's name when the marker gives it one. -/
structure Row where
  module : String
  /-- Where to open it: the module's source, repository-relative. A row
  the reader cannot find is a row nobody discharges, so the anchor is
  part of the row and not a lookup the reader performs. -/
  file : String
  declaration : Option String
  /-- The line the docstring carrying this marker opens on, or `none`
  where the environment carries no range for the declaration. -/
  line : Option Nat := none
  state : String
  /-- The short-kebab id of `owed(id)` / `discharges(id)`, or `none`
  for a bare marker. -/
  id : Option String := none
  keyword : String
  excerpt : String

/-- The rows one keyword class contributes to one docstring: the first
hit (as it always was, now carrying its id when it has one), plus every
OTHER marker of this class that names an id. Rows read in the order the
docstring writes them.

The first hit is computed over the always-valid spellings alone, so no
row the ledger reported before this convention can be displaced by
it. -/
def scanKeyword (e : Entry) (chars : Array Char) (lowered : String)
    (k : Keyword) : List Row :=
  let mk (off width : Nat) (id : Option String) : Row :=
    { module := e.module, file := e.file, declaration := e.declaration,
      line := e.line, state := k.state,
      id, keyword := String.ofList ((chars.toList.drop off).take width),
      excerpt := excerptAt chars off width }
  let first := firstHit chars lowered k
  let head : List (Nat × Row) :=
    match first with
    | none => []
    | some (off, width) => [(off, mk off width (idAt chars (off + width)))]
  let named : List (Nat × Row) :=
    (candidates chars lowered k (k.spellings ++ k.idOnly)).filterMap
      fun (off, width) =>
        if first.map Prod.fst == some off then none
        else (idAt chars (off + width)).map fun id => (off, mk off width (some id))
  ((head ++ named).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd

/-- Every row one docstring contributes, in the keyword set's declared
order. A docstring that says both `owed` and `discharged` yields both:
the ledger is history, so a discharge does not erase the debt it
settled. -/
def scan (e : Entry) : List Row :=
  let chars := e.doc.toList.toArray
  let lowered := e.doc.toLower
  keywords.flatMap (scanKeyword e chars lowered)

def scanAll (es : List Entry) : List Row := es.flatMap scan

/-! ## The health counters

Four of the six are folds over the rows. The other two are read from
the places that already compute them — the point of a counter is to
have one authority, not a second opinion. -/

/-- The counters no docstring carries: the grammar manifest's formless
rows, and the value plane's `Empty` denotations. -/
structure Health where
  formless : Nat
  emptyDenotations : Nat

/-- The grammar rows that state no form. READ from the manifest, which
computes this itself at `Manifest.lean`'s `formless` — a second
computation here would be a second authority. -/
def formlessCount : Nat :=
  (Cas.Grammar.manifestV0.rows.filter (·.forms.isEmpty)).length

/-- One equation of `Cas.Schema.El` — `El.eq_1` … `El.eq_12`, one per
arm. `El.eq_def` is the whole match at once and is not an arm. -/
def isElEquation : Name → Bool
  | .str p last =>
    p == `Cas.Schema.El && last.startsWith "eq_" && last != "eq_def"
  | _ => false

/-- The `El` arms that denote `Empty` — the value plane's declared
holes. Counted over `El`'s own EQUATIONS, one per arm, read from the
compiled environment rather than from the source text: an arm that
stops denoting `Empty` moves this number whether or not anyone
remembers to. `El` is a mutual definition, so its stored body is a
`brecOn` application that mentions no arm; the equations are where the
arms survive. `none` means they are gone, which is a finding and not
a zero. -/
def emptyDenotationCount (env : Environment) : Option Nat :=
  let eqns := env.constants.toList.filter fun (n, _) => isElEquation n
  if eqns.isEmpty then none
  else some (eqns.countP fun (_, ci) => ci.type.getUsedConstants.contains `Empty)

/-! ## The document -/

/-- The source anchor as JSON fields: the file always, the line only
where the environment gave one. Shared with the debt projection, which
carries the same two columns for the same rows. -/
def anchorJson (r : Row) : List (String × Cas.Json.Value) :=
  [("file", Cas.Json.Value.str r.file)] ++
    (match r.line with
     | some l => [("line", Cas.Json.Value.nat l)]
     | none => [])

def rowJson (r : Row) : Cas.Json.Value :=
  .obj (
    [("module", Cas.Json.Value.str r.module)] ++ anchorJson r ++
    (match r.declaration with
     | some d => [("declaration", Cas.Json.Value.str d)]
     | none => []) ++
    (match r.id with
     | some i => [("id", Cas.Json.Value.str i)]
     | none => []) ++
    [("state", .str r.state), ("keyword", .str r.keyword),
     ("excerpt", .str r.excerpt)])

def stateCount (rows : List Row) (s : String) : Nat :=
  (rows.filter (·.state == s)).length

def document (e : Gate.Emitted) (h : Health) (rows : List Row) : String :=
  let moduleRows := rows.filter (·.declaration.isNone)
  let declRows := rows.filter (·.declaration.isSome)
  Cas.Json.render (e.obj [
    ("library", .str "Cas"),
    ("counters", .obj [
      ("formless", .nat h.formless),
      ("emptyDenotations", .nat h.emptyDenotations),
      ("pinPending", .nat (stateCount rows "pin-pending")),
      ("parked", .nat (stateCount rows "parked")),
      ("owed", .nat (stateCount rows "owed")),
      ("discharged", .nat (stateCount rows "discharged"))]),
    ("moduleDocs", .arr (moduleRows.map rowJson)),
    ("declarations", .arr (declRows.map rowJson))]) ++ "\n"

/-! ## Reading the environment -/

/-- Every docstring in the library, in the order the ledger prints:
each module's `/-! -/` blocks, then its declarations, modules and
declarations both in `Walk`'s total order. -/
def entries (env : Environment) : CoreM (List Entry) := do
  let modules ← Walk.collect env
  let declEntries : List Entry :=
    modules.toList.flatMap fun (m, rows) =>
      rows.toList.filterMap fun r =>
        r.doc.map fun d =>
          { module := m.toString, file := Walk.sourceOf m,
            declaration := some r.name, line := r.line, doc := d }
  let mut moduleEntries : List Entry := []
  for m in Walk.libraryModules env do
    let some blocks := getModuleDoc? env m | continue
    for b in blocks do
      moduleEntries :=
        { module := m.toString, file := Walk.sourceOf m,
          declaration := none, line := some b.declarationRange.pos.line,
          doc := b.doc } :: moduleEntries
  return moduleEntries.reverse ++ declEntries

/-- The states a debt projection reads as OPEN: something is owed,
something is parked, something waits on a pin. `discharged`,
`un-parked`, `obligation` and `sub-obligation` are history or framing
and are not debts. -/
def debtStates : List String := ["owed", "parked", "pin-pending"]

def isDebt (r : Row) : Bool := debtStates.contains r.state

end Obl
