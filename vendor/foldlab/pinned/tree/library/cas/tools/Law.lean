import Lean
import Cas.Values.Json
import Gate
import Walk

/-!
# The law index — `tools/Law.lean`

The ruling registry, the `LAW` line grammar, the join between them and
the document they render. Promoted out of `Laws` so a second
projection can read the same rulings — the debt lane wants the UNBOUND
rows, and two exe roots cannot import one another, each having to
declare `main`. The promotion is a MOVE: the registry, the convention,
the failure directions and the bytes are the ones that were there.

`SCHEMA-MATERIALIZATION.md` records rulings and binds none of them to
anything the build reads. That is the defect the old era named in one
sentence — *rewrite the comment and the law is gone*, silently, with
every gate still green — and the discipline that answered it
(`attic/correctness-gating-laws`, `docs/LAWS.md` +
`scripts/check-laws.ts`) is the prior art this module re-adopts in
Lean.

## The convention

A line

```
LAW SM-<n>: <one clause>
```

at the HEAD of an enforcing declaration's docstring. Head means the
first non-blank line, and a run of consecutive `LAW` lines is one
declaration claiming several rulings; the run ends at the first line
that is not a `LAW` line. A `LAW` line further down the docstring is
prose, not a claim — otherwise the convention would fire on any
docstring that discusses a ruling, and the index would bind readers
rather than enforcers.

The docstring won over an attribute on build-graph cost, not on
feasibility. An `@[law]` attribute works (it survives into `.olean` and
is enumerable downstream), but it needs a leaf importing `Lean`,
imported by every tagging module, which pushes `Lean` into the codec
and value planes the first time a theorem there is tagged. The
docstring costs nothing, is already readable from the imported
environment, and matches a convention the estate already runs in forty
docstrings (`NAMED OBLIGATION`, `SUB-OBLIGATION 1, DISCHARGED`).
Because both mechanisms key the binding on the declaration NAME, the
upgrade stays mechanical if declaration-time validation is ever wanted.

## The registry

`Law.registry` is the queue as a Lean value — the `Cas/Architecture.lean`
idiom, a description held as data with the shape's own laws as
`#guard`s. It transcribes `SCHEMA-MATERIALIZATION.md`'s ruling queue
one clause per item. The markdown stays the prose home; the value is
what the build reads.

Two transcription decisions are recorded here rather than hidden:

- **The queue's numbering starts at 6** because it continues the
  `Open rulings (operator)` section above it, so `SM-1`–`SM-5` are
  those five. Registering them keeps the `SM-` namespace TOTAL: a
  future `LAW SM-3` claim is then a binding, not a phantom
  "unregistered" report.
- **`SM-34`–`SM-37` are the queue's four collided items.** Two
  parallel lanes both appended at 15–18 on 2026-08-29 — `0c623f66` at
  07:05 (the float ceiling, the materializer blocker, the two source
  gates) and `b2769c09` at 07:19 (the deriving handler's four union
  items), the second inserted textually after item 6. The estate cites
  the FIRST block by number in live code (`ruling 15, the float
  ceiling` in `Cas/Schema/Ast.lean`, `Cas/Backend/Admission.lean`,
  `tools/Verdicts.lean`; `ruling-queue item 17`/`18` in
  `tools/Materialize.lean`), and cites the second block by number
  nowhere, so 15–18 stay with the earlier block and the later four
  take fresh ids at the end of the namespace. This is exactly the
  collision the ID-namespace ask predicted; the index makes it
  machine-visible, which is the point.

## The gate, failing in both directions

- **unregistered binding** — a declaration claims an id the registry
  does not carry. This is what catches a typo, and it is why the
  attribute's elaboration-time check is not needed.
- **status lie** — a row recorded `owed` that a declaration now claims,
  a row recorded `bound` that no declaration claims (the
  comment-deletion attack, which is the whole reason for the index),
  and a row recorded `superseded` that a declaration still claims.
- **registry hygiene** — a duplicated row, a malformed id, an empty
  statement, ids out of ascending order. Held at elaboration by
  `#guard` as well, so a bad registry is a red build and not merely a
  red gate.

**`unbound` is NOT a failure.** A registry row that no declaration
claims is the debt made visible — the salvaged `UNBOUND` vocabulary,
where every such row "is a cheap upgrade" and none is a violation. It
is counted, named in the fixture, and printed; it does not fail the
gate. Day one is mostly unbound by construction, and a gate that went
red on that would be deleted within a week. `lake exe debts` is the
projection that collects those rows beside the docstring debts.

## What this does NOT buy

Nothing here checks that the claiming declaration actually ENFORCES the
ruling. A bound ruling is checkable, not sufficient. What the binding
buys is that the correspondence cannot be dissolved quietly: strike the
`LAW` line and the gate goes red at the registry row that still claims
it.

The walk reads `Cas` and the `Cas.Backend.*` leaves. Rulings discharged
by TOOLING — the emitters under `tools/` — have no declaration in that
set to carry the line, so they stay `owed` however finished they are.
That is a limit of the convention, not a fact about the work.
-/

open Lean

namespace Law

/-! ## The id namespace

`SM-<n>`, for SCHEMA-MATERIALIZATION. A prefix rather than the queue's
bare integers, because the bare integers already collide with `R<n>`,
`D<n>`, `S<n>`, `AE-<n>` and — live, in this library's own docstrings —
the grammar grill's `ruling 2` and `ruling 3`
(`Cas/Grammar/Sorts.lean`, `Cas/Schema/SelfCodec.lean`), which are not
these rulings at all. -/

def idPrefix : String := "SM-"

/-- `String.drop` answers a slice on this toolchain and the index wants
`String` throughout, so the drop is spelled over the characters. -/
private def dropN (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

/-- The number an id names, or `none` when the id is not of the
namespace. -/
def idNum? (id : String) : Option Nat :=
  if !id.startsWith idPrefix then none
  else
    let digits := dropN id idPrefix.length
    if digits.isEmpty || !digits.all Char.isDigit then none
    else digits.toNat?

def wellFormedId (id : String) : Bool := (idNum? id).isSome

/-! ## Reading a claim off a docstring

The trimming is local: the toolchain's `String.trim` is deprecated in
favour of a slice-returning `trimAscii`, and the index wants `String`
throughout. Whitespace here is the ASCII four — a docstring's own
formatting, nothing exotic. -/

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

def trimStartWs (s : String) : String := String.ofList (s.toList.dropWhile isWs)

def trimWs (s : String) : String :=
  String.ofList
    (((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse)

/-- One `LAW <id>: <clause>` line, or `none`. The clause may itself
contain a colon — the split rejoins everything after the first one, so
`LAW SM-19: the two doors: held in agreement` reads as one clause. -/
def parseLawLine (line : String) : Option (String × String) :=
  let t := trimStartWs line
  if !t.startsWith "LAW " then none
  else match (dropN t 4).splitOn ":" with
    | [] => none
    | [_] => none
    | rawId :: rest =>
      let id := trimWs rawId
      let clause := trimWs (String.intercalate ":" rest)
      if id.isEmpty || clause.isEmpty then none else some (id, clause)

private def headLinesGo :
    List String → List (String × String) → List (String × String)
  | [], acc => acc.reverse
  | l :: ls, acc =>
    if (trimWs l).isEmpty then
      -- Leading blank lines are the docstring's own formatting; a blank
      -- line AFTER the run ends it.
      if acc.isEmpty then headLinesGo ls acc else acc.reverse
    else match parseLawLine l with
      | some c => headLinesGo ls (c :: acc)
      | none => acc.reverse

/-- The ids a docstring claims: the run of `LAW` lines at its head, and
nothing else. -/
def headClaims (doc : String) : List (String × String) :=
  headLinesGo (doc.splitOn "\n") []

/-- One declaration claiming one ruling. The `clause` is the
declaration's own spelling, carried into the fixture verbatim, so
rewording it is a visible diff rather than a silent one. -/
structure Claim where
  id : String
  clause : String
  module : String
  declaration : String
  deriving DecidableEq, Inhabited

/-- Every claim in the walk, in `Walk.collect`'s total order (module,
then declaration). -/
def claimsOf (modules : Array (Name × Array Walk.Row)) : List Claim :=
  modules.toList.flatMap fun (m, rows) =>
    rows.toList.flatMap fun r =>
      match r.doc with
      | none => []
      | some d => (headClaims d).map fun (id, clause) =>
          { id, clause, module := m.toString, declaration := r.name }

/-! ## The registry -/

/-- A row's binding state — about the BINDING, not about whether the
operator has ruled. `owed`: no declaration claims it. `bound`: one or
more do. `superseded`: the row is retired and must not be claimed. -/
inductive Status where
  | owed
  | bound
  | superseded
  deriving DecidableEq, Repr, Inhabited

def Status.word : Status → String
  | .owed => "owed"
  | .bound => "bound"
  | .superseded => "superseded"

/-- One ruling: its id, one clause of what it rules, and whether a
declaration carries it. -/
structure Ruling where
  id : String
  statement : String
  status : Status
  deriving DecidableEq, Inhabited

/-- The queue, transcribed. `SM-1`–`SM-5` are the open operator
rulings the queue's numbering continues from; `SM-6`–`SM-33` are the
queue proper; `SM-34`–`SM-37` are the four items that collided at
15–18 (see the module docstring). -/
def registry : List Ruling := [
  { id := "SM-1", status := .owed
  , statement := "the admitted subset is the ratified construct table, \
not the whole of Effect Schema" },
  { id := "SM-2", status := .owed
  , statement := "a reference names its target by that target's content \
address, and the references table is assembled at materialization" },
  { id := "SM-3", status := .owed
  , statement := "the rev-0/rev-1 Integer disagreement is a spelling \
question only, the safe-integer bound being carried on both sides" },
  { id := "SM-4", status := .owed
  , statement := "nominally distinct brands collapse to one address \
unless brand is minted as an identity-bearing check" },
  { id := "SM-5", status := .owed
  , statement := "variance defect D1 is decided before the first \
libfree corpus run rather than before this lane" },
  { id := "SM-6", status := .bound
  , statement := "a union carries both modes and its member order is \
its identity" },
  { id := "SM-7", status := .bound
  , statement := "the adopted Effect declaration rows are taken \
verbatim and mint no estate identity" },
  { id := "SM-8", status := .owed
  , statement := "whether the store-reference code is sugar for \
declaration row zero is kept open by construction" },
  { id := "SM-9", status := .owed
  , statement := "a kind whose own code spells its tag cannot leave \
that tag to callers, because the tag is then part of the address" },
  { id := "SM-10", status := .owed
  , statement := "the TypeScript door does not yet admit \
declaration-carrying schemas, a root asymmetry rather than a defect" },
  { id := "SM-11", status := .bound
  , statement := "the canonical rendering is injective, discharged by \
the Lean-side strict parser rather than assumed" },
  { id := "SM-12", status := .owed
  , statement := "the declaration registry's wire-identity table lives \
in its own module's docstring and not in REGISTRY.md" },
  { id := "SM-13", status := .owed
  , statement := "Effect's generated text collapses an all-bare-literal \
union and loses its oneOf mode" },
  { id := "SM-14", status := .bound
  , statement := "an empty union refuses illFormed and an unknown mode \
refuses notASchema, with no separate empty-union name" },
  { id := "SM-15", status := .bound
  , statement := "the value plane has no float, so a float-carrying \
schema is refused rather than collapsed" },
  { id := "SM-16", status := .owed
  , statement := "the tree-sitter materializer lane stays blocked on \
recursion and named references, union having landed" },
  { id := "SM-17", status := .owed
  , statement := "materialized source is committed and therefore \
typechecked, so a stale snapshot is a red suite" },
  { id := "SM-18", status := .owed
  , statement := "the estate-native register prints each committed \
payload back through the ingestion door" },
  { id := "SM-19", status := .bound
  , statement := "the two doors are held in agreement by a generated \
admission gate and a committed disagreement corpus" },
  { id := "SM-20", status := .owed
  , statement := "Effect's empty struct admits excess properties where \
the Lean decoder refuses them" },
  { id := "SM-21", status := .owed
  , statement := "a Declaration's annotation bag is read tolerantly, \
with the registry's own keys consumed as required" },
  -- SM-22 MOVED, 2026-08-29 (the brain-stem package). The ruling used
  -- to be a LIMIT: the run manifest spells the puts-with-answer-indices
  -- sub-fragment and does not grow to the whole program table. It was
  -- ruled the other way — a program stored at an address cannot be run
  -- unless the document can name an address — so the manifest grew,
  -- `manifestVersion` bumped to 1, and the two theorems that pinned the
  -- limit flipped into `Mcp.ofPProg_isSome`. The row is amended here
  -- rather than deleted, which is what the index exists to force.
  { id := "SM-22", status := .bound
  , statement := "the run manifest spells the whole program table — \
literal-address operands and loads included — so a stored program can \
be named by the document that runs it" },
  { id := "SM-23", status := .owed
  , statement := "the program emitter routes through the \
defunctionalized table rather than lowering trees straight to source" },
  { id := "SM-24", status := .owed
  , statement := "the surface ledger walks the backend modules as well \
as the library root" },
  { id := "SM-25", status := .owed
  , statement := "the dormant effect-replay vocabulary is reactivated \
by ruling before any utterance slice, not during one" },
  { id := "SM-26", status := .bound
  , statement := "the human kind-tag registry is the Markdown \
projection of the grammar manifest, and every sort has a row" },
  { id := "SM-27", status := .owed
  , statement := "the estate's Effect lock and the front-end lanes' \
pin are one decision with one owner" },
  { id := "SM-28", status := .bound
  , statement := "every grammar form's layout is read off a witness \
term rather than transcribed" },
  { id := "SM-29", status := .owed
  , statement := "the put verb takes the described canonical node \
document, not bytes and a tag" },
  { id := "SM-30", status := .owed
  , statement := "every command-line verb carries a machine-readable \
second register" },
  { id := "SM-31", status := .owed
  , statement := "the architecture capability matrix carries a row for \
every shipped adapter" },
  { id := "SM-32", status := .owed
  , statement := "Effect's MCP pin emits an output schema only for \
object-typed results" },
  { id := "SM-33", status := .owed
  , statement := "every ruling has an enforcing declaration, and the \
index fails in both directions" },
  { id := "SM-34", status := .owed
  , statement := "a derived union orders its members by ascending tag \
string, so shuffling constructors does not move an address" },
  { id := "SM-35", status := .owed
  , statement := "the constructor-alternative deriving path refuses \
parametric and indexed types by name" },
  { id := "SM-36", status := .owed
  , statement := "the discriminant field name is reserved in every \
derived member and bounds the member field names below it" },
  { id := "SM-37", status := .owed
  , statement := "the hand mirror of a derived union spells the union \
constructor with an explicit oneOf mode" }]

/-! ### The registry's own laws

Held at elaboration, in the `Cas/Architecture.lean` idiom: a bad
registry is a red BUILD, before the gate ever runs. -/

private def ascending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a < b && ascending (b :: rest)

-- Every id is of the namespace.
#guard registry.all fun r => wellFormedId r.id

-- No id twice.
#guard decide ((registry.map (·.id)).Nodup)

-- Every row says something.
#guard registry.all fun r => !r.statement.isEmpty

-- Ids ascend, so the registry reads in queue order and a duplicate
-- number cannot hide between two rows.
#guard ascending (registry.filterMap fun r => idNum? r.id)

/-! ## The join -/

def bindingsOf (cs : List Claim) (id : String) : List Claim :=
  cs.filter (·.id == id)

/-- Claims of ids the registry does not carry. A typo lands here. -/
def unregisteredOf (reg : List Ruling) (cs : List Claim) : List Claim :=
  cs.filter fun c => !(reg.any (·.id == c.id))

/-- Registry rows no declaration claims — the debt, counted. NOT a
violation: see the module docstring. -/
def unboundOf (reg : List Ruling) (cs : List Claim) : List String :=
  (reg.filter fun r =>
    r.status == .owed && (bindingsOf cs r.id).isEmpty).map (·.id)

/-- Both directions, plus registry hygiene. The empty list is the gate
passing. -/
def violations (reg : List Ruling) (cs : List Claim) : List String :=
  let dupes := (reg.filterMap fun r =>
    if (reg.filter (·.id == r.id)).length > 1 then
      some s!"{r.id}: duplicate row in the registry"
    else none)
  let malformed := reg.filterMap fun r =>
    if wellFormedId r.id then none
    else some s!"{r.id}: not an id of the SM- namespace"
  let empties := reg.filterMap fun r =>
    if r.statement.isEmpty then
      some s!"{r.id}: the row states nothing"
    else none
  let unreg := (unregisteredOf reg cs).map fun c =>
    s!"{c.id}: claimed by {c.declaration} but absent from the registry \
— a ruling nothing registers is a ruling nothing checks"
  let lies := reg.filterMap fun r =>
    let bs := bindingsOf cs r.id
    match r.status, bs with
    | .owed, b :: _ =>
      some s!"{r.id}: recorded owed, but {b.declaration} claims it — \
an upgrade is not drift, but the registry must say so"
    | .bound, [] =>
      some s!"{r.id}: recorded bound, but no declaration claims it — \
the LAW line was rewritten out of the docstring, which is exactly the \
drift this index exists for"
    | .superseded, b :: _ =>
      some s!"{r.id}: recorded superseded, but {b.declaration} still \
claims it — a retired ruling cannot be enforced"
    | _, _ => none
  (dupes ++ malformed ++ empties ++ unreg ++ lies).eraseDups

/-! ## The document -/

def claimJson (c : Claim) : Cas.Json.Value :=
  .obj [("module", .str c.module), ("declaration", .str c.declaration),
        ("clause", .str c.clause)]

def unregisteredJson (c : Claim) : Cas.Json.Value :=
  .obj [("id", .str c.id), ("module", .str c.module),
        ("declaration", .str c.declaration), ("clause", .str c.clause)]

def rulingJson (cs : List Claim) (r : Ruling) : Cas.Json.Value :=
  .obj [("id", .str r.id), ("status", .str r.status.word),
        ("statement", .str r.statement),
        ("bindings", .arr ((bindingsOf cs r.id).map claimJson))]

def statusCount (reg : List Ruling) (s : Status) : Nat :=
  (reg.filter (·.status == s)).length

def document (e : Gate.Emitted) (reg : List Ruling) (cs : List Claim) :
    String :=
  let unreg := unregisteredOf reg cs
  let unbound := unboundOf reg cs
  Cas.Json.render (e.obj [
    ("library", .str "Cas"),
    ("convention", .str
      "LAW <id>: <one clause> at the head of the enforcing \
declaration's docstring"),
    ("counters", .obj [
      ("rulings", .nat reg.length),
      ("bound", .nat (statusCount reg .bound)),
      ("owed", .nat (statusCount reg .owed)),
      ("superseded", .nat (statusCount reg .superseded)),
      ("claims", .nat cs.length),
      ("claimingDeclarations", .nat (cs.map (·.declaration)).eraseDups.length),
      ("unbound", .nat unbound.length),
      ("unregistered", .nat unreg.length)]),
    ("rulings", .arr (reg.map (rulingJson cs))),
    ("unbound", .arr (unbound.map Cas.Json.Value.str)),
    ("unregistered", .arr (unreg.map unregisteredJson))]) ++ "\n"

end Law
