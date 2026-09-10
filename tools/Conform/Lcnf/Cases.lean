import Lean
import Conform.Core.Report
import Conform.Core.Policy

/-!
# Conform.Lcnf.Cases — the case-site audit, over the whole environment

**What it is.** Two things, kept apart on purpose.

*The scan* (§1–§3) walks the mono-phase LCNF of **every** declaration the imported environment
holds under a configured set of name roots, and records every `cases` node whose scrutinee is one
of a configured set of inductive families: which constructors got an alternative of their own, in
the compiler's order, and whether the node has a default arm. Nothing about Effect4, or about any
particular family, is written here: the roots and the families are arguments.

*The policy and its check* (§4–§6) read a JSON file that says, per family and per function, what
the tree has **decided** about those sites — `exhaustive` (no default arm permitted) or `default`
with the exact constructor list the default is allowed to absorb — and emit one `Conform.Row` per
subject. A site the policy does not name is never a silent pass: it is `refused` or `unresolved`
by the family's `unlisted` setting.

**Depends on.** `Lean` (`Lean.Compiler.LCNF.PhaseExt.getMonoDecl?`, the one door to the compiler's
own IR, and `Lean.Compiler.LCNF.Basic`'s `Cases`/`Alt`), `Conform.Core.Report`,
`Conform.Core.Policy`. Nothing from this repository: the extensibility rule of the wave's common
brief. Effect4's own configuration lives in `tools/Conform/Effect4/cases-policy.json`.

**Why mono LCNF and not the matcher.** A `match` on an inductive compiles through `casesOn`,
a `matcher_N` auxiliary, `Ty.ctorIdx` or `StructProjCases` depending on the arms, so reading the
matcher is reading an accident. Mono LCNF is post-compilation: it shows what the arms *became*,
including that `| .nat | .int => "number"` became a **default arm**, which is precisely the drift
hazard the audit exists for. `Lean.Compiler.LCNF.Cases` carries `typeName`, and `Alt.alt` carries
the constructor name (`Lean/Compiler/LCNF/Basic.lean:359-369, 421-434`), so the question
"which constructors does this function give an arm of their own, and does it have a default?" is
a question about `Code`, answerable over every declaration at once.

**Properties.**
* **Whole domain.** The scan never takes a list of functions to inspect: it walks every constant
  under the configured roots and reports what it finds. The policy lists what is *decided*; the
  scan finds what *exists* — *by construction* (`scan`).
* **Absorbed and unreachable are two things.** At a site with a default arm, the constructors with
  no arm of their own are absorbed by the default. At a site *without* one they are **unreachable**:
  the compiler dropped the alternative. The prototype this extends conflated them; `Site.absorbed`
  and `Site.unreachable` do not — *by construction*.
* **Names are data.** Everything is `Lean.Name` until the report; a compiler auxiliary is
  attributed to the user declaration it belongs to only when the recovered name is a real,
  non-internal constant of the environment, and the raw name is kept either way — *by
  construction* (`Attribution`, `attribute`).
* **Nothing is silently decided.** Every site produces exactly one row, and every policy rule with
  no site produces exactly one row; `Report.expected` is the sum, so a dropped subject is visible —
  *by construction* (`check`).
-/

namespace Conform.Lcnf

open Lean Compiler LCNF

/-! ## 1. The families a scan audits -/

/-- The constructors of each audited family, in declaration order, read from the environment.
Built by `FamilyTable.ofEnv`, which refuses a name that is not an inductive: a family list is
configuration, and a typo in it must not become "no sites found". -/
structure FamilyTable where
  /-- The families, in the order the configuration gave them. -/
  order : Array Name
  /-- Family ↦ its constructors, in declaration order, as **short** names (`never`, not
  `Effect4.Program.Ty.never`). -/
  ctors : Std.HashMap Name (Array Name)
deriving Inhabited

namespace FamilyTable

/-- The short name of a constructor: its last component. `Name.mkSimple` rather than
`String.toName` — the latter runs the *parser* over the string, so a component with a dot or a
French quote in it would come back as something else; `mkSimple` is the identity on the component
the environment stored. Equal on every name in this tree (checked in `Fixtures/Traffic.lean`). -/
def shortCtor (c : Name) : Name := Name.mkSimple c.getString!

/-- The constructors of one inductive, as short names in declaration order, or the reason there
are none. Deliberately **not** `getConstInfoInduct`: that throws, and this tool's three callers
each owe the caller a named refusal (`Except`) rather than an exception — absence, refusal and
frontier are three things. `InductiveVal.ctors` is the built-in that does the work. -/
def ctorsOf (env : Environment) (f : Name) : Except String (Array Name) :=
  match env.find? f with
  | some (.inductInfo i) => .ok (i.ctors.toArray.map shortCtor)
  | some _ => .error s!"`{f}` is a constant but not an inductive type"
  | none => .error s!"`{f}` is not a constant of the imported environment"

def ofEnv (env : Environment) (families : Array Name) : Except String FamilyTable := do
  let mut ctors : Std.HashMap Name (Array Name) := {}
  for f in families do
    if ctors.contains f then
      throw s!"family `{f}` is listed twice"
    ctors := ctors.insert f (← ctorsOf env f)
  return { order := families, ctors }

def contains (t : FamilyTable) (f : Name) : Bool := t.ctors.contains f

def constructors (t : FamilyTable) (f : Name) : Array Name := t.ctors.getD f #[]

end FamilyTable

/-! ## 2. Attribution: a compiler auxiliary belongs to a user declaration -/

/-- The user declaration a raw LCNF declaration name belongs to, and the steps that recovered it.
`steps` is empty exactly when the raw name *is* the user declaration. -/
structure Attribution where
  user : Name
  steps : Array String
deriving Inhabited, Repr

/-- The auxiliary-name suffixes this attribution knows, as `(recogniser, label)`. A component is
recognised when the recogniser accepts it; the label is what goes in `Attribution.steps`. The list
is deliberately explicit rather than "anything starting with `_`": an unrecognised internal name
must stay unattributed and be visible in the report, not be guessed at. -/
private def auxLabel? (s : String) : Option String :=
  let numbered (pre : String) : Bool :=
    match s.dropPrefix? pre with
    | some rest => !rest.isEmpty && rest.all fun c => c.isDigit || c == '_'
    | none => false
  if s == "_redArg" then some "redArg"
  else if s == "_unsafe_rec" then some "unsafeRec"
  else if s == "_sunfold" then some "sunfold"
  else if s == "_unary" then some "unary"
  else if s == "_override" then some "override"
  else if numbered "match_" then some "matcher"
  else if numbered "_spec_" then some "specialization"
  else if numbered "spec_" then some "specialization"
  else if numbered "_lam_" then some "lambda"
  else if numbered "_lambda_" then some "lambda"
  else if numbered "_elambda_" then some "lambda"
  else if numbered "_closed_" then some "closed"
  else if numbered "_cstage" then some "cstage"
  else none

/-- The pure half of attribution: un-mangle a private name, then drop recognised auxiliary
components from the end, reporting which were dropped (outermost first). Nothing here consults an
environment, so it is directly testable — and it is tested, in
`tools/Conform/Effect4/Fixtures/Traffic.lean`, because the Effect4 closure exercises none of it. -/
def stripAux (raw : Name) : Name × Array String := Id.run do
  let mut steps : Array String := #[]
  let mut n := raw
  if let some user := privateToUserName? n then
    steps := steps.push "private"
    n := user
  for _ in [0:8] do
    match n with
    | .str p s =>
      match auxLabel? s with
      | some label => steps := steps.push label; n := p
      | none => break
    | .num p _ => steps := steps.push "num"; n := p
    | .anonymous => break
  return (n, steps)

/-- Attribute `raw` to the user declaration it belongs to. `stripAux` first; the result is then
accepted **only** when it is a constant of `env` that is not itself internal — otherwise the raw
name stands and the single step `unattributed` records that it could not be resolved. A guess is
never silently promoted to an attribution. -/
def attributeOf (env : Environment) (raw : Name) : Attribution :=
  let (n, steps) := stripAux raw
  if steps.isEmpty then { user := raw, steps := #[] }
  else if n != .anonymous && env.contains n && !n.isInternal then { user := n, steps }
  else { user := raw, steps := #["unattributed"] }

/-! ## 3. The scan -/

/-- One `cases` node of one mono-phase declaration, on an audited family. -/
structure Site where
  /-- The name the compiler stored the code under: an auxiliary's own name, unchanged. -/
  raw : Name
  /-- The user declaration it is attributed to (`raw` when attribution did not resolve). -/
  decl : Name
  /-- How `decl` was recovered; empty when `raw = decl`. -/
  steps : Array String
  /-- The scrutinee's inductive type. -/
  family : Name
  /-- The pre-order index of this `cases` node among **all** `cases` nodes of `raw`'s code
  (audited or not). Stable for a given source and toolchain; it is the site's identity in a
  dump, not in the policy. -/
  node : Nat
  /-- The index of this site among the sites of the same `(decl, family)`, in walk order. This
  **is** the policy's key: a function's rules are a list, in this order. -/
  ordinal : Nat
  /-- The constructors with an alternative of their own, in the compiler's order. -/
  named : Array Name
  hasDefault : Bool
deriving Inhabited

namespace Site

/-- The constructors this site's default arm absorbs: the family's constructors, in declaration
order, that have no alternative of their own. Empty when the site has no default arm — at such a
site the same constructors are `unreachable`, which is a different fact. -/
def absorbed (t : FamilyTable) (s : Site) : Array Name :=
  if s.hasDefault then (t.constructors s.family).filter fun c => !s.named.contains c else #[]

/-- The constructors the compiler proved cannot reach this site: no alternative of their own and
no default arm to absorb them. -/
def unreachable (t : FamilyTable) (s : Site) : Array Name :=
  if s.hasDefault then #[] else (t.constructors s.family).filter fun c => !s.named.contains c

def subject (s : Site) : Subject :=
  { kind := "caseSite", path := [s.family.toString, s.decl.toString, toString s.ordinal] }

/-- Hand-written, not `deriving ToJson`: the schema is not the record. `attribution` is the field
`steps` under the name a reader of the dump needs, and `absorbed`/`unreachable` are computed
against the family table, which the record does not carry. -/
def toJson (t : FamilyTable) (s : Site) : Json :=
  Json.mkObj
    [ ("decl", Json.str s.decl.toString)
    , ("raw", Json.str s.raw.toString)
    , ("attribution", Json.arr (s.steps.map Json.str))
    , ("family", Json.str s.family.toString)
    , ("ordinal", Json.num s.ordinal)
    , ("node", Json.num s.node)
    , ("named", Json.arr (s.named.map fun c => Json.str c.toString))
    , ("hasDefault", Json.bool s.hasDefault)
    , ("absorbed", Json.arr ((s.absorbed t).map fun c => Json.str c.toString))
    , ("unreachable", Json.arr ((s.unreachable t).map fun c => Json.str c.toString)) ]

end Site

private structure WalkState where
  node : Nat := 0
  sites : Array Site := #[]

/-- One `cases` node, as a site. `named` is in the compiler's alternative order, which is why
`Cases.getCtorNames` (`LCNF/Basic.lean:449-455`) is **not** used here: it answers with a `NameSet`,
and a set has lost the order the audit reports. -/
private def siteOf (raw : Name) (node : Nat) (c : Cases .pure) : Site :=
  { raw, decl := raw, steps := #[], family := c.typeName, node, ordinal := 0
  , named := c.alts.filterMap fun
      | .alt ctor .. => some (FamilyTable.shortCtor ctor)
      | .default _ => none
  , hasDefault := c.alts.any (· matches .default _) }

/-- The audited case sites of one declaration's code, in the compiler's own pre-order.

`Code.forM` (`LCNF/Basic.lean:860-872`) *is* that walk: it visits a node, then a `let`'s
continuation, a `fun`/`jp`'s body before its continuation, and a `cases`'s alternatives in order.
It replaces the hand-written `partial` walker this seat first wrote, node index for node index —
the index counts `cases` nodes only, and `Code.forM` reaches them in the same order. -/
private def sitesOf (raw : Name) (keep : Name → Bool) (code : Code .pure) : Array Site :=
  let walk : StateM WalkState Unit := code.forM fun
    | .cases c => modify fun s =>
        { node := s.node + 1
        , sites := if keep c.typeName then s.sites.push (siteOf raw s.node c) else s.sites }
    | _ => pure ()
  (walk.run {}).2.sites

/-- Where the scan gets its list of declarations to walk. The two answers are **not** the same set,
and the difference is not small.

* `constants` walks `Environment.constants` — every name the elaborator produced — and asks
  `getMonoDecl?` for each. This is what a human means by "every declaration", and it is what the
  X4 prototype did.
* `monoExtension` walks `monoExt`'s own module entries, which include the declarations the
  *compiler* created during the LCNF passes and never put in the environment: `f._redArg`,
  `f._lam_0`, `f._closed_3`. Measured on this tree's `Effect4` closure: 305,129 mono entries over
  2,443 imported modules, of which **250,735 are not environment constants at all**. It matters:
  `Effect4.Program.effTy`'s own mono code is a one-line tail call to `Effect4.Program.effTy._redArg`,
  and *that* is where its twenty-seven arms live.

`constants` is therefore the conservative denominator and `monoExtension` the complete one; a
configuration says which, and the report's pins say which was used. -/
inductive ScanSource
  | constants
  | monoExtension
deriving Inhabited, DecidableEq

def ScanSource.id : ScanSource → String
  | .constants => "constants"
  | .monoExtension => "monoExtension"

/-- What the scan covers and what it found. The three counts are the audit's own scale and go into
the report as pins: a scan that suddenly sees a tenth of the constants it used to is not a passing
audit, it is a broken one. -/
structure Scan where
  families : FamilyTable
  /-- Which declaration list was walked. -/
  source : ScanSource
  /-- Declarations under the configured roots, in whichever list `source` names. -/
  constants : Nat
  /-- Of those, the ones the environment holds a mono-phase LCNF entry for. -/
  withMonoCode : Nat
  /-- Of those, the ones whose entry is an `extern` stub rather than code (`PhaseExt.lean:96-104`
  replaces a non-transparent declaration's body with one on export). -/
  externs : Nat
  sites : Array Site
  wallMs : Nat
deriving Inhabited

/-- What the scan walks. Every field is configuration: `roots` are name prefixes (empty means
everything, which on a real environment also walks the toolchain), `families` are the inductives
whose case sites are collected, `source` is which declaration list is walked. -/
structure ScanConfig where
  roots : Array Name
  families : Array Name
  source : ScanSource := .constants
deriving Inhabited

/-- Walk every constant under the roots. `CoreM` only for `getMonoDecl?`, which reads the
`monoExt` persistent extension and never compiles anything. -/
def scan (cfg : ScanConfig) : CoreM Scan := do
  let start ← IO.monoMsNow
  let env ← getEnv
  let families ← ofExcept (FamilyTable.ofEnv env cfg.families)
  let underRoots (n : Name) : Bool :=
    cfg.roots.isEmpty || cfg.roots.any fun r => r.isPrefixOf n
  let keep (n : Name) : Bool := families.contains n
  let mut constants := 0
  let mut withMonoCode := 0
  let mut externs := 0
  let mut sites : Array Site := #[]
  -- one declaration: count it, walk it if it has code, attribute it. Ordinals are **not**
  -- assigned here: two raw declarations can attribute to the same user declaration (a function
  -- and its `_redArg` copy), so numbering per raw name would give two site 0s. The whole scan is
  -- numbered once, below, in scan order.
  let visit (n : Name) (d : Decl .pure) (sites : Array Site) : Nat × Array Site :=
    match d.value with
    | .extern _ => (1, sites)
    | .code c =>
      let a := attributeOf env n
      (0, sites ++ (sitesOf n keep c).map fun s => { s with decl := a.user, steps := a.steps })
  match cfg.source with
  | .constants =>
    -- `Environment.constants` is an `SMap`; `toList` would cons a ~300k-element list only for the
    -- roots to throw all but a few thousand of it away. `SMap.fold` visits the same entries, and
    -- the list `toList` builds is the *reverse* of the fold order (`Lean/Data/SMap.lean:107-114`),
    -- so reversing the filtered array reproduces the `toList` walk's order exactly — two builds'
    -- `--dump-scan` receipts stay diffable.
    let underRootNames : Array Name :=
      (env.constants.fold (init := #[]) fun acc n _ =>
        if underRoots n then acc.push n else acc).reverse
    for n in underRootNames do
      constants := constants + 1
      match (← getMonoDecl? n) with
      | none => pure ()
      | some d =>
        withMonoCode := withMonoCode + 1
        let (e, out) := visit n d sites
        externs := externs + e
        sites := out
  | .monoExtension =>
    -- `monoExt`'s own entries, per imported module: this is the only way to reach the
    -- declarations the compiler created and never put in the environment (`f._redArg`).
    let mut seen : Std.HashSet Name := {}
    for i in [0:env.header.moduleNames.size] do
      for d in monoExt.getModuleEntries env i do
        unless underRoots d.name do continue
        if seen.contains d.name then continue
        seen := seen.insert d.name
        constants := constants + 1
        withMonoCode := withMonoCode + 1
        let (e, out) := visit d.name d sites
        externs := externs + e
        sites := out
  -- number the sites per (user declaration, family), in scan order: the policy's key
  let (_, numbered) := sites.foldl (init := (({} : Std.HashMap (Name × Name) Nat), #[]))
    fun (counts, acc) s =>
      let k := counts.getD (s.decl, s.family) 0
      (counts.insert (s.decl, s.family) (k + 1), acc.push { s with ordinal := k })
  return { families, source := cfg.source, constants, withMonoCode, externs, sites := numbered
         , wallMs := (← IO.monoMsNow) - start }

namespace Scan

/-- Sites per family, in the configuration's family order. -/
def byFamily (s : Scan) : Array (Name × Array Site) :=
  s.families.order.map fun f => (f, s.sites.filter fun st => st.family == f)

def pins (s : Scan) : List Pin :=
  [ { name := "scan.source", value := s.source.id }
  , { name := "scan.constants", value := toString s.constants }
  , { name := "scan.withMonoCode", value := toString s.withMonoCode }
  , { name := "scan.externs", value := toString s.externs }
  , { name := "scan.sites", value := toString s.sites.size }
  , { name := "scan.wallMs", value := toString s.wallMs } ]

/-- One family's line of the scan's summary table. Four plain fields: the record is the schema. -/
structure FamilyStat where
  family : String
  constructors : Nat
  caseSites : Nat
  sitesWithDefaultArm : Nat
deriving ToJson

def familyStats (s : Scan) : Array FamilyStat :=
  s.byFamily.map fun (f, fs) =>
    { family := f.toString
    , constructors := (s.families.constructors f).size
    , caseSites := fs.size
    , sitesWithDefaultArm := (fs.filter (·.hasDefault)).size }

/-- The whole scan as JSON: the shape the prototype wrote, plus the attribution and the
absorbed/unreachable split. Hand-written at the top level because the schema is not this record —
`sites` is a *count* while the field is an array, and `site` is that array under another name. -/
def toJson (s : Scan) : Json :=
  Json.mkObj
    [ ("source", Json.str s.source.id)
    , ("constants", Json.num s.constants)
    , ("withMonoCode", Json.num s.withMonoCode)
    , ("externs", Json.num s.externs)
    , ("sites", Json.num s.sites.size)
    , ("wallMs", Json.num s.wallMs)
    , ("byFamily", Lean.toJson s.familyStats)
    , ("site", Json.arr (s.sites.map (Site.toJson s.families))) ]

end Scan

/-! ## 4. The policy -/

/-- What a site is allowed to look like. -/
inductive CaseMode
  /-- No default arm. A default arm is a refusal. Constructors with no alternative at a site with
  no default are *unreachable*, which this mode permits and the row records. -/
  | exhaustive
  /-- A default arm that absorbs exactly `cover`, in the family's declaration order. A constructor
  absorbed but not listed is a refusal (drift); a constructor listed but not absorbed is a refusal
  too (the policy is stale). -/
  | withDefault (cover : Array Name)
deriving Inhabited

namespace CaseMode

def id : CaseMode → String
  | .exhaustive => "exhaustive"
  | .withDefault _ => "default"

def toJson : CaseMode → Json
  | .exhaustive => Json.mkObj [("mode", Json.str "exhaustive")]
  | .withDefault cover =>
    Json.mkObj [("mode", Json.str "default"), ("cover", Json.arr (cover.map fun c => Json.str c.toString))]

end CaseMode

/-- The rule for one function's sites on one family: one `CaseMode` per site, in walk order. -/
structure FunctionRule where
  name : Name
  sites : Array CaseMode
  /-- A free-text reason, for a cover that is a decision rather than a fact. Carried into the
  refusal message so a red row says why the cover was ever granted. -/
  note : Option String := none
deriving Inhabited

/-- What to do with a case site on this family in a function the policy does not name. -/
inductive Unlisted
  /-- Strict: an undeclared site is a refusal. -/
  | refuse
  /-- The site gets an `unresolved` row — the policy did not decide it. Never a pass. -/
  | report
deriving Inhabited, DecidableEq

structure FamilyPolicy where
  name : Name
  unlisted : Unlisted
  functions : Array FunctionRule
deriving Inhabited

structure CasesPolicy where
  families : Array FamilyPolicy
  note : Option String := none
deriving Inhabited

/-! ### 4.1 The reader

Strict throughout (`Conform.Policy`): unknown keys are refusals, a missing required key is a
refusal, and the error carries the JSON path. Exactly one of `mode` and `sites` may appear on a
function; `cover` may appear only with `mode: "default"`, and must appear with it. -/

namespace CasesPolicy

open Conform.Policy

private def readMode (get : String → Option Json) : Policy.Reader CaseMode := do
  let mode ← field get "mode" fun j => enum j [("exhaustive", false), ("default", true)]
  let cover ← field? get "cover" fun j => strings j
  if mode then
    match cover with
    | some cs => pure (.withDefault (cs.map (·.toName)))
    | none => fail "`mode: \"default\"` needs a `cover` (the constructors the default may absorb)"
  else
    match cover with
    | some _ => fail "`cover` is meaningless with `mode: \"exhaustive\"`"
    | none => pure .exhaustive

private def readSiteRule (j : Json) : Policy.Reader CaseMode := do
  let get ← object j ["mode", "cover"]
  readMode get

private def readFunction (j : Json) : Policy.Reader FunctionRule := do
  let get ← object j ["name", "mode", "cover", "sites", "note"]
  let name ← field get "name" Policy.name
  let note ← field? get "note" string
  let sites ← field? get "sites" fun s => array s readSiteRule
  match sites, get "mode" with
  | some _, some _ => fail "a function gives either `mode` (one site) or `sites` (a list), not both"
  | some ss, none =>
    if ss.isEmpty then fail "`sites` is empty: a function with no site is not a rule, remove it"
    else pure { name, sites := ss, note }
  | none, some _ => pure { name, sites := #[← readMode get], note }
  | none, none => fail "a function needs `mode` (one site) or `sites` (a list of them)"

private def readFamily (j : Json) : Policy.Reader FamilyPolicy := do
  let get ← object j ["name", "unlisted", "functions"]
  let name ← field get "name" Policy.name
  let unlisted ← field get "unlisted" fun u =>
    enum u [("refuse", Unlisted.refuse), ("report", Unlisted.report)]
  let functions ← field get "functions" fun f => array f readFunction
  let mut seen : Std.HashSet Name := {}
  for fn in functions do
    let (dup, seen') := seen.containsThenInsert fn.name
    if dup then fail s!"function `{fn.name}` is listed twice under family `{name}`"
    seen := seen'
  return { name, unlisted, functions }

def read (j : Json) : Policy.Reader CasesPolicy := do
  let get ← object j ["families", "note"]
  let note ← field? get "note" string
  let families ← field get "families" fun f => array f readFamily
  let mut seen : Std.HashSet Name := {}
  for fam in families do
    let (dup, seen') := seen.containsThenInsert fam.name
    if dup then fail s!"family `{fam.name}` is listed twice"
    seen := seen'
  return { families, note }

def load (file : System.FilePath) : IO CasesPolicy := Policy.load file read

/-- The families the policy decides, in its own order: what a scan configured *from* the policy
audits. -/
def familyNames (p : CasesPolicy) : Array Name := p.families.map (·.name)

def toJson (p : CasesPolicy) : Json :=
  Json.mkObj
    [ ("families", Json.arr (p.families.map fun f =>
        Json.mkObj
          [ ("name", Json.str f.name.toString)
          , ("unlisted", Json.str (match f.unlisted with | .refuse => "refuse" | .report => "report"))
          , ("functions", Json.arr (f.functions.map fun fn =>
              let base : List (String × Json) :=
                [("name", Json.str fn.name.toString)]
              let body : List (String × Json) :=
                if h : fn.sites.size = 1 then
                  match (fn.sites[0]'(by omega)) with
                  | .exhaustive => [("mode", Json.str "exhaustive")]
                  | .withDefault cover =>
                    [ ("mode", Json.str "default")
                    , ("cover", Json.arr (cover.map fun c => Json.str c.toString)) ]
                else [("sites", Json.arr (fn.sites.map CaseMode.toJson))]
              let tail : List (String × Json) :=
                match fn.note with | some n => [("note", Json.str n)] | none => []
              Json.mkObj (base ++ body ++ tail))) ])) ]

end CasesPolicy

/-! ## 5. The check -/

/-- The `lcnf.cases.stale` row's detail. Four plain fields and no computation: the record **is**
the schema, so the encoder is `deriving ToJson` rather than a hand `Json.mkObj`. (`Site.toJson`
and `Scan.toJson` are not like this — see their notes.) -/
private structure StaleDetail where
  family : String
  decl : String
  rules : Nat
  sitesFound : Nat
deriving ToJson

private def names (cs : Array Name) : String :=
  if cs.isEmpty then "none" else ", ".intercalate (cs.toList.map (·.toString))

/-- Set equality on constructor lists, order-insensitive (the report prints both in the family's
declaration order, so a reader still sees an order). -/
private def sameSet (a b : Array Name) : Bool :=
  a.size == b.size && a.all (b.contains ·) && b.all (a.contains ·)

private def missingFrom (a b : Array Name) : Array Name := a.filter fun x => !b.contains x

/-- One row per site. The check id is `lcnf.cases.<mode>` for a decided site,
`lcnf.cases.unlisted` for one the policy does not name. -/
private def rowForSite (t : FamilyTable) (fam : FamilyPolicy) (s : Site)
    (rule? : Option (FunctionRule × Option CaseMode)) : Row :=
  let detail := Site.toJson t s
  match rule? with
  | none =>
    match fam.unlisted with
    | .refuse =>
      Row.refused "lcnf.cases.unlisted" s.subject
        s!"the policy for `{fam.name}` does not name `{s.decl}`; \
           this case site {if s.hasDefault then s!"has a default arm absorbing {names (s.absorbed t)}" else "is exhaustive"}"
        detail
    | .report =>
      Row.unresolved "lcnf.cases.unlisted" s.subject
        s!"the policy for `{fam.name}` does not decide `{s.decl}`" detail
  | some (fn, none) =>
    Row.refused "lcnf.cases.extraSite" s.subject
      s!"`{fn.name}` has more case sites on `{fam.name}` than the policy rules for it \
         ({fn.sites.size}); this is site #{s.ordinal}" detail
  | some (fn, some mode) =>
    let why := match fn.note with | some n => s!" (policy note: {n})" | none => ""
    match mode with
    | .exhaustive =>
      if s.hasDefault then
        Row.counterexample "lcnf.cases.exhaustive" s.subject
          s!"`{s.decl}` is declared exhaustive on `{fam.name}`, but the compiled code has a \
             default arm absorbing {names (s.absorbed t)}{why}" detail
      else
        Row.pass "lcnf.cases.exhaustive" s.subject .tested
          s!"`{s.decl}` has no default arm on `{fam.name}`; \
             {s.named.size} named, {(s.unreachable t).size} unreachable" detail
    | .withDefault cover =>
      let unknown := missingFrom cover (t.constructors s.family)
      if !unknown.isEmpty then
        Row.refused "lcnf.cases.default" s.subject
          s!"the cover for `{s.decl}` names {names unknown}, not {"constructor" ++ (if unknown.size == 1 then "" else "s")} of `{fam.name}`" detail
      else if !s.hasDefault then
        Row.refused "lcnf.cases.default" s.subject
          s!"the policy gives `{s.decl}` a default cover on `{fam.name}`, but the compiled code \
             has no default arm; the rule is stale{why}" detail
      else
        let absorbed := s.absorbed t
        if sameSet absorbed cover then
          Row.pass "lcnf.cases.default" s.subject .tested
            s!"`{s.decl}`'s default arm on `{fam.name}` absorbs exactly the covered \
               {names cover}{why}" detail
        else
          let extra := missingFrom absorbed cover
          let stale := missingFrom cover absorbed
          Row.counterexample "lcnf.cases.default" s.subject
            (s!"`{s.decl}`'s default arm on `{fam.name}` does not match its cover: " ++
             (if extra.isEmpty then "" else s!"absorbed but not covered: {names extra}. ") ++
             (if stale.isEmpty then "" else s!"covered but no longer absorbed (stale policy): {names stale}. ") ++
             s!"absorbed = {names absorbed}, cover = {names cover}{why}")
            detail

/-- Run the policy against a scan. Every site of every family the policy names gets a row, and
every rule with no site gets one; `expected` is their sum, so `Report.complete` fails if a subject
is dropped. Sites on a family the policy does **not** name are not this check's business — the
driver configures the scan from the policy, so that set is empty by construction. -/
def check (s : Scan) (p : CasesPolicy) : Array Row × Nat := Id.run do
  let mut rows : Array Row := #[]
  let mut expected := 0
  for fam in p.families do
    let famSites := s.sites.filter fun st => st.family == fam.name
    -- The two lookups this loop needs, as maps built once per family rather than as a linear
    -- search per site (`CasesPolicy.readFamily` already refuses a duplicate function name, so
    -- "last insert wins" and "first match wins" are the same rule here).
    let byName : Std.HashMap Name FunctionRule :=
      fam.functions.foldl (init := {}) fun m fn => m.insert fn.name fn
    let siteCount : Std.HashMap Name Nat :=
      famSites.foldl (init := {}) fun m st => m.insert st.decl (m.getD st.decl 0 + 1)
    -- sites, in scan order
    for site in famSites do
      expected := expected + 1
      let paired : Option (FunctionRule × Option CaseMode) :=
        byName[site.decl]?.map fun fn => (fn, fn.sites[site.ordinal]?)
      rows := rows.push (rowForSite s.families fam site paired)
    -- rules with no site: a stale policy, one row each
    for fn in fam.functions do
      let found := siteCount.getD fn.name 0
      for i in [found:fn.sites.size] do
        expected := expected + 1
        let subject : Subject :=
          { kind := "caseSite", path := [fam.name.toString, fn.name.toString, toString i] }
        rows := rows.push <| Row.refused "lcnf.cases.stale" subject
          (if found == 0 then
            s!"the policy decides `{fn.name}` on `{fam.name}`, but the scan found no case site \
               there: the function is gone, was renamed, or no longer matches on this family"
           else
            s!"the policy gives `{fn.name}` {fn.sites.size} case sites on `{fam.name}`, the scan \
               found {found}")
          (toJson (α := StaleDetail)
            { family := fam.name.toString, decl := fn.name.toString
            , rules := fn.sites.size, sitesFound := found })
  return (rows, expected)

/-- Plan the exact check/subject identities from scan and policy, without evaluating verdicts. -/
def required (s : Scan) (p : CasesPolicy) : Array CheckId := Id.run do
  let mut ids := #[]
  for fam in p.families do
    let sites := s.sites.filter (·.family == fam.name)
    for site in sites do
      let check := match fam.functions.find? (·.name == site.decl) with
        | none => "lcnf.cases.unlisted"
        | some fn => match fn.sites[site.ordinal]? with
          | none => "lcnf.cases.extraSite"
          | some .exhaustive => "lcnf.cases.exhaustive"
          | some (.withDefault _) => "lcnf.cases.default"
      ids := ids.push ⟨check, site.subject⟩
    for fn in fam.functions do
      let found := (sites.filter (·.decl == fn.name)).size
      for i in [found:fn.sites.size] do
        ids := ids.push ⟨"lcnf.cases.stale",
          ⟨"caseSite", [fam.name.toString, fn.name.toString, toString i]⟩⟩
  return ids

/-! ## 6. Seeding

A policy that says what the tree does *today* is a pin, not a proof: it is what makes tomorrow's
drift visible. `seed` writes exactly that policy from a scan, so the initial file is measured
rather than typed, and every later edit to it is a diff a human signed. Constructor covers come
out in the family's declaration order. -/

def seed (s : Scan) (unlisted : Unlisted := .refuse) : CasesPolicy :=
  { note := some "seeded from a measured scan; every cover is a decision, not a fix"
  , families := s.families.order.map fun f =>
      -- one pass: the declarations in first-appearance order, and each one's modes in walk order
      let (decls, modes) :=
        (s.sites.filter fun st => st.family == f).foldl
          (init := ((#[] : Array Name), (∅ : Std.HashMap Name (Array CaseMode))))
          fun (decls, modes) st =>
            let mode :=
              if st.hasDefault then CaseMode.withDefault (st.absorbed s.families)
              else CaseMode.exhaustive
            ( if modes.contains st.decl then decls else decls.push st.decl
            , modes.insert st.decl ((modes.getD st.decl #[]).push mode) )
      { name := f
      , unlisted
      , functions := decls.map fun d => { name := d, sites := modes.getD d #[], note := none } } }

end Conform.Lcnf
