import Lean
import OCaml5.Lcnf.Naming

/-!
# OCaml5.Lcnf.Export

**What it is.** The root recipe (`ocaml/gen/roots.json`, format v3) read as a typed export plan:
every root of every artifact in exactly one export class (Codex's R6.1, step 1; ruling D-11 of the
OCaml estate plan, `docs/research/2026-10-17-ocaml-estate-review/plan.md`). The plan says which
facades re-export each root, and the plan checker refuses a recipe whose classes contradict each
other before any artifact is made.

| class | who calls it | the artifact's interface | the public facade |
| --- | --- | --- | --- |
| `public` | any client: a public promise | exports it | re-exports it |
| `linkage` | hand code outside the artifact (the engine, the kit, a lane's test) | exports it | no |
| `coverage` | nothing outside: translated so the route covers its closure | hides it | no |
| `internal` | only the artifact's own code (its prelude) | hides it | no |

A root's identity includes its artifact: the same Lean name in two artifacts is two specialised
nodes (R6.1: "Specialization ... remain part of a node's identity"), so `Effect4.Api.run` may be
public in `Api_gen` and linkage in `Api_engine`, unless one artifact uses the other (below).
Within one artifact a root has one class.

**Consumers (R6.1, step 3).** An artifact may serve several consumers, each through a facade of
its own: the entry's `consumers` list names each facade's file and the `linkage` roots it
re-exports. The artifact is one closure of all its consumers' roots, so the consumers share every
node they both reach, and a facade is a view of that closure, not a second copy. A consumer's root
is a `linkage` root of the artifact whose consumers are the artifact and that facade. A root two
consumers name is one root with both facades among its consumers. The test lanes are such
consumers of one artifact (`ocaml/gen/api_gen.ml`); see `OCaml5.Lcnf.Gen`.

**Scopes (D1).** An artifact may compile its closure in a unit of its own (`closure`), so that
its `out` unit is a facade over it, and the nodes only its consumers reach in a second unit
(`tests`), which includes the closure; the consumers' facades include the tests unit. A
consumer's root is then exported by the tests unit's interface, not by `out`'s: its consumers are
the tests unit and the facade. A root the entry lists itself stays exported by `out` when a
consumer names it too. `tests` needs `closure` and at least one consumer.

**Uses (4b, decisions row 428 (5)).** An artifact may name the artifacts it uses (`uses`, each by
its module and its output, as `open` names the type owner). Its walk stops at every declaration
that a used artifact's walk lowers, and writes that artifact's binding by its module
(`OCaml5.Lcnf.Gen`, `--use`), so a Lean declaration is lowered into one artifact. A root both
list is one node, lowered in the used artifact, with a class in each, and the user binds it by
name. A use names an earlier artifact, which the user walks as that artifact walks itself. So
both lower flat, and the used artifact is one unit that walks its own roots, over its user's type
owner and within its user's cap (`unusableWhy`).

**Depends on.** `Lean.Json`, `Lean.Name`, `OCaml5.Lcnf.Naming` (`capital`, for a unit's module name).

**Properties.**
* **One class per root.** A root listed under two classes of one artifact is refused, naming the
  root and both classes; a root listed twice under one class is refused as a duplicate. Nothing is
  resolved by order — *tested* (the controls below).
* **One public implementation.** A public root lives in one artifact, and every public root lives in
  the same one, so the facade has one implementation unit — *tested*.
* **A misspelt class hides nothing.** An entry key that is neither an option nor a class is
  refused — *tested*.
* **`facade_resolves` and `public_excludes_coverage` are finite checks.** `check` evaluates both
  on the whole plan and refuses a plan where either fails. They are checks of this table, not
  theorems about the lowering — *tested*, each with a red control.
* **A consumer re-exports only `linkage` roots, and every unit has one name.** A consumer key other
  than `out` and `linkage` is refused, a facade's unit name may not repeat an artifact's or another
  facade's, and a consumer's root keeps the one-class rule — *tested*.
* **The scopes are named together.** An entry's `tests` unit needs its `closure` unit and a
  consumer, every unit name stays unique across `out`, `closure`, `tests`, the consumers and the
  public facade, and with a tests unit a consumer's root is no root of `out`'s interface —
  *tested*.
* **A use names one flat walk.** The checker refuses a use of no earlier artifact, a use under a
  module that is not its artifact's unit, and a use with a misspelt key. A use across two profiles
  is refused too, naming a root both list with its class in each. So is a used artifact that its
  user cannot walk as it walks itself — *tested*.
-/

namespace OCaml5.Lcnf.Export

open Lean

/-- What a root of the recipe is for: the four export classes of ruling D-11. -/
inductive ExportClass where
  /-- A public promise: the artifact's interface and the public facade export it. -/
  | «public»
  /-- Hand code outside the artifact calls it: the artifact's interface exports it; no facade does. -/
  | linkage
  /-- Translated so that the route keeps covering its closure; nothing outside calls it. -/
  | coverage
  /-- Only the artifact's own code calls it (its prelude); hidden. -/
  | internal
deriving DecidableEq, Repr, Inhabited

namespace ExportClass

/-- The recipe key that lists a class's roots. -/
def key : ExportClass → String
  | .«public» => "public"
  | .linkage => "linkage"
  | .coverage => "coverage"
  | .internal => "internal"

/-- The four classes, in the order a recipe entry's roots are translated. -/
def all : List ExportClass := [.«public», .linkage, .internal, .coverage]

/-- Whether the artifact's own interface exports a root of the class. -/
def exported : ExportClass → Bool
  | .«public» | .linkage => true
  | .coverage | .internal => false

end ExportClass

/-- One root of the plan. -/
structure ExportRoot where
  /-- The Lean declaration. -/
  source : Name
  cls : ExportClass
  /-- The artifact whose closure emits it, by its OCaml module (`Api_gen`): part of the node's
  identity. -/
  unit : String
  /-- The facades that re-export it: the artifact's own interface for an exported class, and the
  public facade for a public root. A consumer that is no facade sees nothing. -/
  consumers : List String
deriving Repr, Inhabited

/-- One artifact another uses (an entry's `uses`): the user's unit, and the used artifact's module
and output, as the recipe names them (`Api_gen` uses `Eff_image`, `ocaml/eff/eff_image.ml`). -/
structure Use where
  user : String
  unit : String
  artifact : String
deriving Repr, Inhabited, BEq

/-- The typed recipe: the roots of every artifact, each in one class, and the public facade's
module. -/
structure ExportPlan where
  /-- The public facade's OCaml module (`Effect4`): the consumer of every public root. -/
  facadeModule : String
  roots : List ExportRoot
  /-- Each artifact that compiles its consumers' nodes in a tests unit of their own: its unit and
  that tests unit's module (`("Api_gen", "Lanes_gen")`). -/
  tests : List (String × String) := []
  /-- Each use of one artifact by a later one, in recipe order. -/
  uses : List Use := []
deriving Repr, Inhabited

namespace ExportPlan

/-- The roots a consumer may see: those whose consumers name it (R6.1's `rootsFor`). -/
def rootsFor (p : ExportPlan) (consumer : String) : List Name :=
  (p.roots.filter (·.consumers.contains consumer)).map (·.source)

/-- The public roots, in plan order (R6.1's `publicRoots`). -/
def publicRoots (p : ExportPlan) : List Name :=
  (p.roots.filter (·.cls == .«public»)).map (·.source)

/-- Every consumer the plan names. -/
def consumers (p : ExportPlan) : List String :=
  (p.roots.flatMap (·.consumers)).eraseDups

/-- A consumer's facade: one row per root it may see, the name a client writes and the canonical
declaration it resolves to (R6.1's `facade`). `client` spells the client's name; step 1 writes no
alias, so the artifact facades use the Lean name itself, and the public facade's paths come from
`OCaml5.Lcnf.publicName`. -/
def facade (p : ExportPlan) (consumer : String) (client : Name → Name := id) : List (Name × Name) :=
  (p.rootsFor consumer).map fun n => (client n, n)

/-- A root classified `coverage` and never `public` (R6.1's `OnlyCoverage`). -/
def onlyCoverage (p : ExportPlan) (n : Name) : Bool :=
  p.roots.any (fun r => r.source == n && r.cls == .coverage)
    && !p.roots.any (fun r => r.source == n && r.cls == .«public»)

/-- The roots one consumer's facade does not resolve to themselves under a client spelling. -/
def unresolvedAt (p : ExportPlan) (consumer : String) (client : Name → Name := id) : List Name :=
  (p.rootsFor consumer).filter fun n => (p.facade consumer client).lookup (client n) != some n

/-- The roots a consumer's facade does not resolve to themselves, each with its consumer. -/
def unresolved (p : ExportPlan) (client : Name → Name := id) : List (String × Name) :=
  p.consumers.flatMap fun c => (p.unresolvedAt c client).map (c, ·)

/-- `facade_resolves` (R6.1) as a finite check of the plan: every root a consumer may see is a row of
its facade that resolves to the root itself. -/
def facadeResolves (p : ExportPlan) (client : Name → Name := id) : Bool :=
  (p.unresolved client).isEmpty

/-- The coverage-only roots that reach the public facade. -/
def coverageInFacade (p : ExportPlan) : List Name :=
  ((p.rootsFor p.facadeModule).filter p.onlyCoverage).eraseDups

/-- `public_excludes_coverage` (R6.1) as a finite check of the plan: no root classified `coverage`
and never `public` is a root of the public facade. -/
def publicExcludesCoverage (p : ExportPlan) : Bool :=
  p.coverageInFacade.isEmpty

end ExportPlan

/-- Why the plan checker refuses a recipe. Each refusal names what it refuses. -/
inductive PlanRefusal where
  /-- The recipe is no v3 recipe, or an entry is malformed. -/
  | malformed (why : String)
  /-- An entry key that is neither an option nor an export class. -/
  | unknownKey (unit key : String)
  /-- One artifact lists a root under two classes. -/
  | contradictory (unit : String) (source : Name) (first second : ExportClass)
  /-- One artifact lists a root twice under one class. -/
  | duplicate (unit : String) (source : Name) (cls : ExportClass)
  /-- Two artifacts make one root public: the public facade would have two implementations. -/
  | publicTwice (source : Name) (first second : String)
  /-- Public roots in two artifacts: the public facade has one implementation unit. -/
  | publicSplit (first second : String)
  /-- A nominal root that the artifact's interface does not export. -/
  | nominalHidden (unit : String) (source : Name)
  /-- A consumer's facade that does not resolve one of its roots to itself (`facade_resolves`). -/
  | unresolved (consumer : String) (source : Name)
  /-- A coverage-only root that reaches the public facade (`public_excludes_coverage`). -/
  | coverageInFacade (source : Name)
  /-- An artifact uses one that is no earlier artifact of the recipe. -/
  | useUnknown (user artifact : String)
  /-- A use names a module that is not its artifact's unit. -/
  | useModule (user unit artifact : String)
  /-- A used artifact and its user lower over two profiles, so a root both list is two specialised
  nodes: of class `first` in the user and `second` in the used artifact. -/
  | specialisedTwice (user used : String) (source : Name) (first second : ExportClass)
  /-- A used artifact that is no flat walk of its own roots, over its user's type owner and within
  its user's cap: the user could not walk it as it walks itself. -/
  | unusable (user used why : String)
deriving Repr, Inhabited, BEq

/-- The refusal as one line of the generator's report. -/
def PlanRefusal.message : PlanRefusal → String
  | .malformed why => s!"export plan: {why}"
  | .unknownKey u k => s!"export plan: {u}: `{k}` is neither an option nor an export class"
  | .contradictory u n a b =>
    s!"export plan: {u}: {n} is in two classes, `{a.key}` and `{b.key}`; give it one"
  | .duplicate u n c => s!"export plan: {u}: {n} is listed twice under `{c.key}`"
  | .publicTwice n a b => s!"export plan: {n} is public in {a} and in {b}; one artifact implements it"
  | .publicSplit a b =>
    s!"export plan: public roots in {a} and in {b}; the public facade has one implementation artifact"
  | .nominalHidden u n => s!"export plan: {u}: nominal root {n} is not exported (public or linkage)"
  | .unresolved c n => s!"export plan: the facade of {c} does not resolve {n} to itself (facade_resolves)"
  | .coverageInFacade n =>
    s!"export plan: coverage root {n} reaches the public facade (public_excludes_coverage)"
  | .useUnknown u a => s!"export plan: {u} uses {a}, which is no earlier artifact of the recipe"
  | .useModule u m a => s!"export plan: {u} uses {a} as the module {m}, which is not that artifact's unit"
  | .specialisedTwice u v n a b =>
    s!"export plan: {u} uses {v}, which lowers over another profile: {n} would be `{a.key}` in {u} \
      and `{b.key}` in {v}, two specialised nodes; keep the two artifacts apart"
  | .unusable u v why => s!"export plan: {u} uses {v}, which {why}"

/-- The refusals the plan checker finds, in plan order: one class per root of an artifact, every
public root in one artifact, then the two finite checks. Empty means the plan is admitted. -/
def ExportPlan.refusals (p : ExportPlan) : List PlanRefusal := Id.run do
  let mut out : Array PlanRefusal := #[]
  -- one class per (artifact, root): the first listing decides nothing, a second is refused
  let mut seen : Std.HashMap (String × Name) ExportClass := {}
  for r in p.roots do
    match seen[(r.unit, r.source)]? with
    | some c =>
      out := out.push (if c == r.cls then .duplicate r.unit r.source c
                       else .contradictory r.unit r.source c r.cls)
    | none => seen := seen.insert (r.unit, r.source) r.cls
  -- one artifact implements every public root
  let mut owner : Std.HashMap Name String := {}
  let mut publicUnit : Option String := none
  for r in p.roots do
    unless r.cls == .«public» do continue
    match owner[r.source]? with
    | some u => if u != r.unit then out := out.push (.publicTwice r.source u r.unit)
    | none => owner := owner.insert r.source r.unit
    match publicUnit with
    | some u => if u != r.unit then out := out.push (.publicSplit u r.unit)
    | none => publicUnit := some r.unit
  for (c, n) in p.unresolved do out := out.push (.unresolved c n)
  for n in p.coverageInFacade do out := out.push (.coverageInFacade n)
  return out.toList.eraseDups

/-- A plan the checker admitted. The two finite checks travel with it, so every facade the
generator writes comes from a plan where both hold. -/
structure CheckedPlan where
  plan : ExportPlan
  resolves : plan.facadeResolves = true
  excludes : plan.publicExcludesCoverage = true

/-- The plan checker: the first refusal, or the plan with its two finite checks. -/
def ExportPlan.check (p : ExportPlan) : Except PlanRefusal CheckedPlan :=
  match p.refusals with
  | r :: _ => .error r
  | [] =>
    if h₁ : p.facadeResolves = true then
      if h₂ : p.publicExcludesCoverage = true then .ok ⟨p, h₁, h₂⟩
      else .error (.malformed "public_excludes_coverage failed with no refusal named")
    else .error (.malformed "facade_resolves failed with no refusal named")

/-! ## Reading the recipe -/

/-- The format of the recipe this module reads. -/
def recipeFormat : String := "effect4-lcnf-roots-v3"

/-- The keys a recipe entry may hold besides the export classes. -/
def entryOptions : List String :=
  ["out", "closure", "tests", "import", "cap", "types", "modules", "nominal", "abstract", "externs",
   "prelude", "open", "consumers", "uses"]

/-- The keys a use of an entry holds: the used artifact's module and its output. -/
def useKeys : List String := ["module", "artifact"]

/-- The keys a consumer of an entry may hold: its facade's file and the roots the facade
re-exports. -/
def consumerKeys : List String := ["out", "linkage"]

/-- The OCaml module of an artifact's output (`ocaml/gen/api_gen.ml` → `Api_gen`): the unit that
names a root's node and the consumer of its exported roots. -/
def unitOf (out : String) : String :=
  capital ((System.FilePath.mk out).fileStem.getD out)

/-- An entry's roots of one class, in the order listed. -/
def rootsOf (entry : Json) (cls : ExportClass) : Except PlanRefusal (List Name) :=
  match entry.getObjVal? cls.key with
  | .error _ => .ok []
  | .ok v => match fromJson? (α := List String) v with
    | .ok xs => .ok (xs.map String.toName)
    | .error e => .error (.malformed s!"`{cls.key}`: {e}")

/-- An entry's consumers, in the order listed, each as its facade's file and its JSON. -/
def consumersOf (entry : Json) : Except PlanRefusal (List (String × Json)) :=
  match entry.getObjVal? "consumers" with
  | .error _ => .ok []
  | .ok (.arr cs) => cs.toList.mapM fun c => match c.getObjValAs? String "out" with
    | .ok o => .ok (o, c)
    | .error e => .error (.malformed s!"a consumer without `out`: {e}")
  | .ok _ => .error (.malformed "`consumers` is no list")

/-- An entry's uses, in the order listed, each as the used artifact's module and output. -/
def usesOf (entry : Json) : Except PlanRefusal (List (String × String)) :=
  match entry.getObjVal? "uses" with
  | .error _ => .ok []
  | .ok (.arr us) => us.toList.mapM fun u => do
    let keys ← match u.getObj? with
      | .ok fs => pure fs.keys
      | .error e => throw (.malformed s!"a use is no object: {e}")
    for k in keys do
      unless useKeys.contains k do throw (.malformed s!"a use holds `{k}`, which is neither `module` nor `artifact`")
    match u.getObjValAs? String "module", u.getObjValAs? String "artifact" with
    | .ok m, .ok a => pure (m, a)
    | _, _ => throw (.malformed "a use names its `module` and its `artifact`")
  | .ok _ => .error (.malformed "`uses` is no list")

/-- Whether an entry lowers flat: no extern table and no prelude, the profile every use links. -/
def lowersFlat (entry : Json) : Bool :=
  !(entry.getObjVal? "externs").isOk && !(entry.getObjVal? "prelude").isOk

/-- Why `used` cannot be used by `user`, or `none`. A user walks a used artifact as that artifact
walks itself (`OCaml5.Lcnf.Gen`, `--use`), so a used artifact is one unit that walks its own roots
and names no type beyond them: not the type owner, no scope or consumer, no requested, sealed or
nominal type, and no use of its own. It opens its user's type owner, so the two spell every
program type alike, and it walks within its user's cap. -/
def unusableWhy (user used : Json) : Option String :=
  let has (k : String) : Bool := (used.getObjVal? k).isOk
  let ownerOf (e : Json) : Option String := (e.getObjVal? "open" >>= (·.getObjValAs? String "module")).toOption
  let capOf (e : Json) : Nat := (e.getObjValAs? Nat "cap").toOption.getD 0
  if has "modules" then some "is the type owner, which `open` names"
  else if has "closure" || has "tests" || has "consumers" then
    some "compiles its walk in more than one unit or serves consumers; a used artifact is one unit"
  else if has "types" || has "abstract" || has "nominal" then
    some "requests types beyond its walk (`types`, `abstract` or `nominal`)"
  else if has "uses" then some "uses an artifact itself; a used artifact links none"
  else if ownerOf used != ownerOf user then some "opens another type owner than its user"
  else if capOf used > capOf user then some "walks at a larger cap than its user"
  else none

/-- `roots` with root `n` of artifact `unit` re-exported by the facade `facade`, as a `linkage`
root. A root the entry lists under another class, or one this facade names twice, is appended
again, so `ExportPlan.refusals` names the contradiction or the duplicate. A root another consumer
or the entry's own `linkage` list names gains this facade as a consumer: one root, one node. A
fresh root is exported by `scope`'s interface: the artifact's own unit, or its tests unit. -/
def addConsumer (unit facade : String) (roots : List ExportRoot) (n : Name)
    (scope : String := unit) : List ExportRoot :=
  let fresh : ExportRoot := { source := n, cls := .linkage, unit := unit, consumers := [scope, facade] }
  match roots.find? (·.source == n) with
  | none => roots ++ [fresh]
  | some r =>
    if r.cls != .linkage || r.consumers.contains facade then roots ++ [fresh]
    else
      let (before, after) := roots.span (·.source != n)
      before ++ ({ r with consumers := r.consumers ++ [facade] } :: after.drop 1)

/-- The roots of one recipe entry, class by class (`ExportClass.all`), each with its consumers,
then its consumers' roots (`consumersOf`, `addConsumer`). -/
def entryRoots (facade : String) (entry : Json) : Except PlanRefusal (List ExportRoot) := do
  let out ← match entry.getObjValAs? String "out" with
    | .ok o => pure o
    | .error e => throw (.malformed s!"an artifact without `out`: {e}")
  let unit := unitOf out
  let fields ← match entry.getObj? with
    | .ok f => pure f
    | .error e => throw (.malformed s!"{out}: {e}")
  for key in fields.keys do
    unless entryOptions.contains key || ExportClass.all.any (·.key == key) do
      throw (.unknownKey unit key)
  -- the tests unit includes the closure unit and holds the consumers' nodes: both are needed
  let scope ← match entry.getObjValAs? String "tests" with
    | .error _ => pure unit
    | .ok tests => do
      unless (entry.getObjValAs? String "closure").isOk do
        throw (.malformed s!"{out}: `tests` includes the artifact's `closure`, which the entry does not name")
      unless ((← consumersOf entry).length > 0) do
        throw (.malformed s!"{out}: `tests` holds the nodes only consumers reach, and the entry has no consumer")
      pure (unitOf tests)
  let mut roots : List ExportRoot := []
  for cls in ExportClass.all do
    let consumers := (if cls == .«public» then [facade] else []) ++ (if cls.exported then [unit] else [])
    for n in ← rootsOf entry cls do
      roots := roots ++ [{ source := n, cls := cls, unit := unit, consumers := consumers }]
  -- each consumer's facade re-exports its `linkage` roots of this artifact, and nothing else
  for (consumerOut, consumer) in ← consumersOf entry do
    let f := unitOf consumerOut
    let keys ← match consumer.getObj? with
      | .ok fs => pure fs.keys
      | .error e => throw (.malformed s!"{out}: consumer {consumerOut}: {e}")
    for key in keys do
      unless consumerKeys.contains key do throw (.unknownKey f key)
    for n in ← rootsOf consumer .linkage do
      roots := addConsumer unit f roots n scope
  -- a nominal root keeps its source type in the interface, so the interface must export it
  let nominal := ((entry.getObjValAs? (List String) "nominal").toOption.getD []).map String.toName
  for n in nominal do
    unless roots.any (fun r => r.source == n && r.cls.exported) do
      throw (.nominalHidden unit n)
  return roots

/-- The recipe as a plan, unchecked. The public facade's module is the recipe's `facade.module`. -/
def ExportPlan.ofRecipe (recipe : Json) : Except PlanRefusal ExportPlan := do
  let format ← match recipe.getObjValAs? String "format" with
    | .ok f => pure f
    | .error e => throw (.malformed s!"no format: {e}")
  unless format == recipeFormat do
    throw (.malformed s!"unsupported recipe format {format}; this generator reads {recipeFormat}")
  let facade ← match recipe.getObjVal? "facade" >>= (·.getObjValAs? String "module") with
    | .ok m => pure m
    | .error e => throw (.malformed s!"no `facade.module`: {e}")
  let entries ← match recipe.getObjValAs? (Array Json) "artifacts" with
    | .ok es => pure es
    | .error e => throw (.malformed s!"no artifacts: {e}")
  -- every unit has one name: the artifacts, their closure and tests units, their consumers'
  -- facades and the public facade
  let scopeUnits (e : Json) : List String :=
    ["out", "closure", "tests"].filterMap fun k => (e.getObjValAs? String k).toOption.map unitOf
  let mut units := entries.toList.flatMap scopeUnits
  for e in entries do units := units ++ (← consumersOf e).map (unitOf ·.1)
  units := units ++ [facade]
  unless units.eraseDups.length == units.length do
    throw (.malformed s!"two artifacts share one unit name: {units}")
  let mut roots : List ExportRoot := []
  for e in entries do roots := roots ++ (← entryRoots facade e)
  let tests := entries.toList.filterMap fun e =>
    match e.getObjValAs? String "out", e.getObjValAs? String "tests" with
    | .ok o, .ok t => some (unitOf o, unitOf t)
    | _, _ => none
  -- the uses: each names an earlier artifact by its module and its output; the two lower flat, and
  -- the used one is a walk of its own roots that its user can walk as it walks itself
  let outOf (e : Json) : String := (e.getObjValAs? String "out").toOption.getD ""
  let mut uses : List Use := []
  for i in [:entries.size] do
    let e := entries[i]!
    let user := unitOf (outOf e)
    for (m, a) in ← usesOf e do
      let some j := (entries.findIdx? (outOf · == a)).filter (· < i)
        | throw (.useUnknown user a)
      unless unitOf a == m do throw (.useModule user m a)
      if uses.any (fun u => u.user == user && u.artifact == a) then
        throw (.malformed s!"{user} uses {a} twice")
      let used := entries[j]!
      -- a root both list, lowered over two profiles, would be two specialised nodes: named
      unless lowersFlat e && lowersFlat used do
        let shared := (roots.filter (·.unit == user)).findSome? fun r =>
          (roots.find? fun s => s.unit == m && s.source == r.source).map fun s => (r.source, r.cls, s.cls)
        match shared with
        | some (n, mine, theirs) => throw (.specialisedTwice user m n mine theirs)
        | none => throw (.unusable user m
            "lowers over another profile than its user (an extern table or a prelude); a use links flat units")
      unless roots.any (·.unit == m) do throw (.unusable user m "has no roots")
      if let some why := unusableWhy e used then throw (.unusable user m why)
      uses := uses ++ [{ user := user, unit := m, artifact := a }]
  return { facadeModule := facade, roots := roots, tests := tests, uses := uses }

/-- The recipe read and checked: what the generator makes artifacts from. -/
def readChecked (recipe : Json) : Except PlanRefusal CheckedPlan := do
  (← ExportPlan.ofRecipe recipe).check

/-- An artifact's roots of one class, in the order its entry lists them. -/
def CheckedPlan.rootsOf (p : CheckedPlan) (unit : String) (cls : ExportClass) : List Name :=
  (p.plan.roots.filter fun r => r.unit == unit && r.cls == cls).map (·.source)

/-- An artifact's own roots of one class: those no consumer's facade re-exports. A root that both
the entry's `linkage` list and a consumer name is the consumer's (`consumerRoots`), and the
artifact's interface exports it either way. With a tests unit the artifact's interface exports
only its own roots, so a root its entry lists stays its own when a consumer names it too: an
exported root is own when the artifact's unit is among its consumers. -/
def CheckedPlan.ownRootsOf (p : CheckedPlan) (unit : String) (cls : ExportClass) : List Name :=
  let withTests := (p.plan.tests.lookup unit).isSome
  (p.plan.roots.filter fun r => r.unit == unit && r.cls == cls
    && (if withTests then !cls.exported || r.consumers.contains unit
        else r.consumers.all (fun c => c == unit || c == p.plan.facadeModule))).map (·.source)

/-- The roots a consumer's facade re-exports from an artifact, in plan order. -/
def CheckedPlan.consumerRoots (p : CheckedPlan) (unit facade : String) : List Name :=
  (p.plan.roots.filter fun r => r.unit == unit && r.consumers.contains facade).map (·.source)

/-- The artifacts one artifact uses, in the order its entry lists them: each used artifact's
module and output. -/
def CheckedPlan.usesOf (p : CheckedPlan) (unit : String) : List (String × String) :=
  (p.plan.uses.filter (·.user == unit)).map fun u => (u.unit, u.artifact)

/-- An artifact's own roots in the order its walk starts from them, class by class
(`ExportClass.all`): what a user of the artifact walks to reach what it lowers. -/
def CheckedPlan.walkRootsOf (p : CheckedPlan) (unit : String) : List Name :=
  ExportClass.all.flatMap (p.ownRootsOf unit ·)

/-! ## Controls

Each property of the header, positive and red. A recipe is written as JSON text and read by the
same reader the generator uses. -/

private def recipe (entries : String) : Json :=
  (Json.parse ("{\"format\": \"effect4-lcnf-roots-v3\", \"facade\": {\"module\": \"Effect4\"}, \
    \"artifacts\": [" ++ entries ++ "]}")).toOption.getD Json.null

private def refusalOf (j : Json) : Option PlanRefusal :=
  match readChecked j with
  | .ok _ => none
  | .error r => some r

-- a clean recipe: a public, a linkage, a coverage and an internal root of one artifact, and the
-- same Lean name public in one artifact and linkage in another (two specialised nodes)
private def clean : Json := recipe
  "{\"out\": \"a/api_gen.ml\", \"public\": [\"A.run\"], \"linkage\": [\"A.load\"], \
    \"coverage\": [\"M.step\"], \"internal\": [\"M.make\"]}, \
   {\"out\": \"b/api_engine.ml\", \"linkage\": [\"A.run\"], \"coverage\": [\"M.step\"]}"
#guard (refusalOf clean).isNone
#guard match readChecked clean with
  | .ok p => p.plan.rootsFor "Effect4" == [`A.run] && p.plan.rootsFor "Api_gen" == [`A.run, `A.load]
      && p.plan.rootsFor "Api_engine" == [`A.run] && p.plan.publicRoots == [`A.run]
      && p.rootsOf "Api_gen" .internal == [`M.make]
  | .error _ => false
-- one class per root: two classes in one artifact are refused, naming both; nothing wins by order
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"public\": [\"A.run\"], \"coverage\": [\"A.run\"]}") with
  | some (.contradictory u n a b) => u == "Api_gen" && n == `A.run && a == .«public» && b == .coverage
  | _ => false
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"linkage\": [\"A.run\", \"A.run\"]}") with
  | some (.duplicate u n c) => u == "Api_gen" && n == `A.run && c == .linkage
  | _ => false
-- one public implementation: one root public twice, or public roots in two artifacts
#guard match refusalOf (recipe "{\"out\": \"a/one.ml\", \"public\": [\"A.run\"]}, \
    {\"out\": \"b/two.ml\", \"public\": [\"A.run\"]}") with
  | some (.publicTwice n a b) => n == `A.run && a == "One" && b == "Two"
  | _ => false
#guard match refusalOf (recipe "{\"out\": \"a/one.ml\", \"public\": [\"A.run\"]}, \
    {\"out\": \"b/two.ml\", \"public\": [\"A.load\"]}") with
  | some (.publicSplit a b) => a == "One" && b == "Two"
  | _ => false
-- a misspelt class hides nothing, and a hidden nominal root is refused
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"publik\": [\"A.run\"]}") with
  | some (.unknownKey u k) => u == "Api_gen" && k == "publik"
  | _ => false
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"coverage\": [\"A.run\"], \"nominal\": [\"A.run\"]}") with
  | some (.nominalHidden u n) => u == "Api_gen" && n == `A.run
  | _ => false

-- Consumers (R6.1, step 3): one artifact, two facades. Each facade sees its own roots, the
-- artifact's interface exports both sets, and a root both consumers name is one root with both
-- facades among its consumers. The public facade sees none of them.
private def lanes (consumers : String) : Json := recipe
  ("{\"out\": \"a/api_gen.ml\", \"public\": [\"A.run\"]}, {\"out\": \"t/lanes_gen.ml\", " ++
    "\"consumers\": [" ++ consumers ++ "]}")
private def twoLanes : Json := lanes
  "{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\", \"S.image\"]}, \
   {\"out\": \"t/modeled/modeled_gen.ml\", \"linkage\": [\"M.encode\", \"S.image\"]}"
#guard (refusalOf twoLanes).isNone
#guard match readChecked twoLanes with
  | .ok p => p.plan.rootsFor "Todo_gen" == [`T.serve, `S.image]
      && p.plan.rootsFor "Modeled_gen" == [`S.image, `M.encode]
      && p.plan.rootsFor "Lanes_gen" == [`T.serve, `S.image, `M.encode]
      && p.plan.rootsFor "Effect4" == [`A.run]
      && p.consumerRoots "Lanes_gen" "Modeled_gen" == [`S.image, `M.encode]
      && p.ownRootsOf "Lanes_gen" .linkage == []
      && (p.plan.roots.filter (·.source == `S.image)).map (·.consumers)
        == [["Lanes_gen", "Todo_gen", "Modeled_gen"]]
  | .error _ => false
-- red: a consumer re-exports `linkage` roots only, so another key is refused by its facade
#guard match refusalOf (lanes "{\"out\": \"t/todo/todo_gen.ml\", \"public\": [\"T.serve\"]}") with
  | some (.unknownKey u k) => u == "Todo_gen" && k == "public"
  | _ => false
-- red: one consumer naming a root twice, and a consumer root the artifact hides, keep the
-- one-class rule
#guard match refusalOf (lanes "{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\", \"T.serve\"]}") with
  | some (.duplicate u n c) => u == "Lanes_gen" && n == `T.serve && c == .linkage
  | _ => false
#guard match refusalOf (recipe "{\"out\": \"t/lanes_gen.ml\", \"coverage\": [\"T.serve\"], \
    \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\"]}]}") with
  | some (.contradictory u n a b) => u == "Lanes_gen" && n == `T.serve && a == .coverage && b == .linkage
  | _ => false
-- red: a facade may not take an artifact's unit name, or the public facade's
#guard match refusalOf (lanes "{\"out\": \"t/api_gen.ml\", \"linkage\": [\"T.serve\"]}") with
  | some (.malformed _) => true
  | _ => false
#guard match refusalOf (lanes "{\"out\": \"t/effect4.ml\", \"linkage\": [\"T.serve\"]}") with
  | some (.malformed _) => true
  | _ => false
-- an entry's own `linkage` root that a consumer also names is the consumer's
#guard match readChecked (recipe "{\"out\": \"t/lanes_gen.ml\", \"linkage\": [\"T.serve\", \"T.own\"], \
    \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\"]}]}") with
  | .ok p => p.ownRootsOf "Lanes_gen" .linkage == [`T.own]
      && p.consumerRoots "Lanes_gen" "Todo_gen" == [`T.serve]
  | .error _ => false

-- Scopes (D1): with a tests unit, a consumer's root is exported by the tests unit and the facade,
-- not by the artifact's unit; a root the entry lists itself stays its own when a consumer names
-- it too, so the artifact's interface still exports it.
private def scopedEntry (extra : String) : Json := recipe
  ("{\"out\": \"a/api_gen.ml\", \"closure\": \"a/closure_gen.ml\", \"tests\": \"t/lanes_gen.ml\", " ++
    "\"public\": [\"A.run\"], \"linkage\": [\"A.load\"]" ++ extra ++ "}")
private def scopedLanes : Json := scopedEntry
  ", \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\", \"A.load\"]}]"
#guard (refusalOf scopedLanes).isNone
#guard match readChecked scopedLanes with
  | .ok p => p.plan.rootsFor "Api_gen" == [`A.run, `A.load]
      && p.plan.rootsFor "Lanes_gen" == [`T.serve]
      && p.plan.rootsFor "Todo_gen" == [`A.load, `T.serve]
      && p.ownRootsOf "Api_gen" .linkage == [`A.load]
      && p.consumerRoots "Api_gen" "Todo_gen" == [`A.load, `T.serve]
      && p.plan.tests == [("Api_gen", "Lanes_gen")]
  | .error _ => false
-- red: `tests` without the closure it includes, or without a consumer; a tests unit that takes
-- another unit's name
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"tests\": \"t/lanes_gen.ml\", \
    \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\"]}]}") with
  | some (.malformed _) => true
  | _ => false
#guard match refusalOf (scopedEntry "") with
  | some (.malformed _) => true
  | _ => false
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"closure\": \"a/closure_gen.ml\", \
    \"tests\": \"t/closure_gen.ml\", \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\"]}]}") with
  | some (.malformed _) => true
  | _ => false

-- Uses (4b): an artifact links an earlier artifact's lowered declarations. A root both list is one
-- node, lowered in the used artifact, with a class in each; the plan answers which artifacts each
-- one uses, and the used artifact's roots in the order its walk starts from them.
private def ownerSpec : String := "\"open\": {\"module\": \"Eff_types\", \"artifact\": \"e/eff_types.ml\"}"
private def usedImage (rest : String) : Json := recipe
  ("{\"out\": \"e/eff_image.ml\", \"cap\": 300, " ++ ownerSpec ++
    ", \"linkage\": [\"K.enc\", \"K.dec\"], \"coverage\": [\"K.walk\"]}, " ++ rest)
private def userOf (cap : Nat) (uses : String) : String :=
  "{\"out\": \"g/api_gen.ml\", \"cap\": " ++ toString cap ++ ", " ++ ownerSpec ++
    ", \"public\": [\"K.enc\", \"A.run\"], \"uses\": [" ++ uses ++ "]}"
private def imageUse : String := "{\"module\": \"Eff_image\", \"artifact\": \"e/eff_image.ml\"}"
#guard (refusalOf (usedImage (userOf 4000 imageUse))).isNone
#guard match readChecked (usedImage (userOf 4000 imageUse)) with
  | .ok p => p.usesOf "Api_gen" == [("Eff_image", "e/eff_image.ml")] && p.usesOf "Eff_image" == []
      && p.walkRootsOf "Eff_image" == [`K.enc, `K.dec, `K.walk]
      && p.rootsOf "Api_gen" .«public» == [`K.enc, `A.run] && p.rootsOf "Eff_image" .linkage == [`K.enc, `K.dec]
  | .error _ => false
-- red: a use of a later artifact, and a use whose module is not its artifact's unit
#guard match refusalOf (recipe (userOf 4000 imageUse ++ ", {\"out\": \"e/eff_image.ml\", \"linkage\": [\"K.enc\"]}")) with
  | some (.useUnknown u a) => u == "Api_gen" && a == "e/eff_image.ml"
  | _ => false
#guard match refusalOf (usedImage (userOf 4000 "{\"module\": \"Eff_types\", \"artifact\": \"e/eff_image.ml\"}")) with
  | some (.useModule u m a) => u == "Api_gen" && m == "Eff_types" && a == "e/eff_image.ml"
  | _ => false
-- red: a misspelt key of a use hides nothing
#guard match refusalOf (usedImage (userOf 4000 "{\"module\": \"Eff_image\", \"path\": \"e/eff_image.ml\"}")) with
  | some (.malformed _) => true
  | _ => false
-- red: an artifact lowered over another profile is no use; a root both list would be two
-- specialised nodes, named with its class in each artifact
#guard match refusalOf (recipe ("{\"out\": \"e/api_engine.ml\", \"externs\": \"x.txt\", \"linkage\": [\"A.run\"]}, " ++
    "{\"out\": \"g/api_gen.ml\", \"public\": [\"A.run\"], \
      \"uses\": [{\"module\": \"Api_engine\", \"artifact\": \"e/api_engine.ml\"}]}")) with
  | some (.specialisedTwice u v n mine theirs) =>
    u == "Api_gen" && v == "Api_engine" && n == `A.run && mine == .«public» && theirs == .linkage
  | _ => false
-- red: a used artifact its user cannot walk as it walks itself: a larger cap, a scope of its own
#guard match refusalOf (usedImage (userOf 200 imageUse)) with
  | some (.unusable u v _) => u == "Api_gen" && v == "Eff_image"
  | _ => false
#guard match refusalOf (recipe ("{\"out\": \"e/eff_image.ml\", \"closure\": \"e/image_closure.ml\", " ++
    ownerSpec ++ ", \"linkage\": [\"K.enc\"]}, " ++ userOf 4000 imageUse)) with
  | some (.unusable u v _) => u == "Api_gen" && v == "Eff_image"
  | _ => false

-- `public_excludes_coverage`, red: a hand-built plan whose coverage root names the public facade
-- as a consumer (a recipe cannot spell one; C5's per-consumer facades could)
private def leaky : ExportPlan :=
  { facadeModule := "Effect4",
    roots := [{ source := `M.step, cls := .coverage, unit := "Api_gen", consumers := ["Effect4"] }] }
#guard !leaky.publicExcludesCoverage
#guard match leaky.check with
  | .error (.coverageInFacade n) => n == `M.step
  | _ => false
-- a root that is public in some artifact is not coverage-only, so the check stays silent on it
private def shared : ExportPlan :=
  { facadeModule := "Effect4",
    roots := [{ source := `A.run, cls := .«public», unit := "Api_gen", consumers := ["Effect4", "Api_gen"] },
              { source := `A.run, cls := .coverage, unit := "Api_engine", consumers := [] }] }
#guard shared.publicExcludesCoverage

-- `facade_resolves`, red: a client spelling that sends two roots to one name makes the earlier row
-- answer for the later root, so the later root does not resolve to itself
private def two : ExportPlan :=
  { facadeModule := "Effect4",
    roots := [{ source := `A.aB, cls := .«public», unit := "Api_gen", consumers := ["Effect4"] },
              { source := `A.a_b, cls := .«public», unit := "Api_gen", consumers := ["Effect4"] }] }
#guard two.facadeResolves
#guard !two.facadeResolves (fun n => n.getPrefix)
#guard two.unresolved (fun n => n.getPrefix) == [("Effect4", `A.a_b)]

end OCaml5.Lcnf.Export
