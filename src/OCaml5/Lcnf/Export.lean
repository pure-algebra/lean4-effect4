import Lean
import OCaml5.Lcnf.Naming

/-!
# OCaml5.Lcnf.Export

**What it is.** The root recipe (`ocaml/gen/roots.json`, format v3) read as a typed export plan:
every root of every artefact in exactly one export class (Codex's R6.1, step 1; ruling D-11 of the
OCaml estate plan, `docs/research/2026-10-17-ocaml-estate-review/plan.md`). The plan says which
facades re-export each root, and the plan checker refuses a recipe whose classes contradict each
other before any artefact is made.

| class | who calls it | the artefact's interface | the public facade |
| --- | --- | --- | --- |
| `public` | any client: a public promise | exports it | re-exports it |
| `linkage` | hand code outside the artefact (the engine, the kit, a lane's test) | exports it | no |
| `coverage` | nothing outside: translated so the route covers its closure | hides it | no |
| `internal` | only the artefact's own code (its prelude) | hides it | no |

A root's identity includes its artefact: the same Lean name in two artefacts is two specialised
nodes (R6.1: "Specialization ... remain part of a node's identity"), so `Effect4.Api.run` may be
public in `Api_gen` and linkage in `Api_engine`. Within one artefact a root has one class.

**Depends on.** `Lean.Json`, `Lean.Name`, `OCaml5.Lcnf.Naming` (`capital`, for a unit's module name).

**Properties.**
* **One class per root.** A root listed under two classes of one artefact is refused, naming the
  root and both classes; a root listed twice under one class is refused as a duplicate. Nothing is
  resolved by order — *tested* (the controls below).
* **One public implementation.** A public root lives in one artefact, and every public root lives in
  the same one, so the facade has one implementation unit — *tested*.
* **A misspelt class hides nothing.** An entry key that is neither an option nor a class is
  refused — *tested*.
* **`facade_resolves` and `public_excludes_coverage` are finite checks.** `check` evaluates both
  on the whole plan and refuses a plan where either fails. They are checks of this table, not
  theorems about the lowering — *tested*, each with a red control.
-/

namespace OCaml5.Lcnf.Export

open Lean

/-- What a root of the recipe is for: the four export classes of ruling D-11. -/
inductive ExportClass where
  /-- A public promise: the artefact's interface and the public facade export it. -/
  | «public»
  /-- Hand code outside the artefact calls it: the artefact's interface exports it; no facade does. -/
  | linkage
  /-- Translated so that the route keeps covering its closure; nothing outside calls it. -/
  | coverage
  /-- Only the artefact's own code calls it (its prelude); hidden. -/
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

/-- Whether the artefact's own interface exports a root of the class. -/
def exported : ExportClass → Bool
  | .«public» | .linkage => true
  | .coverage | .internal => false

end ExportClass

/-- One root of the plan. -/
structure ExportRoot where
  /-- The Lean declaration. -/
  source : Name
  cls : ExportClass
  /-- The artefact whose closure emits it, by its OCaml module (`Api_gen`): part of the node's
  identity. -/
  unit : String
  /-- The facades that re-export it: the artefact's own interface for an exported class, and the
  public facade for a public root. A consumer that is no facade sees nothing. -/
  consumers : List String
deriving Repr, Inhabited

/-- The typed recipe: the roots of every artefact, each in one class, and the public facade's
module. -/
structure ExportPlan where
  /-- The public facade's OCaml module (`Effect4`): the consumer of every public root. -/
  facadeModule : String
  roots : List ExportRoot
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
alias, so the artefact facades use the Lean name itself, and the public facade's paths come from
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
  /-- One artefact lists a root under two classes. -/
  | contradictory (unit : String) (source : Name) (first second : ExportClass)
  /-- One artefact lists a root twice under one class. -/
  | duplicate (unit : String) (source : Name) (cls : ExportClass)
  /-- Two artefacts make one root public: the public facade would have two implementations. -/
  | publicTwice (source : Name) (first second : String)
  /-- Public roots in two artefacts: the public facade has one implementation unit. -/
  | publicSplit (first second : String)
  /-- A nominal root that the artefact's interface does not export. -/
  | nominalHidden (unit : String) (source : Name)
  /-- A consumer's facade that does not resolve one of its roots to itself (`facade_resolves`). -/
  | unresolved (consumer : String) (source : Name)
  /-- A coverage-only root that reaches the public facade (`public_excludes_coverage`). -/
  | coverageInFacade (source : Name)
deriving Repr, Inhabited, BEq

/-- The refusal as one line of the generator's report. -/
def PlanRefusal.message : PlanRefusal → String
  | .malformed why => s!"export plan: {why}"
  | .unknownKey u k => s!"export plan: {u}: `{k}` is neither an option nor an export class"
  | .contradictory u n a b =>
    s!"export plan: {u}: {n} is in two classes, `{a.key}` and `{b.key}`; give it one"
  | .duplicate u n c => s!"export plan: {u}: {n} is listed twice under `{c.key}`"
  | .publicTwice n a b => s!"export plan: {n} is public in {a} and in {b}; one artefact implements it"
  | .publicSplit a b =>
    s!"export plan: public roots in {a} and in {b}; the public facade has one implementation artefact"
  | .nominalHidden u n => s!"export plan: {u}: nominal root {n} is not exported (public or linkage)"
  | .unresolved c n => s!"export plan: the facade of {c} does not resolve {n} to itself (facade_resolves)"
  | .coverageInFacade n =>
    s!"export plan: coverage root {n} reaches the public facade (public_excludes_coverage)"

/-- The refusals the plan checker finds, in plan order: one class per root of an artefact, every
public root in one artefact, then the two finite checks. Empty means the plan is admitted. -/
def ExportPlan.refusals (p : ExportPlan) : List PlanRefusal := Id.run do
  let mut out : Array PlanRefusal := #[]
  -- one class per (artefact, root): the first listing decides nothing, a second is refused
  let mut seen : Std.HashMap (String × Name) ExportClass := {}
  for r in p.roots do
    match seen[(r.unit, r.source)]? with
    | some c =>
      out := out.push (if c == r.cls then .duplicate r.unit r.source c
                       else .contradictory r.unit r.source c r.cls)
    | none => seen := seen.insert (r.unit, r.source) r.cls
  -- one artefact implements every public root
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
  ["out", "import", "cap", "types", "modules", "nominal", "abstract", "externs", "prelude", "open"]

/-- The OCaml module of an artefact's output (`ocaml/gen/api_gen.ml` → `Api_gen`): the unit that
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

/-- The roots of one recipe entry, class by class (`ExportClass.all`), each with its consumers. -/
def entryRoots (facade : String) (entry : Json) : Except PlanRefusal (List ExportRoot) := do
  let out ← match entry.getObjValAs? String "out" with
    | .ok o => pure o
    | .error e => throw (.malformed s!"an artefact without `out`: {e}")
  let unit := unitOf out
  let fields ← match entry.getObj? with
    | .ok f => pure f
    | .error e => throw (.malformed s!"{out}: {e}")
  for key in fields.keys do
    unless entryOptions.contains key || ExportClass.all.any (·.key == key) do
      throw (.unknownKey unit key)
  let mut roots : List ExportRoot := []
  for cls in ExportClass.all do
    let consumers := (if cls == .«public» then [facade] else []) ++ (if cls.exported then [unit] else [])
    for n in ← rootsOf entry cls do
      roots := roots ++ [{ source := n, cls := cls, unit := unit, consumers := consumers }]
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
  let entries ← match recipe.getObjValAs? (Array Json) "artefacts" with
    | .ok es => pure es
    | .error e => throw (.malformed s!"no artefacts: {e}")
  let units := entries.toList.filterMap fun e => (e.getObjValAs? String "out").toOption.map unitOf
  unless units.eraseDups.length == units.length do
    throw (.malformed s!"two artefacts share one unit name: {units}")
  let mut roots : List ExportRoot := []
  for e in entries do roots := roots ++ (← entryRoots facade e)
  return { facadeModule := facade, roots := roots }

/-- The recipe read and checked: what the generator makes artefacts from. -/
def readChecked (recipe : Json) : Except PlanRefusal CheckedPlan := do
  (← ExportPlan.ofRecipe recipe).check

/-- An artefact's roots of one class, in the order its entry lists them. -/
def CheckedPlan.rootsOf (p : CheckedPlan) (unit : String) (cls : ExportClass) : List Name :=
  (p.plan.roots.filter fun r => r.unit == unit && r.cls == cls).map (·.source)

/-! ## Controls

Each property of the header, positive and red. A recipe is written as JSON text and read by the
same reader the generator uses. -/

private def recipe (entries : String) : Json :=
  (Json.parse ("{\"format\": \"effect4-lcnf-roots-v3\", \"facade\": {\"module\": \"Effect4\"}, \
    \"artefacts\": [" ++ entries ++ "]}")).toOption.getD Json.null

private def refusalOf (j : Json) : Option PlanRefusal :=
  match readChecked j with
  | .ok _ => none
  | .error r => some r

-- a clean recipe: a public, a linkage, a coverage and an internal root of one artefact, and the
-- same Lean name public in one artefact and linkage in another (two specialised nodes)
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
-- one class per root: two classes in one artefact are refused, naming both; nothing wins by order
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"public\": [\"A.run\"], \"coverage\": [\"A.run\"]}") with
  | some (.contradictory u n a b) => u == "Api_gen" && n == `A.run && a == .«public» && b == .coverage
  | _ => false
#guard match refusalOf (recipe "{\"out\": \"a/api_gen.ml\", \"linkage\": [\"A.run\", \"A.run\"]}") with
  | some (.duplicate u n c) => u == "Api_gen" && n == `A.run && c == .linkage
  | _ => false
-- one public implementation: one root public twice, or public roots in two artefacts
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

-- `public_excludes_coverage`, red: a hand-built plan whose coverage root names the public facade
-- as a consumer (a recipe cannot spell one; C5's per-consumer facades could)
private def leaky : ExportPlan :=
  { facadeModule := "Effect4",
    roots := [{ source := `M.step, cls := .coverage, unit := "Api_gen", consumers := ["Effect4"] }] }
#guard !leaky.publicExcludesCoverage
#guard match leaky.check with
  | .error (.coverageInFacade n) => n == `M.step
  | _ => false
-- a root that is public in some artefact is not coverage-only, so the check stays silent on it
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
