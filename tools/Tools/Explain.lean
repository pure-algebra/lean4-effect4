import Lean
import Tools.SemanticsRegistry
import ProofGraph.Goal
import Effect4.Laws.Auto.Semantics
import Effect4.Step
import Effect4.Schema.Modeled.Derive
import Effect4.Schema.Codec
import Effect4.Schema.Bridge
import Effect4.Codegen.Schema
import Effect4.Codegen.Target

/-!
# `#explain` and `#obligations`: one question asked of any part

The agent's first two tools (`docs/research/2026-10-08-agent-authoring.md` §3). Each answers
data, an `Explanation` or an `Obligations` value with a JSON form, so a later MCP tool is a thin
wrapper over the same function. Nothing here is hand-maintained: every answer is read from the
environment, the `@[semantics]` placements and the semantics registry.

- `#explain t` takes any term. When its head is a declaration, it reports the declaration's kind,
  module and type, its placement, the registry claims that point at it and, for a theorem, its
  standing (proved, modulo goals, or a goal). It lists the theorems of the tree whose statement
  names the declaration, each with its standing and placement, and the definitions of the tree
  that use it. When the term is a closed step (`Step Γ t`), it reports the step's inputs and
  answer, its two checks (`Step.normal`, `Step.canonical`), its writing footprint
  (`Step.writes`) and its update spine (`Step.spine`), each by reduction, and which shared law
  each check serves, with its remaining premises.
- `#obligations N` lists every theorem and planned goal declared under the namespace `N`, with
  its standing and placement, the goals the namespace rests on, and the claims that point
  inside it.

The `_json` forms print the same value as JSON. Reduction is bounded: an answer that does not
reduce within the bound is reported as unknown, never guessed. This is tooling only; it never
enters stored program content, and it adds no trust: every standing is the kernel's.
-/

namespace Tools.Explain
open Lean Meta Elab Command Term
open Effect4.Schema (Modeled)

/-! ## The data, with canonical schemas

Each answer type derives `Modeled`, so its `Ty`, its JSON and its Effect Schema come from one
declaration: `#explain_json` prints the canonical codec's JSON (`Effect4.Schema.encode`), and
`#explain_schema` prints the `SchemaRepresentation` that a TypeScript client decodes it with. -/

/-- A closed step's facts, each read by reduction. An aspect that did not reduce within the
bound is absent, and its name is in `unreduced`. -/
structure StepFacts where
  inputs : String
  answers : String
  normal : Option Bool
  canonical : Option Bool
  writes : Option (List String)
  spine : Option Nat
  unreduced : List String
  /-- the shared laws that the checks serve, with their remaining premises -/
  laws : List String
  deriving Inhabited, Modeled

/-- A theorem of the tree, as the plan sees it. -/
structure Statement where
  name : String
  standing : String
  restsOn : List String
  concept : Option String
  requirement : Option String
  claims : List String
  deriving Inhabited, Modeled

/-- The answer of `#explain`. -/
structure Explanation where
  name : Option String
  kind : String
  module : Option String
  type : String
  concept : Option String
  requirement : Option String
  claims : List String
  standing : Option String
  restsOn : List String
  step : Option StepFacts
  statements : List Statement
  usedBy : List String
  deriving Inhabited, Modeled

/-- The answer of `#obligations`. -/
structure Obligations where
  namespace_ : String
  proved : Nat
  modulo : Nat
  goals : Nat
  statements : List Statement
  restsOn : List String
  deriving Inhabited

derive_modeled Obligations (namespace_ := "namespace")

/-- A value's canonical JSON, by the codec at its derived type. -/
def canonicalJson {α : Type} [Modeled α] (a : α) : String :=
  match Effect4.Schema.encode (Modeled.ty (α := α)) ((Modeled.image α).toVal a) with
  | some j => Effect4.Codegen.renderJson j
  | none => "the codec refused the value at its derived type"

/-- A type's Effect Schema, as raw `SchemaRepresentation` JSON syntax. -/
def schemaText (α : Type) [Modeled α] : String :=
  TypeScript.Render.expr TypeScript.house0 0
    (Effect4.Codegen.Schema.representation (Effect4.Program.Ty.schema (Modeled.ty (α := α))))

/-! ## Reading by reduction, with a bound -/

/-- The bound on the cells or successors a reading reduces. -/
def fuel : Nat := 4096

def boolOf? (e : Expr) : MetaM (Option Bool) := do
  let e ← whnf e
  if e.isConstOf ``Bool.true then return some true
  if e.isConstOf ``Bool.false then return some false
  return none

def natOf? : Nat → Expr → MetaM (Option Nat)
  | 0, _ => return none
  | k + 1, e => do
    let e ← whnf e
    match e with
    | .lit (.natVal n) => return some n
    | _ =>
      if e.isConstOf ``Nat.zero then return some 0
      if e.isAppOfArity ``Nat.succ 1 then return (← natOf? k (e.getArg! 0)).map (· + 1)
      return none

def stringsOf? : Nat → Expr → MetaM (Option (List String))
  | 0, _ => return none
  | k + 1, e => do
    let e ← whnf e
    if e.isAppOfArity ``List.nil 1 then return some []
    unless e.isAppOfArity ``List.cons 3 do return none
    let .lit (.strVal s) ← whnf (e.getArg! 1) | return none
    return (← stringsOf? k (e.getArg! 2)).map (s :: ·)

def optionNatOf? (e : Expr) : MetaM (Option (Option Nat)) := do
  let e ← whnf e
  if e.isAppOfArity ``Option.none 1 then return some none
  if e.isAppOfArity ``Option.some 2 then return (← natOf? fuel (e.getArg! 1)).map some
  return none

def render (e : Expr) : MetaM String := return toString (← ppExpr e)

/-- A compact rendering of a `Ty` expression, by reduction to its constructors: `nat`,
`{open: bool, waiters: list {hint: deferred, id: deferred}}`, `(bool, nat)`. A part that does not
reduce within the bound is rendered by the pretty printer. -/
def tyText : Nat → Expr → MetaM String
  | 0, e => render e
  | k + 1, e => do
    let e ← whnf e
    let some (.str _ c) := e.getAppFn.constName? | render e
    unless e.getAppFn.constName?.map (·.getPrefix) == some ``Effect4.Program.Ty do return ← render e
    let arg (i : Nat) : MetaM String := tyText k (e.getArg! i)
    let wrap (s : String) : String :=
      if s.any (· == ' ') && !s.startsWith "{" && !s.startsWith "(" && !s.startsWith "[" then
        s!"({s})" else s
    match c, e.getAppNumArgs with
    | "option", 1 => return s!"option {wrap (← arg 0)}"
    | "list", 1 => return s!"list {wrap (← arg 0)}"
    | "refOf", 1 => return s!"ref {wrap (← arg 0)}"
    | "causeOf", 1 => return s!"cause {wrap (← arg 0)}"
    | "prod", 2 => return s!"({← arg 0}, {← arg 1})"
    | "union", 2 => return s!"{← arg 0} | {← arg 1}"
    | "except", 2 => return s!"except {wrap (← arg 0)} {wrap (← arg 1)}"
    | "exitOf", 2 => return s!"exit {wrap (← arg 0)} {wrap (← arg 1)}"
    | "fiberOf", 2 => return s!"fiber {wrap (← arg 0)} {wrap (← arg 1)}"
    | "deferredOf", 2 => return s!"deferred {wrap (← arg 0)} {wrap (← arg 1)}"
    | "map", 2 => return s!"map {wrap (← arg 0)} {wrap (← arg 1)}"
    | "var", 1 => return s!"'{(← natOf? fuel (e.getArg! 0)).map toString |>.getD "?"}"
    | "lit", 1 => return s!"{← render (e.getArg! 0)}"
    | "handle", 1 => return s!"handle {← render (e.getArg! 0)}"
    | "record", 1 => match ← fieldsText k (e.getArg! 0) with
      | some fs => return "{" ++ ", ".intercalate fs ++ "}"
      | none => render e
    | "tuple", 1 => match ← itemsText k (e.getArg! 0) with
      | some ts => return "[" ++ ", ".intercalate ts ++ "]"
      | none => render e
    | name, 0 => return name
    | _, _ => render e
where
  /-- A record's fields, `name: T` or `name?: T` for an optional one. -/
  fieldsText : Nat → Expr → MetaM (Option (List String))
    | 0, _ => return none
    | k + 1, e => do
      let e ← whnf e
      if e.isAppOfArity ``List.nil 1 then return some []
      unless e.isAppOfArity ``List.cons 3 do return none
      let field ← whnf (e.getArg! 1)
      unless field.isAppOfArity ``Prod.mk 4 do return none
      let rest ← whnf (field.getArg! 3)
      unless rest.isAppOfArity ``Prod.mk 4 do return none
      let .lit (.strVal name) ← whnf (field.getArg! 2) | return none
      let optional ← boolOf? (rest.getArg! 2)
      let mark := if optional == some true then "?" else ""
      let t ← tyText k (rest.getArg! 3)
      return (← fieldsText k (e.getArg! 2)).map (s!"{name}{mark}: {t}" :: ·)
  /-- A list of types. -/
  itemsText : Nat → Expr → MetaM (Option (List String))
    | 0, _ => return none
    | k + 1, e => do
      let e ← whnf e
      if e.isAppOfArity ``List.nil 1 then return some []
      unless e.isAppOfArity ``List.cons 3 do return none
      let t ← tyText k (e.getArg! 1)
      return (← itemsText k (e.getArg! 2)).map (t :: ·)

/-! ## The aspects -/

/-- The step facts of `e`, when its type is `Step Γ t`. -/
def stepFacts? (e : Expr) : MetaM (Option StepFacts) := do
  let ty ← whnfR (← inferType e)
  unless ty.isAppOfArity ``Effect4.Modules.Step 2 do return none
  let normal ← boolOf? (← mkAppM ``Effect4.Modules.Step.normal #[e])
  let canonical ← boolOf? (← mkAppM ``Effect4.Modules.Step.canonical #[e])
  let writes ← stringsOf? fuel (← mkAppM ``Effect4.Modules.Step.writes #[e])
  let spine ← optionNatOf? (← mkAppM ``Effect4.Modules.Step.spine #[e])
  let unreduced := (if normal.isNone then ["normal"] else []) ++
    (if canonical.isNone then ["canonical"] else []) ++
    (if writes.isNone then ["writes"] else []) ++ (if spine.isNone then ["spine"] else [])
  let spine := spine.bind id
  let laws :=
    (if normal == some true then
      ["typing: the normality check closes by `rfl`; `Step.typed_of_normal` also requires native atom typing, typed inputs and fold scope alignment where used"] else []) ++
    (if canonical == some true then
      ["reading: the canonicality check closes by `rfl`; `Step.sound` also requires input readings, fold scope alignment and deferred identity interpretation where used"] else []) ++
    (match spine with
      | some i => [s!"frame: `Step.frame` applies on input {i}, outside the writing footprint"]
      | none => [])
  let inputs ← match ← tyText.itemsText 64 (ty.getArg! 0) with
    | some ts => pure ("[" ++ ", ".intercalate ts ++ "]")
    | none => render (ty.getArg! 0)
  let answers ← tyText 64 (ty.getArg! 1)
  let writes := writes.map fun ws => ws.foldl (fun acc w => if acc.contains w then acc else acc ++ [w]) []
  return some {
    inputs, answers, normal, canonical, writes, spine, unreduced, laws }

/-- Whether `n` was declared in a module of the tree: under `Effect4` or `Test`, or here. -/
def inTree (env : Environment) (n : Name) : Bool :=
  let m := Effect4.Laws.Auto.semanticsModule env n
  m == env.mainModule || [`Effect4, `Test].any (·.isPrefixOf m)

/-- The registry claims whose pointer names `n`. -/
def claimsAt (n : Name) : List String :=
  Tools.Semantics.registry.claims.filterMap fun c =>
    match c.pointer with
    | .witness w => if w == n then some c.id else none
    | .refutedBy _ w => if w == n then some s!"{c.id} (refuted)" else none
    | _ => none

/-- A theorem's standing and the goals it rests on, through the plan's axiom walk. -/
def standingOf (memo : IO.Ref ProofGraph.AxiomMemo) (n : Name) : MetaM (String × List String) := do
  let (reached, table) := (ProofGraph.standing (← getEnv) n).run (← memo.get)
  memo.set table
  match reached with
  | some (.goal, _) => return ("goal", [n.toString])
  | some (.modulo goals, _) => return ("modulo", goals.toList.map toString)
  | some (.proved, _) => return ("proved", [])
  | none => return ("unknown: the walk ran out of budget", [])

def statementOf (memo : IO.Ref ProofGraph.AxiomMemo) (n : Name) : MetaM Statement := do
  let (standing, restsOn) ← standingOf memo n
  let placement := Effect4.Laws.Auto.semanticsAttribute.getParam? (← getEnv) n
  return {
    name := n.toString, standing, restsOn, concept := placement.map (·.concept),
    requirement := placement.bind (·.requirement), claims := claimsAt n }

/-- Whether `c` is an author's theorem of the tree: not an auxiliary, not a structure's field. -/
def authored (env : Environment) (c : Name) : Bool :=
  !ProofGraph.isAuxiliary env c && inTree env c && !env.isProjectionFn c

/-- The theorems of the tree whose statement names one of `targets`, and the definitions of the
tree that use `n`. -/
def neighbours (n : Name) (targets : Array Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let mut about := #[]
  let mut usedBy := #[]
  for (c, ci) in env.constants.toList do
    if c == n || !authored env c then continue
    match ci with
    | .thmInfo t => if targets.any t.type.getUsedConstants.contains then about := about.push c
    | .defnInfo d =>
      if d.value.getUsedConstants.contains n || d.type.getUsedConstants.contains n then
        usedBy := usedBy.push c
    | _ => pure ()
  let byName (a b : Name) : Bool := a.toString < b.toString
  return (about.qsort byName, usedBy.qsort byName)

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.thmInfo _) => if ProofGraph.isGoal env n then "planned goal" else "theorem"
  | some (.defnInfo _) => "definition"
  | some (.inductInfo _) => "inductive type"
  | some (.ctorInfo _) => "constructor"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | some _ => "declaration"
  | none => "term"

/-- **`explain`**: the aspects of a term, and of its head declaration when it has one. -/
def explain (e : Expr) : MetaM Explanation := do
  let env ← getEnv
  let memo ← IO.mkRef {}
  let step ← stepFacts? e
  let type ← render (← inferType e)
  match e.getAppFn.constName? with
  | none => return {
      name := none, kind := "term", module := none, type, concept := none,
      requirement := none, claims := [], standing := none, restsOn := [], step,
      statements := [], usedBy := [] }
  | some n =>
    let kind := kindOf env n
    let placement := Effect4.Laws.Auto.semanticsAttribute.getParam? env n
    let (standing, restsOn) ← if kind == "theorem" || kind == "planned goal" then
        (fun (s, r) => (some s, r)) <$> standingOf memo n
      else pure (none, [])
    let (_, usedBy) ← neighbours n #[]
    -- the statements about the declaration, and about the definitions that use it, one level
    let (about, _) ← neighbours n (usedBy.push n)
    let statements ← about.toList.mapM (statementOf memo)
    return {
      name := n.toString, kind, module := (Effect4.Laws.Auto.semanticsModule env n).toString,
      type, concept := placement.map (·.concept), requirement := placement.bind (·.requirement),
      claims := claimsAt n, standing, restsOn, step, statements,
      usedBy := usedBy.toList.map toString }

/-- **`obligations`**: every theorem and goal declared under a namespace, with its standing. -/
def obligations (ns : Name) : MetaM Obligations := do
  let env ← getEnv
  let memo ← IO.mkRef {}
  let names := (env.constants.toList.filterMap fun (c, ci) =>
    if ci matches .thmInfo _ && ns.isPrefixOf c && authored env c
    then some c else none).toArray.qsort (·.toString < ·.toString)
  let statements ← names.toList.mapM (statementOf memo)
  let count (w : String) := (statements.filter (·.standing == w)).length
  let restsOn := statements.foldl (fun acc s => acc ++ s.restsOn.filter (!acc.contains ·)) []
  return {
    namespace_ := ns.toString, proved := count "proved", modulo := count "modulo",
    goals := count "goal", statements, restsOn }

/-! ## Rendering, for a person or an agent reading the editor -/

def Statement.line (s : Statement) : String :=
  let placed := match s.concept, s.requirement with
    | some c, some r => s!"; {c}, {r}"
    | some c, none => s!"; {c}"
    | _, _ => ""
  let rests := if s.restsOn.isEmpty || s.standing == "goal" then "" else s!" on {s.restsOn}"
  let claims := if s.claims.isEmpty then "" else s!"; claims {s.claims}"
  s!"  {s.name}: {s.standing}{rests}{placed}{claims}"

def Explanation.text (x : Explanation) : String := Id.run do
  let mut out := match x.name with
    | some n => s!"{n} ({x.kind}, {x.module.getD "?"})\n  type: {x.type}"
    | none => s!"a term\n  type: {x.type}"
  if let some c := x.concept then
    out := out ++ s!"\n  placement: {c}" ++ (x.requirement.map (s!", {·}") |>.getD "")
  unless x.claims.isEmpty do out := out ++ s!"\n  claims: {x.claims}"
  if let some s := x.standing then
    out := out ++ s!"\n  standing: {s}" ++ (if x.restsOn.isEmpty || s == "goal" then "" else s!" on {x.restsOn}")
  if let some f := x.step then
    let show? {α : Type} [ToString α] (o : Option α) : String := o.map toString |>.getD "unknown"
    out := out ++ s!"\nstep: inputs {f.inputs}; answers {f.answers}" ++
      s!"\n  checks: normal {show? f.normal}, canonical {show? f.canonical}" ++
      s!"\n  writes: {show? f.writes}; spine: {f.spine.map toString |>.getD "none"}" ++
      (if f.unreduced.isEmpty then "" else s!"\n  did not reduce: {f.unreduced}")
    for l in f.laws do out := out ++ s!"\n  law: {l}"
  unless x.statements.isEmpty do
    out := out ++ s!"\ntheorems that state something about it ({x.statements.length}):"
    for s in x.statements do out := out ++ "\n" ++ s.line
  unless x.usedBy.isEmpty do
    out := out ++ s!"\nused by ({x.usedBy.length}): {x.usedBy}"
  return out

def Obligations.text (o : Obligations) : String := Id.run do
  let mut out := s!"{o.namespace_}: {o.statements.length} theorems; " ++
    s!"{o.proved} proved, {o.modulo} modulo goals, {o.goals} planned goals"
  for s in o.statements do out := out ++ "\n" ++ s.line
  unless o.restsOn.isEmpty do out := out ++ s!"\nrests on: {o.restsOn}"
  return out

/-! ## The commands -/

/-- `#explain t`: the aspects of `t`, as text. -/
syntax (name := explainCmd) "#explain " term : command
/-- `#explain_json t`: the same, as JSON. -/
syntax (name := explainJsonCmd) "#explain_json " term : command
/-- `#obligations N`: the theorems and goals under the namespace `N`, as text. -/
syntax (name := obligationsCmd) "#obligations " ident : command
/-- `#obligations_json N`: the same, as JSON. -/
syntax (name := obligationsJsonCmd) "#obligations_json " ident : command

def explainSyntax (t : Syntax) : CommandElabM Explanation := liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  explain (← instantiateMVars e)

@[command_elab explainCmd] def elabExplain : CommandElab := fun stx => do
  logInfo (← explainSyntax stx[1]).text

@[command_elab explainJsonCmd] def elabExplainJson : CommandElab := fun stx => do
  logInfo (canonicalJson (← explainSyntax stx[1]))

def obligationsOf (id : Syntax) : CommandElabM Obligations := liftTermElabM do
  obligations id.getId

@[command_elab obligationsCmd] def elabObligations : CommandElab := fun stx => do
  logInfo (← obligationsOf stx[1]).text

@[command_elab obligationsJsonCmd] def elabObligationsJson : CommandElab := fun stx => do
  logInfo (canonicalJson (← obligationsOf stx[1]))

/-- `#explain_schema`: the Effect Schemas of the two answers, `Explanation` then `Obligations`. -/
syntax (name := explainSchemaCmd) "#explain_schema" : command

@[command_elab explainSchemaCmd] def elabExplainSchema : CommandElab := fun _ => do
  logInfo s!"Explanation:\n{schemaText Explanation}\nObligations:\n{schemaText Obligations}"

end Tools.Explain
