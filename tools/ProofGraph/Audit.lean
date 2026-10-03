import Lean

/-!
The whole-environment scans of the axiom gate (`Test/Audit/AxiomGate.lean`), separated from its
policy. One fold over the environment's constants records, for every declaration of the modules a
predicate selects, the facts the trust gate rules on; the gate keeps the rulings, their messages
and its lists. This module and `ProofGraph.Axioms` are compiled to native code and loaded into the
elaborator (the lakefile's `ProofGraphNative` library, `precompileModules`), so the scans run
natively inside `lake build Test` instead of in the interpreter. Only Lean is imported.
-/
namespace ProofGraph.Audit
open Lean

/-- The module a declaration was declared in. -/
def moduleOf? (env : Environment) (declaration : Name) : Option Name := do
  let index ← env.getModuleIdxFor? declaration
  env.header.moduleNames[index.toNat]?

/-- The synthesised values Lean gives a bodyless `opaque`. -/
def synthesizedOpaqueBodies : List Name :=
  [``Inhabited.default, ``Classical.ofNonempty]

/-- Strip the binders a parameterised `opaque` puts in front of its value. `opaque f (n : Nat) :
Nat` has value `fun n => default`, and the head constant is what the ruling reads. -/
def stripBinders : Nat → Expr → Expr
  | 0, value => value
  | fuel + 1, value =>
      if value.isLambda then stripBinders fuel value.bindingBody! else value

/-- Whether an `opaque` declaration's value is the one Lean synthesised for a missing body
rather than one an author wrote. -/
def isSynthesizedOpaqueBody (value : Expr) : Bool :=
  match (stripBinders 64 value).getAppFn with
  | .const name _ => synthesizedOpaqueBodies.contains name
  | _ => false

/-- The safe twin the compiler generates for an unsafe recursive definition of a safe one. -/
def isGeneratedSafeRecursor (env : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match env.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

/-- What the trust gate rules on, for one declaration. -/
structure Facts where
  name : Name
  module : Name
  /-- a compiler-generated safe twin, which the trust rulings skip -/
  safeRecursor : Bool
  isUnsafe : Bool
  isPartial : Bool
  isAxiom : Bool
  isExtern : Bool
  implementedBy : Bool
  /-- an `opaque` whose value Lean synthesised for a missing body -/
  bodilessOpaque : Bool
  /-- an `[init]` initializer sets its run-time value -/
  hasInitFn : Bool
  deriving Inhabited

/-- What the trust gate rules on, for one declaration of a module. -/
def factsOf (env : Environment) (module : Name) (info : ConstantInfo) : Facts :=
  let name := info.name
  { name, module
    safeRecursor := isGeneratedSafeRecursor env name
    isUnsafe := info.isUnsafe
    isPartial := info.isPartial
    isAxiom := info matches .axiomInfo _
    isExtern := isExtern env name
    implementedBy := (Compiler.getImplementedBy? env name).isSome
    bodilessOpaque := match info with
      | .opaqueInfo opaqueInfo => isSynthesizedOpaqueBody opaqueInfo.value
      | _ => false
    hasInitFn := (getInitFnNameFor? env name).isSome }

/-- Every declaration of the imported modules `audited` selects, with its facts, and the same
declarations grouped by module. Read from each selected module's own constant list, so the scan
touches only those declarations: a fold over the whole environment also pages in every constant
of Lean and of the dependencies, which under memory pressure was most of the gate's time. The
set is the one `moduleOf?` attributes to those modules (`ModuleData.constants`; the code
generator's auxiliaries in `extraConstNames` are not constants of the environment). -/
def auditedFacts (env : Environment) (audited : Name → Bool) :
    Array Facts × Std.HashMap Name (Array Name) := Id.run do
  let mut facts : Array Facts := #[]
  let mut byModule : Std.HashMap Name (Array Name) := {}
  let mut seen : Std.HashSet Name := {}
  for (module, data) in env.header.moduleNames.zip env.header.moduleData do
    if audited module then
      let mut names : Array Name := #[]
      for info in data.constants do
        -- a name can be listed twice; it is one declaration, of the module the environment says
        if seen.contains info.name || moduleOf? env info.name != some module then continue
        seen := seen.insert info.name
        facts := facts.push (factsOf env module info)
        names := names.push info.name
      byModule := byModule.insert module names
  return (facts, byModule)

/-- The modules a root reaches through imports, the root included. -/
def moduleImportClosure (graph : Array (Name × Array Name)) (root : Name) : Array Name := Id.run do
  let table : Std.HashMap Name (Array Name) := graph.foldl (fun t (n, is) => t.insert n is) {}
  let mut seen : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array Name := #[root]
  for _ in [0:graph.size + 1] do
    if stack.isEmpty then break
    let mut next : Array Name := #[]
    for module in stack do
      if seen.contains module then continue
      seen := seen.insert module
      order := order.push module
      next := next ++ (table.getD module #[])
    stack := next
  return order

end ProofGraph.Audit
