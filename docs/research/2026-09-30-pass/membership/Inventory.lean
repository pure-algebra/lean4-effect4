import Test.All

/-!
# Research probe: every declaration that mentions the old value judgments, read from the kernel

Seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. A reading of the environment, not a proof:
it walks every constant `Test.All` loads (the whole library and battery), and reports those whose
type or value names one of the five judgments `StrongValue`, `HandlesFit`, `ValueOk`,
`StrongExit`, `StrongCause` (plus the two helpers `HandlesLive`, `ServicesOk`), by module.

- A **direct** mention names one of the seven in the declaration's type (its statement) or value.
- The **closure**: a definition, inductive or structure whose type or value names a judgment is
  itself a judgment for this purpose (`TypedProg`, `Ψ_S`, `preds`, `TypedState`, …); the
  iteration adds them until nothing changes. A theorem whose statement names the closure must be
  restated; a theorem that names it only in its proof must be re-proved, not restated.
- The **walk set**: every constant reachable from the slice-5 stack walk and delivery theorems
  (`popR_typed`, `popR_typed_interpR`, `hookLaws_interpR`, `saveAnswerR_typed`, `deliver_active`,
  `deliver_stale`) through types and values, intersected with the closure.

Auxiliary constants (matchers, equation lemmas, `brecOn`, recursors, constructors, private
names) are counted under their parent and not listed.
-/

open Lean Meta Elab Command

namespace Research.Pass.Membership.Inventory

def seeds : List Name :=
  [``Effect4.Program.Typed.StrongValue, ``Effect4.Program.Typed.HandlesFit,
   ``Effect4.Program.Typed.ValueOk, ``Effect4.Program.Typed.StrongExit,
   ``Effect4.Program.Typed.StrongCause, ``Effect4.Program.Typed.HandlesLive,
   ``Effect4.Program.Typed.ServicesOk]

/-- Auxiliary constants: reported through their parent declaration. -/
def auxiliary (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    (match n with
     | .str _ s => s.startsWith "match_" || s.startsWith "eq_" || s == "eq_def" ||
         s.startsWith "proof_" || s == "sizeOf_spec" || s == "injEq" || s == "inj" ||
         s == "ctorIdx" || s.startsWith "_" || s == "below" || s == "brecOn" ||
         s == "binductionOn" || s == "casesOn" || s == "recOn" || s == "rec" || s == "mk" ||
         s == "ibelow"
     | _ => false) ||
    (match env.find? n with
     | some (.ctorInfo _) | some (.recInfo _) => true
     | _ => false)

def inLibrary (n : Name) : Bool :=
  (`Effect4).isPrefixOf n || (`Test).isPrefixOf n

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def usedIn (e : Expr) (set : NameSet) : List Name :=
  (e.getUsedConstants.filter set.contains).toList

def valueOf? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The declarations that are judgments for this purpose: the seeds, then every non-theorem
library constant whose type or value names one (constructors and matchers carry the mention to
their parent through its value or type). -/
def closure (env : Environment) (start : List Name) : NameSet := Id.run do
  let mut set : NameSet := start.foldl (fun s n => s.insert n) {}
  for _ in [0:12] do
    let mut grew := false
    for (n, ci) in env.constants.toList do
      if set.contains n || !inLibrary n then continue
      match ci with
      | .thmInfo _ => continue
      | _ =>
        -- an inductive is a judgment when one of its constructors names one
        let ctorHit := match ci with
          | .inductInfo v => v.ctors.any fun c =>
              match env.find? c with
              | some cc => !(usedIn cc.type set).isEmpty
              | none => false
          | _ => false
        let hit := ctorHit || !(usedIn ci.type set).isEmpty ||
          (match valueOf? ci with | some v => !(usedIn v set).isEmpty | none => false)
        if hit then
          set := set.insert n
          grew := true
    if !grew then break
  return set

/-- Constants reachable from `roots` through types and values, inside the library. -/
def reachable (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  for _ in [0:200000] do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => continue
      | some ci =>
        let next := ci.type.getUsedConstants.toList ++
          (match valueOf? ci with | some v => v.getUsedConstants.toList | none => [])
        for m in next do
          if inLibrary m && !seen.contains m then work := m :: work
  return seen

def walkRoots : List Name :=
  [``Effect4.Program.Typed.popR_typed, ``Effect4.Program.Typed.popR_typed_interpR,
   ``Effect4.Program.Typed.hookLaws_interpR, ``Effect4.Program.Typed.saveAnswerR_typed,
   ``Effect4.Program.Typed.deliver_active, ``Effect4.Program.Typed.deliver_stale]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `current

/-- The obligation macros' markers (`.wanted`, `.checked`) belong to their parent theorem. -/
def listed (env : Environment) (n : Name) : Bool :=
  inLibrary n && !auxiliary env n &&
    (match n with | .str _ s => s != "wanted" && s != "checked" | _ => true)

/-- A name without the typed-state namespace, for reading. -/
def short (n : Name) : String :=
  ((n.toString.replace "Effect4.Program.Typed." "").replace "Test.Counterexamples.Machine.Semantics." "").replace "Test.Program." ""

def names (ns : List Name) : String := ", ".intercalate (ns.map short)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let all := env.constants.toList.filter fun (n, _) => listed env n
  -- 1. direct mentions, per judgment
  logInfo m!"# 1. Direct mentions (type or value), per judgment"
  for seed in seeds do
    let hits := all.filter fun (_, ci) =>
      ci.type.getUsedConstants.contains seed ||
        (match valueOf? ci with | some v => v.getUsedConstants.contains seed | none => false)
    let hits := hits.filter fun (n, _) => n != seed
    let byMod := hits.foldl (fun (acc : List (Name × List Name)) (n, _) =>
      let m := moduleOf env n
      match acc.find? (·.1 == m) with
      | some _ => acc.map fun (m', ns) => if m' == m then (m', n :: ns) else (m', ns)
      | none => acc ++ [(m, [n])]) []
    logInfo m!"{seed.getString!}: {hits.length} declarations"
    for (m, ns) in byMod do
      logInfo m!"  {m} ({ns.length}): {names ns.reverse}"
  -- 2. the migration closure (ValueOk, the shape check, stays: it is not a seed here)
  let seedsA := seeds.filter (· != ``Effect4.Program.Typed.ValueOk)
  let closA := closure env seedsA
  let closB := closure env seeds
  let walk := reachable env walkRoots
  logInfo m!"# 2. Migration set: declarations naming the strong judgments or their closure"
  let mut rows : Array (Name × Name × String × Bool) := #[]
  for (n, ci) in all do
    let ty := !(usedIn ci.type closA).isEmpty
    let va := match valueOf? ci with | some v => !(usedIn v closA).isEmpty | none => false
    if ty || va || closA.contains n then
      rows := rows.push (moduleOf env n, n, kindOf ci, ty)
  let sorted := rows.qsort fun a b =>
    a.1.toString < b.1.toString || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)
  let mut lastMod : Name := .anonymous
  let mut restateCount : Nat := 0
  let mut reproveCount : Nat := 0
  let mut defCount : Nat := 0
  let mut walkCount : Nat := 0
  let mut walkNames : List Name := []
  for (m, n, k, inStatement) in sorted do
    if m != lastMod then
      logInfo m!"## {m}"
      lastMod := m
    let role :=
      if k == "theorem" then (if inStatement then "restate" else "re-prove") else "redefine"
    if k == "theorem" then
      if inStatement then restateCount := restateCount + 1 else reproveCount := reproveCount + 1
    else defCount := defCount + 1
    let w := if walk.contains n then " [walk]" else ""
    if walk.contains n then
      walkCount := walkCount + 1
      walkNames := n :: walkNames
    logInfo m!"  {short n} : {k} : {role}{w}"
  logInfo m!"migration set: {sorted.size} (redefine {defCount}, restate {restateCount}, re-prove {reproveCount}); closure {closA.size} constants"
  logInfo m!"walk set (the slice-5 walk and delivery depend on): {walkCount}: {names walkNames.reverse}"
  -- 3. declarations that reach only the shape check `ValueOk`
  let onlyShape := all.filter fun (n, ci) =>
    let tyB := !(usedIn ci.type closB).isEmpty || closB.contains n
    let vaB := match valueOf? ci with | some v => !(usedIn v closB).isEmpty | none => false
    let tyA := !(usedIn ci.type closA).isEmpty || closA.contains n
    let vaA := match valueOf? ci with | some v => !(usedIn v closA).isEmpty | none => false
    (tyB || vaB) && !(tyA || vaA)
  let byMod := onlyShape.foldl (fun (acc : List (Name × Nat)) (n, _) =>
    let m := moduleOf env n
    match acc.find? (·.1 == m) with
    | some _ => acc.map fun (m', c) => if m' == m then (m', c + 1) else (m', c)
    | none => acc ++ [(m, 1)]) []
  logInfo m!"# 3. Declarations reaching only the shape check ValueOk (unchanged by the migration): {onlyShape.length}"
  for (m, c) in byMod do
    logInfo m!"  {m}: {c}"

end Research.Pass.Membership.Inventory
