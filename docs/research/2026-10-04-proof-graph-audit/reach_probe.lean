import Tools.SemanticsRegistry

/-! Finite probe: which theorems of `Effect4.Laws.*` does the elaborated-term dependency graph
reach from the registry's claim pointers and the ledger goals? Read-only. -/
open Lean Tools.Semantics

def noise (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes || n.components.any fun c =>
    match c with
    | .str _ s =>
      s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        s == "rec" || s == "recOn" || s == "casesOn" || s == "below" || s == "brecOn" ||
        s == "binductionOn" || s == "ibelow" || s == "noConfusion" || s == "noConfusionType" ||
        s == "inj" || s == "injEq" || s == "sizeOf_spec" || s.startsWith "instSizeOf" ||
        s == "ctorIdx" || s == "ctorElim"
    | _ => true

def goalMarker : Expr → Bool
  | .forallE _ _ body _ => goalMarker body
  | e => e.isAppOfArity `ProofGraph.Obligation 1

def usedConstantsOf : ConstantInfo → Array Name
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | _ => #[]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (registry.roots.toArray.map fun m => { module := m }) {} 0
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  let ours (n : Name) : Bool :=
    let m := modOf n; (`Effect4).isPrefixOf m || (`Test).isPrefixOf m
  -- roots: claim pointers, every ledger goal and its checked/wanted companions
  let mut roots : Array Name := #[]
  for c in registry.claims do
    match c.pointer with
    | .witness n => roots := roots.push n
    | .goal n => roots := roots ++ #[n, n ++ `checked]
    | .refutedBy _ w => roots := roots.push w
    | _ => pure ()
  let mut population : Array Name := #[]
  let mut hasConsumer : Std.HashSet Name := {}
  for (n, ci) in env.constants.map₁.toList do
    unless ours n do continue
    if let .thmInfo t := ci then
      if goalMarker t.type then roots := roots ++ #[n, n ++ `checked, n ++ `wanted]
      else if (`Effect4.Laws).isPrefixOf (modOf n) && !noise n &&
          n.getString! != "checked" then population := population.push n
    for d in usedConstantsOf ci do
      if d != n && ours d then hasConsumer := hasConsumer.insert d
  roots := roots.filter (env.contains ·)
  -- forward closure from the roots, inside the tree only
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for d in usedConstantsOf ci do
        if ours d && !seen.contains d then stack := stack.push d
  IO.println s!"#roots\t{roots.size}"
  for n in population do
    let tier := if seen.contains n then "A" else if hasConsumer.contains n then "B" else "C"
    IO.println s!"{tier}\t{n}\t{modOf n}"
  return 0
