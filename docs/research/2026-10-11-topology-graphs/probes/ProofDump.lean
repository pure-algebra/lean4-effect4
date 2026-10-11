import Tools.LoadPaths

/-! Scratch driver (not part of the tree): dump the proof graph of `Effect4.Laws` for graph
analysis. For every authored constant of the tree (`Effect4.*` modules): its kind, module,
the authored theorems its value names (through auxiliaries), and the authored definitions and
inductives its statement (type) names (through auxiliaries). -/

open Lean Tools.LoadPaths ProofGraph

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .axiomInfo _ => "ax"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"

def treeMod (env : Environment) (c : Name) : Bool :=
  (`Effect4).isPrefixOf (moduleOf env c)

/-- The authored tree constants (non-theorem) that an expression names, through auxiliaries. -/
def statementDefs (env : Environment) (e : Expr) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack := e.getUsedConstants
  for _ in [0:200000] do
    let some d := stack.back? | break
    stack := stack.pop
    if seen.contains d then continue
    seen := seen.insert d
    if isAuxiliary env d then
      -- a structure projection or matcher in a statement: look through its type only
      continue
    match env.find? d with
    | some (.thmInfo _) => pure ()
    | some (.ctorInfo ci) =>
      if treeMod env ci.induct then out := out.push ci.induct
    | some _ => if treeMod env d then out := out.push d
    | none => pure ()
  return out

def main (args : List String) : IO UInt32 := do
  let [outPath] := args | IO.eprintln "usage: ProofDump <out.tsv>"; return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Laws }, { module := `Effect4 }] {} 0
  let h ← IO.FS.Handle.mk outPath .write
  let mut n := 0
  for (c, info) in env.constants.toList do
    unless treeMod env c do continue
    if isAuxiliary env c then continue
    let k := kindOf info
    let thmDeps := match k with
      | "thm" => (directTheorems env c).getD #[]
      | _ => #[]
    let thmDeps := thmDeps.filter (treeMod env)
    let sdefs := (statementDefs env info.type).filter (· != c)
    -- value-level definition uses for definitions (to see the definition DAG)
    let vdefs := match info with
      | .defnInfo d => (statementDefs env d.value).filter (· != c)
      | _ => #[]
    h.putStrLn s!"{c}\t{k}\t{moduleOf env c}\t{",".intercalate (thmDeps.toList.map toString)}\t{",".intercalate (sdefs.toList.map toString)}\t{",".intercalate (vdefs.toList.map toString)}"
    n := n + 1
  h.flush
  IO.println s!"constants: {n}"
  -- the modules each tree module's declarations name (every constant, auxiliaries included)
  let mut uses : Std.HashMap Name (Std.HashSet Name) := {}
  for (c, info) in env.constants.toList do
    unless treeMod env c do continue
    let m := moduleOf env c
    let mut s := uses.getD m {}
    let consts := info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    for d in consts do
      let dm := moduleOf env d
      if dm != m then s := s.insert dm
    uses := uses.insert m s
  let h2 ← IO.FS.Handle.mk (outPath ++ ".uses") .write
  for (m, s) in uses.toList do
    h2.putStrLn s!"{m}\t{",".intercalate (s.toList.map toString)}"
  h2.flush
  return 0
