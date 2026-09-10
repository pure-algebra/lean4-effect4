import Lean

/-!
Read constructor payload types from an explicitly built Lean environment. This tool
does not write or promote a baseline. The Python driver pins source provenance.

Run from the selected checkout, after its four imports have been built:
  lake env lean --run /path/to/Extract.lean /path/to/families.json /path/to/reflection.json

Names come from the retained family inventory. Parameterized program families are
instantiated at NativeOp, as the existing World and deriving manifest require.
The export retains all binder types, including proof fields, and resolves reducible
type aliases. Open parameters, metavariables and unsupported expression forms refuse.
This is metadata, not a proof of codec compatibility or execution permission.
-/

open Lean Meta

namespace Compatibility

def obj (xs : List (String × Json)) : Json := Json.mkObj xs
def str (s : String) : Json := .str s

def levelJson : Level → Json
  | .zero => str "zero"
  | .succ a => obj [("succ", levelJson a)]
  | .max a b => obj [("max", .arr #[levelJson a, levelJson b])]
  | .imax a b => obj [("imax", .arr #[levelJson a, levelJson b])]
  | .param n => obj [("parameter", str n.toString)]
  | .mvar _ => str "UNRESOLVED_LEVEL"

/-- Bound-variable indices are stable; fresh local-context names never enter the snapshot. -/
def typeJson : Nat → Expr → MetaM Json
  | 0, _ => throwError "reflected type exceeds depth budget 512"
  | fuel + 1, e => do
    let e ← instantiateMVars e
    -- Abstracted dependent field references are de Bruijn indices. WHNF requires
    -- an actual local context, so retain those nodes rather than reducing loose
    -- indices outside the telescope. Closed children still normalize below.
    let e ← if e.hasLooseBVars then pure e else withReducible (whnf e)
    match e with
    | .bvar i => return obj [("bound", toJson i)]
    | .const n ls =>
      if ls.any Level.hasMVar then throwError "unresolved universe in {e}"
      return obj [("constant", str n.toString), ("levels", toJson (ls.map levelJson))]
    | .app f a => return obj [("apply", .arr #[← typeJson fuel f, ← typeJson fuel a])]
    | .sort l =>
      if l.hasMVar then throwError "unresolved sort in {e}"
      return obj [("sort", levelJson l)]
    | .forallE _ t b bi =>
      return obj [("forall", .arr #[← typeJson fuel t, ← typeJson fuel b]),
        ("binder", str (repr bi).pretty)]
    | .lam _ t b bi =>
      return obj [("lambda", .arr #[← typeJson fuel t, ← typeJson fuel b]),
        ("binder", str (repr bi).pretty)]
    | .lit (.natVal n) => return obj [("nat", toJson n)]
    | .lit (.strVal s) => return obj [("string", str s)]
    | .proj n i x => return obj [("projection", .arr #[str n.toString, toJson i, ← typeJson fuel x])]
    | .mdata _ x => typeJson fuel x
    | _ => throwError "unsupported or open constructor field type: {e}"

def selectedType (name : Name) : MetaM Expr := do
  let info ← getConstInfoInduct name
  let params ← if info.numParams == 0 then pure #[] else
    if info.numParams == 1 && info.all.contains `Effect4.Program.Eff then
      pure #[mkConst `Effect4.Program.NativeOp]
    else throwError "no selected instantiation for {name}: {info.numParams} parameters"
  return mkAppN (mkConst name) params

/-- Follow applied project-owned payload carriers, including nominal Schema helpers
such as ElementOf Representation. Core containers are identified by the toolchain. -/
def nominalTypes : Nat → Expr → MetaM (Array Expr)
  | 0, _ => throwError "payload dependency exceeds depth budget 512"
  | fuel + 1, e => do
    let e ← withReducible (whnf (← instantiateMVars e))
    let mut found := #[]
    let args := e.getAppArgs
    if let .const name _ := e.getAppFn then
      if name.toString.startsWith "Effect4." then
        if let some (.inductInfo info) := (← getEnv).find? name then
          if args.size != info.numParams || e.hasFVar || e.hasMVar then
            throwError "uninstantiated payload carrier: {e}"
          found := found.push e
    for arg in args do
      found := found ++ (← nominalTypes fuel arg)
    return found

def familyJson (instanceTy : Expr) : MetaM (Json × Array Expr) := do
  let .const name _ := instanceTy.getAppFn | throwError "not a nominal carrier: {instanceTy}"
  let info ← getConstInfoInduct name
  let params := instanceTy.getAppArgs
  let mut ctors := #[]
  let mut dependencies := #[]
  for ctor in info.ctors do
    let ci ← getConstInfoCtor ctor
    let (args, nested) ← forallTelescope ci.type fun xs _ => do
      let fieldVars := xs[ci.numParams:].toArray
      let mut fields := #[]
      let mut nested := #[]
      for i in [:fieldVars.size] do
        let x := fieldVars[i]!
        let ty := (← inferType x).replaceFVars (xs[:ci.numParams].toArray) params
        let proof ← isProp ty
        if !proof then nested := nested ++ (← nominalTypes 512 ty)
        let closed := ty.abstract (fieldVars[:i].toArray)
        fields := fields.push (obj [
          ("name", str (← x.fvarId!.getUserName).toString),
          ("type", ← typeJson 512 closed), ("proof", toJson proof)])
      return (fields, nested)
    dependencies := dependencies ++ nested
    ctors := ctors.push (obj [("name", str ctor.getString!),
      ("ordinal", toJson ctors.size), ("arguments", .arr args)])
  let env ← getEnv
  let fields := if isStructure env name then
    (getStructureFields env name).map (str ∘ Name.getString!) else #[]
  return (obj [("family", str name.toString), ("instance", ← typeJson 512 instanceTy),
    ("kind", str (if isStructure env name then "structure" else "inductive")),
    ("mutual", toJson (info.all.map Name.toString)),
    ("fields", .arr fields), ("constructors", .arr ctors)], dependencies)

def closureJson (names : Array String) : MetaM Json := do
  let mut pending ← names.mapM (selectedType ∘ String.toName)
  let mut output := #[]
  let mut index := 0
  for _ in [:256] do
    if index < pending.size then
      let (record, nested) ← familyJson pending[index]!
      output := output.push record
      for ty in nested do
        if !pending.contains ty then pending := pending.push ty
      index := index + 1
  if index < pending.size then throwError "payload carrier closure exceeds reviewed bound 256"
  return obj [("format", .str "effect4-reflected-shapes-v1"),
    ("roots", toJson names), ("families", .arr output)]

end Compatibility

def main (args : List String) : IO Unit := do
  let [inventory, output] := args | throw (IO.userError "expected inventory.json output.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile inventory))
  let families ← IO.ofExcept ((json.getObjVal? "families").bind Json.getArr?)
  let names ← families.mapM fun f => IO.ofExcept ((f.getObjVal? "family").bind Json.getStr?)
  if names.isEmpty then throw (IO.userError "empty family inventory")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Native },
    { module := `Effect4.Schema.Document }, { module := `Effect4.Store.Pin },
    { module := `Effect4.Store.Node }] {} 0
  let action : MetaM Json := do
    Compatibility.closureJson names
  let (json, _) ← (action.run' {}).toIO { fileName := "<compatibility>", fileMap := default } { env }
  IO.FS.writeFile output (json.pretty ++ "\n")
