import Lean
import Effect4.Laws.Auto.Positions
import Effect4.Laws.Program.Typed.Vocabulary

/-!
# Laws.Auto.TypedSources — reading the source table as an expression

The typed-state source table is a plain list, `Effect4.Program.Typed.sources : List Row`
(`Typed/Sources.lean`). The totality gate and the skeleton emitter need it as data at meta
level, and the trust gate refuses the ways of *running* it that leave a trust token: `unsafe`
and `implemented_by` are refused by name, and `initialize x : T ← act` — the binder form an
environment extension is declared with — elaborates to a bodyless `opaque`, which the gate
refuses as a declaration. A *binder-free* `initialize` is a plain `def` and is admitted, which
is why `declare_aesop_rule_sets` compiles (`Test/Audit/AxiomGate.lean:101-105`). So the table
is **read, not run**: the constant is
reduced to its constructor form and decoded, a string literal at a time
(`docs/research/2026-09-18-metaprogramming-review.md` §1, the `whnf` and expression-matching
API). A row the decoder does not recognise is a loud error, never a skipped row.
-/

open Lean Meta
open Effect4.Program.Typed

namespace Effect4.Laws.Auto.TypedSources

/-- A string literal, after reduction. -/
private def decodeString (e : Expr) : MetaM String := do
  match (← whnf e) with
  | .lit (.strVal s) => return s
  | e => throwError "typed sources: not a string literal: {e}"

private def decodeOptString (e : Expr) : MetaM (Option String) := do
  let e ← whnf e
  match e.getAppFn with
  | .const ``Option.some _ => return some (← decodeString e.appArg!)
  | .const ``Option.none _ => return none
  | _ => throwError "typed sources: not an optional string: {e}"

private def decodeExpected (e : Expr) : MetaM Expected := do
  let e ← whnf e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Expected.fiber _ => return .fiber (← decodeString args[0]!)
  | .const ``Expected.inherited _ => return .inherited
  | _ => throwError "typed sources: not an expectation: {e}"

private def decodeSource (e : Expr) : MetaM Source := do
  let e ← whnf e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Source.program _ => return .program (← decodeExpected args[0]!)
  | .const ``Source.continuation _ => return .continuation (← decodeExpected args[0]!)
  | .const ``Source.value _ => return .value (← decodeExpected args[0]!)
  | .const ``Source.exit _ => return .exit (← decodeExpected args[0]!)
  | .const ``Source.cause _ => return .cause (← decodeExpected args[0]!)
  | .const ``Source.hook _ => return .hook (← decodeOptString args[0]!)
  | .const ``Source.column _ =>
    unless args.size == 2 do
      throwError "typed sources: column expects a name and optional key constructor: {e}"
    return .column (← decodeString args[0]!) (← decodeOptString args[1]!)
  | .const ``Source.journal _ => return .journal
  | .const ``Source.custom _ => return .custom (← decodeString args[0]!)
  | .const ``Source.owner _ => return .owner (← decodeString args[0]!)
  | .const ``Source.refused _ => return .refused (← decodeString args[0]!)
  | .const ``Source.nested _ => return .nested (← decodeExpected args[0]!)
  | _ => throwError "typed sources: not a source: {e}"

/-- The rows of a `List Row` expression, reduced one cell at a time; bounded by a length. -/
private def decodeRows : Nat → Expr → MetaM (List Row)
  | 0, e => throwError "typed sources: more rows than the reader's bound at {e}"
  | fuel + 1, e => do
    let e ← whnf e
    let args := e.getAppArgs
    match e.getAppFn with
    | .const ``List.nil _ => return []
    | .const ``List.cons _ =>
      let cell ← whnf args[1]!
      let pair := cell.getAppArgs
      unless cell.getAppFn.isConstOf ``Prod.mk do
        throwError "typed sources: not a row: {cell}"
      let key ← decodeString pair[2]!
      let src ← decodeSource pair[3]!
      return (key, src) :: (← decodeRows fuel args[2]!)
    | _ => throwError "typed sources: not a list: {e}"

/-- The table, read from the environment: `Effect4.Program.Typed.sources`. -/
def readRows (table : Name := `Effect4.Program.Typed.sources) : MetaM (List Row) := do
  -- named without resolution: the table is in the module that runs the gate, not in this reader
  let e := mkConst table
  decodeRows 10000 e

/-- An owner source is keyed by the structure or the constructor, never by a leaf. -/
def ownerSource (rows : List Row) (key : Name) : Option String :=
  match rows.find? (·.1 == key.toString) with
  | some (_, .owner pred) => some pred
  | _ => none

/-- Which whole-owner row covers this direct field. Single-constructor inductives use
unqualified field labels in the census, even when they are not structures. -/
def fieldOwner (rows : List Row) (owner : Name) (field : String) : MetaM (Option String) := do
  if (ownerSource rows owner).isSome then return some owner.toString
  let iv ← getConstInfoInduct owner
  let ctor := if iv.ctors.length == 1 then iv.ctors.head! else
    owner ++ Name.mkSimple (field.splitOn ".").head!
  if (ownerSource rows ctor).isSome then return some ctor.toString
  return none

structure OwnerCoverage where
  ownerKeys : Array String := #[]
  covered : Array String := #[]
  active : Array String := #[]

/-- Ownership is occurrence-sensitive. A nested type reached both under a whole owner and
through another path still needs its ordinary rows on that other path. Only rows entirely
beneath owner coverage are duplicates. Existing whole-field rows keep their earlier census
contract: they do not erase descendant source rows from the table. -/
def ownerCoverage (rows : List Row) (roots : Array Name)
    (edges : Array Positions.Edge)
    (seen : Array Expr) : MetaM OwnerCoverage := do
  let env ← getEnv
  let visited := seen.filterMap fun ty => ty.getAppFn.constName?
  let mut out : OwnerCoverage := {}
  for (key, source) in rows do
    if let .owner _ := source then
      let name := key.toName
      let owner ← match env.find? name with
        | some (.inductInfo _) =>
          if isStructure env name then pure name
          else throwError "typed state: owner row {key} must name a structure or constructor"
        | some (.ctorInfo ci) => pure ci.induct
        | _ => throwError "typed state: owner row {key} must name a structure or constructor"
      unless visited.contains owner do
        throwError "typed state: owner row {key} is outside the census"
      if name != owner && (ownerSource rows owner).isSome then
        throwError "typed state: duplicate owner coverage at {key}"
      out := { out with ownerKeys := out.ownerKeys.push key }
  let mut activeOwners : Array Name := #[]
  for root in roots do
    let ty ← whnf (mkConst root)
    activeOwners := activeOwners.push ty.getAppFn.constName!
  let mut coveredOwners : Array Name := #[]
  -- Metadata is not a value position, but a second row on any real owner field is
  -- still duplicate coverage. Read the constructor signature, including those fields.
  let mut fields : Array (Name × String) := #[]
  let mut ownedFields : Array String := #[]
  for owner in visited.toList.eraseDups do
    let iv ← getConstInfoInduct owner
    for ctor in iv.ctors do
      let ci ← getConstInfoCtor ctor
      for arg in Positions.ctorArgNames ci.type ci.numParams do
        let field := if iv.ctors.length == 1 then arg else s!"{ctor.getString!}.{arg}"
        fields := fields.push (owner, field)
        if (← fieldOwner rows owner field).isSome then
          ownedFields := ownedFields.push s!"{owner}.{field}"
  for _ in [:edges.size + 1] do
    for e in edges do
      let key := s!"{e.parent}.{e.field}"
      if activeOwners.contains e.parent && !ownedFields.contains key &&
          !activeOwners.contains e.child then activeOwners := activeOwners.push e.child
      if (ownedFields.contains key || coveredOwners.contains e.parent) &&
          !coveredOwners.contains e.child then coveredOwners := coveredOwners.push e.child
  for (owner, field) in fields do
    let key := s!"{owner}.{field}"
    if ownedFields.contains key || coveredOwners.contains owner then
      out := { out with covered := out.covered.push key }
    if activeOwners.contains owner && !ownedFields.contains key then
      out := { out with active := out.active.push key }
  for (key, source) in rows do
    match source with
    | .owner _ =>
      let name := key.toName
      let owner := match env.find? name with
        | some (.ctorInfo ci) => ci.induct
        | _ => name
      if coveredOwners.contains owner && !activeOwners.contains owner then
        throwError "typed state: duplicate owner coverage at {key}"
    | _ =>
      if out.covered.contains key && !out.active.contains key then
        throwError "typed state: duplicate owner coverage at {key}"
  return out

end Effect4.Laws.Auto.TypedSources
