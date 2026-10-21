import Lean
import OCaml5.Ml.Identifier
import OCaml5.Lcnf.TypeRows

/-!
# OCaml5.Lcnf.Naming

**What it is.** How a Lean name becomes an OCaml one on the LCNF route: type names, field
names, constructor names, global value names and local binder names. One place, so that
`Types` (which emits the declarations) and `Translate` (which emits the uses) agree by
construction rather than by convention. It also holds the public rule (`publicName`, R6.2): the
path a client writes for a public declaration, read off the Lean name before LCNF changes it.

**Depends on.** `OCaml5.Ml.Identifier` (`reservedNames`, `tyVarName`),
`OCaml5.Lcnf.TypeRows` (`reservedTypeNames`) and `Lean.Name`.

**Properties.**
* Every function is total and produces an OCaml identifier of the right lexical class
  (§11.4: a `value-name`/`field-name`/`typeconstr-name` starts lowercase or `_`, a
  `constr-name` uppercase) — *by construction*: `snake` only ever emits `[a-z0-9_']` and
  `_uNNN` escapes, `ctorName` prefixes the type's own capitalised short name.
* A keyword can never come out: `snake` appends `_` to a reserved word (`exit` → `exit_`,
  `val` → `val_`) — *by construction*.
* A type name never shadows one a type row spells: `typeName` and `fullTypeName` append `_` to a
  name of `reservedTypeNames` (a Lean `Result` is `result_`, and `result` stays `Except`'s) —
  *by construction*.
* Public paths are refused, never renumbered: `publicNames` refuses two declarations with one
  public path by both names — *tested* (`aB` and `a_b`, below).
* Readability over injectivity: `snake` is *not* injective (`aB` and `a_b` both go to
  `a_b`). This route names *whole declarations and fields of one file*, where a collision
  is a build error the generator reports, not a silent hole. Within one function
  body `Translate` makes binder names unique by a numeric suffix, keyed on the LCNF
  `FVarId`, so shadowing in the source can never become capture in the target — *tested*
  (`Dispatcher.insert`, whose `Bucket.mk priority tasks` alternative shadows the parameter
  `priority`). That is the binder-against-binder half. A binder against a name the body
  leaves free (a generated declaration, a function of the prelude, a name of a builtin form)
  is `Translate`'s reservation and its `hygieneProblems`, not a property of this module.

**Table.**

| Lean | rule | OCaml |
| --- | --- | --- |
| type `Effect4.Machine.RunFiber` | last component, camel → snake | `run_fiber` |
| type `Effect4.Api.Result` | as above; a type row's name gets a `_` suffix | `result_` |
| field `currentOpCount`, `exit` | camel → snake, keyword/shadowed → `_` suffix | `current_op_count`, `exit_` |
| constructor `Task.resume` | `<TypeShort>_<ctor>` | `Task_resume` |
| type at its owner `Effect4.Program.Eff` (`TypeNames.modules`) | a module by the short name; the type is `t` | `Eff.t` |
| its constructor `Eff.succeed`, its field `Row.typeArgs` | the Lean name, capitalised; a field as above | `Eff.Succeed`, `Row.type_args` |
| type of a used artifact `Effect4.Store.Image` (`TypeNames.units`), its field `toVal` | the names that artifact gives them, qualified by its module | `Eff_image.image`, `Eff_image.to_val` |
| placeholder type `Prim` | `Placeholder_<type>` | `Placeholder_prim` |
| global `Effect4.Machine.Dispatcher.insert._redArg` | drop `._redArg`, private prefix, `Effect4.[Machine.]`; `._at_.` → `at`; components joined by `_` | `dispatcher_insert` |
| global `List.mapTR.loop._at_.Effect4.Machine.Dispatcher.drain.spec_0` | same | `list_map_tr_loop_at_dispatcher_drain_spec_0` |
| local `_x.10`, `head.6`, `interruptedCause` | components joined by `_`, camel → snake | `_x_10`, `head_6`, `interrupted_cause` |
| type parameter `ν`, `St` | `Ml.Identifier.tyVarName` | `'nu`, `'st` |
-/

namespace OCaml5.Lcnf

open Lean

/-- camelCase → snake_case on one identifier component. `?` becomes `_opt`, `!` becomes
`_bang`, any other character outside `[A-Za-z0-9_']` becomes `_u` followed by its code, and a
result that is an OCaml keyword (or the shadowed `exit`) gets a `_` appended. -/
def snake (s : String) : String := Id.run do
  let mut out := ""
  let mut prevLower := false
  for c in s.toList do
    if c.isUpper then
      if prevLower then out := out.push '_'
      out := out.push c.toLower
      prevLower := false
    else if c.isAlphanum || c == '_' || c == '\'' then
      out := out.push c
      prevLower := c.isLower || c.isDigit
    else if c == '?' then
      out := out ++ "_opt"; prevLower := true
    else if c == '!' then
      out := out ++ "_bang"; prevLower := true
    else
      out := out ++ "_u" ++ toString c.toNat; prevLower := true
  if Ml.reservedNames.contains out then out := out ++ "_"
  return out

/-- The string components of a name, private prefix removed, numeric components as digits. -/
def components (n : Name) : List String :=
  let n := if isPrivateName n then privateToUserName n else n
  n.components.map fun
    | .str _ s => s
    | .num _ k => toString k
    | .anonymous => ""

/-- The last string component of a name (`Effect4.Machine.RunFiber` → `RunFiber`). -/
def shortName (n : Name) : String :=
  match (components n).reverse with
  | s :: _ => s
  | [] => ""

/-- A type name, kept off the names the type rows spell (`reservedTypeNames`). -/
def reserveType (s : String) : String :=
  if reservedTypeNames.contains s then s ++ "_" else s

/-- The OCaml type name of a Lean type constant. -/
def typeName (n : Name) : String := reserveType (snake (shortName n))

/-- The decided OCaml names of a run's type constants, fixed once per run **before** anything is
rendered, so a declaration, an annotation and a constructor never disagree about a name.

* `renamed`: type constants whose short name is claimed by another constant of the same run, and
  the OCaml name they take instead (the full path, snake case). `typeName` is the last
  component, so two Lean types with one short name — `Effect4.Api.Outcome` and
  `Effect4.Machine.Outcome`, say — would otherwise be spelled the same.
* `modules`: the types declared at their owner (`ocaml/eff/eff_types.ml`, the program types),
  each its own OCaml module: the type is `M.t`, a constructor `M.C` and a field `M.f`, by the
  Lean names. Every artifact that opens the owner spells them so.
* `units`: the types an artifact this one uses declares (`OCaml5.Lcnf.Gen`'s `--use`), each with
  that artifact's module. The type, its constructors and its fields keep the names that artifact
  gives them, qualified by its module (`Eff_image.image`, `Eff_image.to_val`), so a value this
  artifact builds and a binding it links have one type. -/
structure TypeNames where
  renamed : Std.HashMap Name String := {}
  modules : Std.HashMap Name String := {}
  units : Std.HashMap Name String := {}
deriving Inhabited

/-- A name of a type's family, qualified by the module of the used artifact that declares the type
(`TypeNames.units`); unqualified for any other type. -/
def inUnit (tn : TypeNames) (typeConst : Name) (s : String) : String :=
  match tn.units[typeConst]? with
  | some u => u ++ "." ++ s
  | none => s

/-- The full-path OCaml name a colliding type constant falls back to. -/
def fullTypeName (n : Name) : String := reserveType (snake ("_".intercalate (components n)))

/-- A name with its first character in upper case: an OCaml module or constructor name from a
Lean one (`succeed` → `Succeed`). -/
def capital (s : String) : String :=
  match s.toList with
  | c :: rest => String.ofList ((if c.isLower then c.toUpper else c) :: rest)
  | [] => "T"

/-- The OCaml module of a type declared at its owner: the Lean short name (`Effect4.Program.Eff`
→ `Eff`). -/
def moduleName (n : Name) : String := capital (shortName n)

/-- The module a type declared at its owner falls back to when its short name is claimed twice
(`Effect4.Row` beside `Effect4.Program.Row` → `Effect4_row`). -/
def fullModuleName (n : Name) : String := capital (fullTypeName n)

/-- The OCaml type name of a Lean type constant under the decided names: `M.t` for a type at its
owner, else its flat name, qualified by its module for a type of a used artifact. -/
def typeNameIn (tn : TypeNames) (n : Name) : String :=
  match tn.modules[n]? with
  | some m => m ++ ".t"
  | none => inUnit tn n (tn.renamed.getD n (typeName n))

/-- The name a declaration states: `t` inside its module for a type at its owner, else the flat
name its uses spell. -/
def declTypeNameIn (tn : TypeNames) (n : Name) : String :=
  if tn.modules.contains n then "t" else typeNameIn tn n

/-- The OCaml field name of a Lean structure field. -/
def fieldName (s : String) : String := snake s

/-- A field of a structure under the decided names: `M.f` for a type at its owner and `U.f` for a
type of a used artifact, so a use never depends on the label being in scope. -/
def fieldNameIn (tn : TypeNames) (typeConst : Name) (s : String) : String :=
  match tn.modules[typeConst]? with
  | some m => m ++ "." ++ fieldName s
  | none => inUnit tn typeConst (fieldName s)

/-- The OCaml constructor name of a Lean constructor: the type's short name, verbatim and
capitalised, then `_`, then the constructor's own name verbatim. -/
def ctorName (typeConst : Name) (ctor : String) : String :=
  capital (shortName typeConst) ++ "_" ++ ctor

/-- A constructor of a type declared at its owner, as the declaration states it inside its
module: the Lean name, capitalised (`succeed` → `Succeed`). -/
def ownedCtor (ctor : String) : String := capital ctor

/-- `ctorName` under the decided names: `M.C` for a type at its owner (`Eff.Succeed`); a renamed
type's constructors are prefixed by the renamed type's own OCaml name, so two types that shared
a short name no longer share their constructor names either; a type of a used artifact's are
qualified by its module. -/
def ctorNameIn (tn : TypeNames) (typeConst : Name) (ctor : String) : String :=
  match tn.modules[typeConst]?, tn.renamed[typeConst]? with
  | some m, _ => m ++ "." ++ ownedCtor ctor
  | none, none => inUnit tn typeConst (ctorName typeConst ctor)
  | none, some t => inUnit tn typeConst (capital t ++ "_" ++ ctor)

/-- The name a declaration states for a constructor: `C` inside its module for a type at its
owner, else the flat name its uses spell. -/
def declCtorNameIn (tn : TypeNames) (typeConst : Name) (ctor : String) : String :=
  if tn.modules.contains typeConst then ownedCtor ctor else ctorNameIn tn typeConst ctor

/-- The constructor name of a placeholder type. -/
def placeholderCtor (typeConst : Name) : String := "Placeholder_" ++ typeName typeConst

/-- `placeholderCtor` under a decided rename map. A type at its owner is declared in full, never
as a placeholder (`generateInFull`). -/
def placeholderCtorIn (tn : TypeNames) (typeConst : Name) : String :=
  "Placeholder_" ++ typeNameIn tn typeConst

/-- The prefixes stripped from a global name, longest first. -/
def globalPrefixes : List String := ["Effect4.Machine.", "Effect4."]

/-- The OCaml value name of a global Lean constant (a definition, a `_redArg` twin, a
lambda-lifted `_lam_N`, a specialisation `…._at_.…spec_N`). -/
def globalName (n : Name) : String := Id.run do
  let cs := components n
  -- drop the reduceArity suffix: the twin is emitted under the wrapper's name
  let cs := match cs.reverse with
    | "_redArg" :: rest => rest.reverse
    | _ => cs
  let mut s := ".".intercalate cs
  s := (s.replace "._at_." ".at.")
  for p in globalPrefixes do
    if s.startsWith p then
      s := (s.drop p.length).toString
      break
  -- a specialisation's `_at_` marker names the host: strip the prefixes there too
  s := s.replace ".at.Effect4.Machine." ".at." |>.replace ".at.Effect4." ".at."
  return "_".intercalate ((s.splitOn ".").map snake)

/-- The OCaml name of a local binder (`_x.10`, `head.6`, `interruptedCause`). -/
def localName (n : Name) : String :=
  let cs := components n
  let cs := if cs.isEmpty then ["_x"] else cs
  let s := "_".intercalate (cs.map snake)
  -- `snake` may leave a leading digit or an uppercase start behind a numeric component
  match s.toList with
  | c :: _ => if c.isDigit then "_" ++ s else s
  | [] => "_x"

/-- An OCaml type variable for a Lean type parameter, without the `'`. -/
def tyVar (n : Name) : String := Ml.tyVarName (shortName n)

/-! ## Checks -/

#guard snake "currentOpCount" == "current_op_count"
#guard snake "RunMachine" == "run_machine"
#guard snake "mapTR" == "map_tr"
#guard snake "exit" == "exit_"
#guard snake "fiber?" == "fiber_opt"
#guard snake "spec_0" == "spec_0"
#guard typeName `Effect4.Machine.RunFiber == "run_fiber"
#guard typeName `Effect4.Supervision.ObserverMode == "observer_mode"
#guard typeName `Effect4.Api.Result == "result_" && typeName `Effect4.Program.Option == "option_"
#guard fullTypeName `Result == "result_"
#guard ctorName `Effect4.Machine.Task "resume" == "Task_resume"
#guard ctorName `Effect4.Machine.Parked "notParked" == "Parked_notParked"
-- a type at its owner: a module, its type `t`, its constructors and fields by the Lean names
private def ownerNames : TypeNames := { modules := ({} : Std.HashMap Name String).insert `Effect4.Program.Eff "Eff" }
#guard typeNameIn ownerNames `Effect4.Program.Eff == "Eff.t"
#guard declTypeNameIn ownerNames `Effect4.Program.Eff == "t"
#guard ctorNameIn ownerNames `Effect4.Program.Eff "failCause" == "Eff.FailCause"
#guard declCtorNameIn ownerNames `Effect4.Program.Eff "failCause" == "FailCause"
#guard fieldNameIn ownerNames `Effect4.Program.Eff "typeArgs" == "Eff.type_args"
-- any other type keeps its flat spelling, and a renamed one its full path
#guard ctorNameIn ownerNames `Effect4.Machine.Task "resume" == "Task_resume"
#guard ctorNameIn { renamed := ({} : Std.HashMap Name String).insert `Effect4.Row "effect4_row" } `Effect4.Row "x"
  == "Effect4_row_x"
-- a type of a used artifact keeps that artifact's names, qualified by its module; the same type
-- in a run that uses no artifact is its own, unqualified
private def usedNames : TypeNames :=
  { units := ({} : Std.HashMap Name String).insert `Effect4.Store.Image "Eff_image",
    renamed := ({} : Std.HashMap Name String).insert `Effect4.Row "effect4_row" }
#guard typeNameIn usedNames `Effect4.Store.Image == "Eff_image.image"
#guard fieldNameIn usedNames `Effect4.Store.Image "toVal" == "Eff_image.to_val"
#guard ctorNameIn usedNames `Effect4.Store.Image "mk" == "Eff_image.Image_mk"
#guard typeNameIn usedNames `Effect4.Row == "effect4_row" && typeNameIn {} `Effect4.Store.Image == "image"
#guard fieldNameIn {} `Effect4.Store.Image "toVal" == "to_val"
#guard fullModuleName `Effect4.Row == "Effect4_row" && moduleName `Effect4.Program.Row == "Row"
#guard globalName `Effect4.Machine.Dispatcher.insert._redArg == "dispatcher_insert"
#guard globalName `Effect4.Machine.RunMachine.fiber?._redArg == "run_machine_fiber_opt"
#guard globalName `List.appendTR._redArg == "list_append_tr"
#guard globalName `List.mapTR.loop._at_.Effect4.Machine.Dispatcher.drain.spec_0._redArg
  == "list_map_tr_loop_at_dispatcher_drain_spec_0"
#guard localName (.num (.str .anonymous "_x") 10) == "_x_10"
#guard localName (.num (.str .anonymous "head") 6) == "head_6"
#guard localName `interruptedCause == "interrupted_cause"
#guard localName `val == "val_"
#guard tyVar `ν == "nu"
#guard tyVar `St == "st"

/-! ## Public names (R6.2)

A public name is the OCaml path a client writes for a Lean declaration. It is read off the Lean
name before LCNF changes it, so a reduction, a specialisation or a lifted lambda never moves a
public path, and `globalName` keeps spelling the generated units as it always has. The rule:

| Lean | public path |
| --- | --- |
| value `Effect4.Run.Tree.ofProgram` | `Effect4.Run.Tree.of_program`: the namespace as modules, the name by `snake` |
| type `Effect4.Program.Eff` | `Effect4.Program.Eff.t`: one module per type, the type `t` |
| constructor `Effect4.Program.Eff.succeed` | `Effect4.Program.Eff.Succeed`: capitalised at its owner (`ownedCtor`) |
| field `Effect4.ServiceKey.name` | `Effect4.ServiceKey.name`: at its owner, by `fieldName` |
| value `Effect4.Live.open` | `Effect4.Live.open_`: a reserved word takes `_`, `snake`'s one rule |

A name the rule cannot spell is refused, never mangled: a private, hygienic or numeric component,
a component that starts with `_` (the compiler's `_redArg`, `_lam_0`, `_at_`, `spec` markers), or a
namespace component that is no OCaml module name. Two declarations with one path are refused by
both names, in the order listed: the rule never renumbers a path because another arrived. -/

/-- What a public name names, which is its namespace in OCaml. -/
inductive PublicKind where
  /-- A value: a root of the recipe. -/
  | value
  /-- A type, `t` in its own module. -/
  | type
  /-- A constructor, at its type's module. -/
  | ctor
  /-- A record field, at its type's module. -/
  | field
deriving DecidableEq, Repr, Inhabited, Hashable

/-- A Lean declaration's public OCaml path. -/
structure PublicName where
  source : Name
  kind : PublicKind
  /-- The module path, outermost first (`["Effect4", "Run", "Tree"]`). -/
  modules : List String
  /-- The name inside the innermost module (`of_program`, `t`, `Succeed`). -/
  localName : String
deriving DecidableEq, Repr, Inhabited

/-- The path as a client writes it (`Effect4.Run.Tree.of_program`). -/
def PublicName.path (p : PublicName) : String := ".".intercalate (p.modules ++ [p.localName])

/-- The path as a name, the client name of a facade row (`OCaml5.Lcnf.Export.ExportPlan.facade`). -/
def PublicName.asName (p : PublicName) : Name :=
  (p.modules ++ [p.localName]).foldl Name.mkStr .anonymous

/-- Why a Lean name has no public path. -/
inductive NameRefusal where
  /-- The rule cannot spell it; `why` says which component. -/
  | unsupported (source : Name) (why : String)
  /-- Two Lean declarations with one public path, the first listed and the second. -/
  | collision (first second : Name)
deriving DecidableEq, Repr, Inhabited

/-- The refusal as one line of the generator's report. -/
def NameRefusal.message : NameRefusal → String
  | .unsupported n why => s!"public names: {n} has no public path: {why}"
  | .collision a b => s!"public names: {a} and {b} have one public path; rename one of them"

/-- The string components of a source name, or the reason the rule cannot read it. -/
private def publicComponents (source : Name) : Except NameRefusal (List String) := do
  if source.isAnonymous then throw (.unsupported source "an anonymous name")
  if isPrivateName source then throw (.unsupported source "a private name")
  if source.hasMacroScopes then throw (.unsupported source "a hygienic name")
  let parts ← source.components.mapM fun
    | .str _ s => pure s
    | _ => throw (.unsupported source "a numeric component")
  if let some s := parts.find? (·.startsWith "_") then
    throw (.unsupported source s!"the compiler-made component `{s}`")
  return parts

/-- The public path of one Lean declaration of the given kind (R6.2's `publicName`). A value's
modules are its namespace; a type is `t` in a module of its own; a constructor and a field live in
their type's module. -/
def publicName (kind : PublicKind) (source : Name) : Except NameRefusal PublicName := do
  let parts ← publicComponents source
  let (owner, last) ← match kind, parts.reverse with
    | .type, _ :: _ => pure (parts, "t")
    | _, l :: rest@(_ :: _) =>
      pure (rest.reverse, match kind with
        | .ctor => ownedCtor l
        | .field => fieldName l
        | _ => snake l)
    | _, _ => throw (.unsupported source "no namespace to hold it")
  let modules := owner.map capital
  if let some m := modules.find? (!Ml.isUpperIdent ·) then
    throw (.unsupported source s!"`{m}` is no OCaml module name")
  let valid := match kind with
    | .ctor => Ml.isUpperIdent last
    | _ => Ml.isLowerIdent last || last == "t"
  unless valid do throw (.unsupported source s!"`{last}` is no OCaml name of its kind")
  return { source := source, kind := kind, modules := modules, localName := last }

/-- The public paths of a list of declarations, refusing the first two distinct declarations of
one kind's namespace that share a path. A declaration listed twice under one kind is one name. -/
def publicNames (sources : List (PublicKind × Name)) : Except NameRefusal (List PublicName) := do
  let mut out : Array PublicName := #[]
  let mut taken : Std.HashMap (PublicKind × List String × String) Name := {}
  for (kind, source) in sources.eraseDups do
    let p ← publicName kind source
    match taken[(kind, p.modules, p.localName)]? with
    | some first => throw (.collision first source)
    | none =>
      taken := taken.insert (kind, p.modules, p.localName) source
      out := out.push p
  return out.toList

/-! ### Controls of the public rule -/

private def pathOf (kind : PublicKind) (n : Name) : String :=
  match publicName kind n with
  | .ok p => p.path
  | .error r => r.message

-- R6.2's frozen paths, by the rule
#guard pathOf .type `Effect4.Program.Eff == "Effect4.Program.Eff.t"
#guard pathOf .ctor `Effect4.Program.Eff.succeed == "Effect4.Program.Eff.Succeed"
#guard pathOf .value `Effect4.Program.Authoring.loopWith == "Effect4.Program.Authoring.loop_with"
#guard pathOf .value `Effect4.Run.Tree.ofProgram == "Effect4.Run.Tree.of_program"
#guard pathOf .type `Effect4.Store.Val == "Effect4.Store.Val.t"
#guard pathOf .type `Effect4.Tool.Native.Session == "Effect4.Tool.Native.Session.t"
-- a reserved word takes `_`, by `snake`'s one rule; a field keeps its owner's spelling
#guard pathOf .value `Effect4.Live.open == "Effect4.Live.open_"
#guard pathOf .value `Effect4.Program.Check.HitRule.or == "Effect4.Program.Check.HitRule.or_"
#guard pathOf .field `Effect4.Program.Row.typeArgs == "Effect4.Program.Row.type_args"
-- the compiler's names have no public path
#guard match publicName .value `Effect4.Machine.stepDecisionState._at_.Effect4.Program.replayCheckedFrom.spec_1 with
  | .error (.unsupported _ _) => true
  | _ => false
#guard match publicName .value `Effect4.Machine.Dispatcher.insert._redArg with
  | .error (.unsupported _ _) => true
  | _ => false
#guard match publicName .value `topLevel with
  | .error (.unsupported _ _) => true
  | _ => false
-- red control (R6.2): `aB` and `a_b` share `a_b`; the rule refuses both by name and never
-- renumbers one of them
#guard match publicNames [(.value, `Test.Names.aB), (.value, `Test.Names.a_b)] with
  | .error (.collision a b) => a == `Test.Names.aB && b == `Test.Names.a_b
  | _ => false
-- green twins: a value `t` and a type share a module but not a namespace, and one name listed
-- twice is one name
#guard match publicNames [(.type, `A.B), (.value, `A.B.t), (.value, `A.B.t)] with
  | .ok ps => ps.map PublicName.path == ["A.B.t", "A.B.t"]
  | .error _ => false

end OCaml5.Lcnf
