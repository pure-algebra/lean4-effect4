import Lean
import OCaml5.Ml.Identifier

/-!
# OCaml5.Lcnf.Naming

**What it is.** How a Lean name becomes an OCaml one on the LCNF route: type names, field
names, constructor names, global value names and local binder names. One place, so that
`Types` (which emits the declarations) and `Translate` (which emits the uses) agree by
construction rather than by convention.

**Depends on.** `OCaml5.Ml.Identifier` (`reservedNames`, `tyVarName`) and `Lean.Name`.

**Properties.**
* Every function is total and produces an OCaml identifier of the right lexical class
  (§11.4: a `value-name`/`field-name`/`typeconstr-name` starts lowercase or `_`, a
  `constr-name` uppercase) — *by construction*: `snake` only ever emits `[a-z0-9_']` and
  `_uNNN` escapes, `ctorName` prefixes the type's own capitalised short name.
* A keyword can never come out: `snake` appends `_` to a reserved word, as
  `Ml.Identifier.mangleField` does (`exit` → `exit_`, `val` → `val_`) — *by construction*.
* Readability over injectivity: `snake` is *not* injective (`aB` and `a_b` both go to
  `a_b`). This route names *whole declarations and fields of one file*, where a collision
  is a build error the generator reports, not a silent hole; the field mangling a
  simulation relation needs is `Ml.Identifier.mangleField`, not this. Within one function
  body `Translate` makes binder names unique by a numeric suffix, keyed on the LCNF
  `FVarId`, so shadowing in the source can never become capture in the target — *tested*
  (`Dispatcher.insert`, whose `Bucket.mk priority tasks` alternative shadows the parameter
  `priority`).

**Table.**

| Lean | rule | OCaml |
| --- | --- | --- |
| type `Effect4.Machine.RunFiber` | last component, camel → snake | `run_fiber` |
| field `currentOpCount`, `exit` | camel → snake, keyword/shadowed → `_` suffix | `current_op_count`, `exit_` |
| constructor `Task.resume` | `<TypeShort>_<ctor>` | `Task_resume` |
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

/-- The OCaml type name of a Lean type constant. -/
def typeName (n : Name) : String := snake (shortName n)

/-- The OCaml field name of a Lean structure field. -/
def fieldName (s : String) : String := snake s

/-- The OCaml constructor name of a Lean constructor: the type's short name, verbatim and
capitalised, then `_`, then the constructor's own name verbatim. -/
def ctorName (typeConst : Name) (ctor : String) : String :=
  let t := shortName typeConst
  let t := match t.toList with
    | c :: rest => String.ofList ((if c.isLower then c.toUpper else c) :: rest)
    | [] => "T"
  t ++ "_" ++ ctor

/-- The constructor name of a placeholder type. -/
def placeholderCtor (typeConst : Name) : String := "Placeholder_" ++ typeName typeConst

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
#guard ctorName `Effect4.Machine.Task "resume" == "Task_resume"
#guard ctorName `Effect4.Machine.Parked "notParked" == "Parked_notParked"
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

end OCaml5.Lcnf
