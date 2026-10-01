import Lean
import Tools.GeneratedStamp

/-!
# Probe U — the table emitter: a per-constructor JSON table to a Lean `TyTable` value

    lake env lean --run U/patches/TableGen.lean faces  <ty-faces.json>   <out.lean>
    lake env lean --run U/patches/TableGen.lean classes <ty-classes.json> <out.lean>

The stage-0 half of a table-driven fold (coherence principle §5: a metaprogram's input is data
in the tree). It reads the constructor list of `Effect4.Program.Ty` from the declaration and
refuses, by name, a table row for no constructor and a constructor with no row — the refusal
`tools/Tools/Variances.lean`'s `headRows` gives a head with no entry — so a constructor
appended to `Ty` cannot reach a generated table without its row. It writes the table as a Lean
value with every field named, so the type checks the columns. A `module` row of the faces table
names the rc.112 module `M` once and is expanded here to both faces (`M.M<…>` and
`effect/schema/M`): the two spellings cannot disagree.
-/

open Lean

namespace ProbeU.TableGen

def ctorsOf (env : Environment) (n : Name) : Except String (List String) :=
  match env.find? n with
  | some (.inductInfo iv) => .ok (iv.ctors.map fun c => c.componentsRev.head!.toString)
  | _ => .error s!"{n} is not an inductive in the environment"

/-- The rows of a table, checked against the constructors: same names, declaration order. -/
def rowsFor (ctors : List String) (rows : Json) : Except String (List (String × Json)) := do
  let .obj kvs := rows | throw "rows: not an object"
  let names := kvs.toArray.toList.map (·.1)
  for n in names do
    unless ctors.contains n do throw s!"row `{n}` names no constructor of the family"
  for c in ctors do
    unless names.contains c do throw s!"constructor `{c}` has no row: give it one before generating"
  ctors.mapM fun c => do
    let some v := kvs.get? c | throw s!"row `{c}` missing"
    return (c, v)

def piece (j : Json) : Except String String := do
  match j.getObjVal? "text", j.getObjVal? "child", j.getObjVal? "leaf" with
  | .ok (.str s), _, _ => return s!".text {s.quote}"
  | _, .ok (.num n), _ => return s!".child {n.mantissa}"
  | _, _, .ok (.bool true) => return ".leaf"
  | _, _, _ => throw s!"piece {j.compress}: expected text, child or leaf"

def schemaSpell (j : Json) : Except String String := do
  if let .ok (.str t) := j.getObjVal? "const" then return s!".const ({t})"
  if (j.getObjVal? "declLeaf").isOk then return ".declLeaf"
  if (j.getObjVal? "literalLeaf").isOk then return ".literalLeaf"
  if (j.getObjVal? "array").isOk then return ".array"
  if (j.getObjVal? "tuple").isOk then return ".tuple"
  if (j.getObjVal? "union").isOk then return ".union"
  throw s!"schema {j.compress}: unknown form"

def natList (j : Json) : Except String (List Nat) := do
  let .arr xs := j | throw "perm: not an array"
  xs.toList.mapM fun x => match x with
    | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then pure n.mantissa.toNat else throw "perm: not a natural"
    | _ => throw "perm: not a number"

def faceRow (c : String) (j : Json) : Except String String := do
  let code ← match j.getObjVal? "code" with
    | .ok (.num n) => pure n.mantissa.toNat
    | _ => throw s!"row `{c}`: no code"
  match j.getObjVal? "module" with
  | .ok (.str m) =>
    let perm ← natList (← j.getObjVal? "perm")
    let extras ← match j.getObjVal? "extras" with
      | .ok (.arr xs) => xs.toList.mapM fun x => match x with
          | .str t => pure t
          | _ => throw s!"row `{c}`: an extra is Lean source text"
      | _ => pure []
    let head := m ++ "." ++ m
    let ts := match perm with
      | [] => [s!".text {head.quote}"]
      | i :: rest => [s!".text {(head ++ "<").quote}", s!".child {i}"] ++
          rest.flatMap (fun k => [s!".text {(", ").quote}", s!".child {k}"]) ++ [s!".text {(">").quote}"]
    let schema := s!".decl {("effect/schema/" ++ m).quote} {perm} [{", ".intercalate extras}]"
    return s!"⟨[{", ".intercalate ts}], {schema}, {code}⟩"
  | _ =>
    let .arr ps ← j.getObjVal? "ts" | throw s!"row `{c}`: ts is not an array"
    let ts ← ps.toList.mapM piece
    let schema ← schemaSpell (← j.getObjVal? "schema")
    return s!"⟨[{", ".intercalate ts}], {schema}, {code}⟩"

def classRow (cols : List String) (c : String) (j : Json) : Except String String := do
  let .arr bs := j | throw s!"row `{c}`: not an array"
  unless bs.size == cols.length do throw s!"row `{c}`: {bs.size} values for {cols.length} columns"
  let vals ← bs.toList.mapM fun b => match b with
    | .bool v => pure (toString v)
    | _ => throw s!"row `{c}`: a value is not a Boolean"
  return "{ " ++ ", ".intercalate ((cols.zip vals).map fun (k, v) => s!"{k} := {v}") ++ " }"

def emit (kind : String) (env : Environment) (j : Json) (src : String) : Except String String := do
  let fam ← match j.getObjVal? "family" with
    | .ok (.str f) => pure f.toName
    | _ => throw "no family"
  let ctors ← ctorsOf env fam
  let rows ← rowsFor ctors (← j.getObjVal? "rows")
  let stamp := Tools.GeneratedStamp.note "docs/research/2026-10-01-type-language-probe/U/patches/TableGen.lean"
  let (imp, decl, ty, body) ← match kind with
    | "faces" => do
      let lines ← rows.mapM fun (c, r) => do return s!"  {c} := {← faceRow c r}"
      pure ("ProbeU.Faces", "tyFaces", "TyTable FaceRow", lines)
    | "classes" => do
      let .arr cs ← j.getObjVal? "columns" | throw "no columns"
      let cols ← cs.toList.mapM fun c => match c with
        | .str s => pure s
        | _ => throw "a column name is not a string"
      let lines ← rows.mapM fun (c, r) => do return s!"  {c} := {← classRow cols c r}"
      pure ("ProbeU.ClassRow", "tyClasses", "TyTable ClassRow", lines)
    | k => throw s!"unknown table kind {k}"
  return s!"-- {stamp}\n-- from {src}\nimport {imp}\n\nset_option autoImplicit false\n\n" ++
    "namespace ProbeU\n\nopen Effect4 Effect4.Program\n\n" ++
    s!"/-- The `{kind}` table of `{fam}`, one row per constructor (from `{src}`). -/\n" ++
    s!"def {decl} : {ty} where\n" ++ "\n".intercalate body ++ "\n\nend ProbeU\n"

end ProbeU.TableGen

open ProbeU.TableGen in
def main (args : List String) : IO Unit := do
  let [kind, input, out] := args | throw (IO.userError "usage: TableGen faces|classes <in.json> <out.lean>")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Ty }] {} 0
  let txt ← IO.FS.readFile input
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{input}: {e}")
  match emit kind env j input with
  | .ok s => IO.FS.writeFile out s
  | .error e => throw (IO.userError s!"{input}: {e}")
