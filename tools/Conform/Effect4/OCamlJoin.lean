import Conform.Effect4.TargetOCamlEff
import Conform.Layout.Check
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render

/-!
# Conform.Effect4.OCamlJoin — the OCaml side of the join, closed the way the TypeScript one was

    lake env lean -M4096 --run tools/Conform/Effect4/OCamlJoin.lean \
      <outdir> <eff_types.ml> <api_gen.ml> [<scanned .ml> …]

Three things, all over the *one* layout datum `Conform.Effect4.targetOCamlEff`:

1. **The type declaration, generated from the datum.** `mlTypeDecl` turns the datum's rule for
   a family — its discrimination, its per-constructor payload, and the OCaml spellings the rule
   carries — into an `OCaml5.Ml.TypeDecl`, and `OCaml5.Ml.renderDecl` writes it. The result is
   compared, structurally and byte for byte, with the `ty` declaration of the two OCaml
   producers this tree already has: `ocaml/eff/eff_types.ml` (written by `OCaml5.Eff.Emit`) and
   `ocaml/gen/api_gen.ml` (written by `OCaml5.Lcnf`).

2. **The differential** is `docs/research/type-tooling/layout/x2_diff.ml`, out of process; this
   driver only records its receipt path.

3. **The audit form of `layout.coherent` over generated OCaml.** `recoverTable` scans `.ml`
   text for the layout's own constructor spellings and splits the occurrences into a
   construction table and a destruction table by OCaml's one syntactic difference — a `|` that
   opens a match arm — and `Conform.Layout.auditCoherence` compares the two with each other and
   with the datum.

**Depends on.** `Conform.Effect4.TargetOCamlEff`, `Conform.Layout.Check`, `OCaml5.Ml.*`.
-/

open Lean Meta
open Conform Conform.Layout

namespace Conform.Effect4

/-! ## The type declaration, from the datum -/

/-- The OCaml type a `TypeRef` has under a target, read off that target's rules. Every arm is
the rule's own discrimination, so the declaration this produces and the values `encodeAt`
produces are the same layout. -/
partial def mlTyOf (T : Target) (W : World) (fuel : Nat) (ty : TypeRef) :
    Except String OCaml5.Ml.Ty := do
  if fuel == 0 then throw s!"{ty.render}: budget exhausted" else
  let some h := ty.head? | throw s!"{ty.render}: a parameter has no OCaml carrier"
  let some r := T.ruleFor? ty | throw s!"no rule for {ty.render} in target {T.name}"
  let fieldTy (c : String) (i : Nat) : Except String TypeRef := do
    match fieldTypes W ty c with
    | .error e => throw e.render
    | .ok tys => match tys[i]? with
      | some t => pure t
      | none => throw s!"{h}.{c} has no field {i}"
  let payloadCtor (arity : Nat) : Except String String := do
    let some tv := W.find? h | throw s!"{h} is not in the world"
    match tv.ctors.find? (·.fields.length == arity) with
    | some cv => pure cv.name
    | none => throw s!"{h} has no constructor of arity {arity}"
  match r.discrimination with
  | .nativeScalar .numK | .nativeScalar .bigintK => pure OCaml5.Ml.Ty.int
  | .nativeScalar .strK => pure OCaml5.Ml.Ty.string
  | .nativeScalar .boolK => pure OCaml5.Ml.Ty.bool
  | .nativeScalar .unitK => pure OCaml5.Ml.Ty.unit
  | .nativeOption _ _ => do
    let c ← payloadCtor 1
    pure (.con "option" [← mlTyOf T W (fuel - 1) (← fieldTy c 0)])
  | .nativeSeq => do
    let c ← payloadCtor 2
    pure (.con "list" [← mlTyOf T W (fuel - 1) (← fieldTy c 0)])
  | .nativeTuple => do
    let some tv := W.find? h | throw s!"{h} is not in the world"
    let some cv := tv.ctors.head? | throw s!"{h} has no constructor"
    let parts ← cv.fields.zipIdx.mapM fun (_, i) => do
      mlTyOf T W (fuel - 1) (← fieldTy cv.name i)
    pure (.tuple parts)
  | .unboxed => do
    let some cr := r.ctors.head? | throw s!"{h}: unboxed rule with no constructor"
    mlTyOf T W (fuel - 1) (← fieldTy cr.ctor 0)
  | .variant | .record | .tagField _ | .intTagField _ | .indexed | .literalUnion | .nullable _ =>
    match onameOf h with
    | some o => pure (.con o [])
    | none => throw s!"{h} has no OCaml name in OCaml5.Eff.World"

/-- The `type <name> = …` declaration the datum prescribes for one family. -/
def mlTypeDecl (T : Target) (W : World) (n : Name) : Except String OCaml5.Ml.TypeDecl := do
  let some tv := W.find? n | throw s!"{n} is not in the world"
  let some r := T.rule? n | throw s!"no rule for {n} in target {T.name}"
  let some oname := onameOf n | throw s!"{n} has no OCaml name"
  match r.discrimination with
  | .variant =>
    let ctors ← tv.ctors.mapM fun cv => do
      let some cr := Target.ctorRule? r cv.name | throw s!"no rule for {n}.{cv.name}"
      let args ← cv.fields.mapM fun f => mlTyOf T W 32 f.type
      pure ({ name := cr.tag, args } : OCaml5.Ml.Ctor)
    pure { name := oname, body := .variant ctors }
  | .record =>
    let some cv := tv.ctors.head? | throw s!"{n} has no constructor"
    let some cr := Target.ctorRule? r cv.name | throw s!"no rule for {n}.{cv.name}"
    let names := cr.payload.fieldNames
    let fields ← cv.fields.zipIdx.mapM fun (f, i) => do
      let t ← mlTyOf T W 32 f.type
      pure ({ name := names[i]!, ty := t } : OCaml5.Ml.Field)
    pure { name := oname, body := .record fields }
  | d => throw s!"{n}: {d} is not a declaration shape for OCaml"

/-! ## Reading a `ty` declaration out of an existing `.ml` -/

/-- The lines of the declaration of `<kw> <name> =` in `text`, up to the next top-level
declaration. The two producers write one constructor per line, so the extraction is the line
range and the parse below is per line. -/
def extractDecl (text : String) (name : String) : Option (List String) :=
  let lines := text.splitOn "\n"
  let isHead (l : String) : Bool := l == s!"type {name} =" || l == s!"and {name} ="
  match lines.findIdx? isHead with
  | none => none
  | some i =>
    let rest := lines.drop (i + 1)
    let body := rest.takeWhile fun l => l.startsWith "  |" || l.startsWith "  " && !l.isEmpty
    some ((lines[i]!) :: body)

/-- One constructor row of a rendered variant: `  | Ty_prod of ty * ty` becomes
`("Ty_prod", ["ty", "ty"])`. -/
def parseCtorLine (l : String) : Option (String × List String) :=
  let t : String := l.trimAscii.toString
  if !t.startsWith "|" then none
  else
    let t : String := (t.drop 1).trimAscii.toString
    match (t.splitOn " of ") with
    | [nm] => some (nm.trimAscii.toString, [])
    | [nm, args] => some (nm.trimAscii.toString, (args.splitOn " * ").map (·.trimAscii.toString))
    | _ => none

def parseVariant (lines : List String) : List (String × List String) :=
  lines.filterMap parseCtorLine

/-! ## Recovering the two tables from OCaml text -/

/-- Every constructor spelling of the target, as `<spelling> ↦ (type, constructor)`. -/
def spellingTable (T : Target) : List (String × Name × String) :=
  T.rules.toList.flatMap fun r =>
    match r.discrimination with
    | .variant => r.ctors.map fun cr => (cr.tag, r.type, cr.ctor)
    | _ => []

/-- Split the occurrences of the target's constructor spellings in `.ml` text into a
construction table and a destruction table. OCaml spells the two the same way, and the one
syntactic difference is position: a spelling that opens a match arm (`|` before it on the line,
with nothing but `(` and spaces between) is a pattern, everything else is an application. A
recovered row carries the line it came from, so the recovery can be checked by eye. -/
def recoverTable (T : Target) (name : String) (files : List (String × String)) : EmitterTable :=
  Id.run do
  let table := spellingTable T
  let mut cons : Array EmitterRow := #[]
  let mut dest : Array EmitterRow := #[]
  -- the first occurrence of a `(type, constructor)` on each side is the row kept; these two
  -- sets are that "already have one", in place of a linear scan of the growing arrays.
  let mut consSeen : Std.HashSet (Name × String) := {}
  let mut destSeen : Std.HashSet (Name × String) := {}
  for (file, text) in files do
    for (line, lineNo) in (text.splitOn "\n").zipIdx do
      for (spelling, ty, ctor) in table do
        if !containsWord line spelling then continue
        let shape := (shapeOf T ty ctor).getD "?"
        let row : EmitterRow :=
          { type := ty, ctor, shape, evidence := s!"{file}:{lineNo + 1} {line.trimAscii.toString}" }
        if isPattern line spelling then
          unless destSeen.contains (ty, ctor) do
            destSeen := destSeen.insert (ty, ctor); dest := dest.push row
        else
          unless consSeen.contains (ty, ctor) do
            consSeen := consSeen.insert (ty, ctor); cons := cons.push row
  return { name, construction := cons, destruction := dest }
where
  /-- `Ty_prod` occurs in the line as a whole token, not as a prefix of `Ty_prodX`. -/
  containsWord (line spelling : String) : Bool :=
    let parts := line.splitOn spelling
    parts.length > 1 &&
      parts.tail.any fun after =>
        after.isEmpty || !after.front.isAlphanum && after.front != '_'
  /-- The spelling opens a match arm or a `function` arm. -/
  isPattern (line spelling : String) : Bool :=
    match line.splitOn spelling with
    | before :: _ =>
      let b := before.trimAscii.toString
      b.endsWith "|" || b == "|"
    | [] => false

/-! ## The driver -/

structure JoinInputs where
  outDir : System.FilePath
  effTypes : System.FilePath
  apiGen : System.FilePath
  scanned : List System.FilePath

def compareDecl (subject : String) (generated : List (String × List String))
    (found : List (String × List String)) (rendered found' : String) : Array Row :=
  Id.run do
  let subj : Subject := { kind := "declaration", path := ["ocaml-eff", "ty", subject] }
  let mut rows : Array Row := #[]
  -- structural: the constructor names and their argument spellings, in order
  if generated == found then
    rows := rows.push (Row.pass "ocaml.type-decl.structural" subj .tested
      s!"{generated.length} constructors agree with the datum, name and argument spellings, in \
declaration order"
      (Lean.Json.arr (generated.toArray.map fun (n, args) =>
        Lean.Json.str (n ++ (if args.isEmpty then "" else " of " ++ " * ".intercalate args)))))
  else
    let diffs := (generated.zip found).filter fun (a, b) => a != b
    rows := rows.push (Row.refused "ocaml.type-decl.structural" subj
      s!"the datum generates {generated.length} constructors and {subject} has {found.length}; \
{diffs.length} rows differ"
      (Lean.Json.mkObj
        [("generated", Lean.Json.arr (generated.toArray.map fun (n, a) =>
            Lean.Json.str (n ++ " of " ++ " * ".intercalate a))),
         ("found", Lean.Json.arr (found.toArray.map fun (n, a) =>
            Lean.Json.str (n ++ " of " ++ " * ".intercalate a)))]))
  -- bytes: the two texts, with the leading keyword normalised (`type` in one producer, `and`
  -- in the other, because `api_gen.ml` puts `ty` inside one big group)
  let norm (s : String) : String := if s.startsWith "and " then "type " ++ (s.drop 4).toString else s
  if norm rendered == norm found' then
    rows := rows.push (Row.pass "ocaml.type-decl.bytes" subj .reproduced
      s!"the datum's rendering is byte-identical to {subject} (after normalising the leading \
`type`/`and` keyword)"
      (Lean.Json.str (norm rendered)))
  else
    rows := rows.push (Row.refused "ocaml.type-decl.bytes" subj
      s!"the datum's rendering differs from {subject}"
      (Lean.Json.mkObj [("generated", Lean.Json.str (norm rendered)),
        ("found", Lean.Json.str (norm found'))]))
  return rows

end Conform.Effect4

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let arg (i : Nat) (d : String) : String := (argv.drop i).headD d
  let outDir : System.FilePath := System.FilePath.mk (arg 0 "/tmp/conform-layout")
  let effTypes : System.FilePath := System.FilePath.mk (arg 1 "ocaml/eff/eff_types.ml")
  let apiGen : System.FilePath := System.FilePath.mk (arg 2 "ocaml/gen/api_gen.ml")
  let scanned : List String := argv.drop 3
  IO.FS.createDirAll outDir
  let env ← importModules #[{ module := `Conform.Effect4.TargetOCamlEff }] {} 0
  let ctx : Core.Context := { fileName := "<conform-ocaml-join>", fileMap := default }
  let act : MetaM UInt32 := do
    let reading ← Conform.Effect4.readEffect4World
    let W := reading.world
    let T := Conform.Effect4.targetOCamlEff W
    -- 1. the declaration, generated from the datum
    let decl ← match Conform.Effect4.mlTypeDecl T W `Effect4.Program.Ty with
      | .ok d => pure d
      | .error e => throwError e
    let rendered := OCaml5.Ml.renderDecl (.types [decl])
    IO.FS.writeFile (outDir / "ty-from-datum.ml") (rendered ++ "\n")
    let mut rows : Array Conform.Row := #[]
    let generated := Conform.Effect4.parseVariant ((rendered.splitOn "\n").drop 1)
    for (label, path) in [("eff_types.ml", effTypes), ("api_gen.ml", apiGen)] do
      let text ← IO.FS.readFile path
      match Conform.Effect4.extractDecl text "ty" with
      | none =>
        rows := rows.push (Conform.Row.unresolved "ocaml.type-decl.structural"
          { kind := "declaration", path := ["ocaml-eff", "ty", label] }
          s!"{path}: no `type ty =` or `and ty =` line")
      | some lines =>
        let found := Conform.Effect4.parseVariant (lines.drop 1)
        rows := rows ++ Conform.Effect4.compareDecl label generated found rendered
          ("\n".intercalate lines)
    let declReport : Conform.Report :=
      { tool := "conform.layout.ocaml-type-decl"
        pins := [⟨"lean", "4.33.1"⟩, ⟨"target", T.name⟩]
        expected := 4, rows }
    IO.FS.writeFile (outDir / "ocaml-type-decl.json") (declReport.sorted.toJson.pretty ++ "\n")
    IO.eprintln declReport.sorted.render
    -- 3. the audit form over the scanned OCaml
    unless scanned.isEmpty do
      let files ← scanned.mapM fun p => do pure (p, ← IO.FS.readFile (System.FilePath.mk p))
      let tbl := Conform.Effect4.recoverTable T "ocaml-eff recovered from generated OCaml" files
      IO.FS.writeFile (outDir / "ocaml-recovered-table.json")
        ((Lean.toJson tbl).pretty ++ "\n")
      let auditRows := Conform.Layout.auditCoherence T tbl
      let auditReport : Conform.Report :=
        { tool := "conform.layout.audit[ocaml-eff recovered]"
          pins := [⟨"lean", "4.33.1"⟩, ⟨"target", T.name⟩]
          expected := auditRows.size, rows := auditRows }
      IO.FS.writeFile (outDir / "ocaml-recovered.json") (auditReport.sorted.toJson.pretty ++ "\n")
      IO.eprintln auditReport.sorted.render
    return declReport.exitCode
  let (code, _) ← (act.run' {}).toIO ctx { env := env }
  return code
