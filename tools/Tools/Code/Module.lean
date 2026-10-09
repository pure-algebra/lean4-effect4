import Tools.Code.TypeScript
import Effect4.Codegen.Admit
import Effect4.Program.Fragment
import Effect4.Store.Carrier.Digest
import Effect4.Api

/-!
# A generated module: its file, its imports, and what was checked of it

What the code generator writes for one program: one TypeScript module that a person or an agent
reads as it is. The module is `Api.emitModule`'s declarations with three additions:

- **its imports, exactly**: the names its declarations use and do not bind, by the core's binding
  analysis (`SourceBindings.moduleUses`). A namespace of `effect` (`effectNamespaces`) and `pipe`
  come from `effect`; every other name from the prelude, which supplies the atoms and the helpers;
- **a header**: the program's content address (SHA-256 of its canonical bytes, `Api.bytesOf`), its
  type, and the checks below;
- **its layout**: Effect's width, 120 columns (`Tools.Code.Ts.decl`). Undone, a layout is the
  house print (`undo_layout`, `Ts.flat_fold_expr`), which the checks read.

The checks are the core's, run on the structured module the text is laid out from. The reading
boundary admits it (`Effect4.Codegen.admitModule`: bindings, read-back, typing, envelope), and
the program it reads back must equal this program. The printed text itself is not parsed here:
it is the structured module laid out, and its flat form is the house print
(`Ts.flat_fold_expr`). `Straight` says whether `run_eq_meaning` covers the program. A refusal is
written in the header and the index, never hidden.
-/

namespace Tools.Code

open Effect4 Effect4.Program Effect4.Codegen TypeScript

/-- The path a generated module imports the prelude from: a folder beside its group's folder. -/
def preludePath : String := "../prelude/prelude.ts"

/-- The names the prelude exports to printed programs: the atoms, the term helpers, and the
printer's heads that are no namespace member. A free name outside these and `effect` is unbound,
and the reading boundary refuses the module. -/
def preludeNames : List String :=
  Effect4.Program.NativeAtom.names ++ Effect4.Program.termHelperNames ++
    (Effect4.Program.reserved.filter fun h => !h.contains '.' && h != "pipe" && h != "undefined")

/-- Whether a free name comes from `effect`. -/
def fromEffect (name : String) : Bool := effectNamespaces.contains name || name == "pipe"

/-- The free names of a module: each use that no binding of the module resolves, once, with
whether every use of it is a type. -/
def freeNames (module : Module) : List (String × Bool) :=
  let uses := (SourceBindings.moduleUses module).uses.filter fun u => !SourceBindings.useResolved u
  uses.foldl (fun acc u =>
    let typeOnly := u.space == .type
    match acc.find? (·.1 == u.name) with
    | some _ => acc.map fun (n, t) => if n == u.name then (n, t && typeOnly) else (n, t)
    | none => acc ++ [(u.name, typeOnly)]) []

/-- Names in order. -/
def sorted (names : List (String × Bool)) : List (String × Bool) :=
  names.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- The imports of a module: from `effect`, then from the prelude, each list in order. A name in
`holes` is no import: the host answers it until the hole is filled. -/
def importsOf (module : Module) (holes : List String := []) : List Import :=
  let free := (sorted (freeNames module)).filter (!holes.contains ·.1)
  let effect := free.filter (fromEffect ·.1)
  let prelude := free.filter (!fromEffect ·.1)
  let binding (p : String × Bool) : ImportBinding := { imported := p.1, localName := p.1, typeOnly := p.2 }
  (if effect.isEmpty then [] else [.named (effect.map binding) "effect" false]) ++
    (if prelude.isEmpty then [] else [.named (prelude.map binding) preludePath false])

/-- The origins a generated module may import from: `effect`'s namespaces, and the prelude's
names at its path. -/
def allowedOrigins : List Bindings.Origin :=
  effectOrigins ++ [.imported "effect" (some "pipe")] ++
    preludeNames.map fun n => .imported preludePath (some n)

/-- A refusal of the reading boundary, in words. -/
def surfaceText : SurfaceRefusal → String
  | .unbound => "a name has no binding or no permitted import"
  | .read why => "it does not read back: " ++ reprStr why
  | .illTyped => "what it reads back to is ill-typed"
  | .unrepresentable _ => "a type has no TypeScript annotation"
  | .unsafeName n => "the export name " ++ n ++ " is unsafe"
  | .exportName e a => "the export is " ++ a ++ ", not " ++ e
  | .notExported n => n ++ " is not exported"
  | .declaredType _ _ => "the declared type is not the printer's"
  | .layerDeclaration n => "the layer declaration " ++ n ++ " is not plain"
  | .formation _ => "what it reads back to is not formed"
  | .classDeclarations => "its classes are not the printer's"

/-- A module laid out at the width `w`: the house's header block and imports, then each
declaration laid out, one blank line between. -/
def moduleText (w : Nat) (m : Module) : String :=
  "/**\n" ++ String.intercalate "\n" (m.header.map fun line => if line.isEmpty then " *" else " * " ++ line) ++
    "\n */\n" ++ String.join (m.imports.map (Render.import_ Ts.house)) ++ "\n" ++
    String.intercalate "\n" (m.decls.map (Ts.decl w))

/-- A program's code as the view shows it: its imports and declarations laid out at the width
`w`, one line a row, without the header; or why it has none. The program's holes are named in a
comment where their import would stand. -/
def codeLines (w : Nat) (program : NativeEff) (table : RowTable := []) (holes : List String := []) :
    Except String (List String) :=
  match Api.emitModule "main" program table with
  | .error why => .error (reprStr why)
  | .ok emission =>
    let m := emission.module
    let used := (freeNames m).filter (holes.contains ·.1) |>.map (·.1)
    let holeLine := if used.isEmpty then ""
      else "// holes " ++ ", ".intercalate used ++ ": the host answers each until it is filled\n"
    let text := String.join ((importsOf m holes).map (Render.import_ Ts.house)) ++ holeLine ++ "\n" ++
      String.intercalate "\n" (m.decls.map (Ts.decl w))
    .ok ((text.splitOn "\n").reverse.dropWhile (·.isEmpty)).reverse

/-- A type's text: the answer, then `! error` when it can fail, then the keys it needs. -/
def effTyText (t : EffTy) : String :=
  t.answer.render ++ (if t.error = .never then "" else " ! " ++ t.error.render) ++
    (if t.requires.elems.isEmpty then ""
     else " needs " ++ " ".intercalate (t.requires.elems.map keyText))

/-- One program, generated: its name and group, its type, its address, its files' texts, and what
was checked. -/
structure Generated where
  name : String
  group : String
  /-- the program's type (`effTyText`); empty when it is ill-typed -/
  type : String
  /-- the SHA-256 of the program's canonical bytes, in hexadecimal -/
  address : String
  /-- the module, or why there is none -/
  module : Except String String
  /-- the reading boundary's verdict on the structured module, and whether the program it reads
  back is this one -/
  reads : Except String Unit
  /-- whether `run_eq_meaning` covers the program -/
  straight : Bool

/-- Generate one program of a group, at the width `w`. -/
def generate (w : Nat) (group name : String) (program : NativeEff) (table : RowTable := []) : Generated :=
  let address := Store.Digest.hex (Store.sha256 (Api.bytesOf program))
  let type := match Api.checkTyping program table with
    | some t => effTyText t.ty
    | none => ""
  let straight := Effect4.Program.Denote.Straight program
  match Api.emitModule "main" program table with
  | .error why =>
    { name, group, type, address, straight, module := .error (reprStr why), reads := .error "no module" }
  | .ok emission =>
    let body := emission.module
    let imports := importsOf body
    let checked := { body with imports }
    let reads : Except String Unit := match admitModule "main" checked table allowedOrigins with
      | .ok reading =>
        if decide (reading.program = program) then .ok ()
        else .error "admitted, but it reads back to another program"
      | .error why => .error (surfaceText why)
    let header := [s!"{name}: generated by the Effect4 code generator. Do not edit.", "",
      s!"program   sha256 {address}", s!"type      {type}", s!"tree      ./{name}.tree.txt",
      "reads     " ++ (match reads with
        | .ok _ => "the structured module back to this program (admitModule: bindings, read-back, typing,"
        | .error why => "refused: " ++ why),
      "          " ++ (match reads with
        | .ok _ => "envelope; the program read back is equal); this text is that module laid out"
        | .error _ => "the structured module, before its layout"),
      "covered   " ++ (if straight then "run_eq_meaning (the straight fragment)"
        else "outside the straight fragment")]
    { name, group, type, address, straight, reads, module := .ok (moduleText w { checked with header }) }

end Tools.Code
