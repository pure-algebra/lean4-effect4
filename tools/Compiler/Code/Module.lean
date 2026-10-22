import Compiler.Code.TypeScript
import Effect4.Codegen.Admit
import Effect4.Program.Fragment
import Effect4.Store.Carrier.Digest
import Effect4.Api.Codegen

/-!
# A generated module: its imports, its address, its header and its layout

The pieces of one TypeScript module that a person or an agent reads as it is. The compiler's one
artifact mechanics (`Compiler.Emit`: `moduleFile`, `header`) composes them, and every producer of
a printed module calls it. The module is `Api.emitModule`'s declarations with three additions:

- **its imports, exactly, and its row namespaces**: the core's file (`ModuleEmission.file`,
  `src/Effect4/Codegen/Checked.lean`; decisions rows 373 (11) and 378 (19)) declares each row
  namespace that is an Effect service and writes the imports from Lean data. A name that the
  declarations use and do not bind comes from `effect` when it is a namespace of `effect`
  (`effectNamespaces`) or `pipe`, and from the prelude when it is a prelude name
  (`preludeNames`); any other stays free;
- **a header**: a title, then rows (`headerBlock`). The compiler's header names the program's
  content address first: the SHA-256 of its canonical bytes (`addressOf`);
- **its layout**: Effect's width, 120 columns (`Tools.Code.Ts.decl`). Undone, a layout is the
  house print (`undo_layout`, `Ts.flat_fold_expr`), which the checks read.

The checks are the core's, run on the structured module the text is laid out from. The reading
boundary admits it (`Effect4.Codegen.admitModule`: bindings, read-back, typing, envelope), and
the program it reads back must equal the program printed. The printed text itself is not parsed
here: it is the structured module laid out, and its flat form is the house print
(`Ts.flat_fold_expr`). The compiler (`Compiler.emitTs`) refuses a module that does not read back,
and writes nothing.
-/

namespace Tools.Code

open Effect4 Effect4.Program Effect4.Codegen TypeScript

/-- The path a generated module imports the prelude from: a folder beside its group's folder. -/
def preludePath : String := "../prelude/prelude.ts"

/-- The imports of a module, as the core writes them (`moduleImports`), the prelude at
`preludePath`. A name in `holes` is no import: the host answers it until the hole is filled. -/
def importsOf (module : Module) (holes : List String := []) : List Import :=
  moduleImports preludePath module holes

/-- The origins a module may import from, its prelude at `prelude`: `effect`'s namespaces and
`pipe`, and the prelude's names. -/
def originsAt (prelude : String) : List Bindings.Origin :=
  effectOrigins ++ [.imported "effect" (some "pipe")] ++
    preludeNames.map fun n => .imported prelude (some n)

/-- The origins a generated module may import from: `effect`'s namespaces, and the prelude's
names at its path. -/
def allowedOrigins : List Bindings.Origin := originsAt preludePath

/-- **A program's content address**: the SHA-256 of its canonical bytes (`Api.bytesOf`), in
hexadecimal. Every header of a generated file names it. -/
def addressOf (program : NativeEff) : String :=
  Store.Digest.hex (Store.sha256 (Api.bytesOf program))

/-- **A generated file's header block**: its title, an empty line, then each row, its label
padded to ten columns before its first line and its further lines indented as far. -/
def headerBlock (title : String) (rows : List (String × List String)) : List String :=
  title :: "" :: rows.flatMap fun (label, lines) =>
    lines.zipIdx.map fun (line, i) =>
      (if i == 0 then label.pushn ' ' (10 - label.length) else "".pushn ' ' 10) ++ line

/-- A refusal of the reading boundary, in words. -/
def surfaceText : SurfaceRefusal → String
  | .unbound name _ => "the name " ++ name ++ " has no binding in its scope"
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
  | .outsideProfile why =>
    let n := match why.reason with
      | .aboveBound n => toString n
      | .belowBound n => "-" ++ toString n
    "the literal " ++ n ++ " at " ++ toString why.site ++ " is outside the target's safe integers"
  | .imports => "an import is not admitted"
  | .lexical => "a form the binding analysis does not read"

/-- A module laid out at the width `w`: the house's header block and imports, then each
declaration laid out, one blank line between. -/
def moduleText (w : Nat) (m : Module) : String :=
  "/**\n" ++ String.intercalate "\n" (m.header.map fun line => if line.isEmpty then " *" else " * " ++ line) ++
    "\n */\n" ++ String.join (m.imports.map (Render.import_ Ts.house)) ++ "\n" ++
    String.intercalate "\n" (m.decls.map (Ts.decl w))

/-- **A program's module, as every lane writes it** (decisions row 392, P1 (a)): the checked
emission's file, its pieces printed typed (`ModuleEmission.file`); or, where the emission refuses,
the program printed plain as `main` with no declared type (`uncheckedFile`), which a lane that
shows what a host makes of an ill-typed program runs or checks. The prelude is at `prelude`, and a
name in `except` is no import. The flag says whether the module is the checked emission's. A
refusal is the plain printer's, where both refuse. -/
def programModule (prelude : String) (program : NativeEff) (table : RowTable := [])
    (except : List String := []) : Except PrintRefusal (Module × Bool) :=
  match Api.emitModule "main" program table with
  | .ok emission => (emission.file prelude except).map fun m => (m, true)
  | .error _ => (uncheckedFile prelude "main" program table except).map fun m => (m, false)

/-- A program's code as the view shows it: its imports and declarations laid out at the width
`w`, one line a row, without the header; or why it has none. The program's holes are named in a
comment where their import would stand. -/
def codeLines (w : Nat) (program : NativeEff) (table : RowTable := []) (holes : List String := []) :
    Except String (List String) :=
  match Api.emitModule "main" program table with
  | .error why => .error (reprStr why)
  | .ok emission =>
    match emission.file preludePath holes with
    | .error why => .error (reprStr why)
    | .ok m =>
      let used := (freeNames m).filter (holes.contains ·.1) |>.map (·.1)
      let holeLine := if used.isEmpty then ""
        else "// holes " ++ ", ".intercalate used ++ ": the host answers each until it is filled\n"
      let text := String.join (m.imports.map (Render.import_ Ts.house)) ++ holeLine ++ "\n" ++
        String.intercalate "\n" (m.decls.map (Ts.decl w))
      .ok ((text.splitOn "\n").reverse.dropWhile (·.isEmpty)).reverse

/-- A type's text: the answer, then `! error` when it can fail, then the keys it needs. -/
def effTyText (t : EffTy) : String :=
  t.answer.render ++ (if t.error = .never then "" else " ! " ++ t.error.render) ++
    (if t.requires.elems.isEmpty then ""
     else " needs " ++ " ".intercalate (t.requires.elems.map keyText))

end Tools.Code
