import Effect4.Api
import Effect4.Codegen.SourceBindings
import Effect4.Laws.Api.Codegen

/-!
# Source-binding contract — the original module's imports and lexical scopes

Finite lexical controls over the original target carrier (`Api.checkSourceBindings`,
`Codegen/SourceBindings.lean`). These check retained imports, names and scopes only.
An accepted annotation here has resolved names; it is not evidence that the initializer
has that type, that a host exports it, or that a resolved `Effect` is the pinned rc.112
namespace. They lived at the end of `Test/Codegen/ReadContract.lean` until 2026-09-16.
-/

namespace Test.Codegen.SourceBindingContract

open TypeScript
open Effect4.Codegen.Bindings
open Effect4.Codegen.SourceBindings

def allowed : List Origin :=
  ["Effect", "Context", "Layer", "Option"].map (fun name => .imported "effect" (some name)) ++
    [.imported "effect" none, .imported "./types" (some "Box")]

def effectImport : Import := .named ["Effect"] "effect"
def boxImport : Import := .named ["Box"] "./types" true

def source (imports : List Import) (value : Expr) (type : Option TypeRef := none) :
    TypeScript.Module :=
  { header := [], imports, decls := [.const { doc := [], name := "main", value, type }] }

def succeed : Expr := .call (.ident "Effect.succeed") [.int 1]
def effectType : TypeRef := .name ["Effect", "Effect"] [.name ["number"] []]

-- Origin, declaration/specifier type-only markers, and aliases remain observable.
#guard check allowed (source [effectImport] succeed)
#guard !check allowed (source [.named ["Effect"] "other-package"] succeed)
#guard !check allowed (source [.named ["Effect"] "effect" true] succeed)
#guard !check allowed (source [.named [⟨"Effect", "Effect", true⟩] "effect"] succeed)
#guard check allowed (source [.named ["Effect"] "effect" true] (.int 1) (some effectType))
#guard check allowed (source [.named [⟨"Effect", "FX", false⟩] "effect"]
  (.call (.ident "FX.succeed") [.int 1]))
#guard !check allowed (source [.named [⟨"Effect", "FX", false⟩] "effect"] succeed)
#guard check allowed (source [.all "E" "effect"] (.ident "E.Effect.succeed"))
#guard !check allowed (source [.all "E" "effect" true] (.ident "E.Effect.succeed"))
#guard !check allowed (source [effectImport, effectImport] succeed)
#guard !check allowed (source [.named [⟨"Effect", "Shared", false⟩,
  ⟨"Context", "Shared", false⟩] "effect"] (.int 0))
#guard !check allowed (source [.named [⟨"Effect", "undefined", false⟩] "effect"] (.int 0))
#guard !check allowed (source [.named [⟨"Effect", "arguments", false⟩] "effect"] (.int 0))
#guard !check allowed (source [.named [] "unlisted-package"] (.int 0))
#guard !check [.imported "effect" (some "Effect, unexpected")]
  (source [.named [⟨"Effect, unexpected", "Effect", false⟩] "effect"] succeed)
#guard (Effect4.Api.checkSourceBindings (source [effectImport] succeed) allowed).isSome
#guard !(Effect4.Api.checkSourceBindings (source [] succeed) allowed).isSome

-- A retained alias resolves to its imported identity, not its local spelling.
example : resolve (ofImports [.named [⟨"Effect", "FX", false⟩] "effect"]) "FX" .value =
    some ⟨"FX", .imported "effect" (some "Effect"), true, true⟩ := rfl

-- A block's pending names mask outer bindings; later statements see initialized locals.
#guard check allowed (source [] (.generator [.letInit "x" (.int 1), .ret (.ident "x")]))
#guard !check allowed (source [] (.generator [.letInit "x" (.ident "x"), .ret (.ident "x")]))
#guard !check allowed (source [] (.generator [.letInit "x" (.int 1), .letInit "x" (.int 2)]))
#guard !check allowed { header := [], imports := [effectImport], decls := [
  .const { doc := [], name := "Effect", value := .int 1 }] }
#guard !check allowed (source [effectImport] (.generator [
  .exprStmt succeed, .letInit "Effect" (.int 1)]))
#guard !check allowed (source [effectImport] (.generator [
  .letInit "Effect" (.ident "Effect"), .ret (.ident "Effect")]))
#guard !check allowed { header := [], imports := [], decls := [
  .const { doc := [], name := "main", value := .objectFromEntries [] },
  .const { doc := [], name := "Object", value := .int 1 }] }

-- Sibling branches have separate local scopes; their bindings do not escape.
#guard check allowed (source [] (.generator [
  .ifElse (.bool true) [.letInit "x" (.int 1), .ret (.ident "x")]
    [.letInit "x" (.int 2), .ret (.ident "x")]]))
#guard !check allowed (source [] (.generator [
  .ifElse (.bool true) [.letInit "x" (.int 1)] [], .ret (.ident "x")]))
#guard !check allowed (source [] (.generator [
  .whileTrue none [.letInit "x" (.int 1)], .ret (.ident "x")]))
#guard !check allowed (source [] (.generator [
  .switch (.int 0) [(0, [.letInit "x" (.int 1)]), (1, [.ret (.ident "x")])]]))

-- Parameters are available to their body and neither duplicate nor leak.
#guard check allowed (source [] (.lambda ["x"] (.ident "x")))
#guard !check allowed (source [] (.lambda ["x", "x"] (.ident "x")))
#guard !check allowed (source [] (.arrowBlock ["x"] [.letInit "x" (.int 1)]))
#guard !check allowed (source [] (.arr [.lambda ["x"] (.ident "x"), .ident "x"]))
#guard check allowed (source [boxImport]
  (.lambda [{ name := "x", type := some (.name ["Box"] []) }] (.ident "x")))
#guard !check allowed (source [boxImport]
  (.lambda ["Box"] (.arrow (some (.name ["Box"] [])) (.int 1))))

-- ProgDecl's implicit Effect.gen is inside its parameter scope, before the inner block.
#guard check [] { header := [], imports := [], decls := [.prog
  { doc := [], name := "main", paramName := "Effect", paramType := .name ["number"] [], stmts := [] }] }
#guard !check [] { header := [], imports := [], decls := [.prog
  { doc := [], name := "main", paramName := "input", paramType := .name ["number"] [], stmts := [] }] }
#guard check allowed { header := [], imports := [effectImport], decls := [.prog
  { doc := [], name := "main", paramName := "input", paramType := .name ["number"] [],
    stmts := [.letInit "input" (.int 1), .ret (.ident "input")] }] }

-- Every nested structural type contributes its references; field names are data.
def nestedType (leaf : String) : TypeRef :=
  .object [("field", true, .name ["ReadonlyArray"] [
    .tuple [.name [leaf] [], .union [.literal "a", .name ["number"] []]] true]),
    ("method", false, .function [("input", .name [leaf] [])] (.name [leaf] []))]
#guard check allowed (source [boxImport] (.int 1) (some (nestedType "Box")))
#guard !check allowed (source [boxImport] (.int 1) (some (nestedType "Missing")))
#guard !check allowed (source [] (.int 1) (some
  (.function [("x", .name ["number"] []), ("x", .name ["string"] [])] (.name ["number"] []))))
#guard check allowed (source [effectImport, boxImport]
  (.call (.generic (.ident "Effect.succeed") [.name ["Box"] []]) [.int 1]))
#guard !check allowed (source [effectImport]
  (.call (.generic (.ident "Effect.succeed") [.name ["Box"] []]) [.int 1]))

-- A class's own type is in scope in heritage arguments, but its value is not.
def serviceClass (heritage : Expr) : TypeScript.Module :=
  { header := [], imports := [.named ["Context"] "effect"], decls := [
    .classDecl { doc := [], name := "Service", heritage := some heritage }] }
#guard check allowed (serviceClass (.call
  (.generic (.ident "Context.Service") [.name ["Service"] []]) []))
#guard !check allowed (serviceClass (.ident "Service"))
#guard !check allowed
  { header := [], imports := [], decls := [.classDecl
    { doc := [], name := "Service", heritage := none, members := ["member: unknown"] }] }
#guard !check allowed { header := [], imports := [], decls := [.raw "const hidden = 1"] }

-- Verbatim property and label positions must have identifier spellings.
#guard check allowed (source [effectImport] (.member (.ident "Effect") "catch"))
#guard !check allowed (source [effectImport] (.member (.ident "Effect") "x-y"))
#guard !check allowed (source [effectImport] (.method (.ident "Effect") "x-y" []))
#guard !check allowed (source [] (.object [("x-y", .int 1)]))
#guard check allowed (source [] (.objectQuoted [("x-y", .int 1)]))
#guard !check allowed (source [] (.generator [.whileTrue (some "bad-label") []]))
#guard !check allowed (source [] (.generator [.labelled "bad-label" []]))
#guard !check allowed (source [] (.generator [.breakTo (some "bad-label")]))
#guard !check allowed (source [] (.generator [.continueTo (some "bad-label")]))

-- These references are introduced by rendering rather than explicit identifier nodes.
#guard check allowed (source [] (.objectFromEntries [("__proto__", .int 1)]))
#guard !((exprUses [] (.objectFromEntries [("__proto__", .int 1)])).resolved)
#guard check allowed (source [] (.float64Bits 0))
#guard !((exprUses [] (.float64Bits 0)).resolved)
#guard check allowed (source [effectImport] (.generator [
  .scopedGen "x" [.ret (.int 1)] (.lambda ["exit"] (.ident "exit")), .ret (.ident "x")]))
#guard !check allowed (source [] (.generator [
  .scopedGen "x" [.ret (.int 1)] (.lambda ["exit"] (.ident "exit"))]))
#guard !check allowed (source [] (.generator [
  .scopedGenMasked "x" [.ret (.int 1)] (.lambda ["exit"] (.ident "exit"))]))

-- Exercise actual producer syntax, retaining the supplied module envelope.
#guard match Effect4.Api.printModule "main" (.succeed (.lit (.nat 1))) with
  | some module => !check allowed module &&
      check allowed { module with imports := [effectImport] }
  | none => false
#guard match Effect4.Api.printModule "main"
    (.provideLayer (.succeed ⟨⟨4⟩, ⟨4⟩⟩ (.nat 7)) false (.service ⟨⟨4⟩, ⟨4⟩⟩)) with
  | some module =>
      check allowed { module with imports := [.named ["Effect", "Context", "Layer"] "effect"] } &&
        !check allowed { module with imports := [.named ["Effect", "Layer"] "effect"] }
  | none => false

-- One owner for the legal binding-name rule: the lexical check reads the same function
-- the printer's export-name check reads.
example : binderName = Effect4.Codegen.Names.binderName := rfl
#guard Effect4.Codegen.Names.binderName "main"
#guard !Effect4.Codegen.Names.binderName "undefined"
#guard !Effect4.Codegen.Names.binderName "export"

#print axioms Effect4.Codegen.Names.binderName
#print axioms Effect4.Api.checkSourceBindings
#print axioms Effect4.Api.checkSourceBindings_iff
#print axioms Effect4.Codegen.Bindings.resolve_iff
#print axioms Effect4.Codegen.Bindings.lawfulImports_resolve
#print axioms Effect4.Codegen.SourceBindings.check_iff
#print axioms Effect4.Codegen.SourceBindings.validate_refusal_iff
#print axioms Effect4.Codegen.SourceBindings.Checked.use_binding
#print axioms Effect4.Codegen.SourceBindings.resolve_pending
#print axioms Effect4.Codegen.SourceBindings.stmtsUses_ifElse

end Test.Codegen.SourceBindingContract
