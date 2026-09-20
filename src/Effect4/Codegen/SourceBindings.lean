import Effect4.Codegen.Bindings
import Effect4.Codegen.Names
import Effect4.Store.Carrier.Utf8

/-!
# Binding requirements of the original target syntax

This traversal describes lexical uses in the existing TypeScript carrier. Each use
retains its actual lexical environment; it is not a second program representation.
Names shadow the enclosing scope throughout their block; their capabilities become
available only after their initializer. Nested blocks do not leak declarations, and
parameters shadow outer bindings by name. Duplicate declarations in one scope refuse.
The generated profile does not merge TypeScript's separate declaration namespaces.
It conservatively refuses forward references, including inside deferred closures.

Every structured constructor has a case, including references introduced by the
renderer. Opaque declarations and raw class members refuse. This check is about
binding, not assignment-before-use, annotation agreement, label targets, package
exports, comment rendering or target execution. Those obligations remain separate.
-/

namespace Effect4.Codegen.SourceBindings

open TypeScript Bindings

/-- A reference together with the scope at its original source occurrence. -/
structure Use where
  env : List Binding
  name : String
  space : Space

/-- Lexical shape and the binding obligations collected from existing syntax. -/
structure Analysis where
  valid : Bool := true
  uses : List Use := []

def Analysis.append (left right : Analysis) : Analysis :=
  ⟨left.valid && right.valid, left.uses ++ right.uses⟩

def Analysis.require (analysis : Analysis) (valid : Bool) : Analysis :=
  ⟨valid && analysis.valid, analysis.uses⟩

private def invalid : Analysis := ⟨false, []⟩
private def empty : Analysis := {}

/-- ASCII identifier characters. A property may be a keyword, as in `Effect.catch`. -/
def identifierBytes : List UInt8 → Bool
  | [] => false
  | first :: rest => identifierStart first && rest.all identifierContinue

/-- Split a qualified identifier without invoking the text renderer or String folds. -/
def qualifiedRoot (name : String) : Option String := do
  let reversed := name.toUTF8.data.toList.foldl (fun (parts : List (List UInt8)) byte =>
    if byte == 46 then [] :: parts
    else match parts with
      | [] => [[byte]]
      | part :: rest => (byte :: part) :: rest) [[]]
  let parts := (reversed.map List.reverse).reverse
  if parts.all identifierBytes then
    match parts with
    | [] => none
    | root :: _ => Effect4.Store.decodeString root
  else none

def rootUse (env : List Binding) (space : Space) (name : String) : Analysis :=
  ⟨true, [⟨env, name, space⟩]⟩

def nameUse (env : List Binding) (space : Space) (name : String) : Analysis :=
  match qualifiedRoot name with
  | some root => rootUse env space root
  | none => invalid

/-- Binding names exclude source keywords and reserved ambient values. The rule itself
lives in `Codegen.Names`, so this check and the printer's export-name check cannot drift. -/
def binderName (name : String) : Bool := Names.binderName name

/-- Empty named imports have no binding to validate; this profile refuses them.
Imported names render verbatim, whereas module paths are quoted by the renderer. -/
def importShape : Import → Bool
  | .all name _ _ => binderName name
  | .named names _ _ => !names.isEmpty && names.all fun binding =>
      binderName binding.localName && identifierBytes binding.imported.toUTF8.data.toList

def valueBinding (name : String) : Binding := ⟨name, .local, true, false⟩
def classBinding (name : String) : Binding := ⟨name, .local, true, true⟩

def freshName (locals : List String) (name : String) : Bool :=
  binderName name && !locals.contains name

def parameterNames (params : List Parameter) : List String := params.map (·.name)
def parametersValid (params : List Parameter) : Bool :=
  params.all (fun param => binderName param.name) && decide (parameterNames params).Nodup

def parameterEnv (env : List Binding) (params : List Parameter) : List Binding :=
  (parameterNames params).map valueBinding ++ env

/-- Unavailable names mask enclosing bindings before the local declaration. -/
def pendingBinding (name : String) : Binding := ⟨name, .local, false, false⟩

def pendingEnv (env : List Binding) (names : List String) : List Binding :=
  names.map pendingBinding ++ env

def statementName : Stmt → Option String
  | .constYield name _ _ | .letDefinite name _ | .letInit name _ _ |
    .scopedGen name _ _ | .scopedGenMasked name _ _ => some name
  | .ret _ | .yieldDiscard _ | .assign _ _ | .whileTrue _ _ | .switch _ _ |
    .ifElse _ _ _ | .labelled _ _ | .breakTo _ | .continueTo _ | .exprStmt _ => none

def blockEnv (env : List Binding) (body : List Stmt) : List Binding :=
  pendingEnv env (body.filterMap statementName)

def labelValid : Option String → Bool
  | none => true
  | some name => binderName name

mutual
  def typeUses (env : List Binding) : TypeRef → Analysis
    | .name names args =>
      let own := match names with
        | [] => invalid
        | name :: _ => (rootUse env .type name).require
            (names.all fun part => identifierBytes part.toUTF8.data.toList)
      own.append (typesUses env args)
    | .literal _ => empty
    | .tuple items _ | .union items => typesUses env items
    | .object fields => fieldsUses env fields
    | .function params result =>
      ((typeParamsUses env params).append (typeUses env result)).require
        (decide (params.map Prod.fst).Nodup)
  termination_by structural t => t

  def typesUses (env : List Binding) : List TypeRef → Analysis
    | [] => empty
    | head :: rest => (typeUses env head).append (typesUses env rest)
  termination_by structural ts => ts

  def fieldsUses (env : List Binding) : List (String × Bool × TypeRef) → Analysis
    | [] => empty
    | (_, _, type) :: rest => (typeUses env type).append (fieldsUses env rest)
  termination_by structural fs => fs

  def typeParamsUses (env : List Binding) : List (String × TypeRef) → Analysis
    | [] => empty
    | (name, type) :: rest =>
      ((typeUses env type).append (typeParamsUses env rest)).require (binderName name)
  termination_by structural ps => ps
end

def optionalTypeUses (env : List Binding) : Option TypeRef → Analysis
  | none => empty
  | some type => typeUses env type

def parametersUses (env : List Binding) (params : List Parameter) : Analysis :=
  params.foldr (fun param rest => (optionalTypeUses env param.type).append rest) empty

mutual
  def exprUses (env : List Binding) : Expr → Analysis
    | .ident name => nameUse env .value name
    | .str _ | .int _ | .bool _ | .jsNull => empty
    | .float64Bits _ => (rootUse env .value "DataView").append (rootUse env .value "Uint8Array")
    | .call fn args => (exprUses env fn).append (exprsUses env args)
    | .object fields | .objectML fields =>
      (objectUses env fields).require (fields.all fun field => identifierBytes field.1.toUTF8.data.toList)
    | .objectQuoted fields | .objectQuotedML fields =>
      objectUses env fields
    | .objectFromEntries fields =>
      (rootUse env .value "Object").append (objectUses env fields)
    | .arr items => exprsUses env items
    | .arrow type body => (optionalTypeUses env type).append (exprUses env body)
    | .generic fn args => (exprUses env fn).append (typesUses env args)
    | .lambda params body type =>
      ((parametersUses env params).append ((optionalTypeUses env type).append
        (exprUses (parameterEnv env params) body))).require (parametersValid params)
    | .method target name args => ((exprUses env target).append (exprsUses env args)).require
      (identifierBytes name.toUTF8.data.toList)
    | .member target name => (exprUses env target).require
      (identifierBytes name.toUTF8.data.toList)
    | .generator body => stmtsUses (blockEnv env body) [] body
    | .cond test yes no => (exprUses env test).append ((exprUses env yes).append (exprUses env no))
    | .arrowBlock params body type =>
      ((parametersUses env params).append ((optionalTypeUses env type).append
        (stmtsUses (blockEnv (parameterEnv env params) body) (parameterNames params) body))).require
          (parametersValid params)
  termination_by structural e => e

  def exprsUses (env : List Binding) : List Expr → Analysis
    | [] => empty
    | head :: rest => (exprUses env head).append (exprsUses env rest)
  termination_by structural es => es

  def objectUses (env : List Binding) : List (String × Expr) → Analysis
    | [] => empty
    | (_, value) :: rest => (exprUses env value).append (objectUses env rest)
  termination_by structural fs => fs

  def stmtsUses (env : List Binding) (locals : List String) : List Stmt → Analysis
    | [] => empty
    | stmt :: rest =>
      let (nextEnv, nextLocals) := match statementName stmt with
        | some name =>
          (valueBinding name :: env, name :: locals)
        | none => (env, locals)
      (stmtUses env locals stmt).append (stmtsUses nextEnv nextLocals rest)
  termination_by structural ss => ss

  def stmtUses (env : List Binding) (locals : List String) : Stmt → Analysis
    | .constYield name value type | .letInit name value type =>
      ((optionalTypeUses env type).append (exprUses env value)).require (freshName locals name)
    | .letDefinite name type => (typeUses env type).require (freshName locals name)
    | .ret value | .yieldDiscard value | .exprStmt value => exprUses env value
    | .assign name value =>
      ((nameUse env .value name).append (exprUses env value)).require (binderName name)
    | .whileTrue label body => (stmtsUses (blockEnv env body) [] body).require (labelValid label)
    | .labelled label body => (stmtsUses (blockEnv env body) [] body).require (binderName label)
    | .switch value cases => (exprUses env value).append (casesUses env cases)
    | .ifElse test yes no =>
      (exprUses env test).append ((stmtsUses (blockEnv env yes) [] yes).append
        (stmtsUses (blockEnv env no) [] no))
    | .scopedGen name body onExit | .scopedGenMasked name body onExit =>
      ((rootUse env .value "Effect").append ((stmtsUses (blockEnv env body) [] body).append
        (exprUses env onExit))).require (freshName locals name)
    | .breakTo label | .continueTo label => empty.require (labelValid label)
  termination_by structural s => s

  def casesUses (env : List Binding) : List (Nat × List Stmt) → Analysis
    | [] => empty
    | (_, body) :: rest => (stmtsUses (blockEnv env body) [] body).append (casesUses env rest)
  termination_by structural cs => cs
end

/-- The selected standard globals. Origin/capability checks still distinguish them
from a same-named import or local binding. This is not a host global-object model. -/
def builtins : List Binding :=
  [⟨"undefined", .builtin, true, true⟩] ++
    ["Object", "DataView", "Uint8Array"].map (fun name => ⟨name, .builtin, true, true⟩) ++
    ["any", "unknown", "never", "void", "null", "number", "string", "boolean", "object",
      "symbol", "bigint", "ReadonlyArray", "Array"].map (fun name => ⟨name, .builtin, false, true⟩)

def declarationName : Decl → Option String
  | .const decl => some decl.name
  | .prog decl => some decl.name
  | .classDecl decl => some decl.name
  | .raw _ | .effectfulField _ => none

def declarationBinding : Decl → Option Binding
  | .const decl => some (valueBinding decl.name)
  | .prog decl => some (valueBinding decl.name)
  | .classDecl decl => some (classBinding decl.name)
  | .raw _ | .effectfulField _ => none

def declarationUses (env : List Binding) (locals : List String) : Decl → Analysis
  | .const decl => ((optionalTypeUses env decl.type).append (exprUses env decl.value)).require
      (freshName locals decl.name)
  | .prog decl =>
    let params := valueBinding decl.paramName :: env
    ((typeUses env decl.paramType).append ((rootUse params .value "Effect").append
      (stmtsUses (blockEnv params decl.stmts) [] decl.stmts))).require
        (freshName locals decl.name && binderName decl.paramName)
  | .classDecl decl =>
    let self := ⟨decl.name, Origin.local, false, true⟩
    let heritage := match decl.heritage with
      | none => empty
      | some value => exprUses (self :: env) value
    heritage.require (freshName locals decl.name && decl.members.isEmpty)
  | .raw _ | .effectfulField _ => invalid

def declarationsUses (env : List Binding) (locals : List String) : List Decl → Analysis
  | [] => empty
  | decl :: rest =>
    match declarationBinding decl with
    | none => invalid
    | some binding => (declarationUses env locals decl).append
        (declarationsUses (binding :: env) (binding.name :: locals) rest)

/-- Analyze the original module: imports establish its initial environment, and
module declarations extend that scope in source order. -/
def moduleUses (module : TypeScript.Module) : Analysis :=
  let imports := ofImports module.imports
  (declarationsUses (pendingEnv (imports ++ builtins) (module.decls.filterMap declarationName))
    (imports.map (·.name)) module.decls).require (module.imports.all importShape)

def useResolved (use : Use) : Bool := (resolve use.env use.name use.space).isSome

def Analysis.resolved (analysis : Analysis) : Bool :=
  analysis.valid && analysis.uses.all useResolved

/-- Lexical admission is separate from core typing and source annotation agreement. -/
def check (allowed : List Origin) (module : TypeScript.Module) : Bool :=
  lawfulImports allowed module.imports && (moduleUses module).resolved

/-- A checked original module. Proofs of individual name resolutions are derived
in Laws; this certificate alone makes no Eff or target-typing claim. -/
structure Checked (allowed : List Origin) (module : TypeScript.Module) : Type where
  checked : check allowed module = true

def validate (allowed : List Origin) (module : TypeScript.Module) : Option (Checked allowed module) :=
  if h : check allowed module = true then some ⟨h⟩ else none

end Effect4.Codegen.SourceBindings
