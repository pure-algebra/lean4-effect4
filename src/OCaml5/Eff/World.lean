import Lean
import Tools.ProgramStructure
import Tools.WireTags
import Effect4.Program.Native
import Effect4.Program.Node

/-!
# OCaml5.Eff.World

**What it is.** The closed world of the `Eff` program IR as OCaml carriers: `OTy`, the carrier
alphabet a field or constructor argument is carried by; `Spec`/`blocks`, the Lean families in
the order their OCaml `type … and …` groups are emitted; and `readBlocks`, which reads every
family's constructors and their carriers off the Lean environment (`Effect4.Program.Native`).
`OCaml5.Eff.Emit` writes the OCaml library from it, `OCaml5.Eff.Goldens` the corpus.

**Depends on.** `Effect4.Program.Native` (the IR and its native signature), `Lean.Meta`.

**Properties.**
* **Closed.** A field whose type has no carrier is an error at generation time, never a hole in
  the output — *by construction* (`ocamlTy` throws).
* **Two numbers per constructor.** Constructors come in the environment's order, and
  `ctor_index_<t>` is that compiled position. The wire tag is a different number: `Ctor.tag` is
  read from the one assignment (`tools/Effect4Gen/wire-tags.json`, through `Tools.WireTags`), and
  only the byte codec, the golden bytes and the wire manifest use it. Every inductive family of
  the program world must be listed there — *by construction* (`readBlocks` refuses).
* **`Effect4.Row α` is carried as `α list`**, the one non-structural rule — *by construction*.
-/

open Lean Meta
open Effect4.Program
open Effect4.Supervision (MaskMode ForkOptions ObserverMode)
open Effect4 (FinalizerStrategy ServiceKey)
open Effect4.Machine (FnName)

namespace OCaml5.Eff

/-! ## OCaml carriers -/

/-- The OCaml type an argument or field is carried by. -/
inductive OTy
  | int | bool | string | unit
  | option (a : OTy)
  | list (a : OTy)
  | prod (a b : OTy)
  | named (n : String)
  /-- Strictly ascending ServiceKey list: proof-free bytes, checked at the boundary. -/
  | requirements
deriving Repr, BEq, Inhabited

mutual
partial def OTy.render : OTy → String
  | .int => "int"
  | .bool => "bool"
  | .string => "string"
  | .unit => "unit"
  | .option a => a.renderArg ++ " option"
  | .list a => a.renderArg ++ " list"
  | .prod a b => a.renderArg ++ " * " ++ b.renderArg
  | .named n => n
  | .requirements => "service_key list"
/-- As a constructor argument or a type-constructor argument: products parenthesised. -/
partial def OTy.renderArg : OTy → String
  | .prod a b => "(" ++ OTy.render (.prod a b) ++ ")"
  | t => t.render
end

/-- The OCaml constructor of `<Type>.<ctor>`: the type's OCaml name capitalised, an underscore,
the Lean constructor name verbatim. -/
def octor (oname short : String) : String := oname.capitalize ++ "_" ++ short

/-- The OCaml record field of `<Type>.<field>`. -/
def ofield (oname field : String) : String := oname ++ "_" ++ field

def shortName : Name → String
  | .str _ s => s
  | n => n.toString

/-- `(0, x₀), (1, x₁), …` -/
def enumL {α : Type} (xs : List α) : List (Nat × α) := (List.range xs.length).zip xs

/-! ## The closed world -/

structure Spec where
  leanName : Name
  oname : String
  /-- The OCaml carrier of each type parameter, by position: the instantiation the mirror is
  taken at (`Eff NativeOp`). Parameters without a carrier (instance arguments) get none; a
  field that mentions one is a refusal. -/
  params : List OTy := []

def natOp : OTy := .named "native_op"

/-- The families, grouped as the OCaml `type … and …` groups are emitted: a Lean mutual block
is one group. Order is dependency order. -/
def projectSpec (spec : Tools.ProgramStructure.Spec) : Spec :=
  ⟨spec.leanName, spec.label, spec.parameters.map fun name =>
    .named ((Tools.ProgramStructure.allSpecs.find? (·.leanName == name)).map (·.label) |>.getD name.toString)⟩

/-- Target grouping projects the single selected source inventory. -/
def blocks : List (List Spec) := Tools.ProgramStructure.blocks.map (·.map projectSpec)

def allSpecs : List Spec := blocks.flatten

/-- The only target-specific erasures; unsupported canonical row elements refuse. -/
def projectShape (path : String) : Tools.ProgramStructure.Shape → Except String OTy
  | .nat => .ok .int
  | .bool => .ok .bool
  | .string => .ok .string
  | .unit => .ok .unit
  | .option a => return .option (← projectShape path a)
  | .list a => return .list (← projectShape path a)
  | .prod a b => return .prod (← projectShape path a) (← projectShape path b)
  | .canonicalRow (.nominal `Effect4.ServiceKey []) => .ok .requirements
  | .canonicalRow _ => .error ("EffGen: unsupported canonical row at " ++ path)
  | .nominal name _ =>
    match Tools.ProgramStructure.allSpecs.find? (·.leanName == name) with
    | some spec => .ok (.named spec.label)
    | none => .error ("EffGen: unselected nominal at " ++ path ++ ": " ++ name.toString)

structure Ctor where
  name : Name
  short : String
  /-- The wire tag: the assignment's number, not the position in `Family.ctors`. -/
  tag : Nat
  args : List (String × OTy)
deriving Inhabited

structure Family where
  spec : Spec
  isStruct : Bool
  ctors : List Ctor

/-- `Effect4.Program.Term`, unambiguous beside `Lean.Term`. -/
abbrev PTerm := Effect4.Program.Term

def projectFamily (tags : Tools.WireTags.Assignment)
    (family : Tools.ProgramStructure.Family) : MetaM Family := do
  let wire ← match Tools.WireTags.tagsOf tags family.spec.leanName family.isStruct
      (family.constructors.map (·.name)) with
    | .ok ws => pure ws
    | .error message => throwError message
  let ctors ← (family.constructors.zip wire).mapM fun (ctor, tag) => do
    let args ← ctor.fields.mapM fun field =>
      match projectShape s!"{family.spec.leanName}.{field.name}" field.shape with
      | .ok shape => pure (field.name, shape)
      | .error message => throwError message
    pure { name := ctor.name, short := shortName ctor.name, tag, args : Ctor }
  pure { spec := projectSpec family.spec, isStruct := family.isStruct, ctors }

/-- The program world with its wire tags. The assignment is read once; an inductive family of
the world that the assignment does not list is refused, so no tag here is a silent default. -/
def readBlocks : MetaM (List (List Family)) := do
  let tags ← Tools.WireTags.load
  let source ← Tools.ProgramStructure.readBlocks
  let inductives := (source.flatten.filter (!·.isStruct)).map (·.spec.leanName)
  match Tools.WireTags.requireListed tags inductives with
  | .ok () => pure ()
  | .error message => throwError message
  source.mapM (·.mapM (projectFamily tags))

/-- The node sorts, read off `Effect4.Program.Node`: each constructor's short name with the
label of the family its one field carries, in `Node`'s declaration order. -/
def readNodeSorts : MetaM (List (String × String)) := do
  let some (.inductInfo node) := (← getEnv).find? ``Effect4.Program.Node
    | throwError "EffGen: Effect4.Program.Node is not an inductive"
  node.ctors.mapM fun ctorName => do
    let ctor ← getConstInfoCtor ctorName
    forallTelescope ctor.type fun xs _ => do
      unless xs.size == ctor.numParams + 1 do
        throwError "EffGen: {ctorName} does not carry exactly one field"
      let head := (← whnfR (← inferType xs[ctor.numParams]!)).getAppFn
      let some family := head.constName?
        | throwError "EffGen: the field of {ctorName} names no family"
      let some spec := Tools.ProgramStructure.allSpecs.find? (·.leanName == family)
        | throwError "EffGen: {ctorName} carries the unselected family {family}"
      pure (shortName ctorName, spec.label)


end OCaml5.Eff
