import Lean
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.TypeRows
import OCaml5.Ml.Render
import OCaml5.Ml.Check
import Effect4.Store.Domain.Store
import Effect4.Store.Domain.Genesis
import Compiler.GeneratedStamp

/-!
# Shared native store facts

The producer reads the kind census, its classifications, and the semantic refusal constructors.
It reduces `Admission.ofRead` symbolically at every input constructor, retaining each field.
An unknown field type or non-constructor result refuses generation.
The output contains the native byte-error adapter once; host capacity stays outside Admission.

Each file is a value of the one OCaml syntax: a module (`OCaml5.Ml.Module`) and its interface
(`OCaml5.Ml.Signature`), checked by `OCaml5.Ml.checkModule` and `OCaml5.Ml.checkSignature` and
printed by the one renderer. A field of a Lean type with a type row is that row's spelling
(`OCaml5.Lcnf.builtinTy?`); a digest, a kind and a node are the store's host carriers.

Properties: constructor coverage follows the imported inductives by construction.
The module checker reads every file before it is written, and the native compiler checks the
emitted interfaces and implementations.
Finite store controls check refusal precedence; this producer claims no native refinement theorem.
-/

namespace OCaml5.Store.Facts
open Lean Meta Effect4.Store

private def source : String := "src/OCaml5/Store/Facts.lean"
private def ctor (name : Name) : String := (Lcnf.snake (Lcnf.shortName name)).capitalize
private def field (index : Nat) : String := s!"a{index}"

/-- The OCaml type of a constructor's field: the store's host carrier of a digest, a kind or a
node, or the spelling of a Lean type's row (`OCaml5.Lcnf.builtinTy?`), the one owner of every
OCaml spelling. Any other type is refused. -/
private def nativeType (type : Expr) : MetaM Ml.Ty := do
  let type ← whnf type
  match type.getAppFn.constName? with
  | some ``Digest => pure (.named "E4_addr.Addr.t")
  | some ``Kind => pure (.named "E4_kind.t")
  | some ``Node => pure (.named "E4_node.t")
  | some n =>
    match Lcnf.builtinTy? n [] with
    | some t => pure t
    | none => throwError "store facts: unsupported field type {type}"
  | none => throwError "store facts: unsupported field type {type}"

private def inductiveCtors (name : Name) : MetaM (List Name) := do
  let .inductInfo info ← getConstInfo name
    | throwError "store facts: {name} is not an inductive"
  return info.ctors

/-- One binding of the module, with no parameter. -/
private def letOne (name : String) (body : Ml.Expr) (params : List String := []) : Ml.Decl :=
  .letD false [{ name, params := params.map (·, none), body }]

/-- A variant of nullary constructors, named. -/
private def variantOf (name : String) (ctors : List String) : Ml.TypeDecl :=
  { name, body := .variant (ctors.map fun c => { name := c }) }

/-- `function | C₁ -> e₁ | …`, one arm per constructor. -/
private def byCtor {α : Type} (all : List α) (name : α → String) (read : α → Ml.Expr) : Ml.Expr :=
  .fnMatch (all.map fun a => (.ctor (name a) [], read a))

/-- The header of every file: the stamp, the regeneration command and what the file holds. -/
private def header (subject : String) : String :=
  Tools.GeneratedStamp.note source ++ ".\n" ++
  "   Regenerate: python3 scripts/generate.py --only cas\n" ++
  "   " ++ subject ++ "\n" ++
  "   A field of a Lean type is its type row's spelling (OCaml5.Lcnf.typeRows).\n" ++
  "   Constructor coverage: by construction. Precedence: tested by store controls."

/-- A unit: its module and its interface, under one name and one header. -/
private def unitOf (name subject : String) (items : List Ml.Decl) (sig : List Ml.SigItem) :
    Ml.Module × Ml.Signature :=
  (⟨name, some (header subject), items⟩, ⟨name, some (header subject), sig⟩)

/-- A module and its interface, each checked, then rendered: the implementation's text and the
interface's. A diagnostic of either refuses the run. -/
def renderUnit (m : Ml.Module) (s : Ml.Signature) : Except String (String × String) := do
  let diags := Ml.checkModule m ++ Ml.checkSignature s m
  unless diags.isEmpty do
    throw s!"store facts: {m.name}: {diags.map Ml.Diag.toLine}"
  return (Ml.render m, Ml.renderSignature s)

/-! ## The semantic node-read refusal mapping -/

private def constructorDecl (name : Name) : MetaM Ml.Ctor := do
  let info ← getConstInfo name
  forallTelescope info.type fun fields _ => do
    let types ← fields.toList.mapM fun value => do nativeType (← inferType value)
    return { name := ctor name, args := types }

private def readArm (name : Name) : MetaM (Ml.Pat × Ml.Expr) := do
  let info ← getConstInfo name
  forallTelescope info.type fun fields _ => do
    let input := mkAppN (mkConst name) fields
    let output ← whnf (← mkAppM ``Admission.ofRead #[input])
    let some outputName := output.getAppFn.constName?
      | throwError "store facts: ofRead does not return a constructor at {name}"
    unless (← inductiveCtors ``Admission).contains outputName do
      throwError "store facts: unexpected result {outputName}"
    let resultFields ← output.getAppArgs.toList.mapM fun value => do
      let some index := fields.findIdx? (· == value)
        | throwError "store facts: ofRead transforms a field at {name}: {value}"
      return Ml.Expr.var (field index)
    let used := output.getAppArgs.toList
    let pattern := (fields.toList.zipIdx).map fun (value, index) =>
      if used.contains value then Ml.Pat.var (field index) else .wild
    return (.ctor ("E4_node." ++ ctor name) pattern,
      .ctor "Model" [.ctor (ctor outputName) resultFields])

/-- `e4_admission`: the semantic refusal alphabet and the one mapping from a node's read refusal
into it. -/
def admissionUnit : MetaM (Ml.Module × Ml.Signature) := do
  let model : Ml.TypeDecl :=
    { name := "model", body := .variant (← (← inductiveCtors ``Admission).mapM constructorDecl) }
  let alternatives : List Ml.Ctor :=
    [⟨"Model", [.named "model"]⟩, ⟨"Capacity", [Ml.Ty.string]⟩, ⟨"Fault", [.named "E4_fault.t"]⟩]
  let t : Ml.TypeDecl := { name := "t", body := .variant alternatives }
  let arms ← (← inductiveCtors ``Node.ReadRefusal).mapM readArm
  let hostLimit : Ml.Pat × Ml.Expr :=
    (.ctor "E4_node.Host_limit" [], .ctor "Capacity" [.str "node frame exceeds host capacity"])
  let subject := "The one semantic node-read refusal mapping; capacity is a host result."
  let ofDecode : Ml.Ty := .arrow (.named "E4_node.decode_error") (.named "t")
  return unitOf "e4_admission" subject
    [.types [model], .types [t], letOne "of_decode" (.fnMatch (arms ++ [hostLimit]))]
    [.type model, .type t, .value "of_decode" ofDecode]

/-! ## The kinds -/

private def kindCtor (k : Kind) : String := k.name.capitalize

/-- `e4_kind`: the kinds, their bytes, names and classifications. -/
def kindUnit : Ml.Module × Ml.Signature :=
  let t := variantOf "t" (Kind.all.map kindCtor)
  let classify (name : String) (read : Kind → Bool) : Ml.Decl :=
    letOne name (byCtor Kind.all kindCtor fun k => .bool (read k))
  let byByte (op : String) : Ml.Expr :=
    Ml.Expr.call op [Ml.Expr.call "byte" [.var "a"], Ml.Expr.call "byte" [.var "b"]]
  let ofByte : Ml.Expr := .fnMatch ((Kind.all.map fun k =>
    (Ml.Pat.int k.byte.toNat, Ml.Expr.some_ (.ctor (kindCtor k) []))) ++ [(.wild, Ml.Expr.none_)])
  let ofName : Ml.Expr := Ml.Expr.call "List.find_opt"
    [.fn ["k"] (Ml.Expr.call "String.equal" [Ml.Expr.call "name" [.var "k"], .var "name_"]), .var "all"]
  let isRegistered : Ml.Expr := .matchE (Ml.Expr.call "of_byte" [.var "b"])
    [(Ml.Pat.none_, .bool false), (Ml.Pat.some_ .wild, .bool true)]
  let subject := "Kind bytes, names, and classifications from Effect4.Store.Kind."
  let kind : Ml.Ty := .named "t"
  unitOf "e4_kind" subject
    [.types [t],
       letOne "byte" (byCtor Kind.all kindCtor fun k => .int k.byte.toNat),
       letOne "name" (byCtor Kind.all kindCtor fun k => .str k.name),
       letOne "all" (.listLit (Kind.all.map fun k => .ctor (kindCtor k) [])),
       letOne "of_byte" ofByte,
       letOne "of_name" ofName ["name_"],
       letOne "sentinel" (.int Kind.sentinel.toNat),
       letOne "version_byte" (.int genesisNode.version.toNat),
       letOne "is_registered" isRegistered ["b"],
       classify "tombstoned" Kind.tombstoned,
       classify "is_run_relative" Kind.runRelative,
       classify "is_content" Kind.isContent,
       classify "is_interior" Kind.isInterior,
       letOne "equal" (byByte "Int.equal") ["a", "b"],
       letOne "compare" (byByte "Int.compare") ["a", "b"]]
    [.type t,
       .value "all" (Ml.Ty.list kind), .value "byte" (.arrow kind Ml.Ty.int),
       .value "of_byte" (.arrow Ml.Ty.int (Ml.Ty.option kind)), .value "name" (.arrow kind Ml.Ty.string),
       .value "of_name" (.arrow Ml.Ty.string (Ml.Ty.option kind)), .value "sentinel" Ml.Ty.int,
       .value "version_byte" Ml.Ty.int, .value "is_registered" (.arrow Ml.Ty.int Ml.Ty.bool),
       .value "tombstoned" (.arrow kind Ml.Ty.bool), .value "is_run_relative" (.arrow kind Ml.Ty.bool),
       .value "is_content" (.arrow kind Ml.Ty.bool), .value "is_interior" (.arrow kind Ml.Ty.bool),
       .value "equal" (.arrow kind (.arrow kind Ml.Ty.bool)),
       .value "compare" (.arrow kind (.arrow kind Ml.Ty.int))]

/-! ## The result envelope -/

/-- Two lowercase hexadecimal digits of a byte. -/
private def hexByte (b : UInt8) : String :=
  String.ofList (Nat.toDigits 16 (b.toNat / 16) ++ Nat.toDigits 16 (b.toNat % 16))

/-- `e4_result`: the result envelope's fixed facts (seams ST3): the common specification's 32
bytes and the one supported envelope version, which `Node.resultQuery?` checks. The native reader
in `ocaml/engine/cas/e4_cas.ml` reads the envelope's grammar; these are its only constants. The
bytes are written as their hexadecimal text and read once, by the one hexadecimal codec
(`E4_hex.digest_of_hex`): an OCaml string literal of the syntax holds a Lean string's UTF-8
bytes, which 32 arbitrary bytes are not. -/
def resultUnit : Ml.Module × Ml.Signature :=
  let hex := String.join ((specOf (Answered Unit)).bytes.map hexByte)
  let spec : Ml.Expr := .matchE (Ml.Expr.call "E4_hex.digest_of_hex" [.str hex])
    [(Ml.Pat.some_ (.var "bytes"), .var "bytes"), (Ml.Pat.none_, .assertE (.bool false))]
  let subject := "The result envelope's specification (the 32 bytes of specOf (Answered Unit)) " ++
    "and version from Effect4.Store.Answered."
  unitOf "e4_result" subject
    [letOne "spec" spec, letOne "envelope_version" (.int 0)]
    [.value "spec" Ml.Ty.string, .value "envelope_version" Ml.Ty.int]

/-! ## The root policies -/

/-- `e4_root_policy`: the canonical root policy alphabet, its bytes and names. -/
def rootPolicyUnit : MetaM (Ml.Module × Ml.Signature) := do
  let constructors ← inductiveCtors ``RootPolicy
  let t := variantOf "t" (constructors.map ctor)
  let policyCtor (p : RootPolicy) : String := p.name.capitalize
  let ofByte : Ml.Expr := .fnMatch ((RootPolicy.all.map fun p =>
    (Ml.Pat.int p.byte.toNat, Ml.Expr.some_ (.ctor (policyCtor p) []))) ++ [(.wild, Ml.Expr.none_)])
  let subject := "Root policy bytes and names from Effect4.Store.RootPolicy."
  let policy : Ml.Ty := .named "t"
  return unitOf "e4_root_policy" subject
    [.types [t],
      letOne "byte" (byCtor RootPolicy.all policyCtor fun p => .int p.byte.toNat),
      letOne "name" (byCtor RootPolicy.all policyCtor fun p => .str p.name),
      letOne "all" (.listLit (RootPolicy.all.map fun p => .ctor (policyCtor p) [])),
      letOne "of_byte" ofByte]
    [.type t, .value "all" (Ml.Ty.list policy), .value "byte" (.arrow policy Ml.Ty.int),
      .value "of_byte" (.arrow Ml.Ty.int (Ml.Ty.option policy)),
      .value "name" (.arrow policy Ml.Ty.string)]

/-- Every unit, checked and rendered: `(file stem, implementation, interface)`. -/
def files : MetaM (List (String × String × String)) := do
  let units := [kindUnit, ← admissionUnit, ← rootPolicyUnit, resultUnit]
  units.mapM fun (m, s) => do
    match renderUnit m s with
    | .ok (impl, intf) => pure (m.name, impl, intf)
    | .error message => throwError message

end OCaml5.Store.Facts
