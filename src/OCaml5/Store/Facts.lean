import Lean
import OCaml5.Lcnf.Naming
import Effect4.Store.Domain.Store
import Effect4.Store.Domain.Genesis
import Tools.GeneratedStamp

/-!
# Shared native store facts

The producer reads the kind census, its classifications, and the semantic refusal constructors.
It reduces `Admission.ofRead` symbolically at every input constructor, retaining each field.
An unknown field type or non-constructor result refuses generation.
The output contains the native byte-error adapter once; host capacity stays outside Admission.

Properties: constructor coverage follows the imported inductives by construction.
The native compiler checks emitted interfaces and implementations.
Finite store controls check refusal precedence; this producer claims no native refinement theorem.
-/

namespace OCaml5.Store.Facts
open Lean Meta Effect4.Store

private def source : String := "src/OCaml5/Store/Facts.lean"
private def ctor (name : Name) : String := (Lcnf.snake (Lcnf.shortName name)).capitalize
private def field (index : Nat) : String := s!"a{index}"
private def argsText (fields : List String) : String :=
  match fields with
  | [] => ""
  | [x] => " " ++ x
  | xs => " (" ++ ", ".intercalate xs ++ ")"

private def nativeType (type : Expr) : MetaM String := do
  let type ← whnf type
  match type.getAppFn.constName? with
  | some ``Digest => pure "E4_addr.Addr.t"
  | some ``Kind => pure "E4_kind.t"
  | some ``Node => pure "E4_node.t"
  | some ``String => pure "string"
  | some ``Nat => pure "Z.t"
  | some ``UInt8 => pure "int"
  | _ => throwError "store facts: unsupported field type {type}"

private def inductiveCtors (name : Name) : MetaM (List Name) := do
  let .inductInfo info ← getConstInfo name
    | throwError "store facts: {name} is not an inductive"
  return info.ctors

private def constructorType (name : Name) : MetaM String := do
  let info ← getConstInfo name
  forallTelescope info.type fun fields _ => do
    let types ← fields.toList.mapM fun value => do nativeType (← inferType value)
    return "  | " ++ ctor name ++
      (if types.isEmpty then "" else " of " ++ " * ".intercalate types)

private def readArm (name : Name) : MetaM String := do
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
      return field index
    let bound := (List.range fields.size).map field
    let used := output.getAppArgs.toList
    let pattern := (fields.toList.zip bound).map fun (value, label) =>
      if used.contains value then label else "_"
    return "  | E4_node." ++ ctor name ++ argsText pattern ++
      " -> Model (" ++ ctor outputName ++ argsText resultFields ++ ")"

private def header (subject : String) : String :=
  "(* " ++ Tools.GeneratedStamp.note source ++ ".\n" ++
  "   Regenerate: python3 scripts/generate.py --only cas\n" ++
  "   " ++ subject ++ "\n" ++
  "   Semantic naturals use Z.t; byte fields use int in the decoder's 0..255 domain.\n" ++
  "   Constructor coverage: by construction. Precedence: tested by store controls. *)\n\n"

def admissionFiles : MetaM (String × String) := do
  let declarations ← (← inductiveCtors ``Admission).mapM constructorType
  let arms ← (← inductiveCtors ``Node.ReadRefusal).mapM readArm
  let types := "type model =\n" ++ "\n".intercalate declarations ++
    "\n\ntype t = Model of model | Capacity of string | Fault of E4_fault.t\n"
  let interface := header "The one semantic node-read refusal mapping; capacity is a host result." ++
    types ++ "\nval of_decode : E4_node.decode_error -> t\n"
  let implementation := header "The one semantic node-read refusal mapping; capacity is a host result." ++
    types ++ "\nlet of_decode = function\n" ++ "\n".intercalate arms ++
    "\n  | E4_node.Host_limit -> Capacity \"node frame exceeds host capacity\"\n"
  return (implementation, interface)

private def kindCtor (k : Kind) : String := k.name.capitalize
private def kindMatch (name : String) (read : Kind → String) : String :=
  "let " ++ name ++ " = function\n" ++
    "\n".intercalate (Kind.all.map fun k => "  | " ++ kindCtor k ++ " -> " ++ read k) ++ "\n"

def kindFiles : String × String := Id.run do
  let types := "type t =\n  | " ++ " | ".intercalate (Kind.all.map kindCtor) ++ "\n"
  let shared := header "Kind bytes, names, and classifications from Effect4.Store.Kind." ++ types
  let implementation := shared ++ "\n" ++
    kindMatch "byte" (fun k => toString k.byte.toNat) ++ "\n" ++
    kindMatch "name" (fun k => "\"" ++ k.name ++ "\"") ++ "\n" ++
    "let all = [" ++ "; ".intercalate (Kind.all.map kindCtor) ++ "]\n\n" ++
    "let of_byte = function\n" ++
    "\n".intercalate (Kind.all.map fun k => s!"  | {k.byte.toNat} -> Some {kindCtor k}") ++
    "\n  | _ -> None\n\n" ++
    "let of_name name_ = List.find_opt (fun k -> String.equal (name k) name_) all\n" ++
    s!"let sentinel = {Kind.sentinel.toNat}\nlet version_byte = {genesisNode.version.toNat}\n" ++
    "let is_registered b = match of_byte b with None -> false | Some _ -> true\n\n" ++
    kindMatch "tombstoned" (fun k => toString k.tombstoned) ++ "\n" ++
    kindMatch "is_run_relative" (fun k => toString k.runRelative) ++ "\n" ++
    kindMatch "is_content" (fun k => toString k.isContent) ++ "\n" ++
    kindMatch "is_interior" (fun k => toString k.isInterior) ++ "\n" ++
    "let equal a b = Int.equal (byte a) (byte b)\n" ++
    "let compare a b = Int.compare (byte a) (byte b)\n"
  let interface := shared ++ "\n" ++ "\n".intercalate
    ["val all : t list", "val byte : t -> int", "val of_byte : int -> t option",
     "val name : t -> string", "val of_name : string -> t option", "val sentinel : int",
     "val version_byte : int", "val is_registered : int -> bool", "val tombstoned : t -> bool",
     "val is_run_relative : t -> bool", "val is_content : t -> bool", "val is_interior : t -> bool",
     "val equal : t -> t -> bool", "val compare : t -> t -> int"] ++ "\n"
  return (implementation, interface)

/-- The canonical root policy alphabet, rendered once for native consumers. -/
def rootPolicyFiles : MetaM (String × String) := do
  let constructors ← inductiveCtors ``RootPolicy
  let types := "type t =\n  | " ++ " | ".intercalate (constructors.map ctor) ++ "\n"
  let shared := header "Root policy bytes and names from Effect4.Store.RootPolicy." ++ types
  let arms (read : RootPolicy → String) := "\n".intercalate
    (RootPolicy.all.map fun policy => "  | " ++ policy.name.capitalize ++ " -> " ++ read policy)
  let implementation := shared ++ "\nlet byte = function\n" ++
    arms (fun policy => toString policy.byte.toNat) ++ "\n\nlet name = function\n" ++
    arms (fun policy => "\"" ++ policy.name ++ "\"") ++ "\n\nlet all = [" ++
    "; ".intercalate (RootPolicy.all.map fun policy => policy.name.capitalize) ++ "]\n\n" ++
    "let of_byte = function\n" ++ "\n".intercalate (RootPolicy.all.map fun policy =>
      s!"  | {policy.byte.toNat} -> Some {policy.name.capitalize}") ++ "\n  | _ -> None\n"
  let interface := shared ++ "\nval all : t list\nval byte : t -> int\nval of_byte : int -> t option\nval name : t -> string\n"
  return (implementation, interface)

end OCaml5.Store.Facts
