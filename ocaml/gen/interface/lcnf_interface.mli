(* Lcnf_interface: the public interface of generated OCaml.
   Depends on compiler-libs and the generator's root/type metadata.
   Properties: selected roots only; whole packages abstract; last binding wins; with
   [Reachable], only the types the exported values name (a consumer's facade).
   These properties are tested by test_interface and the native sealing controls. *)

type refusal =
  | Input of string
  | Not_implementation
  | Missing_values of string list
  | Missing_types of string list

(** Which top-level types an interface keeps: every type of the unit ([All], an artifact), or
    those an exported value, a selected package or a kept type names ([Reachable], a consumer's
    facade over the artifact it includes). *)
type types =
  | All
  | Reachable

val message : refusal -> string

val select
  :  types:types
  -> roots:string list
  -> abstract_types:string list
  -> Types.signature
  -> (Types.signature, refusal) result

val generate
  :  types:types
  -> cmt:string
  -> roots:string list
  -> abstract_types:string list
  -> prelude:string option
  -> (string, refusal) result
