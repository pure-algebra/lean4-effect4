(* Lcnf_interface: the public interface of generated OCaml.
   Depends on compiler-libs and the generator's root/type metadata.
   Properties: selected roots only; whole packages abstract; last binding wins.
   These properties are tested by test_interface and the native sealing controls. *)

type refusal =
  | Input of string
  | Not_implementation
  | Missing_values of string list
  | Missing_types of string list

val message : refusal -> string

val select
  :  roots:string list
  -> abstract_types:string list
  -> Types.signature
  -> (Types.signature, refusal) result

val generate
  :  cmt:string
  -> roots:string list
  -> abstract_types:string list
  -> prelude:string option
  -> (string, refusal) result
