(* Copy of ocaml/engine/e4_program.ml:126-158 (`of_ty` and its count) over the wave family. The
   source type and the engine type are both the wave's `ty` here (the identity instance of the
   functor), which is enough to type-check every arm. *)
module type PROGRAM_TYPES = sig
  type ty = Wave_types.ty =
    | Ty_never | Ty_unit | Ty_nat | Ty_int | Ty_string | Ty_bool | Ty_handle of string
    | Ty_option of ty | Ty_list of ty | Ty_prod of ty * ty | Ty_except of ty * ty
    | Ty_exitOf of ty * ty | Ty_causeOf of ty | Ty_fiberOf of ty * ty | Ty_union of ty * ty
    | Ty_lit of string | Ty_refOf of ty | Ty_deferredOf of ty * ty | Ty_var of int | Ty_unknown
    | Ty_record of (string * (ty * bool)) list | Ty_map of ty * ty | Ty_tuple of ty list
    | Ty_app of string * ty list | Ty_null | Ty_undefined | Ty_number | Ty_bytes
end

let ctor_names_ty = [ "never"; "unit"; "nat"; "int"; "string"; "bool"; "handle"; "option"; "list";
  "prod"; "except"; "exitOf"; "causeOf"; "fiberOf"; "union"; "lit"; "refOf"; "deferredOf"; "var";
  "unknown"; "record"; "map"; "tuple"; "app"; "null"; "undefined"; "number"; "bytes" ]

let () = assert (List.length ctor_names_ty = 28)

module Make (A : PROGRAM_TYPES) = struct
  let rec of_ty : Wave_types.ty -> A.ty = function
    | Wave_types.Ty_never -> A.Ty_never
    | Wave_types.Ty_unit -> A.Ty_unit
    | Wave_types.Ty_nat -> A.Ty_nat
    | Wave_types.Ty_int -> A.Ty_int
    | Wave_types.Ty_string -> A.Ty_string
    | Wave_types.Ty_bool -> A.Ty_bool
    | Wave_types.Ty_handle h -> A.Ty_handle h
    | Wave_types.Ty_option a -> A.Ty_option (of_ty a)
    | Wave_types.Ty_list a -> A.Ty_list (of_ty a)
    | Wave_types.Ty_prod (a, b) -> A.Ty_prod (of_ty a, of_ty b)
    | Wave_types.Ty_except (a, b) -> A.Ty_except (of_ty a, of_ty b)
    | Wave_types.Ty_exitOf (a, b) -> A.Ty_exitOf (of_ty a, of_ty b)
    | Wave_types.Ty_causeOf a -> A.Ty_causeOf (of_ty a)
    | Wave_types.Ty_fiberOf (a, b) -> A.Ty_fiberOf (of_ty a, of_ty b)
    | Wave_types.Ty_union (a, b) -> A.Ty_union (of_ty a, of_ty b)
    | Wave_types.Ty_lit s -> A.Ty_lit s
    | Wave_types.Ty_refOf a -> A.Ty_refOf (of_ty a)
    | Wave_types.Ty_deferredOf (a, b) -> A.Ty_deferredOf (of_ty a, of_ty b)
    | Wave_types.Ty_var i -> A.Ty_var i
    | Wave_types.Ty_unknown -> A.Ty_unknown
    (* the wave: eight arms *)
    | Wave_types.Ty_record fs -> A.Ty_record (List.map (fun (n, (t, o)) -> (n, (of_ty t, o))) fs)
    | Wave_types.Ty_map (k, v) -> A.Ty_map (of_ty k, of_ty v)
    | Wave_types.Ty_tuple xs -> A.Ty_tuple (List.map of_ty xs)
    | Wave_types.Ty_app (n, xs) -> A.Ty_app (n, List.map of_ty xs)
    | Wave_types.Ty_null -> A.Ty_null
    | Wave_types.Ty_undefined -> A.Ty_undefined
    | Wave_types.Ty_number -> A.Ty_number
    | Wave_types.Ty_bytes -> A.Ty_bytes
end
