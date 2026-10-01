(* Seat Q: every constructor index drawn (the 28 of the wave) and of_ty the identity here. *)
open Wave_types
module Id = Of_ty_copy.Make (struct type ty = Wave_types.ty =
    | Ty_never | Ty_unit | Ty_nat | Ty_int | Ty_string | Ty_bool | Ty_handle of string
    | Ty_option of ty | Ty_list of ty | Ty_prod of ty * ty | Ty_except of ty * ty
    | Ty_exitOf of ty * ty | Ty_causeOf of ty | Ty_fiberOf of ty * ty | Ty_union of ty * ty
    | Ty_lit of string | Ty_refOf of ty | Ty_deferredOf of ty * ty | Ty_var of int | Ty_unknown
    | Ty_record of (string * (ty * bool)) list | Ty_map of ty * ty | Ty_tuple of ty list
    | Ty_app of string * ty list | Ty_null | Ty_undefined | Ty_number | Ty_bytes end)
let index = function
  | Ty_never -> 0 | Ty_unit -> 1 | Ty_nat -> 2 | Ty_int -> 3 | Ty_string -> 4 | Ty_bool -> 5
  | Ty_handle _ -> 6 | Ty_option _ -> 7 | Ty_list _ -> 8 | Ty_prod _ -> 9 | Ty_except _ -> 10
  | Ty_exitOf _ -> 11 | Ty_causeOf _ -> 12 | Ty_fiberOf _ -> 13 | Ty_union _ -> 14 | Ty_lit _ -> 15
  | Ty_refOf _ -> 16 | Ty_deferredOf _ -> 17 | Ty_var _ -> 18 | Ty_unknown -> 19 | Ty_record _ -> 20
  | Ty_map _ -> 21 | Ty_tuple _ -> 22 | Ty_app _ -> 23 | Ty_null -> 24 | Ty_undefined -> 25
  | Ty_number -> 26 | Ty_bytes -> 27
let () =
  let seen = Array.make 28 false in
  let ok = ref true in
  for _ = 1 to 5000 do
    let t = Rand_ty_copy.rand_ty 3 in
    seen.(index t) <- true;
    if Id.of_ty t <> t then ok := false
  done;
  let drawn = Array.fold_left (fun n b -> if b then n + 1 else n) 0 seen in
  Printf.printf "rand_ty: %d of 28 constructors drawn at the root in 5000 samples; of_ty identity: %b\n" drawn !ok
