(* Copy of ocaml/eff/test/prop_wire.ml:155-171 (`rand_ty`) over the wave family, every constructor
   reached: today's dispatches on `ri 15` and ends `| _ -> Ty_union`, so lit, refOf, deferredOf,
   var and unknown are never drawn. Leaves first (drawn at depth 0), then the recursive heads; the
   helpers are prop_wire.ml:16-33's. *)
open Wave_types

let rng = Random.State.make [| 42 |]
let ri n = Random.State.int rng n
let rb () = Random.State.bool rng
let pick xs = List.nth xs (ri (List.length xs))
let rand_nat () = ri 100000
let rand_string () = pick [ ""; "a"; "h\xc3\xa9llo"; "quote\"back\\slash" ]
let rand_list f = List.init (ri 4) (fun _ -> f ())

let rec rand_ty d =
  match if d <= 0 then ri 14 else ri 28 with
  | 0 -> Ty_never
  | 1 -> Ty_unit
  | 2 -> Ty_nat
  | 3 -> Ty_int
  | 4 -> Ty_string
  | 5 -> Ty_bool
  | 6 -> Ty_handle (rand_string ())
  | 7 -> Ty_lit (rand_string ())
  | 8 -> Ty_var (rand_nat ())
  | 9 -> Ty_unknown
  | 10 -> Ty_null
  | 11 -> Ty_undefined
  | 12 -> Ty_number
  | 13 -> Ty_bytes
  | 14 -> Ty_option (rand_ty (d - 1))
  | 15 -> Ty_list (rand_ty (d - 1))
  | 16 -> Ty_prod (rand_ty (d - 1), rand_ty (d - 1))
  | 17 -> Ty_except (rand_ty (d - 1), rand_ty (d - 1))
  | 18 -> Ty_exitOf (rand_ty (d - 1), rand_ty (d - 1))
  | 19 -> Ty_causeOf (rand_ty (d - 1))
  | 20 -> Ty_fiberOf (rand_ty (d - 1), rand_ty (d - 1))
  | 21 -> Ty_union (rand_ty (d - 1), rand_ty (d - 1))
  | 22 -> Ty_refOf (rand_ty (d - 1))
  | 23 -> Ty_deferredOf (rand_ty (d - 1), rand_ty (d - 1))
  | 24 -> Ty_record (rand_list (fun () -> (rand_string (), (rand_ty (d - 1), rb ()))))
  | 25 -> Ty_map (rand_ty (d - 1), rand_ty (d - 1))
  | 26 -> Ty_tuple (rand_list (fun () -> rand_ty (d - 1)))
  | _ -> Ty_app (rand_string (), rand_list (fun () -> rand_ty (d - 1)))
