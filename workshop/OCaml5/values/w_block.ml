(* O3 witness: blocks. Native: header tag + fields (mlvalues.h). js_of_ocaml:
   a JS array with the tag at index 0 (generate.ml, `Block`), so Obj.size and
   Obj.tag go through obj.js. Constant constructors are immediates on both. *)
let p k v = Printf.printf "%s\t%s\n" k v
let opaque = Sys.opaque_identity

type t = A | B of int | C of int * int | D of { x : int }
type r = { f1 : int; f2 : string }
type fr = { g1 : float; g2 : float }

let show (o : Obj.t) =
  if Obj.is_int o then "imm:" ^ string_of_int (Obj.magic o : int)
  else Printf.sprintf "blk:%d/%d" (Obj.tag o) (Obj.size o)

let () =
  p "ctor_A" (show (Obj.repr (opaque A)));
  p "ctor_B" (show (Obj.repr (opaque (B 7))));
  p "ctor_C" (show (Obj.repr (opaque (C (1, 2)))));
  p "ctor_D" (show (Obj.repr (opaque (D { x = 9 }))));
  p "field_B0" (string_of_int (Obj.magic (Obj.field (Obj.repr (opaque (B 7))) 0) : int));
  p "field_C1" (string_of_int (Obj.magic (Obj.field (Obj.repr (opaque (C (1, 2)))) 1) : int));
  p "record" (show (Obj.repr (opaque { f1 = 1; f2 = "s" })));
  p "float_record" (show (Obj.repr (opaque { g1 = 1.0; g2 = 2.0 })));
  p "tuple2" (show (Obj.repr (opaque (1, 2))));
  p "tuple3" (show (Obj.repr (opaque (1, 2, 3))));
  p "none" (show (Obj.repr (opaque (None : int option))));
  p "some" (show (Obj.repr (opaque (Some 1))));
  p "nil" (show (Obj.repr (opaque ([] : int list))));
  p "cons" (show (Obj.repr (opaque [1; 2])));
  p "int_array" (show (Obj.repr (opaque [| 1; 2; 3 |])));
  p "float_array" (show (Obj.repr (opaque [| 1.0; 2.0; 3.0 |])));
  p "string_array" (show (Obj.repr (opaque [| "a" |])));
  p "unit" (show (Obj.repr (opaque ())));
  p "true" (show (Obj.repr (opaque true)));
  p "false" (show (Obj.repr (opaque false)));
  p "char" (show (Obj.repr (opaque 'a')));
  p "boxed_float" (show (Obj.repr (opaque 1.5)));
  p "closure" (show (Obj.repr (opaque (fun x -> x + 1))));
  p "exn_ctor" (show (Obj.repr (opaque Not_found)));
  p "exn_arg" (show (Obj.repr (opaque (Invalid_argument "z"))));
  p "double_field" (Printf.sprintf "%.17g"
                      (Obj.double_field (Obj.repr (opaque [| 1.5; 2.5 |])) 1));
  p "array_get_float" (Printf.sprintf "%.17g" (opaque [| 1.5; 2.5 |]).(1));
  p "array_len_float" (string_of_int (Array.length (opaque [| 1.5; 2.5 |])))
