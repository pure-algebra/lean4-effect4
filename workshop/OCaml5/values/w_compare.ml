(* O3 witness: structural compare, equality and hashing.
   Native: runtime/compare.c. js_of_ocaml: compare.js caml_compare_val
   (:66-238), caml_compare (:239), caml_equal (:246); the tag alphabet is
   caml_compare_val_tag (:20-42). *)
let p k v = Printf.printf "%s\t%s\n" k v
let opaque = Sys.opaque_identity
let pc k a b = p k (string_of_int (compare (opaque a) (opaque b)))

type t = A | B of int | C of int * int

let () =
  pc "int_lt" 1 2;
  pc "int_gt" 2 1;
  pc "int_eq" 1 1;
  pc "int_min_max" min_int max_int;
  pc "bool" false true;
  pc "unit" () ();
  pc "char" 'a' 'b';
  pc "string" "abc" "abd";
  pc "string_high" "\xff" "\x01";
  pc "float" 1.0 2.0;
  pc "float_neg0" (-0.0) 0.0;
  pc "tuple" (1, "a", 2.0) (1, "a", 3.0);
  pc "tuple_first" (2, "a") (1, "z");
  pc "list" [1; 2; 3] [1; 2; 4];
  pc "list_len" [1; 2] [1; 2; 3];
  pc "option_none_some" None (Some 1);
  pc "option_some" (Some 1) (Some 2);
  pc "ctor_imm_blk" A (B 1);
  pc "ctor_blk_blk" (B 1) (C (0, 0));
  pc "ctor_same" (B 1) (B 2);
  pc "int64" 1L 2L;
  pc "int32" 1l 2l;
  pc "nativeint" 1n 2n;
  pc "array" [| 1; 2 |] [| 1; 3 |];
  pc "float_array" [| 1.0 |] [| 2.0 |];
  pc "nested" (Some [ (1, "a") ]) (Some [ (1, "b") ]);
  p "eq_tuple" (string_of_bool (opaque (1, 2) = opaque (1, 2)));
  p "phys_tuple" (string_of_bool (opaque (1, 2) == opaque (1, 2)));
  p "eq_list" (string_of_bool (opaque [ 1; 2 ] = opaque [ 1; 2 ]));
  p "eq_nested" (string_of_bool (opaque (Some [ (1, "a") ]) = opaque (Some [ (1, "a") ])));
  p "eq_int64" (string_of_bool (opaque 3L = opaque 3L));
  p "eq_float_array" (string_of_bool (opaque [| 1.0 |] = opaque [| 1.0 |]));
  (* an int and a float are never structurally equal in OCaml's type system;
     the mixed case that IS reachable is a custom block against an immediate *)
  p "cmp_int64_vs_int64_neg" (string_of_int (compare (opaque (-1L)) (opaque 1L)));
  p "hash_int_0" (string_of_int (Hashtbl.hash (opaque 0)));
  p "hash_int_1" (string_of_int (Hashtbl.hash (opaque 1)));
  p "hash_int_max" (string_of_int (Hashtbl.hash (opaque max_int)));
  p "hash_int_2p31" (string_of_int (Hashtbl.hash (opaque 2147483647)));
  p "hash_string" (string_of_int (Hashtbl.hash (opaque "abc")));
  p "hash_string_utf8" (string_of_int (Hashtbl.hash (opaque "h\xc3\xa9llo")));
  p "hash_float" (string_of_int (Hashtbl.hash (opaque 1.5)));
  p "hash_neg0" (string_of_int (Hashtbl.hash (opaque (-0.0))));
  p "hash_zero" (string_of_int (Hashtbl.hash (opaque 0.0)));
  p "hash_tuple" (string_of_int (Hashtbl.hash (opaque (1, "a"))));
  p "hash_list" (string_of_int (Hashtbl.hash (opaque [ 1; 2; 3 ])));
  p "hash_int64" (string_of_int (Hashtbl.hash (opaque 3L)));
  p "hash_unit" (string_of_int (Hashtbl.hash (opaque ())));
  p "hash_true" (string_of_int (Hashtbl.hash (opaque true)));
  p "hash_none" (string_of_int (Hashtbl.hash (opaque (None : int option))))
