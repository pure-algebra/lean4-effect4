(* O3 witness: the native `int`. Native is 63-bit (mlvalues.h:77-80, Val_long/Max_long);
   js_of_ocaml is a JavaScript number truncated with `| 0` (ints.js:90,102) and
   Math.imul (ints.js:94-96), so 32-bit. Shifts are emitted raw
   (generate.ml:925-927), so JS's shift-count-mod-32 shows through. *)
let p k v = Printf.printf "%s\t%s\n" k v
let pi k (v : int) = p k (string_of_int v)
let opaque = Sys.opaque_identity

let () =
  pi "int_size" Sys.int_size;
  pi "max_int" max_int;
  pi "min_int" min_int;
  (* the falsifier of ruling 6 *)
  pi "add_2p31m1_1" (opaque 2147483647 + 1);
  pi "add_max_1" (opaque max_int + 1);
  pi "sub_min_1" (opaque min_int - 1);
  pi "mul_overflow" (opaque 65536 * 65536);
  pi "mul_big" (opaque 123456789 * 987654321);
  pi "neg_min" (- (opaque min_int));
  pi "div_trunc_neg" (opaque (-7) / 2);
  pi "mod_trunc_neg" (opaque (-7) mod 2);
  pi "div_neg_divisor" (opaque 7 / (-2));
  pi "mod_neg_divisor" (opaque 7 mod (-2));
  pi "div_min_m1" (opaque min_int / (-1));
  pi "asr_neg1_1" (opaque (-1) asr 1);
  pi "asr_neg7_1" (opaque (-7) asr 1);
  pi "lsr_neg1_1" (opaque (-1) lsr 1);
  pi "lsr_neg7_1" (opaque (-7) lsr 1);
  pi "lsl_1_30" (opaque 1 lsl 30);
  pi "lsl_1_31" (opaque 1 lsl 31);
  pi "lsl_1_32" (opaque 1 lsl 32);
  pi "lsl_1_62" (opaque 1 lsl 62);
  pi "land_neg1_255" (opaque (-1) land 255);
  pi "lor_neg1_0" (opaque (-1) lor 0);
  pi "lxor_neg1_neg1" (opaque (-1) lxor (-1));
  pi "lnot_0" (lnot (opaque 0));
  pi "abs_min" (abs (opaque min_int));
  p "int_of_string_2p31" (try string_of_int (int_of_string "2147483648")
                          with Failure m -> "Failure:" ^ m);
  p "succ_max" (string_of_int (succ (opaque max_int)))
