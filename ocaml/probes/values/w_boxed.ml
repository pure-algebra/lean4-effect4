(* O3 witness: the boxed integers. Native: Custom_tag 255 blocks
   (mlvalues.h:401). js_of_ocaml: Int32/Nativeint are the same |0 numbers
   as `int` (ints.js), Int64 is a three-limb object (int64.js). *)
let p k v = Printf.printf "%s\t%s\n" k v
let opaque = Sys.opaque_identity

let () =
  p "int32_size" (string_of_int 32);
  p "nativeint_size" (string_of_int Nativeint.size);
  p "int32_max" (Int32.to_string Int32.max_int);
  p "int32_max_succ" (Int32.to_string (Int32.add (opaque Int32.max_int) 1l));
  p "int32_mul_ovf" (Int32.to_string (Int32.mul (opaque 65536l) 65536l));
  p "int32_div_neg" (Int32.to_string (Int32.div (opaque (-7l)) 2l));
  p "int32_lsr_neg" (Int32.to_string (Int32.shift_right_logical (opaque (-1l)) 1));
  p "int32_min_div_m1" (Int32.to_string (Int32.div (opaque Int32.min_int) (-1l)));
  p "nativeint_max" (Nativeint.to_string Nativeint.max_int);
  p "nativeint_max_succ" (Nativeint.to_string (Nativeint.add (opaque Nativeint.max_int) 1n));
  p "int64_max" (Int64.to_string Int64.max_int);
  p "int64_max_succ" (Int64.to_string (Int64.add (opaque Int64.max_int) 1L));
  p "int64_min" (Int64.to_string Int64.min_int);
  p "int64_mul" (Int64.to_string (Int64.mul (opaque 3037000500L) 3037000500L));
  p "int64_div_neg" (Int64.to_string (Int64.div (opaque (-7L)) 2L));
  p "int64_mod_neg" (Int64.to_string (Int64.rem (opaque (-7L)) 2L));
  p "int64_lsr" (Int64.to_string (Int64.shift_right_logical (opaque (-1L)) 1));
  p "int64_asr" (Int64.to_string (Int64.shift_right (opaque (-1L)) 1));
  p "int64_lsl" (Int64.to_string (Int64.shift_left (opaque 1L) 62));
  p "int64_of_int_max" (Int64.to_string (Int64.of_int (opaque max_int)));
  p "int64_to_int_big" (string_of_int (Int64.to_int (opaque 4611686018427387903L)));
  p "int64_bits_of_01" (Printf.sprintf "%Lx" (Int64.bits_of_float 0.1));
  p "int64_compare" (string_of_int (compare (opaque 1L) 2L));
  p "int64_equal" (string_of_bool ((opaque 3L) = 3L));
  p "int64_tag" (string_of_int (Obj.tag (Obj.repr (opaque 3L))));
  p "int32_tag" (string_of_int (Obj.tag (Obj.repr (opaque 3l))));
  p "nativeint_tag" (string_of_int (Obj.tag (Obj.repr (opaque 3n))))
