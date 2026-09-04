(* O3 witness: floats. binary64 on both sides (mlvalues.h:336 Double_tag;
   ieee_754.js). NaN, signed zero, and printing are the observable seams. *)
let p k v = Printf.printf "%s\t%s\n" k v
let opaque = Sys.opaque_identity
let hex (f : float) = Printf.sprintf "%Lx" (Int64.bits_of_float f)

(* a float the compiler cannot fold: written through a reference *)
let dyn = ref 0.0
let small = ref 0.0
let () = dyn := 1e18; small := 3.9

let () =
  p "add_01_02" (Printf.sprintf "%.17g" (opaque 0.1 +. 0.2));
  p "add_01_02_bits" (hex (opaque 0.1 +. 0.2));
  p "add_01_02_eq_03" (string_of_bool (opaque 0.1 +. 0.2 = 0.3));
  p "string_of_float_01" (string_of_float (opaque 0.1));
  p "string_of_float_1" (string_of_float (opaque 1.0));
  p "string_of_float_neg0" (string_of_float (opaque (-0.0)));
  p "printf_g_neg0" (Printf.sprintf "%g" (opaque (-0.0)));
  p "printf_f_neg0" (Printf.sprintf "%.1f" (opaque (-0.0)));
  p "neg0_bits" (hex (opaque (-0.0)));
  p "neg0_eq_0" (string_of_bool (opaque (-0.0) = 0.0));
  p "neg0_compare_0" (string_of_int (compare (opaque (-0.0)) 0.0));
  p "one_div_neg0" (string_of_float (1.0 /. opaque (-0.0)));
  let nan = opaque (0.0 /. 0.0) in
  p "nan_is_nan" (string_of_bool (nan <> nan));
  p "nan_eq_nan" (string_of_bool (nan = nan));
  p "nan_compare_nan" (string_of_int (compare nan nan));
  p "nan_compare_1" (string_of_int (compare nan 1.0));
  p "one_compare_nan" (string_of_int (compare 1.0 nan));
  p "nan_lt_1" (string_of_bool (nan < 1.0));
  p "string_of_float_nan" (string_of_float nan);
  p "string_of_float_inf" (string_of_float (opaque infinity));
  p "string_of_float_neginf" (string_of_float (opaque neg_infinity));
  p "max_float" (Printf.sprintf "%.17g" max_float);
  p "min_float" (Printf.sprintf "%.17g" min_float);
  p "epsilon" (Printf.sprintf "%.17g" epsilon_float);
  p "float_of_string_rt" (Printf.sprintf "%.17g" (float_of_string "0.1"));
  (* js_of_ocaml folds `int_of_float` on a compile-time-known float with a
     SATURATING conversion, but compiles the runtime one to `x | 0`
     (generate.ml:326,947). The two disagree; both rows are kept. *)
  p "int_of_float_big_fold" (string_of_int (int_of_float (opaque 1e18)));
  p "int_of_float_big_rt" (string_of_int (int_of_float (opaque !dyn)));
  p "int_of_float_small_rt" (string_of_int (int_of_float (opaque !small)));
  p "int_of_float_trunc_neg" (string_of_int (int_of_float (opaque (-2.7))));
  p "float_of_int_max" (Printf.sprintf "%.17g" (float_of_int (opaque max_int)));
  p "float_of_int_max_bits" (hex (float_of_int (opaque max_int)));
  p "float_of_string_rt_bits" (hex (float_of_string (opaque "0.1")));
  p "max_float_bits" (hex max_float);
  p "min_float_bits" (hex min_float);
  p "epsilon_bits" (hex epsilon_float);
  p "inf_bits" (hex infinity);
  p "neginf_bits" (hex neg_infinity);
  p "nan_bits" (hex (opaque (0.0 /. 0.0)));
  p "sqrt2_bits" (hex (sqrt (opaque 2.0)));
  p "float_tag" (string_of_int (Obj.tag (Obj.repr (opaque 1.5))));
  p "float_array_tag" (string_of_int (Obj.tag (Obj.repr (opaque [| 1.5; 2.5 |]))))
