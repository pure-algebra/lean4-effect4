let () =
  Printf.printf "OCaml=%s int_size=%d max_int=%d\n" Sys.ocaml_version Sys.int_size max_int;
  List.iter (fun x -> Printf.printf "float=%g bits=%016Lx fits_current_nonnegative_int=%b\n"
    x (Int64.bits_of_float x)
    (Int64.compare (Int64.bits_of_float x) 0L >= 0 && Int64.compare (Int64.bits_of_float x) (Int64.of_int max_int) <= 0))
    [0.; 1.; 2.; -0.; -1.]
