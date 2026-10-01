(* The lowered `GenFix.Lower` at the two vectors its Lean module guards (`ZipIdx.lean`):
   positionsOfA [a; b; a; _; a] = 6 and indexed [x; _] = [(x, 0); (_, 1)]. *)
open Zipidx_gen

let () =
  Printf.printf "%d\n"
    (gen_fix_lower_positions_of_a [Arg_name "a"; Arg_name "b"; Arg_name "a"; Arg_hole; Arg_name "a"]);
  List.iter (fun (s, i) -> Printf.printf "%s %d\n" s i)
    (gen_fix_lower_indexed [Arg_name "x"; Arg_hole])
