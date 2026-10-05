#mod_use "/Users/pooks/Dev/lean4-effect4/ocaml/engine/e4_nat.ml";;
let old = try string_of_int (E4_nat.pow_reference 1 1000000) with Stack_overflow -> "Stack_overflow";;
let new_ = E4_nat.pow 1 1000000;;
assert (E4_nat.pow_reference 2 10=1024 && E4_nat.pow 2 10=1024);;
assert (new_=1);;
Printf.printf "{\"ocaml\":\"%s\",\"old_result\":\"%s\",\"existing_fixed_point_result\":%d,\"positive_control\":1024}\n" Sys.ocaml_version old new_;;
