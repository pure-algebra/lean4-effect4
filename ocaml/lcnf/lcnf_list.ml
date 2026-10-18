(* Lcnf_list -- see lcnf_list.mli. The body is the one the route printed into every generated
   file before slice 2.1, unchanged. *)

let contains inst l a = List.exists (fun e -> inst a e) l
