(* Lcnf_nat -- see lcnf_nat.mli. The bodies are the ones the route printed into every generated
   file before slice 2.1, unchanged. *)

let mul a b = if a = 0 then 0 else if b > max_int / a then max_int else a * b

let rec pow a b =
  if b = 0
  then 1
  else (
    let h = pow a (b - 1) in
    if a = 0 then 0 else if h > max_int / a then max_int else h * a)
;;

let shift_left a b =
  let s = pow 2 b in
  if a = 0 then 0 else if s > max_int / a then max_int else a * s
;;
