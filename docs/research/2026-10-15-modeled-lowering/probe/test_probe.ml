open Eff_types
open Probe_gen
let () =
  let t = { id = 3; title = "milk ✓"; done_ = false } in
  let v = probe_modeled_lower_todo_to_val t in
  let ok1 = probe_modeled_lower_todo_of_val v = Some t in
  let ok2 = probe_modeled_lower_todo_of_val (Val_ctor (0, [Val_list []; Val_list []])) = None in
  let ok3 = (match probe_modeled_lower_status_to_val (Status_closed "x") with
             | Val_ctor (0, [Val_list [Val_str "_tag"; Val_str "reason"]; Val_list [Val_str "closed"; Val_str "x"]]) -> true
             | _ -> false) in
  Printf.printf "round trip %b, refusal %b, sum frame %b\n" ok1 ok2 ok3;
  exit (if ok1 && ok2 && ok3 then 0 else 1)
