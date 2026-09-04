(* Spike P3: `caml_continuation_use_and_update_handler_noexc` on an already-resumed
   continuation.  `fiber.c:637-640` returns early on a taken handle; `effect.js:158-162`
   has no such guard and writes `stack[3]` on the JavaScript number 0 — a silent no-op in
   sloppy mode, a TypeError in strict mode (spike O1 §6, O2 open item 2). *)

open Effect
open Effect.Shallow

let row s = print_string (s ^ "\n")

let () =
  let k = fiber (fun () -> row "body"; 42) in
  let h =
    { retc = (fun v -> row (Printf.sprintf "retc\t%d" v))
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (_ : a Effect.t) -> None)
    }
  in
  continue_with k () h;
  row "again";
  try continue_with k () h with Continuation_already_resumed -> row "already-resumed"
