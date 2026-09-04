(* Spike P3 falsifier: the continuation that `reperform` at the root takes.
   `fiber.c:660` / `interp.c:1374-1381` take it with `caml_continuation_use`, which nulls
   the field; js_of_ocaml's `uncaught_effect_handler` reads `k[1]` directly
   (`jslib.js:77`) and never nulls it.  So on the OCaml hosts the parked continuation is
   already resumed, and on js_of_ocaml it is not. *)

open Effect
open Effect.Deep

type _ Effect.t += Number : int Effect.t

(* `%reperform` is the runtime primitive `Stdlib.Effect` uses internally (effect.ml:69-70),
   which never hands the user the continuation it reperforms.  It is in tail position here, as
   `bytegen.ml:796-800` demands.  The third argument is the last fiber of the captured chain,
   which for a single capture is field 0 of the continuation: `interp.c:1373` checks for the
   root before reading it, but `arm64.S:789-791` splices unconditionally, so passing anything
   else segfaults the native host. *)
external my_reperform : 'a Effect.t -> ('b, 'c) continuation -> Obj.t -> 'd = "%reperform"

let row s = print_string (s ^ "\n")

let parked : (int, unit) continuation option ref = ref None

let fiber () =
  row "fiber-enter";
  let v = try perform Number with Unhandled _ -> row "caught-in-fiber"; 7 in
  row (Printf.sprintf "fiber-got\t%d" v)

let () =
  match_with fiber ()
    { retc = (fun () -> row "retc")
    ; exnc = (fun e -> row "exnc"; raise e)
    ; effc =
        (fun (type a) (e : a Effect.t) ->
          match e with
          | Number ->
              Some
                (fun (k : (a, unit) continuation) ->
                  row "stash";
                  parked := Some k;
                  my_reperform e k (Obj.field (Obj.repr k) 0))
          | _ -> None)
    };
  row "after-handler";
  match !parked with
  | None -> row "no-k"
  | Some k -> (
      row "continue-again";
      try continue k 99 with Continuation_already_resumed -> row "already-resumed")
