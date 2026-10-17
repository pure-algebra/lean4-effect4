(* itree_lane.ml -- the extracted interaction-tree meaning, answered by the to-do lane's hosts.

   What it is: Itree_run is rocq/Extract.v's extraction: the Rocq meaning of an Eff program
   (rocq/Denote.v) with its cells as a state and each host row answered by a host function. Here
   each E4_host provider of the to-do lane (ocaml/engine/test/todo/native_todo.ml) becomes such a
   function, so the same hosts that answer the engine answer the extracted tree. For each request
   of Lean's fixture it compares the run's calls, the root's exit and the host's last state with
   Lean's result, byte for byte; then it times the run against E4_host on the engine's Fast
   instance with the same host. A measurement and a finite check; it is no lane of the estate.
   Depends on: Itree_run (extracted), the to-do lane's library (Todo_gen, Todo_fixture,
   Native_todo), effect4_engine, effect4_eff.

   Properties:
   I1  A provider's answer crosses as the meaning's exit: a success as its value, a failure as
       Lean's exit image (Todo_gen.reify_exit_val, lowered from Lean).     by construction
   I2  For every request and every host here, the extracted meaning's calls, root exit and host
       state are Lean's result (the fixture's result or broken line).      tested
   I3  The timing is CPU time, the median of five samples of at least 0.1 s.  by construction *)

open Todo_fixture

let host_of (table : Eff_types.row list) (provider : Eff_types.row -> Eff_types.val_ -> 's -> _ option) :
    's Itree_run.host =
  let rows = Array.of_list table in
  fun i v st ->
    if i < 0 || i >= Array.length rows then None
    else
      match provider rows.(i) v st with
      | Some (Eff_types.Completion_ofExit (Eff_types.Exit_success value), st') -> Some (Itree_run.Success value, st')
      | Some (Eff_types.Completion_ofExit ex, st') -> Some (Itree_run.Failure (Todo_gen.reify_exit_val ex), st')
      | Some (Eff_types.Completion_ofRefGet _, _) | None -> None

(* The run packed as Lean's result value: [calls; exit; state]. *)
let result_val calls exit_ (state : Native_todo.lane_state) : Eff_types.val_ =
  let next, items = state in
  Eff_types.Val_list
    [ Eff_types.Val_list
        (List.map
           (fun ((i, request), answer) ->
             Eff_types.Val_list
               [ Eff_types.Val_nat i; request;
                 Eff_types.Val_list [ Eff_types.Val_nat 0; Itree_run.exit_image answer ] ])
           calls);
      Eff_types.Val_some (Itree_run.exit_image exit_);
      Eff_types.Val_list
        [ Eff_types.Val_nat next;
          Eff_types.Val_list
            (List.map
               (fun (id, (title, d)) -> Eff_types.Val_list [ Eff_types.Val_nat id; Eff_types.Val_str title; Eff_types.Val_bool d ])
               items) ] ]

let fuel = 1_000_000

let run (built : Todo_gen.built) provider make lane =
  match Itree_run.run_n fuel (host_of built.app.rows provider) built.program (make ()) with
  | Itree_run.Done ((st, calls), ex) -> Some (hex_of (result_val calls ex (lane st)))
  | Itree_run.Waiting _ | Itree_run.Unfinished -> None

let sample f =
  let rec go n =
    let t0 = Sys.time () in
    for _ = 1 to n do
      ignore (Sys.opaque_identity (f ()))
    done;
    let dt = Sys.time () -. t0 in
    if dt < 0.1 then go (n * 2) else dt /. float_of_int n
  in
  go 1

let time f = List.nth (List.sort Float.compare (List.init 5 (fun _ -> sample f))) 2

module F = Effect4_engine.E4_engine.Fast
module H = Effect4_engine.E4_host.Make (F)

let () =
  let path = if Array.length Sys.argv > 1 then Sys.argv.(1) else "ocaml/engine/test/todo/todo-host.txt" in
  let requests = read_fixture path in
  let failures = ref 0 in
  let check name ok =
    Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
    if not ok then incr failures
  in
  let core = Native_todo.host (module Native_todo.Core : Native_todo.REPO with type t = Todo_core.t) in
  List.iteri
    (fun i r ->
      let built = built_of r in
      let state = repo_of (exactly "the state" Eff_val.decode_exact r.state) in
      let name what = Printf.sprintf "%d %s: %s" i r.entry what in
      check (name "the lowered reference repository through the extracted tree is Lean's")
        (run built Todo_gen.test_dogfood_scenario_todo_repository (fun () -> state) Fun.id = Some r.result);
      check (name "the typed record host through the extracted tree is Lean's")
        (run built (Native_todo.provider Native_todo.record) (fun () -> state) Fun.id = Some r.result);
      check (name "the pure core behind REPO through the extracted tree is Lean's")
        (run built (Native_todo.provider core) (fun () -> Native_todo.core_of_lane state) Native_todo.lane_of_core
         = Some r.result);
      check (name "the broken typed host through the extracted tree is Lean's broken result")
        (run built (Native_todo.provider Native_todo.broken) (fun () -> state) Fun.id = Some r.broken))
    requests;
  (* the timing: one request after another, the extracted tree against the engine, one host *)
  let provider = Native_todo.provider Native_todo.record in
  let all = List.map (fun r -> (built_of r, repo_of (exactly "the state" Eff_val.decode_exact r.state))) requests in
  let tree () =
    List.iter
      (fun ((b : Todo_gen.built), st) -> ignore (Itree_run.run_n fuel (host_of b.app.rows provider) b.program st))
      all
  in
  let engine () =
    List.iter (fun ((b : Todo_gen.built), st) -> ignore (H.serve ~table:b.app.rows provider b.program ~fuel:1000 st)) all
  in
  let n = float_of_int (List.length all) in
  let t_tree = time tree /. n and t_engine = time engine /. n in
  Printf.printf "per request, the typed record host, CPU time: extracted tree %.2f us, engine (E4_host, Fast) %.2f us\n"
    (t_tree *. 1e6) (t_engine *. 1e6);
  exit (if !failures = 0 then 0 else 1)
