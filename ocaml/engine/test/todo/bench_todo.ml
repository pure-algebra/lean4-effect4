(* bench_todo.ml -- the cost of a host call on the engine, by host and by stage.

   What it is: a measurement, not a gate. For the requests of the to-do fixture it drives the
   engine (E4_engine.Fast) under E4_host with each host of the lane, and divides by the host
   calls answered. It then times the stages of each request's first host call on their own:
   loading and evaluating the program, reading the calls, the provider's answer, the ingress
   check with the decision, the admission and the step. Last it times the derived codec of a
   to-do against the frame built by hand, and the canonical bytes of the same value. Each figure
   is CPU time (Sys.time): the median of five samples of at least 0.1 s, so the load of other
   processes moves it little.
   Depends on: Todo_gen (GENERATED), Todo_fixture, Native_todo, E4_engine, E4_host, Eff_val.

   Properties:
   B1  Each host's drive is checked to finish with Lean's result once before it is timed, and
       each codec to round-trip, so no figure times a failing path.        by construction
   B2  Nothing is asserted about the numbers.                               by construction

   Run: cd ocaml && opam exec --switch=effect4 -- dune exec engine/test/todo/bench_todo.exe
        [-- PATH-TO-todo-host.txt] *)

open Eff_types
open Todo_fixture
module F = Effect4_engine.E4_engine.Fast
module H = Effect4_engine.E4_host.Make (F)

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

let median xs = List.nth (List.sort Float.compare xs) (List.length xs / 2)
let time f = median (List.init 5 (fun _ -> sample f))
let report name seconds = Printf.printf "  %-62s %10.2f us\n%!" name (seconds *. 1e6)

let fixture_path () =
  if Array.length Sys.argv > 1 then Sys.argv.(1)
  else if Sys.file_exists "todo-host.txt" then "todo-host.txt"
  else "engine/test/todo/todo-host.txt"

let () =
  let requests =
    List.map
      (fun r -> (r, built_of r, repo_of (exactly "the state" Eff_val.decode_exact r.state)))
      (read_fixture (fixture_path ()))
  in
  let drive (built : Todo_gen.built) provider state =
    match H.serve ~table:built.app.rows provider built.program ~fuel:1000 state with
    | Ok served -> served
    | Error (H.Load_outside_profile why) -> failwith ("a request's program did not load: " ^ why)
  in
  let result (type st) (s : st H.served) lane =
    hex_of
      (Todo_gen.test_dogfood_scenario_todo_host_result_val
         ( ( List.map
               (fun (c : H.call) ->
                 ({ Todo_gen.row = c.row; request = c.request; completion = c.answer } : Todo_gen.call))
               s.calls,
             F.root_exit_of s.engine ),
           lane ))
  in
  Printf.printf "bench_todo: %d requests, engine %s, CPU time per unit\n" (List.length requests) F.name;
  (* 1. a whole drive per host, divided by the host calls it answered *)
  Printf.printf "1. a drive under E4_host, per host call\n";
  let per_call (type s) name (provider : row -> val_ -> s -> _) (make : Native_todo.lane_state -> s)
      (lane : s -> Native_todo.lane_state) =
    let calls =
      List.fold_left
        (fun n (r, built, state) ->
          let s = drive built provider (make state) in
          (match s.stop with
           | H.Machine H.Finished when result s (lane s.state) = r.result -> ()
           | _ -> failwith (name ^ ": the drive is not Lean's"));
          n + List.length s.calls)
        0 requests
    in
    let t =
      time (fun () -> List.iter (fun (_, built, state) -> ignore (drive built provider (make state))) requests)
    in
    report (Printf.sprintf "%s (%d calls)" name calls) (t /. float_of_int calls)
  in
  per_call "the lowered reference repository (untyped)" Todo_gen.test_dogfood_scenario_todo_repository Fun.id Fun.id;
  per_call "the lowered typed model, through the derived codecs"
    (Native_todo.provider Todo_gen.test_dogfood_scenario_todo_typed_model) Fun.id Fun.id;
  per_call "OCaml, frames built by hand (Native_todo.Untyped)" Native_todo.Untyped.provider Fun.id Fun.id;
  per_call "OCaml, the record (Native_todo.record)" (Native_todo.provider Native_todo.record) Fun.id Fun.id;
  per_call "OCaml, the pure core behind REPO"
    (Native_todo.provider (Native_todo.host (module Native_todo.Core : Native_todo.REPO with type t = Todo_core.t)))
    Native_todo.core_of_lane Native_todo.lane_of_core;
  per_call "OCaml, the hash table behind REPO"
    (Native_todo.provider
       (Native_todo.host (module Native_todo.Table : Native_todo.REPO with type t = Native_todo.Table.t)))
    (fun state -> Native_todo.Table.create state) Native_todo.Table.snapshot;
  (* 2. the stages of each request's first host call, summed over the requests *)
  Printf.printf "2. the stages of each request's first host call, mean over the requests\n";
  let n = float_of_int (List.length requests) in
  let evaluated (built : Todo_gen.built) = F.step (F.load ~table:built.app.rows built.program ~fuel:1000) (F.evaluate 0) in
  let firsts =
    List.map
      (fun (_, (built : Todo_gen.built), state) ->
        let t = evaluated built in
        match F.host_calls t with
        | (fiber, token, row, request) :: _ -> (built, state, t, fiber, token, List.nth built.app.rows row, request)
        | [] -> failwith "a request with no host call")
      requests
  in
  let typed = Native_todo.provider Native_todo.record in
  let answer provider (_, state, _, _, _, row, request) =
    match provider row request state with Some (c, _) -> c | None -> failwith "declined"
  in
  let mean f = time (fun () -> List.iter (fun x -> ignore (f x)) firsts) /. n in
  report "load the program and evaluate the root" (mean (fun (built, _, _, _, _, _, _) -> evaluated built));
  report "read the host calls (E4_engine.host_calls)" (mean (fun (_, _, t, _, _, _, _) -> F.host_calls t));
  report "answer: the typed reactor over the record (decode, dispatch, encode)" (mean (answer typed));
  report "answer: the frames built by hand (Native_todo.Untyped)" (mean (answer Native_todo.Untyped.provider));
  report "the ingress check and the decision (E4_engine.answer_async)"
    (mean (fun ((_, _, _, fiber, token, _, _) as x) -> F.answer_async fiber token (answer typed x)));
  let decided =
    List.map (fun ((_, _, t, fiber, token, _, _) as x) -> (t, F.answer_async fiber token (answer typed x))) firsts
  in
  let mean_decided f = time (fun () -> List.iter (fun x -> ignore (f x)) decided) /. n in
  report "the admission (E4_engine.admits, Lean's checked replay)" (mean_decided (fun (t, d) -> F.admits t d));
  report "the step to the next host call or the end (E4_engine.step)" (mean_decided (fun (t, d) -> F.step t d));
  (* 3. the derived codec of a to-do, against the frame built by hand *)
  Printf.printf "3. the derived codec of a to-do\n";
  let image =
    Todo_gen.store_image_equiv Todo_gen.test_dogfood_scenario_todo_typed_todo_modeled_staged
      Todo_gen.test_dogfood_scenario_todo_typed_todo_modeled_of_c
      Todo_gen.test_dogfood_scenario_todo_typed_todo_modeled_to_c
  in
  let list_image = Todo_gen.store_image_list image in
  let one = Native_todo.todo 7 "write the bench" false in
  let many = List.init 100 (fun i -> Native_todo.todo i (Printf.sprintf "item %d" i) (i mod 2 = 0)) in
  let frame = list_image.to_val many in
  if image.of_val (image.to_val one) <> Some one || list_image.of_val frame <> Some many then
    failwith "the derived codec does not round-trip";
  if Eff_val.to_bytes (image.to_val one) <> Eff_val.to_bytes (Native_todo.Untyped.todo 7 "write the bench" false) then
    failwith "the derived codec and the hand frame disagree";
  report "encode one to-do, derived (Modeled image)" (time (fun () -> image.to_val one));
  report "encode one to-do, frame built by hand" (time (fun () -> Native_todo.Untyped.todo 7 "write the bench" false));
  report "decode one to-do, derived" (let v = image.to_val one in time (fun () -> image.of_val v));
  report "encode 100 to-dos, derived" (time (fun () -> list_image.to_val many));
  report "decode 100 to-dos, derived" (time (fun () -> list_image.of_val frame));
  report "canonical bytes of 100 to-dos (Eff_val.to_bytes)" (time (fun () -> Eff_val.to_bytes frame))
