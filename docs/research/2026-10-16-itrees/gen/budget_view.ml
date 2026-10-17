(* budget_view.ml -- the frames of budgeted runs, as JSON for the animated view, and their timing.

   What it is: Budget_run is rocq/BudgetExtract.v's extraction: Lean's budgeted call tree
   (denoteRowsB, transcribed in rocq/Budget.v) run under a host at budgets 0 .. n with every
   answered call kept (Api.frames). For each program of rocq/Examples.v it writes the program,
   its frames and the budget at which it settles; then it times the frames of a long run. A view
   and a measurement; it is no lane of the estate.
   Depends on: Budget_run (extracted), effect4_eff (Eff_types, Eff_json, Eff_json_text).

   Usage: budget_view OUT.json

   Properties:
   V1  Frame k is Budget_run.run_at k: the run of denoteRowsB k under the host.    by construction
   V2  A frame takes back no step of the frame before it, and a frame that is not cut is
       the next frame (Api.frames_grow, proved); each frame written is checked here. tested
   V3  The timing is CPU time (Sys.time), the median of five samples.             by construction *)

module J = Eff_json_text
open Budget_run

(* A value as the estate's JSON rule writes a constructor: ["name", arg, ...]. *)
let rec json_val (v : Eff_types.val_) : J.t =
  let c name args = J.Array (J.String name :: args) in
  match v with
  | Eff_types.Val_unit -> c "unit" []
  | Eff_types.Val_bool b -> c "bool" [ J.Bool b ]
  | Eff_types.Val_nat n -> c "nat" [ J.Int n ]
  | Eff_types.Val_str s -> c "str" [ J.String s ]
  | Eff_types.Val_bytes bs -> c "bytes" [ J.Array (List.map (fun b -> J.Int b) bs) ]
  | Eff_types.Val_list vs -> c "list" [ J.Array (List.map json_val vs) ]
  | Eff_types.Val_pair (a, b) -> c "pair" [ json_val a; json_val b ]
  | Eff_types.Val_none -> c "none" []
  | Eff_types.Val_some a -> c "some" [ json_val a ]
  | Eff_types.Val_ctor (k, vs) -> c "ctor" [ J.Int k; J.Array (List.map json_val vs) ]
  | Eff_types.Val_ref (k, path) -> c "ref" [ J.Int k; J.Array (List.map (fun i -> J.Int i) path) ]
  | Eff_types.Val_handle (kind, k) -> c "handle" [ J.Int kind; J.Int k ]
  | Eff_types.Val_negInt n -> c "negInt" [ J.Int n ]
  | Eff_types.Val_float n -> c "float" [ J.Int n ]

let json_exit = function
  | Success v -> J.Array [ J.String "success"; json_val v ]
  | Failure v -> J.Array [ J.String "failure"; json_val v ]

let json_step = function
  | Called (row, request, answer) ->
    J.Object [ ("kind", J.String "call"); ("row", J.Int row); ("request", json_val request); ("answer", json_exit answer) ]
  | Celled (op, arg, answer) ->
    J.Object [ ("kind", J.String "cell"); ("op", J.String op); ("arg", json_val arg); ("answer", json_val answer) ]

let json_stop = function
  | Finished ex -> J.Object [ ("kind", J.String "finished"); ("exit", json_exit ex) ]
  | Cut -> J.Object [ ("kind", J.String "cut") ]
  | Waiting (row, request) -> J.Object [ ("kind", J.String "waiting"); ("row", J.Int row); ("request", json_val request) ]
  | Refused (op, arg) -> J.Object [ ("kind", J.String "refused"); ("op", J.String op); ("arg", json_val arg) ]

(* V2: frame k is cut after a prefix of frame k+1's steps, or is frame k+1. *)
let rec is_prefix a b = match a, b with [], _ -> true | x :: a', y :: b' -> x = y && is_prefix a' b' | _ -> false

let check_grows name frames =
  let rec go = function
    | (k, ((s1, st1), _)) :: ((_, ((s2, st2), _)) :: _ as rest) ->
      let ok = (st1 = Cut && is_prefix s1 s2) || (s1 = s2 && st1 = st2) in
      if not ok then (Printf.printf "FAIL %s: frame %d takes back a step of frame %d\n" name (k + 1) k; exit 1);
      go rest
    | _ -> ()
  in
  go frames;
  Printf.printf "frames grow: %s, %d frames\n" name (List.length frames)

let example name about host_name host start n prog =
  let frames = frames n host prog start in
  check_grows name frames;
  let settled =
    match settle n host prog start with
    | Some (k, ((_, st), _)) -> J.Object [ ("budget", J.Int k); ("stop", json_stop st) ]
    | None -> J.Null
  in
  J.Object
    [ ("name", J.String name); ("about", J.String about); ("host", J.String host_name);
      ("ready", J.Bool (Author.ready prog)); ("program", Eff_json.json_eff prog); ("settled", settled);
      ( "frames",
        J.Array
          (List.map
             (fun (k, ((steps, st), _)) ->
               J.Object [ ("budget", J.Int k); ("steps", J.Array (List.map json_step steps)); ("stop", json_stop st) ])
             frames) ) ]

(* A host as the extracted runner takes it: the answer type's erased argument first, as the
   extraction writes inside Budget_run ("route (fun _ -> cells_host) ..."). *)
let host h = fun _ -> h

let median xs = let a = Array.of_list (List.sort compare xs) in a.(Array.length a / 2)

let cpu f =
  median
    (List.init 5 (fun _ ->
         let t0 = Sys.time () in
         ignore (Sys.opaque_identity (f ()));
         Sys.time () -. t0))

let () =
  let out = Sys.argv.(1) in
  (* List.map runs the examples in order, so the log lists them in order *)
  let examples =
    List.map (fun f -> f ())
    [ (fun () -> example "doubling" "doubles its cursor from 1 while it is below 16, one host call a round" "a tape of 4 replies"
        (host by_tape) ([], units 4) 8 doubling);
      (fun () -> example "doubling, short tape" "the same loop; the tape ends after 3 replies" "a tape of 3 replies"
        (host by_tape) ([], units 3) 8 doubling);
      (fun () -> example "forever" "a loop whose test is always true; it calls nothing" "a tape of no replies"
        (host by_tape) ([], []) 8 forever);
      (fun () -> example "ping" "a loop whose test is always true; one host call a round" "every call answered with unit"
        (host by_unit) ([], ()) 8 ping);
      (fun () -> example "cell counter" "a cell written at each round of a doubling loop, read at the end" "the cells alone"
        (host by_tape) ([], []) 8 cell_counter);
      (fun () -> example "before an edit" "a decision on the literal true: doubling, else ping" "a tape of 4 replies"
        (host by_tape) ([], units 4) 8 before_edit);
      (fun () -> example "after the edit" "the decision removed by when_true_law" "a tape of 4 replies"
        (host by_tape) ([], units 4) 8 after_edit) ]
  in
  (* the long run: ping under a host that always answers, budgets 0 .. n *)
  let n = 1000 in
  let t_frames = cpu (fun () -> frames n (host by_unit) ping ([], ())) in
  let t_one = cpu (fun () -> run_at 100_000 (host by_unit) ping ([], ())) in
  let steps = n * (n + 1) / 2 in
  Printf.printf "frames 0..%d of ping (%d steps in all): %.3f s CPU, %.0f ns a step\n" n steps t_frames
    (t_frames *. 1e9 /. float_of_int steps);
  Printf.printf "one frame at budget 100000 of ping: %.3f s CPU, %.0f ns a step\n" t_one (t_one *. 1e9 /. 100_000.);
  let timing =
    J.Object
      [ ("frames_of_ping", J.Int n); ("steps", J.Int steps); ("seconds", J.String (Printf.sprintf "%.3f" t_frames));
        ("one_frame_budget", J.Int 100_000); ("one_frame_seconds", J.String (Printf.sprintf "%.3f" t_one)) ]
  in
  let oc = open_out out in
  output_string oc (J.render (J.Object [ ("examples", J.Array examples); ("timing", timing) ]));
  close_out oc;
  Printf.printf "wrote %s\n" out
