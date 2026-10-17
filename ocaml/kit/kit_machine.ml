(* Kit_machine — see kit_machine.mli for what it is and the behaviours it holds itself to. *)

open Eff_types
module E4_engine = Effect4_engine.E4_engine
module E4_host = Effect4_engine.E4_host
module E = E4_engine.Fast
module H = E4_host.Make (E4_engine.Fast)
module J = Eff_json_text

type stop =
  | Finished of Kit.exit
  | Waiting of int * val_
  | Refused of int * val_ * Kit.exit
  | Out_of_fuel
  | Out_of_rounds
  | Stopped of string

type 's run = { stop : stop; calls : (int * val_ * Kit.exit) list; state : 's }

(* The engine hands the provider the table's own row record: its position is found by identity,
   so two rows with one name stay apart. *)
let position (rows : row list) (r : row) =
  let rec go i = function [] -> -1 | x :: rest -> if x == r then i else go (i + 1) rest in
  go 0 rows

let run ?(fuel = 10_000_000) ?(rounds = 100_000) (app : Kit.app) (host : 's Kit.host) (st : 's)
    (p : Kit.program) : 's run =
  let rows = app.Kit_gen.rows in
  let provider r v st =
    Option.map (fun (ex, st') -> (Completion_ofExit ex, st')) (host (position rows r) v st)
  in
  let served = H.serve ~table:rows ~rounds provider p ~fuel st in
  let calls =
    List.filter_map
      (fun (c : H.call) ->
        match c.answer with Completion_ofExit ex -> Some (c.row, c.request, ex) | Completion_ofRefGet _ -> None)
      served.calls
  in
  let first_call () = match E.host_calls served.engine with (_, _, i, v) :: _ -> Some (i, v) | [] -> None in
  let stop =
    match served.stop with
    | H.Settled ->
      (match E.answer served.engine with
       | E4_engine.Finished ->
         (match E.root_exit_of served.engine with Some ex -> Finished ex | None -> Stopped "finished with no root exit")
       | E4_engine.Delay _ -> Out_of_fuel
       | E4_engine.Suspended _ -> Stopped "suspended: no host call, a timer or a decision is due"
       | E4_engine.Refused why -> Stopped ("stuck: " ^ why)
       | E4_engine.Outside_profile why -> Stopped ("outside the host profile: " ^ why))
    | H.Declined -> (match first_call () with Some (i, v) -> Waiting (i, v) | None -> Stopped "declined")
    | H.Refused ->
      (match first_call () with
       | Some (i, v) ->
         (match host i v served.state with
          | Some (ex, _) -> Refused (i, v, ex)
          | None -> Waiting (i, v))
       | None -> Stopped "refused")
    | H.Out_of_rounds -> Out_of_rounds
    | H.Raised e -> Stopped ("the host raised " ^ Printexc.to_string e)
    | H.Outside_profile why -> Stopped ("a reply outside the host profile: " ^ why)
    | H.Unknown_row -> Stopped "a call's row is not in the table"
  in
  { stop; calls; state = served.state }

let agree (t : 's Kit.run) (m : 't run) =
  Kit.calls t = m.calls
  &&
  match t.stop, m.stop with
  | Kit.Stop_finished a, Finished b -> a = b
  | Kit.Stop_waiting (i, v), Waiting (j, w) -> i = j && v = w
  | _ -> false

let json ?app (r : 's run) =
  let named i = match app with
    | Some (a : Kit.app) -> (match List.nth_opt a.Kit_gen.rows i with Some (row : row) -> [ ("name", J.String row.name) ] | None -> [])
    | None -> [] in
  let call (i, v, ex) =
    J.Object ((("row", J.Int i) :: named i) @ [ ("request", Kit.Json.value_json v); ("answer", Kit.Json.exit_json ex) ]) in
  let stop = match r.stop with
    | Finished ex -> [ ("status", J.String "finished"); ("exit", Kit.Json.exit_json ex) ]
    | Waiting (i, v) -> [ ("status", J.String "waiting"); ("waiting", J.Object ((("row", J.Int i) :: named i) @ [ ("request", Kit.Json.value_json v) ])) ]
    | Refused (i, v, ex) -> [ ("status", J.String "refused"); ("refused", J.Object ((("row", J.Int i) :: named i) @ [ ("request", Kit.Json.value_json v); ("reply", Kit.Json.exit_json ex) ])) ]
    | Out_of_fuel -> [ ("status", J.String "unsettled"); ("note", J.String "the machine's fuel ended first: a finite probe, not a divergence") ]
    | Out_of_rounds -> [ ("status", J.String "unsettled"); ("note", J.String "the drive's rounds ended first: a finite probe, not a divergence") ]
    | Stopped why -> [ ("status", J.String "stopped"); ("note", J.String why) ] in
  J.Object ((("via", J.String "machine") :: stop) @ [ ("calls", J.Array (List.map call r.calls)) ])
