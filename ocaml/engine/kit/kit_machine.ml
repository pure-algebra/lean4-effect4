(* Kit_machine — see kit_machine.mli for what it is and the behaviours it holds itself to. *)

open Eff_types
module E4_engine = Effect4_engine.E4_engine
module E4_host = Effect4_engine.E4_host
module E = E4_engine.Fast
module H = E4_host.Make (E4_engine.Fast)

type exit = (val_, err, defect, int, unit) exit_
type completion = (val_, err, defect, int, unit) Eff_types.completion

type stop =
  | Finished of exit
  | Waiting of int * val_
  | Refused of int * val_
  | Out_of_fuel
  | Out_of_rounds
  | Stopped of string

type 's run = { stop : stop; calls : (int * val_ * exit) list; state : 's }

let run ?(fuel = 10_000_000) ?(rounds = 100_000) (rows : row list) reactor (st : 's) program : 's run =
  let served = H.serve ~table:rows ~rounds reactor program ~fuel st in
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
    | H.Refused -> (match first_call () with Some (i, v) -> Refused (i, v) | None -> Stopped "refused")
    | H.Out_of_rounds -> Out_of_rounds
    | H.Raised e -> Stopped ("the host raised " ^ Printexc.to_string e)
    | H.Outside_profile why -> Stopped ("a reply outside the host profile: " ^ why)
    | H.Unknown_row -> Stopped "a call's row is not in the table"
  in
  { stop; calls; state = served.state }
