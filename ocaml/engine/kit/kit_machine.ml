(* Kit_machine — see kit_machine.mli for what it is and the behaviours it holds itself to. *)

open Eff_types
module E4_engine = Effect4_engine.E4_engine
module E4_host = Effect4_engine.E4_host
module E = E4_engine.Fast
module H = E4_host.Make (E4_engine.Fast)

type exit = (Val.t, Err.t, Defect.t, int, unit) Exit.t
type completion = (Val.t, Err.t, Defect.t, int, unit) Eff_types.Completion.t

type stop =
  | Finished of exit
  | Waiting of int * Val.t
  | Refused of int * Val.t
  | Out_of_fuel
  | Out_of_rounds
  | Stopped of string

type 's run = { stop : stop; calls : (int * Val.t * exit) list; state : 's }

let run ?(fuel = 10_000_000) ?(rounds = 100_000) (rows : Row.t list) reactor (st : 's) program : 's run =
  match H.serve ~table:rows ~rounds reactor program ~fuel st with
  | Error (H.Load_outside_profile why) ->
    { stop = Stopped ("a program outside the host profile: " ^ why); calls = []; state = st }
  | Ok served ->
    let calls =
      List.filter_map
        (fun (c : H.call) ->
          match c.answer with Completion.OfExit ex -> Some (c.row, c.request, ex) | Completion.OfRefGet _ -> None)
        served.calls
    in
    let first_call () = match E.host_calls served.engine with (_, _, i, v) :: _ -> Some (i, v) | [] -> None in
    let stop =
      match served.stop with
      | H.Machine H.Finished ->
        (match E.root_exit_of served.engine with Some ex -> Finished ex | None -> Stopped "finished with no root exit")
      | H.Machine H.Delay -> Out_of_fuel
      | H.Machine H.Waiting -> Stopped "suspended: no host call, a timer or a decision is due"
      | H.Machine (H.Stuck why) -> Stopped ("stuck: " ^ why)
      | H.Host H.Declined -> (match first_call () with Some (i, v) -> Waiting (i, v) | None -> Stopped "declined")
      | H.Host H.Refused -> (match first_call () with Some (i, v) -> Refused (i, v) | None -> Stopped "refused")
      | H.Host H.Out_of_rounds -> Out_of_rounds
      | H.Host (H.Raised e) -> Stopped ("the host raised " ^ Printexc.to_string e)
      | H.Host (H.Outside_profile why) -> Stopped ("outside the host profile: " ^ why)
      | H.Host H.Unknown_row -> Stopped "a call's row is not in the table"
    in
    { stop; calls; state = served.state }
