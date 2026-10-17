(* Kit — the native kit's face; see kit.mli for what it is and the behaviours it holds itself to. *)

open Eff_types
module G = Kit_gen

type program = native_op eff
type exit = (val_, err, defect, int, unit) exit_
type app = G.sig_app

let app ?(rows = []) ?(services = []) () : app = { G.rows; services; types = [] }

let succeed (v : val_) : exit = Exit_success v
let fail (v : val_) : exit = Exit_failure [ Reason_fail (G.program_err_of v, []) ]

let check (a : app) (p : program) = G.run_kit_check a p
let admit (a : app) (p : program) = G.run_kit_admit a p
let ty_text = G.run_kit_ty_text
let outside = G.run_tree_outside_at

type reply_fault = G.reply_fault =
  | ReplyFault_answerType of ty
  | ReplyFault_errorType of ty
  | ReplyFault_reservedDefect

let reply_fault (a : app) i ex = G.run_kit_reply_fault a i ex

type 's host = int -> val_ -> 's -> (exit * 's) option

module Host = struct
  let silent : unit host = fun _ _ () -> None

  (* The lowered `Host.tape` keeps only the state its body reads. *)
  let tape : exit list host = fun _ _ t -> G.run_tree_host_tape t

  let pure f : unit host = fun i v () -> Option.map (fun ex -> (ex, ())) (f i v)

  let rows (a : app) named : unit host =
    let by_index = List.mapi (fun i (r : row) -> (i, List.assoc_opt r.name named)) a.G.rows in
    fun i v () ->
      match List.assoc_opt i by_index with
      | Some (Some f) -> Option.map (fun ex -> (ex, ())) (f v)
      | _ -> None

  let first (hosts : 's host list) : 's host =
   fun i v st -> List.find_map (fun h -> h i v st) hosts

  let counted (h : 's host) : ('s * int) host =
   fun i v (st, n) -> Option.map (fun (ex, st') -> (ex, (st', n + 1))) (h i v st)

  let guarded (a : app) (h : 's host) : 's host =
   fun i v st ->
    match h i v st with
    | Some (ex, _) as answer when Option.is_none (reply_fault a i ex) -> answer
    | _ -> None
end

type stop = G.stop =
  | Stop_finished of exit
  | Stop_cut
  | Stop_waiting of int * val_

type step = G.step =
  | Step_called of int * val_ * exit
  | Step_celled of G.sync_op * val_

type 's run = 's G.outcome = {
  steps : step list;
  stop : stop;
  stores : G.stores;
  state : 's;
}

let probe (a : app) ~budget host st p = G.run_tree_probe a.G.rows budget host st p

type 's settled =
  | Settled of { budget : int; run : 's run }
  | Unsettled of { limit : int; last : 's run }

let settle ?(limit = 1024) (a : app) host st p =
  match G.run_tree_settle a.G.rows limit host st p with
  | Some (budget, run) -> Settled { budget; run }
  | None -> Unsettled { limit; last = probe a ~budget:limit host st p }

let frames (a : app) ~limit host st p = G.run_tree_frames a.G.rows limit host st p

let calls (r : 's run) =
  List.filter_map (function Step_called (i, v, ex) -> Some (i, v, ex) | Step_celled _ -> None) r.steps

type wait = No_answer | Refused of exit * reply_fault

let wait_reason (a : app) (h : 's host) (r : 's run) =
  match r.stop with
  | Stop_waiting (i, v) ->
    (match h i v r.state with
     | None -> Some No_answer
     | Some (ex, _) ->
       (match reply_fault a i ex with Some f -> Some (Refused (ex, f)) | None -> Some No_answer))
  | _ -> None

module Json = struct
  module J = Eff_json_text

  type t = J.t

  let parse = Kit_json.parse
  let render = Kit_json.render
  let of_doc doc ofv j = Option.bind (Kit_json.read doc j) ofv
  let program j = of_doc G.run_kit_program_shape G.run_kit_program_of_val j
  let program_json p = Kit_json.print G.run_kit_program_shape (G.run_kit_program_to_val p)
  let rows j = of_doc G.run_kit_rows_shape G.run_kit_rows_of_val j
  let rows_json rows = Kit_json.print G.run_kit_rows_shape (G.run_kit_rows_to_val rows)
  let services j = of_doc G.run_kit_services_shape G.run_kit_services_of_val j

  let exits (j : t) =
    match j with
    | J.Array js ->
      List.fold_right
        (fun j acc ->
          Option.bind acc (fun xs ->
              Option.map (fun x -> x :: xs) (of_doc G.run_kit_exit_shape G.run_kit_exit_of_val j)))
        js (Some [])
    | _ -> None

  let exit_json ex = Kit_json.print G.run_kit_exit_shape (G.run_kit_exit_to_val ex)
  let value_json v = Kit_json.print G.run_kit_val_shape v
  let ty_json t = Kit_json.print G.run_kit_ty_shape (G.run_kit_ty_to_val t)
  let eff_ty_json t = Kit_json.print G.run_kit_eff_ty_shape (G.run_kit_eff_ty_to_val t)
  let refusal_json r = Kit_json.print G.run_kit_refusal_shape (G.run_kit_refusal_to_val r)

  let admit_json r = Kit_json.print G.run_kit_admit_shape (G.run_kit_admit_to_val r)

  let check_json a p =
    match check a p with
    | Ok t ->
      (match admit a p with
       | Some why -> J.Object [ ("status", J.String "refused"); ("admission", admit_json why) ]
       | None ->
         J.Object
           [ ("status", J.String "ok");
             ("type", eff_ty_json t);
             ("text", J.String (Printf.sprintf "Effect<%s, %s>" (ty_text t.answer) (ty_text t.error))) ])
    | Error r -> J.Object [ ("status", J.String "refused"); ("refusal", refusal_json r) ]

  let row_fields app i =
    let name = match app with
      | Some (a : app) -> (match List.nth_opt a.G.rows i with Some (r : row) -> [ ("name", J.String r.name) ] | None -> [])
      | None -> [] in
    ("row", J.Int i) :: name

  let call_json app (i, v, ex) =
    J.Object (row_fields app i @ [ ("request", value_json v); ("answer", exit_json ex) ])

  let stop_json app = function
    | Stop_finished ex -> [ ("status", J.String "finished"); ("exit", exit_json ex) ]
    | Stop_cut -> [ ("status", J.String "cut") ]
    | Stop_waiting (i, v) ->
      [ ("status", J.String "waiting"); ("waiting", J.Object (row_fields app i @ [ ("request", value_json v) ])) ]

  let run_json ?app ?budget (r : 's run) =
    J.Object
      ((match budget with Some k -> [ ("budget", J.Int k) ] | None -> [])
      @ stop_json app r.stop
      @ [ ("calls", J.Array (List.map (call_json app) (calls r))); ("steps", J.Int (List.length r.steps)) ])

  let settled_json ?app = function
    | Settled { budget; run } -> run_json ?app ~budget run
    | Unsettled { limit; last } ->
      J.Object
        [ ("status", J.String "unsettled");
          ("limit", J.Int limit);
          ("note", J.String "cut at every budget up to the limit: a finite probe, not a divergence");
          ("calls", J.Array (List.map (call_json app) (calls last)));
          ("steps", J.Int (List.length last.steps)) ]

  let wait_json ?app:_ = function
    | No_answer -> J.Object [ ("reason", J.String "noAnswer") ]
    | Refused (ex, f) ->
      let fault = match f with
        | ReplyFault_answerType t -> [ ("fault", J.String "answerType"); ("expected", J.String (ty_text t)) ]
        | ReplyFault_errorType t -> [ ("fault", J.String "errorType"); ("expected", J.String (ty_text t)) ]
        | ReplyFault_reservedDefect -> [ ("fault", J.String "reservedDefect") ] in
      J.Object (("reason", J.String "refused") :: ("reply", exit_json ex) :: fault)
end

let program_of_bytes = Eff_wire.decode_eff_exact
let program_bytes = Eff_wire.encode_eff
