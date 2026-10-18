(* Kit — the native kit's face; see kit.mli for what it is and the behaviours it holds itself to. *)

open Eff_types
module G = Effect4_gen.Api_gen

type program = NativeOp.t Eff.t
type exit = (Val.t, Err.t, Defect.t, int, unit) Exit.t
type completion = (Val.t, Err.t, Defect.t, int, unit) Eff_types.Completion.t
type app = G.sig_app

let app ?(rows = []) ?(services = []) () : app = { G.rows; services; types = [] }
let succeed (v : Val.t) : exit = Exit.Success v
let fail (v : Val.t) : exit = Exit.Failure [ Reason.Fail (G.program_err_of v, []) ]
let check (a : app) (p : program) = G.run_kit_check a p
let admit (a : app) (p : program) = G.run_kit_admit a p
let ty_text = G.run_kit_ty_text

type 's reactor = Row.t -> Val.t -> 's -> (completion * 's) option

module Reactor = struct
  let silent : unit reactor = fun _ _ () -> None

  let tape : exit list reactor =
   fun _ _ t -> match t with ex :: rest -> Some (Completion.OfExit ex, rest) | [] -> None

  let by_name named : unit reactor =
   fun (r : Row.t) v () ->
    match List.assoc_opt r.Row.name named with
    | Some f -> Option.map (fun ex -> (Completion.OfExit ex, ())) (f v)
    | None -> None

  let first (rs : 's reactor list) : 's reactor = fun r v st -> List.find_map (fun h -> h r v st) rs

  let counted (h : 's reactor) : ('s * int) reactor =
   fun r v (st, n) -> Option.map (fun (c, st') -> (c, (st', n + 1))) (h r v st)
end

type reply_fault = G.reply_fault =
  | ReplyFault_answerType of Ty.t
  | ReplyFault_errorType of Ty.t
  | ReplyFault_reservedDefect

type stop =
  | Finished of exit
  | Waiting of int * Val.t
  | Refused of int * Val.t * exit * reply_fault option
  | Unsettled
  | Stopped of string

type step = G.step =
  | Step_called of int * Val.t * exit
  | Step_celled of G.sync_op * Val.t

type trace = { steps : step list; stop : stop }

let calls (t : trace) = List.filter_map (function Step_called (i, v, ex) -> Some (i, v, ex) | Step_celled _ -> None) t.steps
let tape_of t = List.map (fun (_, _, ex) -> ex) (calls t)

type 's report = {
  by_tree : bool;
  budget : int option;
  trace : trace;
  state : 's;
  frames : trace list;
  agrees : bool option;
}

let reply_fault (a : app) i ex = G.run_kit_reply_fault a i ex

(* A row's position in the table, found by identity: both runners hand the reactor the table's
   own records (Kit_machine M3). *)
let position (a : app) (row : Row.t) =
  let rec go i = function [] -> None | r :: rest -> if r == row then Some i else go (i + 1) rest in
  go 0 a.G.rows

(* Reply admission (B5): a reply that does not fit its row is no answer, so the call waits. *)
let admitted (a : app) (r : 's reactor) : 's reactor =
 fun row v st ->
  match r row v st, position a row with
  | Some (Completion.OfExit ex, _), Some i when Option.is_some (reply_fault a i ex) -> None
  | answer, _ -> answer

(* Why a call waits: the reactor asked again; a reply that does not fit is named with its
   fault. A refused reply leaves the state as it was, so asking again gives the same reply. *)
let waiting (a : app) (r : 's reactor) st i v =
  match List.nth_opt a.G.rows i with
  | Some row -> (
    match r row v st with
    | Some (Completion.OfExit ex, _) -> (
      match reply_fault a i ex with Some f -> Refused (i, v, ex, Some f) | None -> Waiting (i, v))
    | _ -> Waiting (i, v))
  | None -> Waiting (i, v)

let tree_trace a r st (steps : step list) (stop : G.stop) =
  { steps;
    stop =
      (match stop with
       | G.Stop_finished ex -> Finished ex
       | G.Stop_cut -> Unsettled
       | G.Stop_waiting (i, v) -> waiting a r st i v) }

let machine_trace a r (m : 's Kit_machine.run) =
  { steps = List.map (fun (i, v, ex) -> Step_called (i, v, ex)) m.calls;
    stop =
      (match m.stop with
       | Kit_machine.Finished ex -> Finished ex
       | Kit_machine.Waiting (i, v) -> waiting a r m.state i v
       | Kit_machine.Refused (i, v) -> (
         match List.nth_opt a.G.rows i with
         | Some row -> (
           match r row v m.state with
           | Some (Completion.OfExit ex, _) -> Refused (i, v, ex, None)
           | _ -> Waiting (i, v))
         | None -> Waiting (i, v))
       | Kit_machine.Out_of_fuel | Kit_machine.Out_of_rounds -> Unsettled
       | Kit_machine.Stopped why -> Stopped why) }

(* An exit compares through its value tree, which Lean's `Canonical.ofVal_toVal` makes injective. *)
let equal_exit (a : exit) (b : exit) = Eff_val.equal (G.run_kit_exit_to_val a) (G.run_kit_exit_to_val b)

let equal_call (i, v, a) (j, w, b) = Int.equal i j && Eff_val.equal v w && equal_exit a b

(* Two traces agree when they make the same host calls and stop the same way; a refusal agrees
   with a refusal of the same call, whoever named its fault. *)
let agree (x : trace) (y : trace) =
  List.equal equal_call (calls x) (calls y)
  &&
  match x.stop, y.stop with
  | Finished a, Finished b -> equal_exit a b
  | Waiting (i, v), Waiting (j, w) -> Int.equal i j && Eff_val.equal v w
  | Refused (i, v, _, _), Refused (j, w, _, _) -> Int.equal i j && Eff_val.equal v w
  | _ -> false

let run ?(limit = 1024) ?(frames = false) ?(check = true) (a : app) (r : 's reactor) (st : 's) (p : program) : 's report =
  let rows = a.G.rows in
  let guarded = admitted a r in
  if Option.is_none (G.run_tree_outside_at p) then begin
    let host = G.run_tree_host_of_reactor rows guarded in
    let traces k =
      List.map (fun (o : 's G.effect4_run_tree_outcome) -> tree_trace a r o.state o.steps o.stop) (G.run_tree_frames rows k host st p)
    in
    match G.run_tree_settle rows limit host st p with
    | Some (k, o) ->
      let trace = tree_trace a r o.state o.steps o.stop in
      let agrees = if check then Some (agree trace (machine_trace a r (Kit_machine.run rows guarded st p))) else None in
      { by_tree = true; budget = Some k; trace; state = o.state; frames = (if frames then traces k else []); agrees }
    | None ->
      let o = G.run_tree_probe rows limit host st p in
      { by_tree = true; budget = None; trace = tree_trace a r o.state o.steps o.stop; state = o.state;
        frames = (if frames then traces limit else []); agrees = None }
  end else begin
    let m = Kit_machine.run ~rounds:limit rows guarded st p in
    { by_tree = false; budget = None; trace = machine_trace a r m; state = m.state; frames = []; agrees = None }
  end

let samples (a : app) t = G.run_kit_samples a.G.types 4 t
let replies (a : app) i = G.run_kit_replies a i

let explore (a : app) ~budget ~width p =
  match G.run_tree_outside_at p with
  | Some at -> Error at
  | None ->
    Ok (List.map (fun (path : G.path) ->
        { steps = path.steps;
          stop = (match path.stop with
              | G.Stop_finished ex -> Finished ex
              | G.Stop_cut -> Unsettled
              | G.Stop_waiting (i, v) -> Waiting (i, v)) })
        (G.run_kit_explore a budget width p))

let replays (a : app) p (t : trace) =
  match t.stop with
  | Unsettled -> None
  | _ ->
    let r = admitted a Reactor.tape in
    Some (agree t (machine_trace a Reactor.tape (Kit_machine.run a.G.rows r (tape_of t) p)))

(* The carriers' format version: moved with the pins of engine/test/kit/test_shapes.ml, in one
   commit, whenever a shape of Effect4.Run.Kit changes (the rule is kit.mli's). *)
let format_version = 1

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
             ("text", J.String (Printf.sprintf "Effect<%s, %s>" (ty_text t.EffTy.answer) (ty_text t.EffTy.error))) ])
    | Error r -> J.Object [ ("status", J.String "refused"); ("refusal", refusal_json r) ]

  let row_fields (a : app) i =
    ("row", J.Int i) :: (match List.nth_opt a.G.rows i with Some (r : Row.t) -> [ ("name", J.String r.Row.name) ] | None -> [])

  let call_json a (i, v, ex) = J.Object (row_fields a i @ [ ("request", value_json v); ("answer", exit_json ex) ])

  let fault_json = function
    | Some (ReplyFault_answerType t) -> [ ("fault", J.String "answerType"); ("expected", J.String (ty_text t)) ]
    | Some (ReplyFault_errorType t) -> [ ("fault", J.String "errorType"); ("expected", J.String (ty_text t)) ]
    | Some ReplyFault_reservedDefect -> [ ("fault", J.String "reservedDefect") ]
    | None -> [ ("fault", J.String "refusedByTheEngine") ]

  let stop_json a = function
    | Finished ex -> [ ("status", J.String "finished"); ("exit", exit_json ex) ]
    | Waiting (i, v) -> [ ("status", J.String "waiting"); ("waiting", J.Object (row_fields a i @ [ ("request", value_json v) ])) ]
    | Refused (i, v, ex, f) ->
      [ ("status", J.String "refused");
        ("refused", J.Object (row_fields a i @ [ ("request", value_json v); ("reply", exit_json ex) ] @ fault_json f)) ]
    | Unsettled -> [ ("status", J.String "unsettled"); ("note", J.String "the budget ended first: a finite probe, not a divergence") ]
    | Stopped why -> [ ("status", J.String "stopped"); ("note", J.String why) ]

  let trace_json a (t : trace) =
    J.Object
      (stop_json a t.stop
      @ [ ("calls", J.Array (List.map (call_json a) (calls t)));
          ("tape", J.Array (List.map exit_json (tape_of t))) ])

  let report_json a (r : 's report) =
    J.Object
      ((match r.budget with Some k -> [ ("budget", J.Int k) ] | None -> [])
      @ stop_json a r.trace.stop
      @ [ ("via", J.String (if r.by_tree then "tree" else "machine"));
          ("calls", J.Array (List.map (call_json a) (calls r.trace))) ]
      @ (match r.agrees with Some b -> [ ("machine", J.String (if b then "agrees" else "disagrees")) ] | None -> [])
      @ (if List.is_empty r.frames then []
         else [ ("frames", J.Array (List.mapi (fun k t ->
             match trace_json a t with J.Object fields -> J.Object (("budget", J.Int k) :: fields) | j -> j) r.frames)) ]))
end

let program_of_bytes = Eff_wire.decode_eff_exact
let program_bytes = Eff_wire.encode_eff
