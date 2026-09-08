(* E4_diff -- see e4_diff.mli. *)

type decision =
  | Evaluate of int
  | Flush
  | Fire of int
  | Yield_verdict of int * bool
  | Answer_async of int * int * int
  | Interrupt_from of int option * int
  | Install_middleware

let show_decision (d : decision) : string =
  match d with
  | Evaluate i -> Printf.sprintf "evaluate %d" i
  | Flush -> "flush"
  | Fire i -> Printf.sprintf "fire %d" i
  | Yield_verdict (i, b) -> Printf.sprintf "yieldVerdict %d %b" i b
  | Answer_async (f, t, n) -> Printf.sprintf "answerAsync %d %d %d" f t n
  | Interrupt_from (w, t) ->
    Printf.sprintf "interruptFrom %s %d" (match w with None -> "-" | Some i -> string_of_int i) t
  | Install_middleware -> "installMiddleware"

let show_tape (ds : decision list) : string =
  "[" ^ String.concat "; " (List.map show_decision ds) ^ "]"

let drive_tape : decision list = [ Evaluate 0; Flush ]

(* ==================================================================== the projection *)

type projection = {
  p1_outcome : string;
  p2_stuck : string option;
  p3_settled : bool;
  p4_answer : string;
  p5_fiber_count : int;
  p6_fiber_ids : int list;
  p7_exits : (int * string) list;
  p8_root_exit : string option;
  p9_fiber_rows : (int * string) list;
  p10_armed : string;
  p11_trace_length : int;
  p12_trace_rows : string list;
  p13_store_row : string;
}

type divergence = {
  d_field : string;
  d_index : int option;
  d_left : string;
  d_right : string;
}

let show_divergence (d : divergence) : string =
  Printf.sprintf "%s%s\n      left  = %s\n      right = %s" d.d_field
    (match d.d_index with None -> "" | Some i -> Printf.sprintf " [%d]" i)
    d.d_left d.d_right

(* -------- the field comparators; each answers [] or exactly one divergence -------- *)

let one field l r = [ { d_field = field; d_index = None; d_left = l; d_right = r } ]

let cmp_str field (a : string) (b : string) : divergence list =
  if a = b then [] else one field a b

let cmp_int field (a : int) (b : int) : divergence list =
  if a = b then [] else one field (string_of_int a) (string_of_int b)

let cmp_bool field (a : bool) (b : bool) : divergence list =
  if a = b then [] else one field (string_of_bool a) (string_of_bool b)

let cmp_opt field (a : string option) (b : string option) : divergence list =
  let s = function None -> "<none>" | Some x -> x in
  if a = b then [] else one field (s a) (s b)

(* A list field: the first index at which the two disagree, or the lengths when one side
   runs out first.  This is the position D2 promises. *)
let cmp_list field (show : 'a -> string) (a : 'a list) (b : 'a list) : divergence list =
  let rec go i xs ys =
    match xs, ys with
    | [], [] -> []
    | [], _ ->
      [ { d_field = field; d_index = Some i; d_left = "<end of list>"; d_right = show (List.hd ys) } ]
    | _, [] ->
      [ { d_field = field; d_index = Some i; d_left = show (List.hd xs); d_right = "<end of list>" } ]
    | x :: xs', y :: ys' ->
      if x = y then go (i + 1) xs' ys'
      else [ { d_field = field; d_index = Some i; d_left = show x; d_right = show y } ]
  in
  let d = go 0 a b in
  if d = [] && List.length a <> List.length b then
    one field
      (Printf.sprintf "<length %d>" (List.length a))
      (Printf.sprintf "<length %d>" (List.length b))
  else d

let show_id_row (i, s) = Printf.sprintf "%d: %s" i s

let compare (a : projection) (b : projection) : divergence list =
  List.concat
    [ cmp_str "p1_outcome" a.p1_outcome b.p1_outcome;
      cmp_opt "p2_stuck" a.p2_stuck b.p2_stuck;
      cmp_bool "p3_settled" a.p3_settled b.p3_settled;
      cmp_str "p4_answer" a.p4_answer b.p4_answer;
      cmp_int "p5_fiber_count" a.p5_fiber_count b.p5_fiber_count;
      cmp_list "p6_fiber_ids" string_of_int a.p6_fiber_ids b.p6_fiber_ids;
      cmp_list "p7_exits" show_id_row a.p7_exits b.p7_exits;
      cmp_opt "p8_root_exit" a.p8_root_exit b.p8_root_exit;
      cmp_list "p9_fiber_rows" show_id_row a.p9_fiber_rows b.p9_fiber_rows;
      cmp_str "p10_armed" a.p10_armed b.p10_armed;
      cmp_int "p11_trace_length" a.p11_trace_length b.p11_trace_length;
      cmp_list "p12_trace_rows" (fun s -> s) a.p12_trace_rows b.p12_trace_rows;
      cmp_str "p13_store_row" a.p13_store_row b.p13_store_row ]

(* ==================================================================== one engine's side *)

module type SIDE = sig
  val name : string
  val carriers : string

  type t

  val load : Eff_types.eff -> fuel:int -> t
  val step : t -> decision -> t
  val project : t -> projection
  val positions : Eff_types.eff -> fuel:int -> decision list -> projection list
  val gen_tape : Eff_types.eff -> fuel:int -> seed:int -> max_len:int -> decision list
end

(* the armed field of `E4_engine.ENGINE.store_row`, which prints it LAST as `armed=[…]`,
   so the last occurrence of the key is the field and never a `refs=` payload that happens
   to spell it *)
let armed_field (store_row : string) : string =
  let needle = "armed=" in
  let n = String.length needle and l = String.length store_row in
  let rec go i best =
    if i + n > l then best
    else go (i + 1) (if String.sub store_row i n = needle then Some i else best)
  in
  match go 0 None with
  | None -> "<no armed field>"
  | Some i -> String.sub store_row (i + n) (l - i - n)

module Of (E : E4_engine.ENGINE) : SIDE with type t = E.t = struct
  let name = E.name
  let carriers = E.carriers

  type t = E.t

  let decision_of (d : decision) : E.decision =
    match d with
    | Evaluate i -> E.evaluate i
    | Flush -> E.flush
    | Fire i -> E.fire i
    | Yield_verdict (i, b) -> E.yield_verdict i b
    | Answer_async (f, tok, n) -> E.answer_async_success f tok n
    | Interrupt_from (w, t) -> E.interrupt_from w t
    | Install_middleware -> E.install_middleware

  let load (p : Eff_types.eff) ~(fuel : int) : t = E.load p ~fuel
  let step (t : t) (d : decision) : t = E.step t (decision_of d)

  let show_frontier (f : E4_engine.frontier) =
    Printf.sprintf "parked=[%s] armed=[%s] due=%d"
      (String.concat ","
         (List.map (fun (a, b) -> Printf.sprintf "%d:%d" a b) f.E4_engine.parked))
      (String.concat "," (List.map string_of_int f.E4_engine.armed))
      f.E4_engine.due

  let show_answer (a : E4_engine.answer) =
    match a with
    | E4_engine.Finished -> "Finished"
    | E4_engine.Suspended f -> "Suspended " ^ show_frontier f
    | E4_engine.Refused r -> "Refused " ^ r
    | E4_engine.Delay f -> "Delay " ^ show_frontier f

  let project (t : t) : projection =
    let ans = E.answer t in
    let store = E.store_row t in
    { p1_outcome = E.outcome t;
      p2_stuck = (match ans with E4_engine.Refused r -> Some r | _ -> None);
      p3_settled = (match ans with E4_engine.Delay _ -> false | _ -> true);
      p4_answer = show_answer ans;
      p5_fiber_count = E.fiber_count t;
      p6_fiber_ids = List.map fst (E.fiber_rows t);
      p7_exits = E.exits t;
      p8_root_exit = E.root_exit t;
      p9_fiber_rows = E.fiber_rows t;
      p10_armed = armed_field store;
      p11_trace_length = E.trace_length t;
      p12_trace_rows = E.trace_rows t;
      p13_store_row = store }

  let positions (p : Eff_types.eff) ~(fuel : int) (tape : decision list) : projection list =
    let t0 = E.load p ~fuel in
    List.of_seq (Seq.map project (E.replay_steps t0 (List.map decision_of tape)))

  (* -------------------------------------------------------------- admissible tapes *)

  (* the same 48-bit LCG as Corpora's, so a tape and a program come from one family *)
  let gen_tape (p : Eff_types.eff) ~(fuel : int) ~(seed : int) ~(max_len : int)
    : decision list =
    let st = ref ((seed lxor 25214903917) land 0xFFFFFFFFFFFF) in
    let rnd n =
      st := ((!st * 25214903917) + 11) land 0xFFFFFFFFFFFF;
      if n <= 1 then 0 else (!st lsr 17) mod n
    in
    let t = ref (E.load p ~fuel) in
    let acc = ref [] in
    let stop = ref false in
    let i = ref 0 in
    while (not !stop) && !i < max_len do
      incr i;
      let ans = E.answer !t in
      let ids = List.map fst (E.fiber_rows !t) in
      let frontier =
        match ans with
        | E4_engine.Suspended f | E4_engine.Delay f -> Some f
        | _ -> None
      in
      (match ans with E4_engine.Refused _ -> stop := true | _ -> ());
      if not !stop then begin
        let armed = match frontier with Some f -> f.E4_engine.armed | None -> [] in
        let parked = match frontier with Some f -> f.E4_engine.parked | None -> [] in
        (* every candidate names an id this machine has shown (D6) *)
        let cands =
          [ Flush ]
          @ List.map (fun k -> Evaluate k) ids
          @ List.map (fun k -> Fire k) (if armed = [] then ids else armed)
          @ List.concat_map (fun k -> [ Yield_verdict (k, true); Yield_verdict (k, false) ]) ids
          @ List.map (fun (f, tok) -> Answer_async (f, tok, 1 + (!i mod 7))) parked
          @ List.map (fun k -> Interrupt_from (None, k)) ids
          @ List.concat_map
              (fun w -> List.map (fun k -> Interrupt_from (Some w, k)) ids)
              (match ids with [] -> [] | x :: _ -> [ x ])
          @ (if rnd 16 = 0 then [ Install_middleware ] else [])
        in
        match cands with
        | [] -> stop := true
        | _ ->
          let d = List.nth cands (rnd (List.length cands)) in
          acc := d :: !acc;
          t := step !t d
          (* A FINISHED machine does NOT end the tape: `replayEval` keeps consuming
             decisions past the last exit (api_engine.ml:11489-11507) and whether the three
             engines agree about that is part of what is being asked.  Only a stuck machine
             ends it, because from there every engine holds the same value forever and the
             remaining positions would compare nothing. *)
      end
    done;
    List.rev !acc
end
