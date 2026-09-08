(* e4_logindex.ml — the indexes over the log, built in the append and never by a rescan.
   The property list X1-X4, the carrier choices and the owed rows are in e4_logindex.mli.

   THE COST PER ROW, stated so the bench cell can be read against it.  One `E4_log.Vec`
   append (a cons, and one array fill per 256 rows), one `Map` insertion for the kind, one
   for the fiber when the row names one, one for the token / scope / task owner when the row
   carries one -- and NOTHING for the decision, whose segment is one insertion per decision.
   So a `frame` or an `exited` row costs two insertions, a `parkedOn` three, and a row that
   names no identity one.  The design's §6.3 cell measured a SINGLE posting map at 14.3 M
   rows/s; this module's floor is that cell, and the lane receipt reports both.

   THE POSTING LISTS ARE HELD DESCENDING and reversed on read.  `add` must stay O(log n) --
   it is on the per-row path -- and appending to the head of a list is the only way to do
   that without a second carrier.  X2 (ascending, duplicate-free) is then a fact about
   `by_*`, and it is guaranteed by the refusal in `add`: an entry whose index is not above
   the last one is an `Invalid_argument`, so a caller cannot build an index whose posting
   lists are out of order. *)

module Im = Map.Make (Int)

(* ------------------------------------------------------------------ the row alphabet *)

(* The `RunEvent` constructor ordinals, api_engine.ml:174-195, as positions in a content
   table (CAS amendment M17).  Append-only. *)
let kind_forked = 0
let kind_started = 1
let kind_scheduled_task = 2
let kind_ran_task = 3
let kind_yield_injected = 4
let kind_parked_on = 5
let kind_resumed_with = 6
let kind_interrupt_recorded = 7
let kind_interrupt_deferred = 8
let kind_children_interrupted = 9
let kind_observer_fired = 10
let kind_frame = 11
let kind_finalizer_program = 12
let kind_scope_linked = 13
let kind_scope_closed_on_link = 14
let kind_race_started = 15
let kind_race_launched = 16
let kind_race_settled = 17
let kind_context_set = 18
let kind_callback = 19
let kind_exited = 20
let kind_unknown = -1
let kind_count = 21

let kind_names =
  [| "forked"; "started"; "scheduledTask"; "ranTask"; "yieldInjected"; "parkedOn";
     "resumedWith"; "interruptRecorded"; "interruptDeferred"; "childrenInterrupted";
     "observerFired"; "frame"; "finalizerProgram"; "scopeLinked"; "scopeClosedOnLink";
     "raceStarted"; "raceLaunched"; "raceSettled"; "contextSet"; "callback"; "exited" |]

let kind_name k =
  if k >= 0 && k < kind_count then kind_names.(k)
  else if k = kind_unknown then "unknown"
  else Printf.sprintf "kind%d" k

let kind_of_name = function
  | "forked" -> kind_forked
  | "started" -> kind_started
  | "scheduledTask" -> kind_scheduled_task
  | "ranTask" -> kind_ran_task
  | "yieldInjected" -> kind_yield_injected
  | "parkedOn" -> kind_parked_on
  | "resumedWith" -> kind_resumed_with
  | "interruptRecorded" -> kind_interrupt_recorded
  | "interruptDeferred" -> kind_interrupt_deferred
  | "childrenInterrupted" -> kind_children_interrupted
  | "observerFired" -> kind_observer_fired
  | "frame" -> kind_frame
  | "finalizerProgram" -> kind_finalizer_program
  | "scopeLinked" -> kind_scope_linked
  | "scopeClosedOnLink" -> kind_scope_closed_on_link
  | "raceStarted" -> kind_race_started
  | "raceLaunched" -> kind_race_launched
  | "raceSettled" -> kind_race_settled
  | "contextSet" -> kind_context_set
  | "callback" -> kind_callback
  | "exited" -> kind_exited
  | _ -> kind_unknown

(* ------------------------------------------------------------------------- the codec *)

type entry = {
  index : int;
  kind : int;
  fiber : int option;
  token : int option;
  scope : int option;
  task_owner : int option;
  decision : int;
}

(* `name(a,b,c)` with the arguments nested by `(`/`[` and by OCaml string literals -- a
   `Val.str` payload prints through `%S` (e4_engine.ml:332) and may hold any delimiter, so
   the quote state is tracked and a backslash escapes the next character inside it. *)
let head_and_args (row : string) : string * string list =
  let n = String.length row in
  let rec find_open i =
    if i >= n then -1 else if String.unsafe_get row i = '(' then i else find_open (i + 1)
  in
  let o = find_open 0 in
  if o < 0 then (row, [])
  else begin
    let name = String.sub row 0 o in
    let buf = Buffer.create 24 in
    let args = ref [] in
    let depth = ref 0 and inq = ref false and esc = ref false in
    let i = ref (o + 1) and fin = ref false in
    while (not !fin) && !i < n do
      let c = String.unsafe_get row !i in
      if !inq then begin
        if !esc then esc := false
        else if c = '\\' then esc := true
        else if c = '"' then inq := false;
        Buffer.add_char buf c
      end
      else
        (match c with
         | '"' ->
           inq := true;
           Buffer.add_char buf c
         | '(' | '[' ->
           incr depth;
           Buffer.add_char buf c
         | ']' ->
           decr depth;
           Buffer.add_char buf c
         | ')' ->
           if !depth = 0 then begin
             args := Buffer.contents buf :: !args;
             fin := true
           end
           else begin
             decr depth;
             Buffer.add_char buf c
           end
         | ',' when !depth = 0 ->
           args := Buffer.contents buf :: !args;
           Buffer.clear buf
         | _ -> Buffer.add_char buf c);
      incr i
    done;
    if not !fin then args := Buffer.contents buf :: !args;
    (name, List.rev !args)
  end

let arg_int (args : string list) (k : int) : int option =
  match List.nth_opt args k with
  | None -> None
  | Some s -> int_of_string_opt (String.trim s)

let parse_run_event_row ~(decision : int) (index : int) (row : E4_log.row) : entry =
  let name, args = head_and_args row in
  let kind = kind_of_name name in
  let a k = arg_int args k in
  let none = { index; kind; fiber = None; token = None; scope = None; task_owner = None;
               decision }
  in
  if kind = kind_unknown then none
  else if kind = kind_scheduled_task || kind = kind_ran_task then
    { none with fiber = a 0; task_owner = a 0 }
  else if kind = kind_parked_on || kind = kind_resumed_with then
    { none with fiber = a 0; token = a 1 }
  else if kind = kind_interrupt_recorded then { none with fiber = a 1 }
    (* `interruptRecorded(who,target)`: `who` may be `-`; the row is ABOUT the target
       (Fibers.lean:358). *)
  else if kind = kind_scope_linked then { none with scope = a 1; fiber = a 3 }
    (* `scopeLinked(mode,scope,key,fiber)` -- Fibers.lean:369. *)
  else if kind = kind_scope_closed_on_link then { none with scope = a 0; fiber = a 1 }
  else if kind = kind_race_started || kind = kind_race_launched then { none with fiber = a 1 }
  else if kind = kind_race_settled || kind = kind_callback then none
  else { none with fiber = a 0 }

(* ------------------------------------------------------------------------- the index *)

(* THE SEGMENTS ARE A VECTOR, NOT A MAP, and the in-flight one is three ints beside it.
   A `Map` insertion per row cost more than everything else in `add` put together: the
   decision key is dense and monotone like the row index, and at one decision per handful of
   rows a 1e6-row log has ~1.4e5 decisions, so a per-row `Im.add` walks a depth-17 tree a
   million times.  Segments arrive in ascending decision order, so they append to an
   `E4_log.Vec` -- one append per DECISION, not per row -- and `segment` is a binary search
   over it.  Measured: this alone took the 1e6-row build from 416 ms to the number in the
   lane receipt's bench table. *)
type t = {
  entries : entry E4_log.Vec.t;
  fib : int list Im.t;
  knd : int list Im.t;
  tok : int list Im.t;
  scp : int list Im.t;
  own : int list Im.t;
  segs : (int * int * int) E4_log.Vec.t;  (** closed segments: (decision, from, upto) *)
  cur_dec : int;  (** the in-flight segment; [no_decision] when the index is empty *)
  cur_from : int;
  cur_upto : int;
  last_index : int;
}

let no_decision = min_int

let empty =
  { entries = E4_log.Vec.empty; fib = Im.empty; knd = Im.empty; tok = Im.empty;
    scp = Im.empty; own = Im.empty; segs = E4_log.Vec.empty; cur_dec = no_decision;
    cur_from = 0; cur_upto = 0; last_index = -1 }

let push m k v =
  Im.add k (v :: (match Im.find_opt k m with None -> [] | Some l -> l)) m

let push_opt m k v = match k with None -> m | Some k -> push m k v

let add t e =
  if e.index <= t.last_index then
    invalid_arg
      (Printf.sprintf "E4_logindex.add: index %d is not above the last index %d (X2)" e.index
         t.last_index);
  if t.cur_dec <> no_decision && e.decision < t.cur_dec then
    invalid_arg
      (Printf.sprintf "E4_logindex.add: decision %d is below the last decision %d" e.decision
         t.cur_dec);
  let segs, cur_dec, cur_from =
    if e.decision = t.cur_dec then (t.segs, t.cur_dec, t.cur_from)
    else
      ( (if t.cur_dec = no_decision then t.segs
         else E4_log.Vec.append t.segs (t.cur_dec, t.cur_from, t.cur_upto)),
        e.decision,
        e.index )
  in
  { entries = E4_log.Vec.append t.entries e;
    knd = push t.knd e.kind e.index;
    fib = push_opt t.fib e.fiber e.index;
    tok = push_opt t.tok e.token e.index;
    scp = push_opt t.scp e.scope e.index;
    own = push_opt t.own e.task_owner e.index;
    segs;
    cur_dec;
    cur_from;
    cur_upto = e.index + 1;
    last_index = e.index }

let of_log (l : E4_log.t) ~(parse : int -> E4_log.row -> entry) : t =
  E4_log.fold l ~init:empty ~f:(fun i row acc -> add acc (parse i row))

let count t = E4_log.Vec.length t.entries
let by_index t i = E4_log.Vec.get t.entries i
let posting m k = match Im.find_opt k m with None -> [] | Some l -> List.rev l
let by_fiber t f = posting t.fib f
let by_kind t k = posting t.knd k
let by_token t k = posting t.tok k
let by_scope t k = posting t.scp k
let by_task_owner t k = posting t.own k

(* the closed segments are ascending in the decision, so a binary search answers in
   O(log (decisions) * log (decisions / 256)) and no map is kept *)
let segment t d =
  if t.cur_dec <> no_decision && d = t.cur_dec then Some (t.cur_from, t.cur_upto)
  else begin
    let n = E4_log.Vec.length t.segs in
    let rec go lo hi =
      if lo > hi then None
      else
        let mid = (lo + hi) / 2 in
        let dm, a, z = E4_log.Vec.get_exn t.segs mid in
        if dm = d then Some (a, z) else if dm < d then go (mid + 1) hi else go lo (mid - 1)
    in
    go 0 (n - 1)
  end

let by_decision t d =
  match segment t d with
  | None -> []
  | Some (from, upto) -> List.init (upto - from) (fun i -> from + i)

let keys m = List.map fst (Im.bindings m)
let fibers t = keys t.fib
let tokens t = keys t.tok
let scopes t = keys t.scp
let kinds t = keys t.knd
let task_owners t = keys t.own

let decisions t =
  E4_log.Vec.length t.segs + if t.cur_dec = no_decision then 0 else 1

let decision_keys t =
  let closed =
    List.rev (E4_log.Vec.fold t.segs ~init:[] ~f:(fun _ (d, _, _) acc -> d :: acc))
  in
  if t.cur_dec = no_decision then closed else closed @ [ t.cur_dec ]
let decision_of t i = match by_index t i with None -> None | Some e -> Some e.decision
