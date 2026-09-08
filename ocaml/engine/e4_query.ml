(* e4_query.ml — the read-only face of a run.
   INV-TAPE-1(query), the cost model, Q1-Q4 and the two deviations are in e4_query.mli.

   THE THREE THINGS A SOURCE HOLDS, and nothing else: the log and its index (the reading
   axis), the tape as an array (random access to a decision, so `at` is not a list walk),
   and the checkpoint schedule as an array of machines.  There is no mutable field, no
   memo table and no cache: every number this module reports is a function of the source
   as constructed, which is what makes Q3 ("leaves the source unchanged") a fact about the
   type rather than a promise about the code.

   WHY `of_run` REPLAYS THE TAPE ONCE.  A lazy checkpoint would be cheaper to build and it
   was refused: `cost` must be EXACT (bench cell B-Q5b) and Q3 must hold, and both fail the
   moment the answer depends on which positions have already been asked for.  One forward
   pass, every k-th machine retained, and from then on `cost s ~from ~upto` is
   `(from mod k) + (upto - from)` and it is the number of times `s_replay` is actually
   called.  `test_query.ml` checks that equality by counting the calls.

   WHY `by_cid` / `by_occurrence` / `by_path` ARE A LINEAR PASS.  The address is never
   computed here (brief rule 2, trap #1) -- these look for a seal the writer already put in
   the row, as text.  The log's public codec carries no seal today, so there is nothing to
   index: a posting list would be an empty map with a per-row cost.  The functions are total
   and honest instead of absent, they answer [] on a log with no seals, and when the codec
   gains one they become three more `E4_logindex` posting lists behind this signature. *)

type status = { finished : bool; stuck : string option; fuel_left : int }

type ('m, 'd) source = {
  s_log : E4_log.t;
  s_index : E4_logindex.t;
  s_tape : 'd array;
  s_replay : 'm -> 'd -> 'm;
  s_k : int;
  s_ckpt : 'm array;  (** [s_ckpt.(j)] is the machine at position [j * s_k] *)
  s_status : 'm -> status;
}

type frontier = {
  open_scopes : int list;
  awaited : string option;
  fuel_left : int;
}

(* ------------------------------------------------------------------- the constructor *)

let of_run ~log ~index ~tape ~replay ~initial ~checkpoint_every ~status =
  if checkpoint_every < 1 then
    invalid_arg
      (Printf.sprintf "E4_query.of_run: checkpoint_every = %d, must be >= 1" checkpoint_every);
  let n = Array.length tape in
  let k = checkpoint_every in
  let ckpt = Array.make ((n / k) + 1) initial in
  let m = ref initial in
  for i = 0 to n - 1 do
    m := replay !m tape.(i);
    let p = i + 1 in
    if p mod k = 0 then ckpt.(p / k) <- !m
  done;
  { s_log = log; s_index = index; s_tape = tape; s_replay = replay; s_k = k;
    s_ckpt = ckpt; s_status = status }

(* --------------------------------------------------------------- the reading axis *)

let length s = E4_log.length s.s_log
let row s i = E4_log.get s.s_log i
let rows s ~from ~upto = E4_log.slice s.s_log ~from ~upto
let segment_of_decision s d = E4_logindex.segment s.s_index d
let decision_of_row s i = E4_logindex.decision_of s.s_index i

(* ------------------------------------------------------------------- by identity *)

let at_rows s (ixs : int list) : (int * string) list =
  List.filter_map (fun i -> match row s i with None -> None | Some r -> Some (i, r)) ixs

let fiber_rows s f = at_rows s (E4_logindex.by_fiber s.s_index f)
let scope_rows s k = at_rows s (E4_logindex.by_scope s.s_index k)
let token_rows s k = at_rows s (E4_logindex.by_token s.s_index k)
let task_rows s ~owner = at_rows s (E4_logindex.by_task_owner s.s_index owner)
let fibers s = E4_logindex.fibers s.s_index
let scopes s = E4_logindex.scopes s.s_index
let tokens s = E4_logindex.tokens s.s_index

let open_scopes s =
  List.filter
    (fun k ->
       not
         (List.exists
            (fun i ->
               match E4_logindex.by_index s.s_index i with
               | Some e -> e.E4_logindex.kind = E4_logindex.kind_scope_closed_on_link
               | None -> false)
            (E4_logindex.by_scope s.s_index k)))
    (E4_logindex.scopes s.s_index)

(* -------------------------------------------------------------- the three addresses *)

let contains (hay : string) (needle : string) : bool =
  let n = String.length needle and h = String.length hay in
  if n = 0 then true
  else if n > h then false
  else begin
    let c0 = String.unsafe_get needle 0 in
    let rec go i =
      i + n <= h
      && ((String.unsafe_get hay i = c0 && String.sub hay i n = needle) || go (i + 1))
    in
    go 0
  end

let scan s needle =
  List.rev
    (E4_log.fold s.s_log ~init:[] ~f:(fun i r acc ->
         if contains r needle then (i, r) :: acc else acc))

let path_text path = "[" ^ String.concat " " (List.map string_of_int path) ^ "]"
let occurrence_text ~program ~path = program ^ "/" ^ path_text path

let by_cid s ~cid =
  if cid = "" then invalid_arg "E4_query.by_cid: the empty address matches every row";
  scan s cid

let by_occurrence s ~program ~path = scan s (occurrence_text ~program ~path)
let by_path s ~path = scan s (path_text path)

(* -------------------------------------------------------- the tape and the outcome *)

let tape s = Array.to_list s.s_tape
let tape_length s = Array.length s.s_tape
let checkpoint_every s = s.s_k

let checkpoints s =
  List.init (Array.length s.s_ckpt) (fun j -> j * s.s_k)

(* ------------------------------------------------------- the machine at a position *)

let bounds s name i =
  if i < 0 || i > Array.length s.s_tape then
    invalid_arg
      (Printf.sprintf "E4_query.%s: %d outside [0,%d]" name i (Array.length s.s_tape))

let at s i =
  bounds s "at" i;
  let c = i / s.s_k in
  let m = ref s.s_ckpt.(c) in
  for j = c * s.s_k to i - 1 do
    m := s.s_replay !m s.s_tape.(j)
  done;
  !m

let cost s ~from ~upto =
  bounds s "cost" from;
  bounds s "cost" upto;
  if upto < from then
    invalid_arg (Printf.sprintf "E4_query.cost: from %d is above upto %d" from upto);
  (from mod s.s_k) + (upto - from)

let replay_steps s ~from ~upto =
  bounds s "replay_steps" from;
  bounds s "replay_steps" upto;
  if upto < from then
    invalid_arg (Printf.sprintf "E4_query.replay_steps: from %d is above upto %d" from upto);
  let m0 = at s from in
  let rec go i m acc =
    if i >= upto then List.rev (m :: acc)
    else
      let m' = s.s_replay m s.s_tape.(i) in
      go (i + 1) m' (m :: acc)
  in
  go from m0 []

type ('m, 'd) cursor = {
  c_src : ('m, 'd) source;
  c_pos : int;
  c_m : 'm;
}

let cursor s ~from =
  bounds s "cursor" from;
  { c_src = s; c_pos = from; c_m = at s from }

let position c = c.c_pos
let current c = c.c_m

let next c =
  let s = c.c_src in
  if c.c_pos >= Array.length s.s_tape then None
  else
    let m = s.s_replay c.c_m s.s_tape.(c.c_pos) in
    Some (m, { c with c_pos = c.c_pos + 1; c_m = m })

let outcome s =
  let st = s.s_status (at s (Array.length s.s_tape)) in
  match st.stuck with
  | Some why -> `Stuck why
  | None ->
    if st.finished then `Finished
    else
      `Frontier
        { open_scopes = open_scopes s;
          (* INV-TAPE-2: `None` until X2 lands the row (A3 §1.3.4, R-A3-3).  Never a
             guess: the machine's Pending/Observer state can name a token, but the ROW the
             frontier awaits is not in the log and this module does not invent it. *)
          awaited = None;
          fuel_left = st.fuel_left }
