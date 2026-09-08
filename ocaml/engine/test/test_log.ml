(* test_log.ml -- lane Q3, first half: the persistent log and its incremental indexes.

   The laws, under the names 2026-09-08-engine-a3-queue-query.md §4.1 gives them:

     log-append-only   L1  a row already written never changes, and `length` only grows
     log-dense         L2  `get` is Some on [0, length) and None outside it
     log-order         L3  `to_list` = `slice 0 length` = emission order
     log-persistent    L4  an old `t` still answers the old length and the old rows
     log-frozen        L5  two appends onto one prefix do not see each other; no array a `t`
                           can reach is written after the append that created it
     index-incremental X1  `add (of_log l) e` = `of_log (append l e)`, on every observable
     index-ascending   X2  every posting list is strictly ascending, and `add` REFUSES an
                           entry whose index is not above the last one
     index-total       X3  every row is in `by_index`, and in `by_fiber` iff it names a fiber

   plus the codec (`parse_run_event_row`) against the rows `E4_engine` renders, including
   the two shapes that break a naive splitter -- a nested `resume(1,1,success 7)` argument
   and a `Val.str` payload holding a comma and a paren inside quotes -- and the segment law
   (a decision's rows are contiguous, design-language §1.6).

   Everything here is pure: no engine, no machine, no tape.  The engine's own rows are the
   subject of test_query.ml.

   Run: cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* the same 48-bit LCG the other lanes use, so a corpus is reproducible *)
let seed0 = 20260908

let lcg s =
  let st = ref ((s lxor 25214903917) land 0xFFFFFFFFFFFF) in
  fun n ->
    st := ((!st * 25214903917) + 11) land 0xFFFFFFFFFFFF;
    if n <= 1 then 0 else (!st lsr 17) mod n

(* ============================================================ a corpus of rendered rows *)

(* Every template is a row `E4_engine.ENGINE.trace_rows` can actually print
   (e4_engine.ml:472-505).  Two of them exist to break a naive argument splitter: `ranTask`
   nests a `resume(...)` with its own commas, and the last `exited` carries a `Val.str`
   printed through `%S`, whose payload holds a comma, a paren and an escaped quote. *)
let make_row rnd i =
  let f = rnd 8 and tok = rnd 16 and sc = rnd 5 and n = rnd 100 in
  match i mod 12 with
  | 0 -> Printf.sprintf "started(%d)" f
  | 1 -> Printf.sprintf "parkedOn(%d,%d)" f tok
  | 2 -> Printf.sprintf "resumedWith(%d,%d,success %d)" f tok n
  | 3 -> Printf.sprintf "frame(%d,popped(onSuccess(success %d,<name>)))" f n
  | 4 -> Printf.sprintf "scopeLinked(forkIn,%d,%d,%d)" sc (rnd 9) f
  | 5 -> Printf.sprintf "scopeClosedOnLink(%d,%d)" sc f
  | 6 -> Printf.sprintf "scheduledTask(%d,0,start(%d))" f (rnd 8)
  | 7 -> Printf.sprintf "ranTask(%d,resume(%d,%d,success %d))" f f tok n
  | 8 -> Printf.sprintf "finalizerProgram(%d,<name>,success unit)" f
  | 9 -> Printf.sprintf "interruptRecorded(-,%d)" f
  | 10 -> Printf.sprintf "forked(%d,%d,false)" f (rnd 8)
  | _ -> Printf.sprintf "exited(%d,success %S)" f "a,b(c\"d"

let corpus n =
  let rnd = lcg seed0 in
  Array.init n (fun i -> make_row rnd i)

(* the decision each row falls in: ascending, contiguous, with some decisions empty *)
let decision_of_row_index i = i / 7

(* ==================================================================== L1..L5, the log *)

let log_laws () =
  print_endline "== the log: L1..L5 ==";
  let n = 2_000 in
  let rows = corpus n in
  (* every prefix, kept, so persistence is checked against real older values *)
  let prefixes = Array.make (n + 1) E4_log.empty in
  let l = ref E4_log.empty in
  for i = 0 to n - 1 do
    l := E4_log.append !l rows.(i);
    prefixes.(i + 1) <- !l
  done;
  let full = !l in
  check "log-append-only: length is the number of appends"
    (E4_log.length full = n
    && List.for_all (fun i -> E4_log.length prefixes.(i) = i) (List.init (n + 1) Fun.id));
  check "log-append-only: a row already written never changes, in EVERY later prefix"
    (List.for_all
       (fun i ->
          List.for_all
            (fun j -> E4_log.get prefixes.(j) i = Some rows.(i))
            (List.filter (fun j -> j > i) [ i + 1; i + 2; n / 2; n - 1; n ]))
       (List.init 200 (fun k -> k * (n / 200))));
  check "log-dense: Some inside [0,length), None outside"
    (List.for_all (fun i -> E4_log.get full i = Some rows.(i)) (List.init n Fun.id)
    && E4_log.get full (-1) = None
    && E4_log.get full n = None
    && E4_log.get full (n + 1_000) = None
    && E4_log.get E4_log.empty 0 = None);
  check "log-order: to_list = slice 0 length = emission order"
    (E4_log.to_list full = Array.to_list rows
    && E4_log.slice full ~from:0 ~upto:n = Array.to_list rows);
  check "log-order: slice is the half-open range, clamped"
    (E4_log.slice full ~from:300 ~upto:305
     = [ rows.(300); rows.(301); rows.(302); rows.(303); rows.(304) ]
    && E4_log.slice full ~from:5 ~upto:5 = []
    && E4_log.slice full ~from:9 ~upto:3 = []
    && E4_log.slice full ~from:(-4) ~upto:2 = [ rows.(0); rows.(1) ]
    && E4_log.slice full ~from:(n - 2) ~upto:(n + 50) = [ rows.(n - 2); rows.(n - 1) ]);
  check "log-order: fold visits every row once, ascending"
    (List.rev (E4_log.fold full ~init:[] ~f:(fun i r acc -> (i, r) :: acc))
     = List.mapi (fun i r -> (i, r)) (Array.to_list rows));
  check "log-persistent: every prefix still answers its own length and rows"
    (List.for_all
       (fun j ->
          E4_log.length prefixes.(j) = j
          && E4_log.get prefixes.(j) (j - 1) = (if j = 0 then None else Some rows.(j - 1))
          && E4_log.get prefixes.(j) j = None)
       (List.init (n + 1) Fun.id));
  (* L5: two appends onto ONE prefix, at a chunk boundary and inside a chunk.  If any array
     were written after its append, one branch would see the other's row. *)
  let frozen_at p =
    let base = prefixes.(p) in
    let a = E4_log.append base "A" and b = E4_log.append base "B" in
    E4_log.get a p = Some "A"
    && E4_log.get b p = Some "B"
    && E4_log.get base p = None
    && E4_log.length base = p
    && E4_log.get a (p - 1) = E4_log.get b (p - 1)
  in
  check "log-frozen: sibling appends onto one prefix do not see each other"
    (List.for_all frozen_at
       [ 1; 2; E4_log.chunk_size - 1; E4_log.chunk_size; E4_log.chunk_size + 1;
         2 * E4_log.chunk_size; (7 * E4_log.chunk_size) - 1; n - 1; n ]);
  check "log-frozen: a full chunk's rows survive 1 000 further appends onto a sibling"
    (let base = prefixes.(E4_log.chunk_size) in
     let grown = ref base in
     for i = 0 to 999 do
       grown := E4_log.append !grown (Printf.sprintf "junk%d" i)
     done;
     E4_log.length base = E4_log.chunk_size
     && E4_log.to_list base
        = Array.to_list (Array.sub rows 0 E4_log.chunk_size));
  check "log: of_list / to_list / append_all agree"
    (E4_log.to_list (E4_log.of_list (Array.to_list rows)) = Array.to_list rows
    && E4_log.to_list (E4_log.append_all E4_log.empty (Array.to_list rows))
       = Array.to_list rows
    && E4_log.length (E4_log.of_list []) = 0);
  check "log: chunk_size is the named constant 256, and it is not max_int"
    (E4_log.chunk_size = 256)

(* ================================================================== the codec *)

let codec () =
  print_endline "";
  print_endline "== the codec: parse_run_event_row over the rendered rows ==";
  let p row = E4_logindex.parse_run_event_row ~decision:3 0 row in
  let e = p "started(5)" in
  check "codec: started(5) -> kind 1, fiber 5"
    (e.E4_logindex.kind = E4_logindex.kind_started
    && e.E4_logindex.fiber = Some 5
    && e.E4_logindex.token = None
    && e.E4_logindex.decision = 3);
  let e = p "parkedOn(2,9)" in
  check "codec: parkedOn(2,9) -> fiber 2, token 9"
    (e.E4_logindex.kind = E4_logindex.kind_parked_on
    && e.E4_logindex.fiber = Some 2
    && e.E4_logindex.token = Some 9);
  let e = p "scopeLinked(forkIn,7,4,1)" in
  check "codec: scopeLinked(mode,scope,key,fiber) -> scope 7, fiber 1 (Fibers.lean:369)"
    (e.E4_logindex.kind = E4_logindex.kind_scope_linked
    && e.E4_logindex.scope = Some 7
    && e.E4_logindex.fiber = Some 1);
  let e = p "scopeClosedOnLink(7,1)" in
  check "codec: scopeClosedOnLink(scope,fiber) -> scope 7, fiber 1"
    (e.E4_logindex.scope = Some 7 && e.E4_logindex.fiber = Some 1);
  let e = p "ranTask(3,resume(3,8,success 7))" in
  check "codec: a NESTED argument does not fool the splitter"
    (e.E4_logindex.kind = E4_logindex.kind_ran_task
    && e.E4_logindex.fiber = Some 3
    && e.E4_logindex.task_owner = Some 3);
  let e = p "exited(4,success \"a,b(c\\\"d\")" in
  check "codec: a quoted Val.str holding a comma, a paren and an escaped quote"
    (e.E4_logindex.kind = E4_logindex.kind_exited && e.E4_logindex.fiber = Some 4);
  let e = p "interruptRecorded(-,6)" in
  check "codec: interruptRecorded(-,target) -> the TARGET, and `-` is not an int"
    (e.E4_logindex.kind = E4_logindex.kind_interrupt_recorded
    && e.E4_logindex.fiber = Some 6);
  let e = p "finalizerProgram(2,<name>,success unit)" in
  check "codec: finalizerProgram carries NO scope key (owed to X2, A3 §1.3.4)"
    (e.E4_logindex.kind = E4_logindex.kind_finalizer_program
    && e.E4_logindex.fiber = Some 2
    && e.E4_logindex.scope = None);
  let e = p "somethingElse(1,2)" in
  check "codec: an unrecognised head is kind_unknown with no identity, never a guess"
    (e.E4_logindex.kind = E4_logindex.kind_unknown
    && e.E4_logindex.fiber = None
    && e.E4_logindex.token = None
    && e.E4_logindex.scope = None
    && e.E4_logindex.task_owner = None);
  check "codec: the 21 ordinals are the content table's own order, and kind_count = 21"
    (E4_logindex.kind_forked = 0
    && E4_logindex.kind_started = 1
    && E4_logindex.kind_scheduled_task = 2
    && E4_logindex.kind_ran_task = 3
    && E4_logindex.kind_yield_injected = 4
    && E4_logindex.kind_parked_on = 5
    && E4_logindex.kind_resumed_with = 6
    && E4_logindex.kind_interrupt_recorded = 7
    && E4_logindex.kind_interrupt_deferred = 8
    && E4_logindex.kind_children_interrupted = 9
    && E4_logindex.kind_observer_fired = 10
    && E4_logindex.kind_frame = 11
    && E4_logindex.kind_finalizer_program = 12
    && E4_logindex.kind_scope_linked = 13
    && E4_logindex.kind_scope_closed_on_link = 14
    && E4_logindex.kind_race_started = 15
    && E4_logindex.kind_race_launched = 16
    && E4_logindex.kind_race_settled = 17
    && E4_logindex.kind_context_set = 18
    && E4_logindex.kind_callback = 19
    && E4_logindex.kind_exited = 20
    && E4_logindex.kind_count = 21
    && E4_logindex.kind_unknown = -1
    && E4_logindex.kind_name 13 = "scopeLinked")

(* ============================================================== X1..X3, the indexes *)

let parse_at i r = E4_logindex.parse_run_event_row ~decision:(decision_of_row_index i) i r

(* every observable of an index, as one string: what X1's equality is checked on *)
let digest (t : E4_logindex.t) : string =
  let b = Buffer.create 4096 in
  Printf.bprintf b "count=%d decisions=%d\n" (E4_logindex.count t) (E4_logindex.decisions t);
  for i = 0 to E4_logindex.count t - 1 do
    match E4_logindex.by_index t i with
    | None -> Buffer.add_string b "MISSING\n"
    | Some e ->
      let o = function None -> "-" | Some v -> string_of_int v in
      Printf.bprintf b "%d %d %s %s %s %s %d\n" e.E4_logindex.index e.E4_logindex.kind
        (o e.E4_logindex.fiber) (o e.E4_logindex.token) (o e.E4_logindex.scope)
        (o e.E4_logindex.task_owner) e.E4_logindex.decision
  done;
  let list name f keys =
    List.iter
      (fun k ->
         Printf.bprintf b "%s %d [%s]\n" name k
           (String.concat "," (List.map string_of_int (f t k))))
      keys
  in
  list "fiber" E4_logindex.by_fiber (E4_logindex.fibers t);
  list "token" E4_logindex.by_token (E4_logindex.tokens t);
  list "scope" E4_logindex.by_scope (E4_logindex.scopes t);
  list "owner" E4_logindex.by_task_owner (E4_logindex.task_owners t);
  list "kind" E4_logindex.by_kind (E4_logindex.kinds t);
  list "decision" E4_logindex.by_decision (E4_logindex.decision_keys t);
  List.iter
    (fun d ->
       match E4_logindex.segment t d with
       | None -> ()
       | Some (a, z) -> Printf.bprintf b "seg %d %d %d\n" d a z)
    (E4_logindex.decision_keys t);
  Buffer.contents b

let ascending l =
  let rec go = function a :: (b :: _ as r) -> a < b && go r | _ -> true in
  go l

let index_laws () =
  print_endline "";
  print_endline "== the indexes: X1..X3 ==";
  let n = 1_500 in
  let rows = corpus n in
  let log = E4_log.of_list (Array.to_list rows) in
  let idx = E4_logindex.of_log log ~parse:parse_at in
  check "index: of_log covers every row (count = length)"
    (E4_logindex.count idx = n && n = E4_log.length log);
  (* X1: incremental = built-from-the-whole, at EVERY prefix length that matters *)
  let incremental_ok =
    List.for_all
      (fun j ->
         let l_j = E4_log.of_list (Array.to_list (Array.sub rows 0 j)) in
         let i_j = E4_logindex.of_log l_j ~parse:parse_at in
         let l_j1 = E4_log.append l_j rows.(j) in
         digest (E4_logindex.add i_j (parse_at j rows.(j)))
         = digest (E4_logindex.of_log l_j1 ~parse:parse_at))
      [ 0; 1; 2; 7; 13; 255; 256; 257; 512; 999; n - 1 ]
  in
  check "index-incremental (X1): add (of_log l) e = of_log (append l e), every observable"
    incremental_ok;
  let posting_ok =
    List.for_all (fun f -> ascending (E4_logindex.by_fiber idx f)) (E4_logindex.fibers idx)
    && List.for_all (fun k -> ascending (E4_logindex.by_token idx k)) (E4_logindex.tokens idx)
    && List.for_all (fun k -> ascending (E4_logindex.by_scope idx k)) (E4_logindex.scopes idx)
    && List.for_all
         (fun k -> ascending (E4_logindex.by_task_owner idx k))
         (E4_logindex.task_owners idx)
    && List.for_all (fun k -> ascending (E4_logindex.by_kind idx k)) (E4_logindex.kinds idx)
    && List.for_all
         (fun d -> ascending (E4_logindex.by_decision idx d))
         (E4_logindex.decision_keys idx)
  in
  check "index-ascending (X2): every posting list is strictly ascending, duplicate-free"
    posting_ok;
  check "index-ascending (X2): the key lists themselves are ascending"
    (ascending (E4_logindex.fibers idx)
    && ascending (E4_logindex.tokens idx)
    && ascending (E4_logindex.scopes idx)
    && ascending (E4_logindex.kinds idx)
    && ascending (E4_logindex.decision_keys idx));
  (* X2's teeth: `add` REFUSES a row out of order, so no caller can build a bad index *)
  let refuses f = try (ignore (f () : E4_logindex.t); false) with Invalid_argument _ -> true in
  check "index-ascending (X2): add refuses an index at or below the last one"
    (refuses (fun () -> E4_logindex.add idx (parse_at (n - 1) rows.(n - 1)))
    && refuses (fun () -> E4_logindex.add idx (parse_at 0 rows.(0)))
    && refuses (fun () ->
           E4_logindex.add E4_logindex.empty
             { (parse_at 0 rows.(0)) with E4_logindex.index = -1 }));
  check "index: add refuses a decision below the last one (the segment law)"
    (refuses (fun () ->
         E4_logindex.add idx
           { (parse_at n rows.(0)) with E4_logindex.decision = 0 }));
  (* X3 *)
  let total_ok =
    List.for_all
      (fun i ->
         match E4_logindex.by_index idx i with
         | None -> false
         | Some e ->
           e.E4_logindex.index = i
           && (match e.E4_logindex.fiber with
               | None -> not (List.exists (fun f -> List.mem i (E4_logindex.by_fiber idx f))
                                (E4_logindex.fibers idx))
               | Some f -> List.mem i (E4_logindex.by_fiber idx f))
           && List.mem i (E4_logindex.by_kind idx e.E4_logindex.kind))
      (List.init n Fun.id)
  in
  check "index-total (X3): every row is in by_index and in by_fiber iff it names a fiber"
    total_ok;
  check "index-total (X3): by_index is None outside [0,count)"
    (E4_logindex.by_index idx n = None && E4_logindex.by_index idx (-1) = None);
  (* the segments: contiguous, in order, covering every row exactly once *)
  let segs = List.filter_map (E4_logindex.segment idx) (E4_logindex.decision_keys idx) in
  let cover =
    List.fold_left (fun acc (a, z) -> acc @ List.init (z - a) (fun i -> a + i)) [] segs
  in
  check "index: the decision segments are contiguous and cover every row exactly once"
    (cover = List.init n Fun.id
    && List.for_all (fun (a, z) -> z > a) segs
    && E4_logindex.decisions idx = List.length segs);
  check "index: decision_of is the inverse of segment on its domain"
    (List.for_all
       (fun i ->
          match E4_logindex.decision_of idx i with
          | None -> false
          | Some d -> (
            match E4_logindex.segment idx d with
            | None -> false
            | Some (a, z) -> a <= i && i < z))
       (List.init n Fun.id));
  check "index: a decision that appended nothing has no segment, and that is not a gap"
    (E4_logindex.segment idx 100_000 = None && E4_logindex.by_decision idx 100_000 = [])

let () =
  print_endline
    "== lane Q3a: the persistent log (L1-L5), the codec, and the incremental indexes (X1-X3) ==";
  print_endline "";
  log_laws ();
  codec ();
  index_laws ();
  print_endline "";
  Printf.printf "== %s: %d failure(s) in %d checks ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures !checks;
  exit (if !failures = 0 then 0 else 1)
