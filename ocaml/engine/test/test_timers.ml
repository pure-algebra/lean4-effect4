(* test_timers.ml — the checks of the timer store (lane Q2, 2026-09-08).

   What it checks, and against what:
     P-T1..P-T7  the seven property statements of
                 docs/research/2026-09-08-engine-a3-queue-query.md §2.3, under the test names
                 §4.1 fixes: timers-now-monotone, timers-due-exact, timers-fire-order,
                 timers-cancel, timers-edges, timers-staged-eq-batched, timers-wf.
     the mutation test  §4.1's "let `advance_to` accept a target below `now`" — implemented
                 as a test of the refusal (R1, no clockAdjust): removing the guard in
                 E4_time.advance_to turns `timers-mutation-advance-backwards` red, and with
                 it `timers-now-monotone`.
     the workshop witnesses  the eight `#guard`s executed in workshop/Timer/Timer.lean:606-624
                 (`w1`, `w2`), replayed here against the OCaml carrier: the Lean spike is the
                 oracle for the fire lists, the staged clock and the park token.
     the carrier's own facts  persistence (T7), the canonical form (to_list/of_list), and
                 E4_time's C1-C6.
   Every random case uses a fixed LCG, so a failure is reproducible.
   Exit code 0 iff every check passed. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n
let reseed () = seed := 20260908

let raises f =
  match f () with
  | exception Invalid_argument _ -> true
  | exception _ -> false
  | _ -> false

(* A table of n timers with deadlines uniform in [0, span), waiter = the key. *)
let build n span =
  let rec go t i =
    if i >= n then t
    else
      let t', _ = E4_timers.sleep t (E4_timers.Fin (rand span)) i in
      go t' (i + 1)
  in
  go E4_timers.empty 0

let keys_of l = List.map (fun (k, _, _) -> k) l

(* ============================================================ P-T1 *)

let test_now_monotone () =
  print_endline "-- P-T1 now moves only under advance / pop_due, and never backwards";
  check "timers-now-monotone empty starts at tick 0" (E4_timers.now E4_timers.empty = 0);
  let t = build 200 1000 in
  check "timers-now-monotone registration does not move the clock" (E4_timers.now t = 0);
  (* advance ~by:d puts the clock exactly d ticks on *)
  let t1, _ = E4_timers.advance t ~by:250 in
  check "timers-now-monotone now (advance ~by:d) = now + d" (E4_timers.now t1 = 250);
  let t2, _ = E4_timers.advance t1 ~by:0 in
  check "timers-now-monotone advance ~by:0 is a no-op on the clock" (E4_timers.now t2 = 250);
  let t3, _ = E4_timers.advance_to t2 ~target:900 in
  check "timers-now-monotone advance_to sets the clock at the target" (E4_timers.now t3 = 900);
  (* pop_due stages the clock at the FIRED deadline, never at upto, and never backwards *)
  let ok = ref true in
  let prev = ref 0 in
  let rec drain t =
    match E4_timers.pop_due t ~upto:1000 with
    | None -> t
    | Some ((_, d, _), t') ->
        if E4_timers.now t' <> d then ok := false;
        if E4_timers.now t' < !prev then ok := false;
        prev := E4_timers.now t';
        drain t'
  in
  let drained = drain (build 200 1000) in
  check "timers-now-monotone pop_due stages the clock at the fired deadline, monotonically"
    !ok;
  check "timers-now-monotone the staged drain leaves the clock at the last fired deadline"
    (E4_timers.now drained = !prev && E4_timers.is_empty drained);
  (* the refusals that make the monotonicity true rather than accidental *)
  check "timers-now-monotone advance_to below now is Invalid_argument"
    (raises (fun () -> E4_timers.advance_to t3 ~target:899));
  check "timers-now-monotone advance ~by:(-1) is Invalid_argument"
    (raises (fun () -> E4_timers.advance t3 ~by:(-1)));
  (* E4_time's own C2/C3 *)
  let c = E4_time.advance_to E4_time.start ~target:10 in
  check "C2 E4_time.advance_to below now raises"
    (raises (fun () -> E4_time.advance_to c ~target:9));
  check "C3 advance_by = advance_to (now + by)"
    (E4_time.now (E4_time.advance_by c ~by:7)
    = E4_time.now (E4_time.advance_to c ~target:17));
  check "C2 reaches agrees with what advance_to accepts"
    (E4_time.reaches c 10 && E4_time.reaches c 11
    && (not (E4_time.reaches c 9))
    && not (E4_time.reaches c (E4_time.max_deadline_ms + 1)))

(* ============================================================ P-T2 *)

let test_due_exact () =
  print_endline "-- P-T2 a timer fires only when due, and every due timer fires";
  reseed ();
  let t = build 500 1000 in
  let ok = ref true in
  List.iter
    (fun upto ->
      let f = E4_timers.fired t ~upto in
      let fired_keys = keys_of f in
      (* forward: everything fired is registered and due *)
      List.iter
        (fun (k, d, w) ->
          if not (E4_timers.mem t k) then ok := false;
          if w <> k then ok := false;
          if d > upto then ok := false;
          match E4_timers.deadline_of t k with
          | Some dl -> if not (E4_timers.time_le dl (E4_timers.Fin upto)) then ok := false
          | None -> ok := false)
        f;
      (* backward: every registered due timer is in the fire list *)
      List.iter
        (fun (k, dl, _) ->
          let due = E4_timers.time_le dl (E4_timers.Fin upto) in
          let listed = List.mem k fired_keys in
          if due <> listed then ok := false)
        (E4_timers.to_list t))
    [ 0; 1; 100; 499; 500; 999; 1000; 100_000 ];
  check "timers-due-exact fired ~upto = exactly the registered timers with deadline <= upto"
    !ok;
  (* and `advance_to` fires exactly what `fired` predicted, leaving the rest *)
  let t', fires = E4_timers.advance_to t ~target:500 in
  check "timers-due-exact advance_to fires exactly `fired ~upto:target`"
    (fires = E4_timers.fired t ~upto:500);
  check "timers-due-exact the rest are exactly the not-due timers"
    (E4_timers.size t' = E4_timers.size t - List.length fires
    && List.for_all
         (fun (_, dl, _) -> E4_timers.time_lt (E4_timers.Fin 500) dl)
         (E4_timers.to_list t'));
  check "timers-due-exact `fired` is free: it moves nothing"
    (E4_timers.now t = 0 && E4_timers.size t = 500);
  (* an upto below `now` fires nothing and does not raise (a free row never refuses) *)
  let t2, _ = E4_timers.advance_to t ~target:800 in
  check "timers-due-exact fired ~upto below now is [] and does not raise"
    (E4_timers.fired t2 ~upto:3 = [])

(* ============================================================ P-T3 *)

let test_fire_order () =
  print_endline "-- P-T3 fire order is deadline, then registration";
  reseed ();
  let t = build 400 50 (* many equal deadlines on purpose *) in
  let f = E4_timers.fired t ~upto:49 in
  let rec ascending = function
    | (k1, d1, _) :: (((k2, d2, _) :: _) as rest) ->
        (d1 < d2 || (d1 = d2 && k1 < k2)) && ascending rest
    | _ -> true
  in
  check "timers-fire-order the fire list is strictly ascending under (deadline, seq)"
    (ascending f);
  check "timers-fire-order every timer of the table fires at upto = span - 1"
    (List.length f = E4_timers.size t);
  (* equal deadlines fire in registration order (SleepOrder, TestClock.ts:201-204) *)
  let s0, k0 = E4_timers.sleep E4_timers.empty (E4_timers.Fin 10) "a" in
  let s1, k1 = E4_timers.sleep s0 (E4_timers.Fin 10) "b" in
  let s2, k2 = E4_timers.sleep s1 (E4_timers.Fin 5) "c" in
  let s3, k3 = E4_timers.sleep s2 (E4_timers.Fin 10) "d" in
  let _, fires = E4_timers.advance_to s3 ~target:20 in
  check "timers-fire-order equal deadlines fire in registration order, earlier first"
    (List.map (fun (_, _, w) -> w) fires = [ "c"; "a"; "b"; "d" ]);
  check "timers-fire-order the park token is the registration number, ascending"
    (k0 = Some 0 && k1 = Some 1 && k2 = Some 2 && k3 = Some 3);
  check "timers-fire-order `min` is the head of the fire list"
    (match E4_timers.min s3 with Some (k, d, w) -> (k, d, w) = (2, E4_timers.Fin 5, "c") | None -> false);
  (* TIM-UNIQ: no two timers share a priority, so `min` needs no tie-break rule *)
  let prios = List.map (fun (k, d, _) -> (d, k)) (E4_timers.to_list s3) in
  check "timers-fire-order TIM-UNIQ: every (deadline, seq) is distinct"
    (List.length (List.sort_uniq compare prios) = List.length prios);
  (* to_list is the canonical, priority-ascending order (trap #16) *)
  check "timers-fire-order to_list is priority-ascending, not key-ascending"
    (List.map (fun (k, _, _) -> k) (E4_timers.to_list s3) = [ 2; 0; 1; 3 ])

(* ============================================================ P-T4 *)

let test_cancel () =
  print_endline "-- P-T4 cancel removes the entry, and it never fires again";
  reseed ();
  let t = build 300 1000 in
  let cancelled = List.filter (fun k -> k mod 3 = 0) (List.init 300 (fun i -> i)) in
  let t' = List.fold_left (fun acc k -> E4_timers.cancel acc k) t cancelled in
  check "timers-cancel the cancelled keys are gone"
    (List.for_all (fun k -> not (E4_timers.mem t' k)) cancelled);
  check "timers-cancel cancel_keeps: everything else is untouched"
    (List.for_all
       (fun k ->
         k mod 3 = 0
         || (E4_timers.mem t' k
            && E4_timers.deadline_of t' k = E4_timers.deadline_of t k
            && E4_timers.waiter_of t' k = E4_timers.waiter_of t k))
       (List.init 300 (fun i -> i)));
  check "timers-cancel the size drops by exactly the number cancelled"
    (E4_timers.size t' = 300 - List.length cancelled);
  check "timers-cancel a cancelled timer never fires, at any upto"
    (List.for_all
       (fun upto ->
         List.for_all (fun k -> k mod 3 <> 0) (keys_of (E4_timers.fired t' ~upto)))
       [ 0; 250; 999; 1000; E4_time.max_deadline_ms ]);
  check "timers-cancel is idempotent, and a no-op on an unknown key"
    (E4_timers.to_list (E4_timers.cancel (E4_timers.cancel t' 0) 0) = E4_timers.to_list t'
    && E4_timers.to_list (E4_timers.cancel t' 999_999) = E4_timers.to_list t'
    && E4_timers.size (E4_timers.cancel t' 999_999) = E4_timers.size t');
  check "timers-cancel does not move the clock or the counter"
    (E4_timers.now t' = 0 && E4_timers.next_seq t' = 300);
  check "timers-cancel remove_by_key is cancel"
    (E4_timers.to_list (E4_timers.remove_by_key t 7) = E4_timers.to_list (E4_timers.cancel t 7));
  (* cancelling every timer empties the store *)
  let empty' = List.fold_left (fun acc k -> E4_timers.cancel acc k) t (List.init 300 (fun i -> i)) in
  check "timers-cancel cancelling all of them empties the table"
    (E4_timers.is_empty empty' && E4_timers.to_list empty' = [] && E4_timers.wf empty')

(* ============================================================ P-T5 *)

let test_edges () =
  print_endline "-- P-T5 sleep 0 registers nothing; sleep Inf never fires; the domain bounds";
  let t0 = E4_timers.empty in
  let t1, k1 = E4_timers.sleep t0 (E4_timers.Fin 0) "zero" in
  check "timers-edges sleep (Fin 0) registers nothing and answers None"
    (k1 = None && E4_timers.is_empty t1 && E4_timers.next_seq t1 = 0);
  let t2, k2 = E4_timers.sleep t1 E4_timers.Inf "forever" in
  check "timers-edges sleep Inf registers and takes a token" (k2 = Some 0 && E4_timers.size t2 = 1);
  check "timers-edges an Inf timer never fires under a finite advance"
    (E4_timers.fired t2 ~upto:E4_time.max_deadline_ms = []
    && E4_timers.fired t2 ~upto:max_int = []
    && snd (E4_timers.advance_to t2 ~target:E4_time.max_deadline_ms) = []);
  check "timers-edges an Inf timer survives the advance that fires everything else"
    (E4_timers.size (fst (E4_timers.advance_to t2 ~target:E4_time.max_deadline_ms)) = 1);
  check "timers-edges Inf is the deadline that comes back out"
    (E4_timers.deadline_of t2 0 = Some E4_timers.Inf
    && E4_timers.min t2 = Some (0, E4_timers.Inf, "forever"));
  check "timers-edges Inf is above every finite time"
    (E4_timers.time_le (E4_timers.Fin E4_time.max_deadline_ms) E4_timers.Inf
    && E4_timers.time_lt (E4_timers.Fin 0) E4_timers.Inf
    && (not (E4_timers.time_le E4_timers.Inf (E4_timers.Fin E4_time.max_deadline_ms)))
    && E4_timers.time_le E4_timers.Inf E4_timers.Inf
    && not (E4_timers.time_lt E4_timers.Inf E4_timers.Inf));
  (* the domain bound is a named constant, refused at the row and never clamped (C5) *)
  check "timers-edges max_deadline_ms is the named constant, not max_int"
    (E4_timers.max_deadline_ms = 1_000_000_000
    && E4_timers.max_deadline_ms = E4_time.max_deadline_ms
    && E4_timers.max_deadline_ms < max_int);
  check "timers-edges a deadline exactly at max_deadline_ms is admissible"
    (E4_timers.deadline_of
       (fst (E4_timers.sleep t0 (E4_timers.Fin E4_time.max_deadline_ms) "top"))
       0
    = Some (E4_timers.Fin E4_time.max_deadline_ms));
  check "timers-edges a deadline above max_deadline_ms is Invalid_argument, not clamped"
    (raises (fun () -> E4_timers.sleep t0 (E4_timers.Fin (E4_time.max_deadline_ms + 1)) "over"));
  check "timers-edges now + d above the bound is Invalid_argument"
    (let t, _ = E4_timers.advance_to t0 ~target:1000 in
     raises (fun () -> E4_timers.sleep t (E4_timers.Fin E4_time.max_deadline_ms) "over"));
  check "timers-edges a negative duration is refused (R6: the fold to zero is the row's)"
    (raises (fun () -> E4_timers.sleep t0 (E4_timers.Fin (-1)) "neg")
    && raises (fun () -> E4_timers.time_add 0 (E4_timers.Fin (-1))));
  check "timers-edges time_add: now + d, and Inf absorbs"
    (E4_timers.time_add 10 (E4_timers.Fin 5) = E4_timers.Fin 15
    && E4_timers.time_add 10 E4_timers.Inf = E4_timers.Inf
    && E4_timers.time_add 10 (E4_timers.Fin 0) = E4_timers.Fin 10);
  check "timers-edges an empty store fires nothing and has no min"
    (E4_timers.min t0 = None
    && E4_timers.fired t0 ~upto:1000 = []
    && snd (E4_timers.advance_to t0 ~target:1000) = []
    && E4_timers.now (fst (E4_timers.advance_to t0 ~target:1000)) = 1000);
  check "timers-edges lookups on an unknown key answer None"
    (E4_timers.deadline_of t2 42 = None
    && E4_timers.waiter_of t2 42 = None
    && not (E4_timers.mem t2 42));
  check "timers-edges C1: the clock cannot be built outside the domain"
    (raises (fun () -> E4_time.of_tick (-1))
    && raises (fun () -> E4_time.of_tick (E4_time.max_deadline_ms + 1))
    && E4_time.now (E4_time.of_tick 5) = 5)

(* ============================================================ P-T6 *)

(* Iterate the staged fire to exhaustion, then `finish` at the target: workshop
   `Store.iterate` (Timer.lean:538-543). *)
let staged t ~target =
  let rec go t acc =
    match E4_timers.pop_due t ~upto:target with
    | None ->
        let t', extra = E4_timers.advance_to t ~target in
        (* `finish`: nothing is due, so this only moves the clock *)
        (t', List.rev acc, extra)
    | Some (fire, t') -> go t' (fire :: acc)
  in
  go t []

let test_staged_eq_batched () =
  print_endline "-- P-T6 staged = batched (iterate_eq_advance)";
  reseed ();
  let ok = ref true in
  for _ = 1 to 40 do
    let n = 1 + rand 60 in
    let span = 1 + rand 200 in
    let t = build n span in
    let target = rand (span + 50) in
    let st, staged_fires, extra = staged t ~target in
    let bt, batched_fires = E4_timers.advance_to t ~target in
    if staged_fires <> batched_fires then ok := false;
    if extra <> [] then ok := false;
    if E4_timers.now st <> E4_timers.now bt then ok := false;
    if E4_timers.to_list st <> E4_timers.to_list bt then ok := false;
    if E4_timers.next_seq st <> E4_timers.next_seq bt then ok := false;
    if not (E4_timers.wf st && E4_timers.wf bt) then ok := false
  done;
  check
    "timers-staged-eq-batched the staged loop and advance_to agree on fires, order, clock \
     and table (40 random tables)"
    !ok;
  (* the one thing they differ on is what `now` reads BETWEEN fires: staged is the fired
     deadline, batched is the target. That difference is the host loop's, and it is real. *)
  let t = build 3 100 in
  let target = 99 in
  let first = E4_timers.pop_due t ~upto:target in
  check "timers-staged-eq-batched between fires the staged clock is the fired deadline"
    (match first with
    | Some ((_, d, _), t') -> E4_timers.now t' = d && d <= target
    | None -> false);
  check "timers-staged-eq-batched the batched clock is the target at the end"
    (E4_timers.now (fst (E4_timers.advance_to t ~target)) = target);
  (* advance ~by is advance_to (now + by) *)
  let t2, _ = E4_timers.advance_to t ~target:10 in
  check "timers-staged-eq-batched advance ~by:d = advance_to ~target:(now + d)"
    (let a, fa = E4_timers.advance t2 ~by:30 in
     let b, fb = E4_timers.advance_to t2 ~target:40 in
     fa = fb && E4_timers.now a = E4_timers.now b && E4_timers.to_list a = E4_timers.to_list b)

(* ============================================================ P-T7 *)

let test_wf () =
  print_endline "-- P-T7 wf is preserved by every operation";
  reseed ();
  let ok = ref true in
  let t = ref E4_timers.empty in
  let clock = ref 0 in
  for _ = 1 to 3000 do
    (match rand 5 with
    | 0 | 1 ->
        let d = rand 500 in
        let t', _ = E4_timers.sleep !t (E4_timers.Fin d) (E4_timers.next_seq !t) in
        t := t'
    | 2 -> t := E4_timers.cancel !t (rand (E4_timers.next_seq !t + 1))
    | 3 -> (
        match E4_timers.pop_due !t ~upto:(!clock + rand 50) with
        | None -> ()
        | Some ((_, d, _), t') ->
            clock := d;
            t := t')
    | _ ->
        let by = rand 20 in
        let t', _ = E4_timers.advance !t ~by in
        clock := !clock + by;
        t := t');
    if not (E4_timers.wf !t) then ok := false;
    if E4_timers.now !t <> !clock then ok := false
  done;
  check "timers-wf 3000 random sleep/cancel/pop_due/advance steps keep wf and the clock" !ok;
  check "timers-wf empty is wf" (E4_timers.wf E4_timers.empty);
  (* of_list refuses everything wf refuses; to_list/of_list round-trips *)
  let s = build 50 200 in
  let round = E4_timers.of_list ~now:(E4_timers.now s) ~next_seq:(E4_timers.next_seq s) (E4_timers.to_list s) in
  check "timers-wf to_list -> of_list is the identity on (now, next_seq, table)"
    (E4_timers.to_list round = E4_timers.to_list s
    && E4_timers.now round = E4_timers.now s
    && E4_timers.next_seq round = E4_timers.next_seq s
    && E4_timers.size round = E4_timers.size s
    && E4_timers.wf round);
  check "timers-wf of_list refuses TIM-FRESH (a key at or above next_seq)"
    (raises (fun () -> E4_timers.of_list ~now:0 ~next_seq:1 [ (1, E4_timers.Fin 5, "x") ]));
  check "timers-wf of_list refuses TIM-PAST (a deadline before now)"
    (raises (fun () -> E4_timers.of_list ~now:10 ~next_seq:1 [ (0, E4_timers.Fin 5, "x") ]));
  check "timers-wf of_list refuses TIM-UNIQ (a repeated registration number)"
    (raises (fun () ->
         E4_timers.of_list ~now:0 ~next_seq:2
           [ (0, E4_timers.Fin 5, "x"); (0, E4_timers.Fin 9, "y") ]));
  check "timers-wf of_list refuses a deadline outside the domain"
    (raises (fun () ->
         E4_timers.of_list ~now:0 ~next_seq:1
           [ (0, E4_timers.Fin (E4_time.max_deadline_ms + 1), "x") ])
    && raises (fun () -> E4_timers.of_list ~now:0 ~next_seq:1 [ (0, E4_timers.Fin (-3), "x") ]));
  check "timers-wf of_list refuses a clock outside the domain"
    (raises (fun () -> E4_timers.of_list ~now:(-1) ~next_seq:0 [])
    && raises (fun () -> E4_timers.of_list ~now:(E4_time.max_deadline_ms + 1) ~next_seq:0 []));
  check "timers-wf of_list accepts an Inf deadline at any clock"
    (E4_timers.wf (E4_timers.of_list ~now:500 ~next_seq:1 [ (0, E4_timers.Inf, "x") ]))

(* ============================================================ the mutation test *)

(* §4.1: "let `advance_to` accept a target below `now`" must turn a test red. The guard lives
   in E4_time.advance_to (refusal R1); this test states the refusal, and states what the
   store would be if the guard were dropped, so the mutation cannot pass silently. *)
let test_mutation_advance_backwards () =
  print_endline "-- the mutation test: advance_to must refuse a target below now (R1)";
  let t = build 10 1000 in
  let t, _ = E4_timers.advance_to t ~target:500 in
  check "timers-mutation-advance-backwards advance_to ~target:(now - 1) raises"
    (raises (fun () -> E4_timers.advance_to t ~target:499));
  check "timers-mutation-advance-backwards advance_to ~target:0 on a moved clock raises"
    (raises (fun () -> E4_timers.advance_to t ~target:0));
  check "timers-mutation-advance-backwards advance ~by a negative duration raises"
    (raises (fun () -> E4_timers.advance t ~by:(-1))
    && raises (fun () -> E4_timers.advance t ~by:(-500)));
  check "timers-mutation-advance-backwards advance_to ~target:now is accepted and fires \
         nothing new"
    (let t', f = E4_timers.advance_to t ~target:500 in
     E4_timers.now t' = 500 && f = [] && E4_timers.to_list t' = E4_timers.to_list t);
  check "timers-mutation-advance-backwards the refusal leaves the store untouched"
    (let before = E4_timers.to_list t in
     (try ignore (E4_timers.advance_to t ~target:1) with Invalid_argument _ -> ());
     E4_timers.to_list t = before && E4_timers.now t = 500);
  check "timers-mutation-advance-backwards E4_time carries the guard (the mutation point)"
    (raises (fun () -> E4_time.advance_to (E4_time.of_tick 500) ~target:499)
    && raises (fun () -> E4_time.advance_by (E4_time.of_tick 500) ~by:(-1)));
  (* what the guard buys: without it, TIM-PAST and P-T1 both fail. Stated as the reason. *)
  note
    "were the guard dropped, `advance_to t ~target:0` on this store would answer now = 0 \
     with 10 timers whose deadlines are below the clock: TIM-PAST breaks, `timers-wf` and \
     `timers-now-monotone` go red with it.";
  check "timers-mutation-advance-backwards the clock's domain top is guarded too"
    (raises (fun () -> E4_timers.advance_to t ~target:(E4_time.max_deadline_ms + 1))
    && raises (fun () -> E4_timers.advance t ~by:E4_time.max_deadline_ms))

(* ============================================================ the workshop witnesses *)

(* workshop/Timer/Timer.lean:599-624, executed there as `#guard`. `w1`: two sleeps to the
   same deadline and a longer one; waiters 1, 2, 3 taking registration numbers 0, 1, 2. *)
let w1 () =
  let s, _ = E4_timers.sleep E4_timers.empty (E4_timers.Fin 10) 1 in
  let s, _ = E4_timers.sleep s (E4_timers.Fin 10) 2 in
  let s, _ = E4_timers.sleep s (E4_timers.Fin 20) 3 in
  s

let waiters l = List.map (fun (_, _, w) -> w) l

let test_workshop_guards () =
  print_endline "-- the workshop witnesses (workshop/Timer/Timer.lean:606-624) replayed";
  let w1 = w1 () in
  let a10, f10 = E4_timers.advance_to w1 ~target:10 in
  check "workshop #guard (advance 10 w1).due = [1, 2]" (waiters f10 = [ 1; 2 ]);
  check "workshop #guard (advance 10 w1).table.map waiter = [3]"
    (List.map (fun (_, _, w) -> w) (E4_timers.to_list a10) = [ 3 ]);
  check "workshop #guard (advance 10 w1).now = 10" (E4_timers.now a10 = 10);
  check "workshop #guard (advance 25 w1).due = [1, 2, 3]"
    (waiters (snd (E4_timers.advance_to w1 ~target:25)) = [ 1; 2; 3 ]);
  check "workshop #guard staged: (fireNext 25 w1) = some (waiter 1, now 10)"
    (match E4_timers.pop_due w1 ~upto:25 with
    | Some ((_, d, w), t') -> w = 1 && d = 10 && E4_timers.now t' = 10
    | None -> false);
  (* w2: a sleep registered DURING an advance is due in the same advance *)
  let w2 =
    match E4_timers.pop_due w1 ~upto:25 with
    | Some (_, s) -> fst (E4_timers.sleep s (E4_timers.Fin 3) 4)
    | None -> w1
  in
  check "workshop #guard (advance 25 w2).due = [1, 2, 4, 3]"
    (1 :: waiters (snd (E4_timers.advance_to w2 ~target:25)) = [ 1; 2; 4; 3 ]);
  check "workshop #guard (advance 25 (cancel 1 w1)).due = [1, 3]"
    (waiters (snd (E4_timers.advance_to (E4_timers.cancel w1 1) ~target:25)) = [ 1; 3 ]);
  check "workshop #guard (advance 1000 (sleep inf 9 w1)).due = [1, 2, 3]"
    (waiters (snd (E4_timers.advance_to (fst (E4_timers.sleep w1 E4_timers.Inf 9)) ~target:1000))
    = [ 1; 2; 3 ]);
  check "workshop #guard (sleep (fin 0) 7 w1) = (w1, none) and the table is still 3"
    (let s, k = E4_timers.sleep w1 (E4_timers.Fin 0) 7 in
     k = None && E4_timers.size s = 3);
  check "workshop #guard the registration number is the park token: (sleep (fin 5) 8 w1).2 = some 3"
    (snd (E4_timers.sleep w1 (E4_timers.Fin 5) 8) = Some 3)

(* ============================================================ T7 persistence, canonicity *)

let test_persistent () =
  print_endline "-- T7 persistence and the canonical form";
  let t = build 100 500 in
  let l0 = E4_timers.to_list t in
  let n0 = E4_timers.now t in
  let s0 = E4_timers.size t in
  let t1, _ = E4_timers.advance_to t ~target:250 in
  let t2 = E4_timers.cancel t1 0 in
  let t3, _ = E4_timers.sleep t2 (E4_timers.Fin 10) 999 in
  let _ = E4_timers.pop_due t3 ~upto:1000 in
  check "timers-persistent the original value still answers the original questions"
    (E4_timers.to_list t = l0 && E4_timers.now t = n0 && E4_timers.size t = s0);
  check "timers-persistent every intermediate value is still itself"
    (E4_timers.now t1 = 250
    && E4_timers.size t2 <= E4_timers.size t1
    && E4_timers.size t3 = E4_timers.size t2 + 1
    && E4_timers.wf t1 && E4_timers.wf t2 && E4_timers.wf t3);
  check "timers-persistent two stores with the same now, next_seq and to_list agree"
    (let a = E4_timers.of_list ~now:250 ~next_seq:(E4_timers.next_seq t1) (E4_timers.to_list t1) in
     E4_timers.to_list a = E4_timers.to_list t1
     && E4_timers.now a = E4_timers.now t1
     && E4_timers.next_seq a = E4_timers.next_seq t1
     && E4_timers.fired a ~upto:400 = E4_timers.fired t1 ~upto:400);
  check "timers-persistent of_list does not depend on the input order (to_list is canonical)"
    (let l = E4_timers.to_list t1 in
     let rev = E4_timers.of_list ~now:250 ~next_seq:(E4_timers.next_seq t1) (List.rev l) in
     E4_timers.to_list rev = l);
  check "timers-persistent size / length / is_empty agree"
    (E4_timers.size t = E4_timers.length t
    && E4_timers.is_empty E4_timers.empty
    && not (E4_timers.is_empty t))

(* ============================================================ *)

let () =
  Printf.printf "== lane Q2: the timer store (OCaml %s) ==\n" Sys.ocaml_version;
  test_now_monotone ();
  test_due_exact ();
  test_fire_order ();
  test_cancel ();
  test_edges ();
  test_staged_eq_batched ();
  test_wf ();
  test_mutation_advance_backwards ();
  test_workshop_guards ();
  test_persistent ();
  if !failures = 0 then print_endline "\nall timer checks passed"
  else Printf.printf "\n%d FAILURE(S)\n" !failures;
  exit (if !failures = 0 then 0 else 1)
