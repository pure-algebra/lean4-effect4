(* test_wake.ml — lane Q1's checks of E4_wake (the one allocation-and-wake protocol).

   What it checks, and against what: W1..W6 and DL3 of
   docs/research/2026-09-08-engine-a3-queue-query.md §1.1.4 / §2.4, one test per law, named as
   §4.1 names them. The WHATWG fixtures F1..F5c are a separate binary, test_whatwg.ml.
     W1  registration order          [Stores.lean:1416, deferredStore_complete_due :1532]
     W2  register on a settled cell  [DeferredStore.register, Stores.lean:1386-1393]
     W3  completion is once          [DeferredStore.complete, Stores.lean:1407-1416]
     W4  the cancelled waiter owes one wake, and W4a its vacuous sub-case  [Eio sem_state.ml]
     W5  capture                     [transform-backpressure.contract.md:141]
     W6  coalescing is phase equality
     DL3 the Delay budget: a bounded re-presentation, never a silent spin (DB-04)
   Exit code 0 iff every check passed. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* Register and keep the waiter row the caller would have kept. *)
let reg t c ~fiber ~token =
  let t', ans = E4_wake.register t c ~fiber ~token in
  match ans with
  | E4_wake.Park p -> (t', Some { E4_wake.fiber; token; at_phase = p })
  | _ -> (t', None)

let fibers ws = List.map (fun (w : E4_wake.waiter) -> w.fiber) ws

(* ============================================================ W1 *)

let test_registration_order () =
  print_endline "-- E4_wake: W1, registration order";
  let c, t = E4_wake.alloc E4_wake.empty in
  let t = List.fold_left (fun t f -> fst (reg t c ~fiber:f ~token:(f * 10))) t [ 1; 2; 3; 4 ] in
  let in_order = fibers (E4_wake.waiters_of t c) in
  let t', res = E4_wake.complete t c "done" in
  let handed = match res with `Completed ws -> fibers ws | _ -> [] in
  check "wake-registration-order  W1 (register appends; the list is request order)"
    (in_order = [ 1; 2; 3; 4 ]);
  check "wake-registration-order  W1 (completion hands every waiter back IN REQUEST ORDER)"
    (handed = [ 1; 2; 3; 4 ]);
  check "wake-registration-order  W1 (the token travels with the waiter)"
    (match res with
    | `Completed ws -> List.map (fun (w : E4_wake.waiter) -> w.token) ws = [ 10; 20; 30; 40 ]
    | _ -> false);
  check "wake-registration-order  W1 (and the cell is left with no waiter)"
    (E4_wake.waiters_of t' c = [])

(* ============================================================ W2 *)

let test_settled_register () =
  print_endline "-- E4_wake: W2, register on a settled cell";
  let c, t = E4_wake.alloc E4_wake.empty in
  let t, _ = reg t c ~fiber:1 ~token:11 in
  let before = E4_wake.waiters_of t c in
  let t, _ = E4_wake.complete t c "v" in
  let after_complete = E4_wake.waiters_of t c in
  let t', ans = E4_wake.register t c ~fiber:2 ~token:22 in
  check "wake-settled-register  W2 (a settled cell answers now)"
    (match ans with E4_wake.Answer v -> v = "v" | _ -> false);
  check "wake-settled-register  W2 (and appends to NO reaction list)"
    (E4_wake.waiters_of t' c = [] && after_complete = [] && List.length before = 1);
  check "wake-settled-register  W2 (a pending cell parks and retains the subscription)"
    (let c2, t2 = E4_wake.alloc t' in
     let t2, ans2 = E4_wake.register t2 c2 ~fiber:3 ~token:33 in
     (match ans2 with E4_wake.Park p -> p = 0 | _ -> false)
     && List.length (E4_wake.waiters_of t2 c2) = 1);
  check "wake-refuse  an unknown cell is Refuse, never a hang (gap G1)"
    (match E4_wake.register t' 9999 ~fiber:4 ~token:44 with
    | _, E4_wake.Refuse -> true
    | _ -> false)

(* ============================================================ W3 *)

let test_complete_once () =
  print_endline "-- E4_wake: W3, completion is once";
  let c, t = E4_wake.alloc E4_wake.empty in
  let t, _ = reg t c ~fiber:1 ~token:11 in
  let t, _ = reg t c ~fiber:2 ~token:22 in
  let waiters_before = E4_wake.waiters_of t c in
  let phase_before = E4_wake.phase_of t c in
  let t1, r1 = E4_wake.complete t c "first" in
  let t2, r2 = E4_wake.complete t1 c "second" in
  check "wake-complete-once  W3 (the first completion settles and bumps the phase)"
    (E4_wake.poll t1 c = Some (Some "first")
    && E4_wake.is_done t1 c = Some true
    && phase_before = Some 0
    && E4_wake.phase_of t1 c = Some 1);
  check "wake-complete-once  W3 (it clears the waiter list AND hands every waiter back -- F5c)"
    (E4_wake.waiters_of t1 c = []
    && (match r1 with `Completed ws -> ws = waiters_before | _ -> false));
  check "wake-complete-once  W3 (a second complete reports Already and changes NOTHING)"
    ((match r2 with `Already -> true | _ -> false)
    && E4_wake.poll t2 c = Some (Some "first")
    && E4_wake.phase_of t2 c = Some 1
    && E4_wake.waiters_of t2 c = []);
  check "wake-complete-once  W3 (an unknown cell is Unknown)"
    (match E4_wake.complete t 4242 "x" with _, `Unknown -> true | _ -> false)

(* ============================================================ W4, W4a *)

let test_cancel_owes () =
  print_endline "-- E4_wake: W4, the cancelled waiter owes one wake";
  let c, t = E4_wake.alloc E4_wake.empty in
  let t, w1 = reg t c ~fiber:1 ~token:11 in
  let t, w2 = reg t c ~fiber:2 ~token:22 in
  let t, w3 = reg t c ~fiber:3 ~token:33 in
  let w1 = Option.get w1 and w2 = Option.get w2 and w3 = Option.get w3 in
  (* (a) the phase has not moved: splice out, owe nothing *)
  let ta, ra = E4_wake.cancel t c w2 in
  check "wake-cancel-owes  W4 (phase unchanged: Removed, and the waiter is spliced out)"
    ((match ra with `Removed -> true | _ -> false)
    && List.map (fun (w : E4_wake.waiter) -> w.fiber) (E4_wake.waiters_of ta c) = [ 1; 3 ]);
  (* (b) the phase advanced and the resumer already took this waiter: the canceller owes one
     wake, and it is handed the NEXT waiter to resume. *)
  let tb, woken = E4_wake.signal t c ~count:1 in
  let tb', rb = E4_wake.cancel tb c w1 in
  check "wake-cancel-owes  W4 (phase advanced: Owes_wake, naming the next waiter)"
    (List.map (fun (w : E4_wake.waiter) -> w.fiber) woken = [ 1 ]
    && (match rb with `Owes_wake w -> w.fiber = 2 | _ -> false)
    && E4_wake.phase_of tb c = Some 1
    && List.map (fun (w : E4_wake.waiter) -> w.fiber) (E4_wake.waiters_of tb' c) = [ 2; 3 ]);
  (* (c) W4a: the phase advanced but nobody is left to hand the wake to. *)
  let c2, t2 = E4_wake.alloc E4_wake.empty in
  let t2, wa = reg t2 c2 ~fiber:7 ~token:77 in
  let wa = Option.get wa in
  let t2, _ = E4_wake.signal t2 c2 ~count:1 in
  let _, rc = E4_wake.cancel t2 c2 wa in
  check "wake-cancel-owes  W4a (phase advanced, no waiter left: the obligation is vacuous)"
    ((match rc with `Removed -> true | _ -> false) && E4_wake.waiters_of t2 c2 = []);
  (* (d) an unknown cell *)
  check "wake-cancel-owes  W4 (an unknown cell is Unknown)"
    (match E4_wake.cancel t 31337 w3 with _, `Unknown -> true | _ -> false);
  (* (e) cancelling twice owes at most what W4 says: the second cancel finds nothing to
     splice and answers from the phase alone. *)
  let td, _ = E4_wake.cancel ta c w2 in
  check "wake-cancel-owes  W4 (a second cancel of the same waiter changes nothing)"
    (E4_wake.waiters_of td c = E4_wake.waiters_of ta c)

(* ============================================================ W5 *)

let test_capture () =
  print_endline "-- E4_wake: W5, capture";
  let c1, t = E4_wake.alloc E4_wake.empty in
  let t, w = reg t c1 ~fiber:1 ~token:11 in
  let w = Option.get w in
  let t, _ = E4_wake.signal t c1 ~count:0 in
  (* the phase moved under the waiter; its recorded phase is NOT rewritten *)
  let still =
    match E4_wake.waiters_of t c1 with [ x ] -> x.at_phase = 0 && w.at_phase = 0 | _ -> false
  in
  let c2, t = E4_wake.alloc t in
  let t, _ = E4_wake.complete t c1 "old" in
  let t, _ = E4_wake.complete t c2 "new" in
  check "wake-capture  W5 (at_phase is written once at registration, never rewritten)"
    (still && E4_wake.phase_of t c1 = Some 2);
  check "wake-capture  W5 (a later cell cannot retarget an outstanding wake: ids are never reused)"
    (c2 <> c1 && E4_wake.poll t c1 = Some (Some "old") && E4_wake.poll t c2 = Some (Some "new"));
  check "wake-capture  W5 (a waiter registered after a phase bump captures the NEW phase)"
    (let c3, t3 = E4_wake.alloc E4_wake.empty in
     let t3, _ = E4_wake.signal t3 c3 ~count:0 in
     let t3, _ = E4_wake.signal t3 c3 ~count:0 in
     match snd (E4_wake.register t3 c3 ~fiber:5 ~token:55) with
     | E4_wake.Park p -> p = 2
     | _ -> false)

(* ============================================================ W6 *)

let test_coalesce () =
  print_endline "-- E4_wake: W6, coalescing is the phase equality";
  let c, t = E4_wake.alloc E4_wake.empty in
  let t = List.fold_left (fun t f -> fst (reg t c ~fiber:f ~token:f)) t [ 1; 2; 3 ] in
  (* five signals of two: no waiter may be handed back twice, and no more than three wakes
     exist to hand back at all. *)
  let rec go t acc n =
    if n = 0 then (t, acc)
    else
      let t', woken = E4_wake.signal t c ~count:2 in
      go t' (acc @ List.map (fun (w : E4_wake.waiter) -> w.fiber) woken) (n - 1)
  in
  let t', all = go t [] 5 in
  check "wake-coalesce  W6 (at most one pending wake per (cell, waiter))"
    (List.sort compare all = [ 1; 2; 3 ]
    && List.length (List.sort_uniq compare all) = List.length all);
  check "wake-coalesce  W6 (the phase counts every signal; the cell is not settled)"
    (E4_wake.phase_of t' c = Some 5 && E4_wake.poll t' c = Some None);
  check "wake-coalesce  W6 (a signal on an unknown cell wakes nobody and settles nothing)"
    (snd (E4_wake.signal t 777 ~count:3) = []);
  check "wake-coalesce  W6 (count <= 0 takes no waiter and still bumps the phase -- F5a's rule)"
    (let t2, woken = E4_wake.signal t c ~count:0 in
     woken = [] && E4_wake.phase_of t2 c = Some 1 && List.length (E4_wake.waiters_of t2 c) = 3)

(* ============================================================ DL3 *)

(* The driver DL1-DL3 describe, in miniature: a row that answers `Delay` is re-presented with
   no frame consumed and no trace row, and the re-presentation is BOUNDED. The counter lives
   here, in the driver, and not in a cell -- a cell that counted re-presentations would put a
   host fact into a saved machine. *)
let drive_delay t c ~fiber ~token =
  let rec loop n phase =
    if n >= E4_wake.delay_budget then `Frontier (fiber, token, n)
    else
      match E4_wake.poll t c with
      | Some (Some v) -> `Answered (v, n)
      | _ ->
        (* no intervening state change: the phase is the same as the one observed *)
        if E4_wake.phase_of t c = Some phase then loop (n + 1) phase else `Rearmed n
  in
  match E4_wake.phase_of t c with None -> `Refused | Some p -> loop 0 p

let test_delay_budget () =
  print_endline "-- E4_wake: DL3, the Delay budget";
  let c, t = E4_wake.alloc E4_wake.empty in
  check "wake-delay-budget  DL3 (the bound is a named constant, 1024, and is not max_int)"
    (E4_wake.delay_budget = 1024 && E4_wake.delay_budget < max_int);
  check "wake-delay-budget  DL3 (a row that never becomes ready is a FRONTIER naming the row)"
    (match drive_delay t c ~fiber:3 ~token:9 with
    | `Frontier (f, tok, n) -> f = 3 && tok = 9 && n = E4_wake.delay_budget
    | _ -> false);
  check "wake-delay-budget  DL3 (a ready row answers and consumes no budget)"
    (let t', _ = E4_wake.complete t c "v" in
     match drive_delay t' c ~fiber:3 ~token:9 with
     | `Answered (v, n) -> v = "v" && n = 0
     | _ -> false);
  check "wake-delay-budget  DL3 (an unknown cell is refused, never spun on)"
    (match drive_delay t 12345 ~fiber:3 ~token:9 with `Refused -> true | _ -> false);
  note
    "DL1/DL2 are the driver's obligations (no frame consumed, no fuel, no trace row, no tape \
     entry); this module supplies the bound and the store answer, and holds no counter"

(* ============================================================ persistence *)

let test_persistent () =
  print_endline "-- E4_wake: persistence (brief rule 3)";
  let c, t = E4_wake.alloc E4_wake.empty in
  let t, w = reg t c ~fiber:1 ~token:11 in
  let w = Option.get w in
  let waiters = E4_wake.waiters_of t c in
  let phase = E4_wake.phase_of t c in
  let size = E4_wake.size t in
  let _ = E4_wake.complete t c "v" in
  let _ = E4_wake.signal t c ~count:2 in
  let _ = E4_wake.cancel t c w in
  let _ = E4_wake.alloc t in
  check "wake-persistent  an older value answers every question exactly as before"
    (E4_wake.waiters_of t c = waiters
    && E4_wake.phase_of t c = phase
    && E4_wake.size t = size
    && E4_wake.poll t c = Some None)

let () =
  test_registration_order ();
  test_settled_register ();
  test_complete_once ();
  test_cancel_owes ();
  test_capture ();
  test_coalesce ();
  test_delay_budget ();
  test_persistent ();
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
