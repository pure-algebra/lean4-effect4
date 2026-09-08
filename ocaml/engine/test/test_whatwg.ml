(* test_whatwg.ml — the seven WHATWG fixtures F1..F5c, verbatim as the wake protocol's
   acceptance set (docs/research/2026-09-08-engine-a3-queue-query.md §1.1.4, the fixture
   table; lit-siblings Q5, "take their two capture rules and the zero-HWM demand rule as
   fixtures").

   Each test names the CONTRACT ROW it comes from and the law it pins:

     F1   register W on cell C at phase p; complete C; allocate a fresh cell; W's wake must
          carry the OLD completion.
          [transform-backpressure.contract.md:141 -- "every subscription contains the promise
          identity captured at registration -- a later slot replacement cannot retarget it"]
          pins W5
     F2   register on an already-settled cell -> answered now, waiter list untouched; register
          on a pending cell -> subscription retained.
          [transform-backpressure.contract.md:141]   pins W2
     F3   a taker registered on an empty zero-capacity queue creates demand: a later offer
          passes straight through and wakes it, and must not refuse "full".
          [readable-default.contract.md:109 -- "a pending read creates demand even at zero
          high-water-mark"]                          pins Queue's instance of W1/W7
     F4   close fulfils every pending waiter with `done` IN REQUEST ORDER; error rejects them
          in the SAME order.
          [readable-default.contract.md:148,152,158] pins W1
     F5a  complete a cell whose waiter list is empty STILL bumps the phase.
          [PROMISE-DAG.md:209 defect F1, "a conditional step that should be unconditional"]
          pins W3, W6
     F5b  register on a settled cell appends to NO reaction list.
          [defect F2, "settled branches appending to reaction lists"]        pins W2
     F5c  complete clears `waiters` AND appends to `due` -- both halves asserted in ONE step.
          [defect F3, "settling clearing one list when it should clear both"] pins W3

   These three (F5a/F5b/F5c) are the only fidelity defects the WHATWG team shipped, and all
   three were in exactly this bookkeeping.
   Exit code 0 iff every check passed. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let fibers ws = List.map (fun (w : E4_wake.waiter) -> w.fiber) ws

let park t c ~fiber ~token =
  let t', ans = E4_wake.register t c ~fiber ~token in
  match ans with
  | E4_wake.Park p -> (t', Some { E4_wake.fiber; token; at_phase = p })
  | _ -> (t', None)

(* The completion payload of a stream cell: `close` fulfils with Done, `error` rejects. *)
type outcome =
  | Done
  | Error of string

(* ============================================================ F1 *)

let f1 () =
  let c1, t = E4_wake.alloc E4_wake.empty in
  let t, w = park t c1 ~fiber:1 ~token:11 in
  let w = Option.get w in
  let t, res = E4_wake.complete t c1 "old completion" in
  (* the slot is "replaced": a fresh cell is allocated and settled with something else *)
  let c2, t = E4_wake.alloc t in
  let t, _ = E4_wake.complete t c2 "new completion" in
  check "whatwg-f1  W5 -- the wake carries the completion of the cell it registered at"
    ((match res with `Completed ws -> fibers ws = [ 1 ] | _ -> false)
    && E4_wake.poll t c1 = Some (Some "old completion")
    && w.at_phase = 0);
  check "whatwg-f1  W5 -- a later cell cannot be mistaken for the captured one"
    (c2 <> c1
    && E4_wake.poll t c2 = Some (Some "new completion")
    && E4_wake.waiters_of t c2 = [])

(* ============================================================ F2 *)

let f2 () =
  let c, t = E4_wake.alloc E4_wake.empty in
  (* pending: the subscription is retained *)
  let t, w = park t c ~fiber:1 ~token:11 in
  let retained = Option.is_some w && List.length (E4_wake.waiters_of t c) = 1 in
  let t, _ = E4_wake.complete t c "settled" in
  let waiters_after_settle = E4_wake.waiters_of t c in
  (* settled: answered now, waiter list untouched *)
  let t', ans = E4_wake.register t c ~fiber:2 ~token:22 in
  check "whatwg-f2  W2 -- register on a pending cell retains the subscription" retained;
  check "whatwg-f2  W2 -- register on a settled cell is answered now, the list untouched"
    ((match ans with E4_wake.Answer v -> v = "settled" | _ -> false)
    && E4_wake.waiters_of t' c = waiters_after_settle
    && waiters_after_settle = [])

(* ============================================================ F3 *)

(* A zero-capacity queue holds no item: an offer can only pass through to a taker. *)
let offer t c =
  let t', woken = E4_wake.signal t c ~count:1 in
  match woken with w :: _ -> (t', `Passed_through w) | [] -> (t', `Would_block)

let f3 () =
  let c, t = E4_wake.alloc E4_wake.empty in
  (* no taker: the offer has nowhere to go -- it blocks, and this is the case the defect
     confuses with "full" *)
  let _, no_taker = offer t c in
  (* a taker registers first: that IS the demand *)
  let t, taker = park t c ~fiber:5 ~token:55 in
  let taker = Option.get taker in
  let t', passed = offer t c in
  check "whatwg-f3  a pending read creates demand even at zero high-water-mark"
    ((match passed with
     | `Passed_through w -> w.fiber = taker.fiber && w.token = taker.token
     | `Would_block -> false)
    && (match no_taker with `Would_block -> true | _ -> false));
  check "whatwg-f3  the offer passes THROUGH: the cell is never settled and never refuses full"
    (E4_wake.poll t' c = Some None && E4_wake.waiters_of t' c = [])

(* ============================================================ F4 *)

let f4 () =
  let close_or_error out =
    let c, t = E4_wake.alloc E4_wake.empty in
    let t =
      List.fold_left (fun t f -> fst (park t c ~fiber:f ~token:(f * 10))) t [ 1; 2; 3; 4; 5 ]
    in
    let _, res = E4_wake.complete t c out in
    match res with `Completed ws -> fibers ws | _ -> []
  in
  check "whatwg-f4  W1 -- close fulfils every pending waiter in REQUEST order"
    (close_or_error Done = [ 1; 2; 3; 4; 5 ]);
  check "whatwg-f4  W1 -- error rejects them in the SAME order"
    (close_or_error (Error "boom") = [ 1; 2; 3; 4; 5 ])

(* ============================================================ F5a, F5b, F5c *)

let f5a () =
  let c, t = E4_wake.alloc E4_wake.empty in
  let before = E4_wake.phase_of t c in
  let t', res = E4_wake.complete t c Done in
  check "whatwg-f5a  W3/W6 -- completing a cell with NO waiter still bumps the phase"
    (before = Some 0
    && E4_wake.phase_of t' c = Some 1
    && match res with `Completed [] -> true | _ -> false)

let f5b () =
  let c, t = E4_wake.alloc E4_wake.empty in
  let t, _ = E4_wake.complete t c Done in
  let t1, _ = E4_wake.register t c ~fiber:1 ~token:11 in
  let t2, _ = E4_wake.register t1 c ~fiber:2 ~token:22 in
  check "whatwg-f5b  W2 -- a settled branch appends to NO reaction list, however often it is asked"
    (E4_wake.waiters_of t1 c = [] && E4_wake.waiters_of t2 c = [])

let f5c () =
  let c, t = E4_wake.alloc E4_wake.empty in
  let t = List.fold_left (fun t f -> fst (park t c ~fiber:f ~token:f)) t [ 1; 2; 3 ] in
  let waiters_before = E4_wake.waiters_of t c in
  let t', res = E4_wake.complete t c Done in
  (* BOTH halves, in ONE step: the waiter list is cleared and every waiter is handed to the
     due queue. The shipped defect cleared one list and not the other. *)
  let handed = match res with `Completed ws -> ws | _ -> [] in
  let due = E4_due.owe_all E4_due.empty E4_due.Deferred handed in
  check "whatwg-f5c  W3 -- complete CLEARS the waiters and APPENDS them to due, in one step"
    (E4_wake.waiters_of t' c = []
    && handed = waiters_before
    && List.length waiters_before = 3
    && fibers (fst (E4_due.drain due)) = [ 1; 2; 3 ])

let () =
  print_endline "-- the WHATWG fixtures (design §1.1.4)";
  f1 ();
  f2 ();
  f3 ();
  f4 ();
  f5a ();
  f5b ();
  f5c ();
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
