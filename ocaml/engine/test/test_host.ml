(* test_host.ml — the property tests behind the `tested` marks of the engine's host
   primitives (lane Q4): E4_mailbox, E4_inbox, E4_ring, E4_quiescence, E4_reply, E4_trigger,
   E4_admit.

   Where the checks come from:
     - `mailbox-*`, `inbox-*`, `reply-once`, `ring-*`, `quiescence-*` are the property tests
       of `git:14e6835:ocaml/link/e4_test.ml` (7d53312) for the five modules copied into the engine,
       ported unchanged apart from the module paths;
     - `mailbox-refuse-never-drop` is the added multi-domain test: N producer domains push
       into ONE mailbox against one draining consumer, and refuse-never-drop (M2, M3) is
       verified by counts;
     - `trigger-once`, `trigger-double-signal`, `trigger-signal-before-await`, `admit-pure`
       and `admit-monotone` are the new tests named in the design's §4.1 for TR1-TR4 and
       A1-A2 (2026-09-08-engine-a3-queue-query.md);
     - `bench-q4a-no-drop` is the assertion beside the B-Q4a MEASUREMENT (design §4.3): 8
       producer domains, 1e5 pushes each, into one mailbox, with the contended-push fraction
       printed. The fraction is REPORTED, not asserted: the acceptance "< 1 %" of §4.3 is
       stated for the existing 8-domain harness, where each machine owns its own mailbox,
       and a single shared mailbox is the adversarial fan-in case §4.3 keeps in reserve.

   One line per check, `PASS <name>` or `FAIL <name>` (the `ocaml/gen/gen_check.ml` style);
   the last line is `== ALL PASS: 0 failure(s) ==` and the exit code is 0 iff every check
   passed. Run: `dune test --root . --force` from ocaml/engine. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n%!" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let raises_invalid f = match f () with exception Invalid_argument _ -> true | _ -> false

(* ---- E4_mailbox: M1 M2 M3 M4 M5 ---- *)

let () =
  let m = E4_mailbox.create ~bound:10 () in
  List.iter (fun i -> ignore (E4_mailbox.push m i)) [ 1; 2; 3; 4; 5 ];
  let b1 = E4_mailbox.pop_batch m ~max:3 in
  let b2 = E4_mailbox.pop_batch m ~max:3 in
  let b3 = E4_mailbox.pop_batch m ~max:3 in
  check "mailbox-fifo" (b1 = [ 1; 2; 3 ] && b2 = [ 4; 5 ] && b3 = []);
  let m = E4_mailbox.create ~bound:2 () in
  let r1 = E4_mailbox.push m 1 in
  let r2 = E4_mailbox.push m 2 in
  let r3 = E4_mailbox.push m 3 in
  let len = E4_mailbox.length m in
  let popped = E4_mailbox.pop_batch m ~max:5 in
  check "mailbox-bounded-refuse"
    (r1 = Ok () && r2 = Ok () && r3 = Error `Full && len = 2 && popped = [ 1; 2 ]
    && (E4_mailbox.stats m).E4_mailbox.refused = 1
    && E4_mailbox.bound m = 2
    && E4_mailbox.is_empty m
    && raises_invalid (fun () -> E4_mailbox.create ~bound:0 ())
    && raises_invalid (fun () -> E4_mailbox.pop_batch m ~max:0))

let producers = 4
let per_producer = 1000

let () =
  let m = E4_mailbox.create ~bound:16 () in
  let prods =
    List.init producers (fun p ->
        Domain.spawn (fun () ->
            for i = 0 to per_producer - 1 do
              let x = (p * per_producer) + i in
              let rec push () =
                match E4_mailbox.push m x with
                | Ok () -> ()
                | Error `Full ->
                    Domain.cpu_relax ();
                    push ()
              in
              push ()
            done))
  in
  let seen = ref [] and count = ref 0 in
  while !count < producers * per_producer do
    match E4_mailbox.pop_batch m ~max:8 with
    | [] -> Domain.cpu_relax ()
    | xs ->
        seen := List.rev_append xs !seen;
        count := !count + List.length xs
  done;
  List.iter Domain.join prods;
  let stats = E4_mailbox.stats m in
  check "mailbox-exactly-once"
    (List.sort compare !seen = List.init (producers * per_producer) Fun.id
    && stats.E4_mailbox.pushed = producers * per_producer
    && stats.E4_mailbox.popped = producers * per_producer
    && stats.E4_mailbox.length = 0)

let () =
  let m = E4_mailbox.create ~bound:16 () in
  let counter = Atomic.make 0 in
  let prods =
    List.init producers (fun _ ->
        Domain.spawn (fun () ->
            for _ = 1 to per_producer do
              let rec push () =
                match E4_mailbox.push_with m (fun () -> Atomic.fetch_and_add counter 1) with
                | Ok () -> ()
                | Error `Full ->
                    Domain.cpu_relax ();
                    push ()
              in
              push ()
            done))
  in
  let last = ref (-1) and monotone = ref true and count = ref 0 in
  while !count < producers * per_producer do
    match E4_mailbox.pop_batch m ~max:8 with
    | [] -> Domain.cpu_relax ()
    | xs ->
        List.iter
          (fun s ->
            if s <= !last then monotone := false;
            last := s)
          xs;
        count := !count + List.length xs
  done;
  List.iter Domain.join prods;
  check "mailbox-stamp-monotone" (!monotone && Atomic.get counter = producers * per_producer)

let () =
  let wakes = ref 0 in
  let m = E4_mailbox.create ~bound:10 ~wake:(fun () -> incr wakes) () in
  ignore (E4_mailbox.push m 1);
  let w1 = !wakes in
  ignore (E4_mailbox.push m 2);
  let w2 = !wakes in
  let b1 = E4_mailbox.pop_batch m ~max:1 in
  let w3 = !wakes in
  let b2 = E4_mailbox.pop_batch m ~max:1 in
  let w4 = !wakes in
  ignore (E4_mailbox.push m 3);
  let w5 = !wakes in
  check "mailbox-wake" (w1 = 1 && w2 = 1 && b1 = [ 1 ] && w3 = 2 && b2 = [ 2 ] && w4 = 2 && w5 = 3)

(* The waiting consumer: `wait` must return once a push from another domain has landed.
   This is the check Q-A3-8's change is about — the broadcast now happens after the mutex
   is released, so a lost wake-up would hang here. *)
let () =
  let m = E4_mailbox.create ~bound:4 () in
  let d =
    Domain.spawn (fun () ->
        E4_mailbox.wait m;
        E4_mailbox.pop_batch m ~max:4)
  in
  Unix.sleepf 0.02;
  ignore (E4_mailbox.push m 42);
  let got = Domain.join d in
  check "mailbox-wait-broadcast" (got = [ 42 ])

(* The added multi-domain test: N producers into ONE mailbox, one consumer draining, and
   refuse-never-drop (M2, M3) verified by counts — every accepted element is seen exactly
   once, every refusal is counted, and nothing is unaccounted for. *)
let () =
  let np = 4 and per = 5_000 in
  let n = np * per in
  let m = E4_mailbox.create ~bound:8 () in
  let refused = Atomic.make 0 in
  let prods =
    List.init np (fun p ->
        Domain.spawn (fun () ->
            for i = 0 to per - 1 do
              let x = (p * per) + i in
              let rec push () =
                match E4_mailbox.push m x with
                | Ok () -> ()
                | Error `Full ->
                    ignore (Atomic.fetch_and_add refused 1);
                    Domain.cpu_relax ();
                    push ()
              in
              push ()
            done))
  in
  let seen = ref [] and count = ref 0 in
  while !count < n do
    match E4_mailbox.pop_batch m ~max:16 with
    | [] -> Domain.cpu_relax ()
    | xs ->
        seen := List.rev_append xs !seen;
        count := !count + List.length xs
  done;
  List.iter Domain.join prods;
  let s = E4_mailbox.stats m in
  Printf.printf "     mailbox-refuse-never-drop: %d producer domains x %d, %d refusals at bound %d\n%!" np per
    (Atomic.get refused) (E4_mailbox.bound m);
  check "mailbox-refuse-never-drop"
    (List.sort compare !seen = List.init n Fun.id
    && s.E4_mailbox.pushed = n
    && s.E4_mailbox.popped = n
    && s.E4_mailbox.refused = Atomic.get refused
    && s.E4_mailbox.length = 0)

(* ---- E4_inbox: I1 I2 I3 ---- *)

let () =
  let ib = E4_inbox.create () in
  let consumer =
    Domain.spawn (fun () ->
        let a = E4_inbox.pop ib in
        let b = E4_inbox.pop ib in
        let c = E4_inbox.pop ib in
        let d = E4_inbox.pop ib in
        (a, b, c, d))
  in
  Unix.sleepf 0.02;
  let p1 = E4_inbox.push ib 1 in
  let p2 = E4_inbox.push ib 2 in
  let p3 = E4_inbox.push ib 3 in
  E4_inbox.close ib;
  let a, b, c, d = Domain.join consumer in
  check "inbox-fifo"
    (p1 && p2 && p3 && a = Some 1 && b = Some 2 && c = Some 3 && d = None && E4_inbox.stats ib = (3, 3));
  check "inbox-close"
    ((not (E4_inbox.push ib 4))
    && E4_inbox.pop ib = None
    && E4_inbox.is_closed ib
    && E4_inbox.length ib = 0
    && E4_inbox.pop_opt ib = None)

(* ---- E4_reply: P1 P2 ---- *)

let () =
  let r = E4_reply.create () in
  let d =
    Domain.spawn (fun () ->
        Unix.sleepf 0.02;
        E4_reply.fill r "x")
  in
  let v = E4_reply.await r in
  Domain.join d;
  check "reply-once" (v = "x" && raises_invalid (fun () -> E4_reply.fill r "y") && E4_reply.peek r = Some "x")

(* ---- E4_ring: G1 G2 G3 ---- *)

let () =
  let r = E4_ring.create ~domain:0 ~capacity:4 in
  let e i = { E4_ring.domain = 0; machine = 0; seq = i; decision = "d"; row = "r" ^ string_of_int i } in
  for i = 0 to 5 do
    E4_ring.append r (e i)
  done;
  let seqs (x : E4_ring.read) = List.map (fun (e : E4_ring.entry) -> e.seq) x.entries in
  let a = E4_ring.read r ~cursor:0 in
  let b = E4_ring.read r ~cursor:3 in
  let c = E4_ring.read r ~cursor:6 in
  check "ring-bounded-gap"
    (seqs a = [ 2; 3; 4; 5 ] && a.gap && a.next = 6 && seqs b = [ 3; 4; 5 ] && (not b.gap) && seqs c = []
    && (not c.gap) && c.next = 6 && E4_ring.written r = 6 && E4_ring.domain r = 0 && E4_ring.capacity r = 4
    && raises_invalid (fun () -> E4_ring.create ~domain:0 ~capacity:0));
  let other = Domain.spawn (fun () -> raises_invalid (fun () -> E4_ring.append r (e 6))) in
  check "ring-single-writer" (Domain.join other && E4_ring.written r = 6)

(* ---- E4_quiescence: Q1 Q2 Q3 ---- *)

let () =
  let q = E4_quiescence.create () in
  E4_quiescence.enter q;
  E4_quiescence.enter q;
  E4_quiescence.enter q;
  let d =
    Domain.spawn (fun () ->
        Unix.sleepf 0.02;
        E4_quiescence.leave q;
        E4_quiescence.leave q;
        E4_quiescence.leave q)
  in
  E4_quiescence.wait_zero q;
  Domain.join d;
  check "quiescence-counter"
    (E4_quiescence.outstanding q = 0 && E4_quiescence.totals q = (3, 3)
    && raises_invalid (fun () -> E4_quiescence.leave q)
    && E4_quiescence.wait_zero_for q ~seconds:0.01);
  E4_quiescence.enter q;
  check "quiescence-timeout" (not (E4_quiescence.wait_zero_for q ~seconds:0.005));
  E4_quiescence.leave q

(* ---- E4_trigger: TR1 TR2 TR3 TR4 ---- *)

let () =
  let t = E4_trigger.create () in
  let a = { E4_trigger.machine = 1; fiber = 2; token = 3 } in
  let initial = E4_trigger.state t = E4_trigger.Initial && not (E4_trigger.is_signaled t) in
  let posts = ref [] in
  let post x = posts := x :: !posts in
  let first = E4_trigger.await t a in
  let awaiting = E4_trigger.state t = E4_trigger.Awaiting a in
  (* TR2: a second await is an error, not an answer *)
  let twice = raises_invalid (fun () -> E4_trigger.await t a) in
  E4_trigger.signal t ~post;
  let signaled = E4_trigger.state t = E4_trigger.Signaled in
  (* TR1: the second signal changes nothing and posts nothing *)
  E4_trigger.signal t ~post;
  let after = E4_trigger.await t a in
  check "trigger-once"
    (initial && first = `Awaiting && awaiting && twice && signaled
    && !posts = [ a ] (* one wake per signal burst *)
    && E4_trigger.is_signaled t
    && E4_trigger.state t = E4_trigger.Signaled (* TR3: no address is retained *)
    && after = `Already_signaled)

let () =
  let t = E4_trigger.create () in
  let a = { E4_trigger.machine = 9; fiber = 9; token = 9 } in
  let posts = ref 0 in
  E4_trigger.signal t ~post:(fun _ -> incr posts);
  let answer = E4_trigger.await t a in
  check "trigger-signal-before-await"
    (!posts = 0 && answer = `Already_signaled && E4_trigger.is_signaled t
    && E4_trigger.state t = E4_trigger.Signaled)

(* Two domains signalling the same awaited triggers: exactly one post per trigger, so a
   foreign domain signalling twice cannot post a duplicate row (S4). *)
let () =
  let n = 4_000 in
  let ts =
    Array.init n (fun i ->
        let t = E4_trigger.create () in
        (match E4_trigger.await t { E4_trigger.machine = i; fiber = i; token = i } with
        | `Awaiting -> ()
        | `Already_signaled -> failwith "fresh trigger already signaled");
        t)
  in
  let posted = Atomic.make 0 and sum = Atomic.make 0 in
  let signal_all () =
    Array.iter
      (fun t ->
        E4_trigger.signal t ~post:(fun (x : E4_trigger.addr) ->
            ignore (Atomic.fetch_and_add posted 1);
            ignore (Atomic.fetch_and_add sum x.machine)))
      ts
  in
  let d = Domain.spawn signal_all in
  signal_all ();
  Domain.join d;
  check "trigger-double-signal"
    (Atomic.get posted = n
    && Atomic.get sum = n * (n - 1) / 2 (* each address posted exactly once *)
    && Array.for_all (fun t -> E4_trigger.state t = E4_trigger.Signaled) ts)

(* ---- E4_admit: A1 A2 ---- *)

let admit_rank = function E4_admit.None_now -> 0 | E4_admit.Priority_only -> 1 | E4_admit.Any -> 2

let admit_table () =
  List.concat_map
    (fun mailbox_bound ->
      List.concat_map
        (fun mailbox_len ->
          List.map
            (fun in_flight ->
              let t = E4_admit.of_state ~mailbox_len ~mailbox_bound ~in_flight in
              (admit_rank t, E4_admit.admits t ~priority:true, E4_admit.admits t ~priority:false))
            [ 0; 1; 2; 3; 7 ])
        [ 0; 1; 2; 3; 4; 5; 8; 13; 21 ])
    [ 0; 1; 4; 5; 8; 16; 64 ]

(* A1: a pure function of the saved host state. The same arguments answer the same thing
   after the clock moved, after the RNG was drawn from, and on another domain. *)
let () =
  let a = admit_table () in
  ignore (Random.int 1000);
  Unix.sleepf 0.01;
  ignore (Random.int 1000);
  let b = admit_table () in
  let c = Domain.join (Domain.spawn admit_table) in
  check "admit-pure" (List.length a = 7 * 9 * 5 && a = b && a = c)

(* A2: monotone in room — one more element queued never admits more, one more slot of bound
   never admits less, and `admits` respects the order at both priorities. *)
let () =
  let ok = ref true in
  for mailbox_bound = 0 to 24 do
    for in_flight = 0 to 6 do
      for mailbox_len = 0 to 24 do
        let here = E4_admit.of_state ~mailbox_len ~mailbox_bound ~in_flight in
        let fuller = E4_admit.of_state ~mailbox_len:(mailbox_len + 1) ~mailbox_bound ~in_flight in
        let busier = E4_admit.of_state ~mailbox_len ~mailbox_bound ~in_flight:(in_flight + 1) in
        let roomier = E4_admit.of_state ~mailbox_len ~mailbox_bound:(mailbox_bound + 1) ~in_flight in
        if admit_rank fuller > admit_rank here then ok := false;
        if admit_rank busier > admit_rank here then ok := false;
        if admit_rank roomier < admit_rank here then ok := false;
        List.iter
          (fun priority ->
            if E4_admit.admits fuller ~priority && not (E4_admit.admits here ~priority) then ok := false;
            if E4_admit.admits here ~priority && not (E4_admit.admits roomier ~priority) then ok := false)
          [ true; false ]
      done
    done
  done;
  (* and the three bands are all reachable, so the sweep is not vacuous *)
  let bands =
    List.sort_uniq compare
      (List.map (fun len -> admit_rank (E4_admit.of_state ~mailbox_len:len ~mailbox_bound:16 ~in_flight:0))
         [ 0; 12; 16 ])
  in
  check "admit-monotone" (!ok && bands = [ 0; 1; 2 ])

(* ---- B-Q4a: the contended-push fraction (design §4.3) ----
   8 producer domains, 1e5 pushes each, into ONE mailbox against one draining consumer.
   `contended` counts the pushes whose `Mutex.try_lock` failed; the denominator is every
   push attempt (accepted plus refused at the bound). The number is printed; the assertion
   beside it is that nothing was dropped. *)

let () =
  let np = 8 and per = 100_000 in
  let n = np * per in
  let batch = 64 in
  let m = E4_mailbox.create ~bound:4096 () in
  let t0 = Unix.gettimeofday () in
  let prods =
    List.init np (fun p ->
        Domain.spawn (fun () ->
            for i = 0 to per - 1 do
              let x = (p * per) + i in
              let rec push () =
                match E4_mailbox.push m x with
                | Ok () -> ()
                | Error `Full ->
                    Domain.cpu_relax ();
                    push ()
              in
              push ()
            done))
  in
  let count = ref 0 and checksum = ref 0 in
  while !count < n do
    match E4_mailbox.pop_batch m ~max:batch with
    | [] -> Domain.cpu_relax ()
    | xs ->
        List.iter (fun x -> checksum := !checksum + x) xs;
        count := !count + List.length xs
  done;
  List.iter Domain.join prods;
  let dt = Unix.gettimeofday () -. t0 in
  let s = E4_mailbox.stats m in
  let attempts = s.E4_mailbox.pushed + s.E4_mailbox.refused in
  let pct = 100.0 *. float_of_int s.E4_mailbox.contended /. float_of_int attempts in
  Printf.printf
    "     B-Q4a  %d producer domains x %d pushes into one mailbox (bound %d, pop_batch %d)\n\
    \            attempts %d = accepted %d + refused %d ; contended %d = %.3f %%\n\
    \            %.3f s, %.0f accepted pushes/s\n%!"
    np per (E4_mailbox.bound m) batch attempts s.E4_mailbox.pushed s.E4_mailbox.refused
    s.E4_mailbox.contended pct dt
    (float_of_int n /. dt);
  check "bench-q4a-no-drop"
    (!count = n && s.E4_mailbox.pushed = n && s.E4_mailbox.popped = n && s.E4_mailbox.length = 0
    && !checksum = n * (n - 1) / 2)

let () =
  Printf.printf "== %s: %d failure(s) ==\n%!" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
