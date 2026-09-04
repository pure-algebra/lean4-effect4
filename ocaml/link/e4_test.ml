(* e4_test.ml — the property tests behind the `tested` marks in each module's header.
   One line per check: `ok <name>` or `FAIL <name>`; the exit code is the number of
   failures. Run: `dune test --root . --force`. *)

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n%!" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n%!" name
  end

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
    && (E4_mailbox.stats m).refused = 1)

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
    && stats.pushed = producers * per_producer
    && stats.popped = producers * per_producer
    && stats.length = 0)

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
  check "inbox-fifo" (p1 && p2 && p3 && a = Some 1 && b = Some 2 && c = Some 3 && d = None);
  check "inbox-close" ((not (E4_inbox.push ib 4)) && E4_inbox.pop ib = None && E4_inbox.is_closed ib)

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
    && (not c.gap) && c.next = 6 && E4_ring.written r = 6);
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

(* ---- E4_bridge: B2 B3 B4 B5 B6, E4_snapshot: S1 ---- *)

let fuel = 100

let () =
  E4_bridge.init ();
  let ds =
    [ E4_bridge.Evaluate; Flush; Fire 3; Evaluate_fiber 2; Answer { fiber = 0; token = 5; value = 7 } ]
  in
  check "bridge-wire"
    (List.for_all (fun d -> E4_bridge.of_wire (E4_bridge.to_wire d) = Some d) ds
    && E4_bridge.of_wire "fire:0x1" = None
    && E4_bridge.of_wire "answer:1:2" = None
    && E4_bridge.of_wire "fire:-1" = None
    && E4_bridge.of_wire "" = None
    && List.mem "pAwait" (E4_bridge.program_names ()))

let s0 = E4_bridge.load ~program:"pFork" ~fuel
let snap0 = E4_bridge.snapshot s0
let s1 = E4_bridge.step s0 ~fuel E4_bridge.Evaluate
let s2 = E4_bridge.step s1 ~fuel E4_bridge.Flush

let () =
  check "bridge-values"
    (E4_bridge.snapshot s0 = snap0 && E4_bridge.trace_len s0 = 0 && E4_bridge.trace_len s1 > 0
    && E4_bridge.trace_len s2 > E4_bridge.trace_len s1);
  let f1 = E4_bridge.fibers s1 and f2 = E4_bridge.fibers s2 in
  check "bridge-armed-finished"
    (E4_bridge.armed s0 = [] && E4_bridge.armed s1 = [ 0 ]
    && (not (E4_bridge.finished s1))
    && E4_bridge.armed s2 = [] && E4_bridge.finished s2 && List.length f1 = 2 && (List.hd f1).live
    && (List.hd f1).parked_token <> None
    && List.for_all (fun (f : E4_bridge.fiber) -> not f.live) f2
    (* the child exits with nat 7; the root's value is the awaited exit, tagged `value` *)
    && (List.nth f2 1).exit = Some (E4_bridge.Success "nat 7")
    && (match (List.hd f2).exit with Some (E4_bridge.Success _) -> true | _ -> false)
    && E4_bridge.nat_of_tag "nat 7" = Some 7);
  let rows1 = E4_bridge.events s1 ~cursor:0 in
  let n1 = E4_bridge.trace_len s1 in
  let rows2 = E4_bridge.events s2 ~cursor:n1 in
  let all2 = E4_bridge.events s2 ~cursor:0 in
  check "bridge-events-cursor"
    (List.length rows1 = n1
    && E4_bridge.events s1 ~cursor:n1 = []
    && all2 = rows1 @ rows2
    && List.length all2 = E4_bridge.trace_len s2
    && E4_bridge.events s2 ~cursor:2 = List.filteri (fun i _ -> i >= 2) all2)

let t0 = E4_bridge.load ~program:"pTwo" ~fuel
let t1 = E4_bridge.step t0 ~fuel E4_bridge.Evaluate
let t2 = E4_bridge.step t1 ~fuel E4_bridge.Flush
let u0 = E4_bridge.load ~program:"pAwait" ~fuel
let u1 = E4_bridge.step u0 ~fuel E4_bridge.Evaluate

let () =
  let agrees s =
    let p = E4_snapshot.parse (E4_bridge.snapshot s) in
    p.armed = E4_bridge.armed s && p.finished = E4_bridge.finished s
    && p.trace_len = E4_bridge.trace_len s
    && p.fibers = E4_bridge.fibers s
    && p.events = E4_bridge.events s ~cursor:0
    && p.fiber_count = List.length p.fibers
    && List.length p.events = p.trace_len
  in
  check "bridge-snapshot-agrees" (List.for_all agrees [ s0; s1; s2; t0; t1; t2; u0; u1 ]);
  let token =
    match E4_bridge.fibers u1 with
    | { id = 0; live = true; parked_token = Some t; _ } :: _ -> t
    | _ -> -1
  in
  let u2 = E4_bridge.step u1 ~fuel (E4_bridge.Answer { fiber = 0; token; value = 7 }) in
  check "bridge-answer"
    (token >= 0
    && (not (E4_bridge.finished u1))
    && E4_bridge.finished u2
    && (List.hd (E4_bridge.fibers u2)).exit = Some (E4_bridge.Success "nat 7"));
  E4_bridge.release s0;
  let after_release = raises_invalid (fun () -> E4_bridge.step s0 ~fuel E4_bridge.Evaluate) in
  E4_bridge.release s0;
  check "bridge-release"
    (E4_bridge.is_released s0 && after_release && (not (E4_bridge.is_released s1))
    && raises_invalid (fun () -> E4_bridge.snapshot s0));
  List.iter E4_bridge.release [ s1; s2; t0; t1; t2; u0; u1; u2 ]

(* ---- E4_bridge, the bytes path: B7 (name, program_hex, load_hex) ---- *)

(* Hex helpers, and a walker over the canonical framing (`tag :: be64 length :: payload`,
   Effect4.Program.Wire): enough to flip one byte and to carve one sub-frame out of a
   program's bytes. *)
let hex_bytes hex = String.length hex / 2
let hex_byte hex i = int_of_string ("0x" ^ String.sub hex (2 * i) 2)
let hex_slice hex i n = String.sub hex (2 * i) (2 * n)

let hex_set_byte hex i b =
  String.sub hex 0 (2 * i)
  ^ Printf.sprintf "%02x" (b land 0xff)
  ^ String.sub hex (2 * (i + 1)) (String.length hex - (2 * (i + 1)))

(* The length of the frame starting at byte `i`: one tag byte, eight big-endian length
   bytes, then that many payload bytes. *)
let frame_len hex i =
  let len = ref 0 in
  for k = 1 to 8 do
    len := (!len * 256) + hex_byte hex (i + k)
  done;
  9 + !len

(* A session stepped `evaluate` then `flush`; the intermediate is released, the argument is
   not (the caller owns both ends). *)
let evaluate_flush s =
  let a = E4_bridge.step s ~fuel E4_bridge.Evaluate in
  let b = E4_bridge.step a ~fuel E4_bridge.Flush in
  E4_bridge.release a;
  b

(* The snapshot without its `machine <name>` head: what two sessions of the same program
   share whether it was loaded by name or from its bytes. The name is dropped by length,
   not by the first colon — a refusal name (`!refused:decode`) has one of its own. *)
let snapshot_body s =
  let text = E4_bridge.snapshot s in
  let head = "machine " ^ E4_bridge.name s in
  let n = String.length head in
  if String.length text >= n && String.sub text 0 n = head then
    String.sub text n (String.length text - n)
  else text

(* `Ok` never escapes a comparison: a session is abstract (B1) and its custom block has no
   compare. This is the only way this file inspects a `load_hex` answer. *)
let refusal_of hex =
  match E4_bridge.load_hex ~hex ~fuel with
  | Error r -> Some r
  | Ok s ->
      E4_bridge.release s;
      None

let () =
  let s = E4_bridge.load ~program:"pFork" ~fuel in
  let s' = E4_bridge.step s ~fuel E4_bridge.Evaluate in
  let hex = Option.get (E4_bridge.program_hex "pFork") in
  let from_bytes = Result.get_ok (E4_bridge.load_hex ~hex ~fuel) in
  let gone = E4_bridge.load ~program:"p42" ~fuel in
  E4_bridge.release gone;
  check "bridge-name"
    (E4_bridge.name s = "pFork"
    && E4_bridge.name s' = "pFork" (* a step keeps the session's name *)
    && E4_bridge.name from_bytes = E4_bridge.bytes_session_name
    && E4_bridge.program_hex "nope" = None
    && E4_bridge.program_hex "" = None
    && String.length hex > 0
    && String.length hex mod 2 = 0
    && raises_invalid (fun () -> E4_bridge.name gone));
  List.iter E4_bridge.release [ s; s'; from_bytes ]

(* Every program of the table: its canonical bytes decode to a machine that steps exactly
   like the one loaded by name. *)
let () =
  let round_trips program =
    match E4_bridge.program_hex program with
    | None -> false
    | Some hex -> (
        match E4_bridge.load_hex ~hex ~fuel with
        | Error _ -> false
        | Ok from_bytes ->
            let by_name = E4_bridge.load ~program ~fuel in
            let a = evaluate_flush by_name and b = evaluate_flush from_bytes in
            let same =
              E4_bridge.name by_name = program
              && E4_bridge.name from_bytes = E4_bridge.bytes_session_name
              && snapshot_body a = snapshot_body b
              && E4_bridge.armed a = E4_bridge.armed b
              && E4_bridge.finished a = E4_bridge.finished b
              && E4_bridge.trace_len a = E4_bridge.trace_len b
              && E4_bridge.fibers a = E4_bridge.fibers b
              && E4_bridge.events a ~cursor:0 = E4_bridge.events b ~cursor:0
            in
            List.iter E4_bridge.release [ by_name; from_bytes; a; b ];
            same)
  in
  let programs = E4_bridge.program_names () in
  check "bridge-hex-roundtrip" (List.length programs >= 5 && List.for_all round_trips programs)

(* Tampered bytes are refused by name, and the refusal is not a repair: the session Lean
   answers for them holds p42's machine, which is exactly why `load_hex` releases it. *)
let () =
  let hex = Option.get (E4_bridge.program_hex "pFork") in
  let n = hex_bytes hex in
  let cases =
    [
      ("empty", "");
      ("odd-length hex", String.sub hex 0 (String.length hex - 1));
      ("not hex", "zz" ^ String.sub hex 2 (String.length hex - 2));
      ("first byte flipped", hex_set_byte hex 0 (hex_byte hex 0 lxor 0xff));
      ("truncated by one byte", hex_slice hex 0 (n - 1));
      ("truncated by half", hex_slice hex 0 (n / 2));
      ("one trailing byte", hex ^ "00");
      ("the program twice", hex ^ hex);
    ]
  in
  let not_refused =
    List.filter_map
      (fun (what, h) ->
        match refusal_of h with
        | Some E4_bridge.Decode -> None
        | Some r -> Some (what ^ " -> " ^ E4_bridge.pp_refusal r)
        | None -> Some (what ^ " -> loaded"))
      cases
  in
  List.iter (fun s -> Printf.printf "     tamper not refused as decode: %s\n%!" s) not_refused;
  let all_refused = not_refused = [] in
  (* the same tampering through the raw external: a `!refused:` name over p42's machine *)
  let raw = E4_bridge.load_hex_raw (hex ^ "00") fuel in
  let raw_run = evaluate_flush raw in
  let p42 = E4_bridge.load ~program:"p42" ~fuel in
  let p42_run = evaluate_flush p42 in
  let refused_by_name =
    E4_bridge.name raw = "!refused:decode" && snapshot_body raw_run = snapshot_body p42_run
  in
  if not refused_by_name then
    Printf.printf "     one trailing byte: name=%s\n%!" (E4_bridge.name raw);
  List.iter E4_bridge.release [ raw; raw_run; p42; p42_run ];
  check "bridge-hex-refuses" (all_refused && refused_by_name)

(* pBind = bind (succeed (lit (nat 1))) (succeed (app "succ" [var 0])): its second Eff
   sub-frame is a program with a free variable. It decodes exactly, and the typing check is
   what refuses it — so the two refusal reasons are distinguishable, and `load_hex` answers
   which one it was. *)
let () =
  let bind_hex = Option.get (E4_bridge.program_hex "pBind") in
  let index = frame_len bind_hex 9 in
  let first = frame_len bind_hex (9 + index) in
  let at = 9 + index + first in
  let free_var = hex_slice bind_hex at (frame_len bind_hex at) in
  let answer = refusal_of free_var in
  if answer <> Some E4_bridge.Ill_typed then
    Printf.printf "     carved sub-frame at byte %d (%d bytes of %d): %s\n%!" at
      (frame_len bind_hex at) (hex_bytes bind_hex)
      (match answer with None -> "loaded" | Some r -> E4_bridge.pp_refusal r);
  check "bridge-hex-ill-typed" (answer = Some E4_bridge.Ill_typed)

(* Every single-byte flip, over every program of the table: refused, or a different program
   — never silently the one the bytes claimed to be. *)
let () =
  let sweep program =
    let hex = Option.get (E4_bridge.program_hex program) in
    let base = Result.get_ok (E4_bridge.load_hex ~hex ~fuel) in
    let base_run = evaluate_flush base in
    let base_body = snapshot_body base_run in
    E4_bridge.release base;
    E4_bridge.release base_run;
    let refused = ref 0 and other = ref [] and same = ref [] in
    for i = 0 to hex_bytes hex - 1 do
      let flipped = hex_set_byte hex i (hex_byte hex i lxor 0xff) in
      match E4_bridge.load_hex ~hex:flipped ~fuel with
      | Error _ -> incr refused
      | Ok s ->
          let r = evaluate_flush s in
          (* what the flipped byte made of it: the fiber exits of the tampered run *)
          let exits =
            String.concat "/" (List.map (fun (f : E4_bridge.fiber) -> E4_bridge.pp_exit f.exit) (E4_bridge.fibers r))
          in
          if snapshot_body r = base_body then same := (i, exits) :: !same
          else other := (i, exits) :: !other;
          E4_bridge.release s;
          E4_bridge.release r
    done;
    (hex_bytes hex, !refused, List.rev !other, List.rev !same)
  in
  let rows = List.map (fun p -> (p, sweep p)) (E4_bridge.program_names ()) in
  let bytes_at = function
    | [] -> ""
    | is -> " at " ^ String.concat ", " (List.map (fun (i, exits) -> Printf.sprintf "%d [%s]" i exits) is)
  in
  List.iter
    (fun (p, (n, refused, other, same)) ->
      Printf.printf "     %-6s %3d bytes flipped: %3d refused, %d another program%s, %d silently the same%s\n%!"
        p n refused (List.length other) (bytes_at other) (List.length same) (bytes_at same))
    rows;
  check "bridge-hex-tamper"
    (List.for_all
       (fun (_, (n, refused, other, same)) ->
         n > 0 && same = [] && refused > 0 && refused + List.length other = n)
       rows)

(* ---- E4_host / E4_worker / E4_router: W3 W4 R1 R2 R3 H2 H4 H5 ---- *)

let () =
  let host = E4_host.start { E4_host.default_config with domains = 2 } in
  let ids = List.map (fun program -> E4_host.spawn host ~program ~fuel) [ "pFork"; "pTwo"; "pFork"; "pTwo" ] in
  List.iter
    (fun id ->
      ignore (E4_host.send host id E4_bridge.Evaluate);
      ignore (E4_host.send host id E4_bridge.Flush))
    ids;
  let quiescent = E4_host.run_until_quiescent ~timeout:10.0 host in
  let statuses = List.filter_map (fun id -> E4_host.inspect host id) ids in
  let entries, gap = E4_host.events host in
  let of_machine id = List.filter (fun (e : E4_ring.entry) -> e.machine = id) entries in
  let per_machine_monotone =
    List.for_all
      (fun id ->
        let seqs = List.map (fun (e : E4_ring.entry) -> e.seq) (of_machine id) in
        seqs = List.sort compare seqs)
      ids
  in
  let rows_match =
    List.for_all (fun (s : E4_worker.status) -> List.length (of_machine s.id) = s.trace_len) statuses
  in
  let domains_ok =
    List.for_all
      (fun (s : E4_worker.status) -> List.for_all (fun (e : E4_ring.entry) -> e.domain = s.domain) (of_machine s.id))
      statuses
  in
  (* three steps each: evaluate, flush, and the rule's fire:0 (queued after evaluate armed
     the root's dispatcher; a no-op by then, since flush drained it, so it emits no row) *)
  check "host-four-machines"
    (quiescent && List.length statuses = 4
    && List.for_all (fun (s : E4_worker.status) -> s.finished && s.steps = 3) statuses
    && (not gap) && per_machine_monotone && rows_match && domains_ok
    && E4_host.refusals host = 0
    && List.sort compare (List.map (fun id -> Option.get (E4_host.domain_of host id)) ids) = [ 0; 0; 1; 1 ]);
  (* the rule alone: evaluate only, and pFork finishes through fire:0 then fire:1 (W3) *)
  let r = E4_host.spawn host ~program:"pFork" ~fuel in
  ignore (E4_host.send host r E4_bridge.Evaluate);
  let quiescent = E4_host.run_until_quiescent ~timeout:10.0 host in
  let entries, _ = E4_host.events host in
  let decisions =
    List.sort_uniq compare
      (List.map (fun (e : E4_ring.entry) -> (e.seq, e.decision)) (List.filter (fun (e : E4_ring.entry) -> e.machine = r) entries))
  in
  check "host-rule-alone"
    (quiescent
    && (match E4_host.inspect host r with Some { finished = true; steps = 3; _ } -> true | _ -> false)
    && List.map snd decisions = [ "evaluate"; "fire:0"; "fire:1" ]);
  check "host-refusals"
    (E4_host.send host 999 E4_bridge.Evaluate = Error `Unknown
    && raises_invalid (fun () -> E4_host.spawn host ~program:"nope" ~fuel)
    && E4_host.inspect host 999 = None);
  E4_host.shutdown host;
  check "host-stopped" (E4_host.send host (List.hd ids) E4_bridge.Evaluate = Error `Stopped)

let () =
  let host = E4_host.start { E4_host.default_config with domains = 2 } in
  let a = E4_host.spawn ~domain:0 host ~program:"pAwait" ~fuel in
  ignore (E4_host.send host a E4_bridge.Evaluate);
  ignore (E4_host.run_until_quiescent ~timeout:10.0 host);
  let token =
    match E4_host.inspect host a with
    | Some { fibers = { id = 0; parked_token = Some t; _ } :: _; _ } -> t
    | _ -> -1
  in
  let b = E4_host.spawn ~domain:1 host ~program:"pFork" ~fuel in
  let sent = ref None in
  E4_host.subscribe_finished host (fun id ->
      if id = b then
        match E4_host.send host a (E4_bridge.Answer { fiber = 0; token; value = 7 }) with
        | Ok seq -> sent := Some seq
        | Error _ -> ());
  ignore (E4_host.send host b E4_bridge.Evaluate);
  ignore (E4_host.send host b E4_bridge.Flush);
  let quiescent = E4_host.run_until_quiescent ~timeout:10.0 host in
  let a_ok =
    match E4_host.inspect host a with
    | Some { finished = true; fibers = { exit = Some (E4_bridge.Success "nat 7"); _ } :: _; _ } -> true
    | _ -> false
  in
  let entries, _ = E4_host.events host in
  let answer_logged =
    List.exists (fun (e : E4_ring.entry) -> e.machine = a && e.decision = Printf.sprintf "answer:0:%d:7" token) entries
  in
  E4_host.shutdown host;
  check "host-cross-machine" (quiescent && token >= 0 && !sent <> None && a_ok && answer_logged)

let () =
  Printf.printf "%d failure(s)\n%!" !failures;
  exit !failures
