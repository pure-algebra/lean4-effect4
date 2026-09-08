(* prop_trace.ml — the property tests of E4_trace (lane C, docs/research/
   2026-09-08-engine-a1-state.md §4.3 TR1-TR6, plus TR7 nth_opt and TR8 the twin
   differential; TR9 was added by lane W when `E4_trace` became `E4_log.Vec`).

   Every law of e4_trace.mli is one named PASS/FAIL line.  The twin is e4_trace_list.ml,
   which reproduces `Effect4.Machine.RunMachine.emit` (src/Effect4/Machine/Fibers.lean:585-587)
   verbatim, empty guard included.  Exit code 0 iff every line passed.

   The TRACE module type below is lane G's text (A1 §1.5), verbatim: if either carrier drifts
   from the contract, this file stops compiling. *)

open Effect4_engine

[@@@warning "-32"]
(* A module type used only for an ascription has, by definition, no used values. *)

module type TRACE = sig
  type 'e t

  val empty : 'e t
  val emit : 'e list -> 'e t -> 'e t
  val to_list : 'e t -> 'e list
  val length : 'e t -> int
end

module _ : TRACE = E4_trace
module _ : TRACE = E4_trace_list
[@@@warning "+32"]


module R = E4_trace
module L = E4_trace_list

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let argue name why = Printf.printf "PASS %s [by construction: %s]\n" name why

(* Java's 48-bit LCG (multiplier 25214903917, increment 11): its constants fit a 63-bit
   OCaml int, and the top 32 bits are taken so the weak low bits never reach `rand`. *)
let lcg_mask = 0xFFFFFFFFFFFF
let lcg_seed = 0x1234ABCD5678
let s = ref lcg_seed
let reset () = s := lcg_seed

let next () =
  s := ((!s * 25214903917) + 11) land lcg_mask;
  !s lsr 16

let rand n = if n <= 0 then 0 else next () mod n

(* An emission schedule shaped like the machine's: `emit` is called on the innermost step
   (Fibers.lean:1123) and USUALLY with [] — the empty case is the common one, which is why
   TR2 is a law and not a micro-optimisation. *)
let schedule n =
  reset ();
  List.init n (fun i ->
      match rand 10 with
      | 0 | 1 | 2 | 3 | 4 | 5 -> []
      | 6 | 7 | 8 -> [ i ]
      | _ -> List.init (1 + rand 4) (fun j -> (i * 100) + j))

let tr1_tr8 n =
  let sch = schedule n in
  let expected = ref [] and fast = ref R.empty and slow = ref L.empty in
  let ok1 = ref true and ok8 = ref true in
  List.iter
    (fun evs ->
      expected := !expected @ evs;
      fast := R.emit evs !fast;
      slow := L.emit evs !slow;
      if R.to_list !fast <> !expected then ok1 := false;
      if L.to_list !slow <> R.to_list !fast then ok8 := false)
    sch;
  check (Printf.sprintf "TR1 to_list (emit evs t) = to_list t @ evs (%d emits)" n) !ok1;
  check (Printf.sprintf "TR8 agreement with the list twin (%d emits)" n) !ok8;
  (!fast, !slow, !expected)

let tr2 () =
  reset ();
  let ok = ref true in
  let t = ref R.empty in
  for i = 1 to 500 do
    let t' = R.emit [] !t in
    if not (t' == !t) then ok := false;
    t := R.emit [ i ] !t
  done;
  (* and the twin, which carries the same Lean guard *)
  let u = ref L.empty in
  for i = 1 to 100 do
    if not (L.emit [] !u == !u) then ok := false;
    u := L.emit [ i ] !u
  done;
  check "TR2 emit [] t == t (physically equal, both carriers)" !ok

let tr4 (fast, _, expected) =
  check "TR4 length t = List.length (to_list t), maintained incrementally"
    (R.length fast = List.length expected && R.length fast = List.length (R.to_list fast))

let tr5 () =
  reset ();
  let t = List.fold_left (fun t i -> R.emit [ i; i + 1 ] t) R.empty (List.init 200 (fun i -> i)) in
  let before = R.to_list t and n = R.length t in
  for i = 1 to 500 do
    ignore (R.emit [ i ] t);
    ignore (R.emit [] t);
    ignore (R.to_list t)
  done;
  check "TR5 persistence: t is unchanged by any emit on it" (R.to_list t = before && R.length t = n)

let tr6 () =
  (* Equal event sequences give equal lists, whatever the chunking. *)
  let evs = List.init 300 (fun i -> i) in
  let whole = R.emit evs R.empty in
  let one_by_one = List.fold_left (fun t e -> R.emit [ e ] t) R.empty evs in
  let chunks =
    let rec go t = function
      | [] -> t
      | l ->
          let k = 1 + (List.length l mod 7) in
          let rec split i l = if i = 0 then ([], l) else match l with [] -> ([], []) | x :: r -> let a, b = split (i - 1) r in (x :: a, b) in
          let head, tail = split k l in
          go (R.emit head t) tail
    in
    go R.empty evs
  in
  check "TR6 the reversal is stable: same events, any chunking, same to_list"
    (R.to_list whole = evs && R.to_list one_by_one = evs && R.to_list chunks = evs)

let tr7 (fast, slow, expected) =
  let n = List.length expected in
  let ok = ref true in
  List.iter (fun i -> if R.nth_opt i fast <> None then ok := false) [ -5; -1; n; n + 1; n + 100 ];
  for i = 0 to n - 1 do
    if R.nth_opt i fast <> List.nth_opt expected i then ok := false;
    if L.nth_opt i slow <> R.nth_opt i fast then ok := false
  done;
  check "TR7 nth_opt i t = List.nth_opt (to_list t) i, None outside the range" !ok

(* TR9 — lane W, proposal N2: the carrier is `E4_log.Vec`, so `nth_opt` is a lookup and not a
   walk.  The law is TR7's, taken over a trace LONGER THAN THE CHUNK (6 003 rows against a
   chunk of 256, so 23 frozen chunks and an open tail of 131): every index, in an order that
   is not the walk's, against the list twin AND against the list the trace itself renders.
   The old carrier passes this too — it is a law, not a benchmark — but the time it takes is
   the whole point, and bench_carriers.ml has the number. *)
let tr9 () =
  let n = 6003 in
  let sch =
    reset ();
    List.init n (fun i -> i)
  in
  let fast = List.fold_left (fun t e -> R.emit [ e ] t) R.empty sch in
  let slow = List.fold_left (fun t e -> L.emit [ e ] t) L.empty sch in
  let rendered = R.to_list fast in
  let ok = ref (rendered = sch && R.length fast = n && L.to_list slow = sch) in
  (* forward, backward and a strided order: a carrier that answered only its own walk's
     direction, or only the tail, would be caught by one of the three *)
  let visit i =
    if R.nth_opt i fast <> Some i then ok := false;
    if R.nth_opt i fast <> List.nth_opt rendered i then ok := false;
    if L.nth_opt i slow <> R.nth_opt i fast then ok := false
  in
  for i = 0 to n - 1 do
    visit i
  done;
  for i = n - 1 downto 0 do
    visit i
  done;
  let j = ref 0 in
  for _ = 1 to n do
    visit !j;
    j := (!j + 2731) mod n
  done;
  List.iter (fun i -> if R.nth_opt i fast <> None then ok := false) [ -1; -256; n; n + 255 ];
  (* the chunk boundaries themselves: the last row of a frozen chunk and the first of the
     next, and the first row of the open tail *)
  List.iter
    (fun i -> if i < n && R.nth_opt i fast <> Some i then ok := false)
    [ 0; 255; 256; 511; 512; 5887; 5888 ];
  check
    (Printf.sprintf
       "TR9 nth_opt is the reading axis: %d rows (23 frozen chunks + a tail), every index \
        forward, backward and strided"
       n)
    !ok

let () =
  let st = tr1_tr8 4000 in
  tr2 ();
  tr4 st;
  tr5 ();
  tr6 ();
  tr7 st;
  tr9 ();
  argue "TR3 emit is O(length evs); to_list is O(length t), called once per run"
    "emit is one E4_log.Vec.append per event onto the open chunk (a cons, plus one 256-element array and one Map insertion every 256 events) and never walks t; to_list is one Vec.fold and one List.rev; the numbers are in test/bench_carriers.ml";
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
