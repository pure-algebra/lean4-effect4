(* test_due.ml — lane Q1's checks of E4_due (the due-resume queue and ORD-FAM).

   What it checks, and against what:
     ORD-FAM     the declaration itself: eight families, ordinals 0..7, total, duplicate-free,
                 ascending, no hole, Deferred at 0 (the byte-identity licence of design §2.2);
     P-U1..P-U4  the property statements of docs/research/2026-09-08-engine-a3-queue-query.md
                 §2.2, over pseudo-random owe/drain sequences (a fixed LCG);
     U5          persistence;
     MUTATION    the discipline design §4.1 asks for: the SAME drain run under a deliberately
                 wrong family order must differ observably, so the law is pinned by a test
                 that goes red and not by a comment.
   Exit code 0 iff every check passed. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n
let sorted l = List.sort compare l
let families = E4_due.families
let nth_family i = List.nth families (i mod E4_due.family_count)

(* A pseudo-random queue, and the (family, payload) pairs that built it. *)
let random_queue ~n ~tag =
  let t = ref E4_due.empty in
  let owed = ref [] in
  for i = 0 to n - 1 do
    let f = nth_family (rand E4_due.family_count) in
    let x = (tag * 1_000_000) + i in
    if rand 4 = 0 then begin
      (* owe_all: the shape a completion uses, `due := due ++ waiters.map ...` *)
      let xs = [ x; x + 100_000; x + 200_000 ] in
      t := E4_due.owe_all !t f xs;
      owed := !owed @ List.map (fun y -> (f, y)) xs
    end
    else begin
      t := E4_due.owe !t f x;
      owed := !owed @ [ (f, x) ]
    end
  done;
  (!t, !owed)

let states = List.init 200 (fun k -> random_queue ~n:(k mod 30) ~tag:k)

(* ============================================================ ORD-FAM *)

let test_ord_fam () =
  print_endline "-- E4_due: ORD-FAM, declared once (design §2.2)";
  let ords = List.map E4_due.ordinal families in
  check "due-ordinals  eight families, ordinals 0..7, ascending, no hole, no duplicate"
    (List.length families = E4_due.family_count
    && E4_due.family_count = 8
    && ords = List.init E4_due.family_count (fun i -> i));
  check "due-ordinals  Deferred is 0 (the byte-identity licence: dueResumes IS deferreds.drainDue)"
    (E4_due.ordinal E4_due.Deferred = 0);
  check "due-ordinals  the declared order is Deferred Timer Memo Queue Semaphore Latch PubSub External"
    (List.map E4_due.name families
    = [ "Deferred"; "Timer"; "Memo"; "Queue"; "Semaphore"; "Latch"; "PubSub"; "External" ]);
  check "due-ordinals  the ordinal is injective (an ordinal is a position in a content table)"
    (List.length (List.sort_uniq compare ords) = E4_due.family_count)

(* ============================================================ P-U1 .. P-U4, U5 *)

let test_properties () =
  print_endline "-- E4_due: the property statements of A3 §2.2";
  (* P-U1: drain = concat (map pending families) *)
  let u1 =
    List.for_all
      (fun (t, _) -> fst (E4_due.drain t) = List.concat (List.map (E4_due.pending t) families))
      states
  in
  check "due-family-order  P-U1 (concatenation in ORD-FAM order)" u1;

  (* P-U1, second half: to_list is every family, ORD-FAM order, empty lists included *)
  let u1b =
    List.for_all
      (fun (t, _) ->
        let l = E4_due.to_list t in
        List.length l = E4_due.family_count
        && List.map fst l = families
        && List.concat (List.map snd l) = fst (E4_due.drain t))
      states
  in
  check "due-family-order  P-U1 (to_list mentions every family, empty lists included)" u1b;

  (* P-U2: owe appends at the tail, and touches no other family *)
  let u2 =
    List.for_all
      (fun (t, _) ->
        let f = nth_family (rand E4_due.family_count) in
        let x = -1 in
        let t' = E4_due.owe t f x in
        E4_due.pending t' f = E4_due.pending t f @ [ x ]
        && List.for_all
             (fun g -> g = f || E4_due.pending t' g = E4_due.pending t g)
             families
        && E4_due.pending (E4_due.owe_all t f [ -2; -3 ]) f = E4_due.pending t f @ [ -2; -3 ])
      states
  in
  check "due-registration-order  P-U2 (owe/owe_all append at the tail, others untouched)" u2;

  (* P-U3: drained once, every family *)
  let u3 =
    List.for_all
      (fun (t, _) ->
        let _, t' = E4_due.drain t in
        E4_due.is_empty t'
        && E4_due.length t' = 0
        && fst (E4_due.drain t') = []
        && List.for_all (fun f -> E4_due.pending t' f = []) families)
      states
  in
  check "due-drained-once  P-U3" u3;

  (* P-U4: exactly once -- the drain is the multiset of what was owed, and its length is
     `length` *)
  let u4 =
    List.for_all
      (fun (t, owed) ->
        let drained = fst (E4_due.drain t) in
        sorted drained = sorted (List.map snd owed)
        && List.length drained = E4_due.length t)
      states
  in
  check "due-exactly-once  P-U4 (every owed resume returned by exactly one drain)" u4;

  (* U5: persistence *)
  let u5 =
    List.for_all
      (fun (t, _) ->
        let before = E4_due.to_list t in
        let n = E4_due.length t in
        let _ = E4_due.owe t E4_due.Timer (-9) in
        let _ = E4_due.drain t in
        E4_due.to_list t = before && E4_due.length t = n)
      states
  in
  check "due-persistent  U5" u5

(* ============================================================ the mutation test *)

(* ORD-FAM with two families swapped: Timer before Deferred. If the concatenation order were
   not the declared one, this order would agree with `drain` and the test below would go
   green -- which is the point (design §4.1, "swap two families in ORD-FAM ... must turn a
   test red"). *)
let swapped =
  [ E4_due.Timer
  ; E4_due.Deferred
  ; E4_due.Memo
  ; E4_due.Queue
  ; E4_due.Semaphore
  ; E4_due.Latch
  ; E4_due.PubSub
  ; E4_due.External
  ]

let test_mutation () =
  print_endline "-- E4_due: the ORD-FAM mutation test";
  (* A witness: Deferred and Timer both owe, and their payloads are distinguishable. *)
  let t =
    E4_due.owe_all
      (E4_due.owe_all E4_due.empty E4_due.Deferred [ 1; 2 ])
      E4_due.Timer [ 3; 4 ]
  in
  let declared = fst (E4_due.drain t) in
  let mutated = E4_due.drain_under t swapped in
  check "due-family-order-mutation  the declared order delivers Deferred first"
    (declared = [ 1; 2; 3; 4 ]);
  check "due-family-order-mutation  swapping Deferred and Timer is OBSERVABLE"
    (mutated = [ 3; 4; 1; 2 ] && mutated <> declared);
  check "due-family-order-mutation  drain_under families IS drain, on every random state"
    (List.for_all
       (fun (t, _) -> E4_due.drain_under t families = fst (E4_due.drain t))
       states);
  (* And the swap is invisible exactly when only one family owes -- which is the licence of
     §2.2: with Deferred alone the trace is byte-identical whatever the other ordinals are. *)
  let only_deferred = E4_due.owe_all E4_due.empty E4_due.Deferred [ 7; 8; 9 ] in
  check "due-family-order  with only Deferred owing, every order agrees (the §2.2 licence)"
    (E4_due.drain_under only_deferred swapped = fst (E4_due.drain only_deferred)
    && fst (E4_due.drain only_deferred) = [ 7; 8; 9 ]);
  note
    "the mutation is run as data (drain_under swapped), so the law is checked by this binary \
     and not by editing e4_due.ml"

let () =
  test_ord_fam ();
  test_properties ();
  test_mutation ();
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
