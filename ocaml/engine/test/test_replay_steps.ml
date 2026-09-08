(* test_replay_steps.ml — lane W, item 3: the two axes of a replay.

   Lane P6's finding F1 (2026-09-08-engine-lane-p6-delivery.md §4): `E4_engine.replay_steps`
   stops consuming the tape once the command residue is non-empty, so a 64-decision tape at
   low fuel yields ONE machine 64 times, and a caller that counted positions counted
   repetitions.  Lean is where that comes from: `replayEval`
   (src/Effect4/Machine/Fibers.lean:2028-2040) answers `stuck why m` on a stuck machine
   WITHOUT applying the decision, and `frontier r.1` after a step that did not settle, and in
   both cases reads no more of the tape.  Past that point Lean defines no machine at all.

   So there are two axes and this file is the difference between them (E4_engine EN4/EN4b):

     the TAPE axis   `replay_steps`      |tape| + 1 machines; position i is `replay` of the
                                         first i decisions; TOTAL, because a viewer and a
                                         differential index by tape position.  Past the stop
                                         the machine is PHYSICALLY the halted one.
     the RUN axis    `replay_positions`  the machines the replay actually visits; it ENDS at
                                         the stop and repeats nothing.
     the stop        `replay_to`         the machine and the decisions never read; the head
                                         of that residue is the REFUSED decision when the
                                         machine is stuck, at position |tape| - |residue|.

   Every law is a named PASS/FAIL line, on BOTH instances (Fast and Ref).  Exit code 0 iff
   every line passed.

   Run: cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine

module E = Eff_types

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ================================================================ the programs *)

let p42 : E.eff = E.Eff_succeed (E.Term_lit (E.Lit_nat 42))

let fork_opts : E.fork_options =
  { E.fork_options_startImmediately = false;
    fork_options_daemon = false;
    fork_options_maskMode = E.Mask_mode_inherit }

let p_fork : E.eff =
  E.Eff_bind
    ( E.Eff_withFiber
        (E.Action_term_fork
           (E.Eff_bind (E.Eff_yieldNow 0, E.Eff_succeed (E.Term_lit (E.Lit_nat 7))), fork_opts)),
      E.Eff_awaitFiber (E.Term_var 0, E.Observer_mode_awaitValue) )

(* A refusal, exhibited: `join` on a fiber the machine never minted halts it with
   `Stuck.unknownFiber` (src/Effect4/Machine/Fibers.lean:1508-1512), and that is the only way
   into `Refused` from a well-formed program -- no decision of the alphabet can do it (R0). *)
let p_await_unknown : E.eff =
  E.Eff_awaitFiber (E.Term_lit (E.Lit_nat 99), E.Observer_mode_awaitValue)

(* the quadratic detector of A1 §6.1 W2, and the program P6 checkpointed: at a small fuel its
   `evaluate` leaves a non-empty command residue, which is the whole of finding F1 *)
let rec chain n : E.eff =
  if n <= 0 then E.Eff_succeed (E.Term_lit E.Lit_unit)
  else E.Eff_bind (E.Eff_perform (E.Native_op_refMake, E.Term_lit (E.Lit_nat (n - 1))), chain (n - 1))

(* ================================================================ the laws, per instance *)

module Laws (En : E4_engine.ENGINE) = struct
  let name = En.name

  (* Two machines are the same when every projection of them is: the answer alphabet, the
     trace, the fiber table and the store row (the projection E4_diff compares). *)
  let same a b =
    En.outcome a = En.outcome b
    && En.trace_rows a = En.trace_rows b
    && En.store_row a = En.store_row b
    && En.fiber_rows a = En.fiber_rows b
    && En.exits a = En.exits b

  let rec nth_tail l k = if k <= 0 then l else match l with [] -> [] | _ :: r -> nth_tail r (k - 1)

  let prefix_of_tape tape k = List.filteri (fun j _ -> j < k) tape

  (* the position the replay stopped at, and the machine it stopped in *)
  let stop t tape =
    let m, residue = En.replay_to t tape in
    (List.length tape - List.length residue, m, residue)

  let is_refused t = match En.answer t with E4_engine.Refused _ -> true | _ -> false
  let is_delay t = match En.answer t with E4_engine.Delay _ -> true | _ -> false

  (* -------------------------------------------------------------- RS1: the tape axis *)

  let rs1 label (p : E.eff) ~fuel tape =
    let t0 = En.load p ~fuel in
    let steps = List.of_seq (En.replay_steps t0 tape) in
    let n = List.length tape in
    let ok_len = List.length steps = n + 1 in
    let ok_prefix =
      ok_len
      && List.for_all
           (fun i -> same (List.nth steps i) (En.replay t0 (prefix_of_tape tape i)))
           (List.init (n + 1) Fun.id)
    in
    let ok_last = ok_len && same (List.nth steps n) (En.replay t0 tape) in
    check
      (Printf.sprintf "RS1 %s/%s: replay_steps is |tape|+1 = %d, position i is replay of the \
                       first i, last is replay" name label (n + 1))
      (ok_len && ok_prefix && ok_last)

  (* ------------------------------------- RS2/RS3: the run axis, and what the tape axis pads *)

  let rs2 label (p : E.eff) ~fuel tape =
    let t0 = En.load p ~fuel in
    let steps = List.of_seq (En.replay_steps t0 tape) in
    let runs = List.of_seq (En.replay_positions t0 tape) in
    let pos, m, residue = stop t0 tape in
    let n = List.length tape in
    (* the run axis is the tape axis truncated at the stop *)
    let ok_len = List.length runs = pos + 1 in
    let ok_prefix =
      ok_len
      && List.for_all (fun i -> same (List.nth runs i) (List.nth steps i)) (List.init (pos + 1) Fun.id)
    in
    let ok_last = ok_len && same (List.nth runs pos) m && same m (En.replay t0 tape) in
    (* the residue is PHYSICALLY the suffix of the tape at that position: `replay_to` hands
       back the cons cell it stopped on, so no decision is copied or invented *)
    let ok_residue = residue == nth_tail tape pos in
    check
      (Printf.sprintf
         "RS2 %s/%s: replay_positions is replay_steps truncated at the stop (%d of %d \
          positions), last = replay, residue is the tape's own suffix"
         name label (pos + 1) (n + 1))
      (ok_len && ok_prefix && ok_last && ok_residue);
    (* past the stop the tape axis PADS, and it pads with the very same machine — physical
       equality, so a caller can tell a repetition from a step for the cost of one compare *)
    let padded = List.filteri (fun i _ -> i > pos) steps in
    let ok_pad = List.for_all (fun t -> t == List.nth steps pos) padded in
    (* and the run axis repeats nothing: `step` allocates, so two consecutive machines of a
       real run are never physically equal *)
    let rec no_repeat = function a :: (b :: _ as r) -> (not (a == b)) && no_repeat r | _ -> true in
    check
      (Printf.sprintf "RS3 %s/%s: the %d padded tape positions are PHYSICALLY the machine at \
                       the stop; the run axis repeats none" name label (List.length padded))
      (ok_pad && no_repeat runs);
    (pos, n, m)

  (* -------------------------------------------------------------- RS4: replay is replay_to *)

  let rs4 label (p : E.eff) ~fuel tape =
    let t0 = En.load p ~fuel in
    let m, _ = En.replay_to t0 tape in
    let steps = List.of_seq (En.replay_steps t0 tape) in
    let runs = List.of_seq (En.replay_positions t0 tape) in
    check
      (Printf.sprintf "RS4 %s/%s: replay = fst replay_to = last replay_steps = last \
                       replay_positions" name label)
      (same m (En.replay t0 tape)
      && same m (List.nth steps (List.length steps - 1))
      && same m (List.nth runs (List.length runs - 1)))
end

module L_fast = Laws (E4_engine.Fast)
module L_ref = Laws (E4_engine.Ref)

(* ================================================================ the cells *)

let () =
  print_endline "== lane W: replay_steps, replay_positions and replay_to (E4_engine EN4/EN4b) ==";
  print_endline "";

  (* ---- 1. the general laws, on both instances, over four (program, fuel, tape) cells ---- *)
  let cells_fast =
    [ ("p42 spent", p42, 1000, [ E4_engine.Fast.evaluate 0; E4_engine.Fast.flush ]);
      ("pFork spent", p_fork, 1000, [ E4_engine.Fast.evaluate 0; E4_engine.Fast.flush ]);
      ( "pFork long",
        p_fork,
        1000,
        [ E4_engine.Fast.evaluate 0; E4_engine.Fast.flush; E4_engine.Fast.flush;
          E4_engine.Fast.fire 0; E4_engine.Fast.yield_verdict 0 true ] );
      ("chain40 low fuel", chain 40, 12, List.init 8 (fun _ -> E4_engine.Fast.evaluate 0));
      ("chain40 empty tape", chain 40, 1000, []) ]
  in
  List.iter
    (fun (l, p, fuel, tape) ->
      L_fast.rs1 l p ~fuel tape;
      ignore (L_fast.rs2 l p ~fuel tape);
      L_fast.rs4 l p ~fuel tape)
    cells_fast;
  print_endline "";
  let cells_ref =
    [ ("p42 spent", p42, 1000, [ E4_engine.Ref.evaluate 0; E4_engine.Ref.flush ]);
      ( "pFork long",
        p_fork,
        1000,
        [ E4_engine.Ref.evaluate 0; E4_engine.Ref.flush; E4_engine.Ref.flush;
          E4_engine.Ref.fire 0; E4_engine.Ref.yield_verdict 0 true ] );
      ("chain40 low fuel", chain 40, 12, List.init 8 (fun _ -> E4_engine.Ref.evaluate 0)) ]
  in
  List.iter
    (fun (l, p, fuel, tape) ->
      L_ref.rs1 l p ~fuel tape;
      ignore (L_ref.rs2 l p ~fuel tape);
      L_ref.rs4 l p ~fuel tape)
    cells_ref;

  (* ---- 2. finding F1 itself, as P6 met it: 64 decisions, one machine ---- *)
  print_endline "";
  print_endline "== finding F1: the 64-decision tape ==";
  let module En = E4_engine.Fast in
  let fuel = 200 in
  let p = chain 2000 in
  let tape = List.init 64 (fun _ -> En.evaluate 0) in
  let t0 = En.load p ~fuel in
  let steps = List.of_seq (En.replay_steps t0 tape) in
  let runs = List.of_seq (En.replay_positions t0 tape) in
  let pos, m, residue = L_fast.stop t0 tape in
  Printf.printf
    "  chain 2000 at fuel %d, a tape of %d `evaluate` decisions: tape positions %d, run \
     positions %d, stop at %d, residue %d, answer %s\n"
    fuel (List.length tape) (List.length steps) (List.length runs) pos (List.length residue)
    (En.outcome m);
  check "F1 the tape axis is still total: 65 machines for a 64-decision tape"
    (List.length steps = 65);
  check "F1 the run axis says what P6 measured: the run has 2 positions, not 65"
    (List.length runs = 2 && pos = 1);
  check "F1 the 63 tape positions past the stop are ONE machine, physically"
    (List.for_all (fun t -> t == List.nth steps 1) (List.filteri (fun i _ -> i > 1) steps));
  check "F1 the machine ran out of fuel (Delay), which is why the replay stopped"
    (L_fast.is_delay m);
  check "F1 the residue is the 63 decisions never read, and it is the tape's own suffix"
    (List.length residue = 63 && residue == L_fast.nth_tail tape 1);
  (* the mutation check: more fuel and the same tape IS a run of many positions, so the two
     axes are not the same thing by accident *)
  let t1 = En.load (chain 40) ~fuel:100000 in
  let tape1 = [ En.evaluate 0; En.flush; En.flush ] in
  let runs1 = List.of_seq (En.replay_positions t1 tape1) in
  check "F1 (mutation) with fuel to spare the same shape of tape is spent: run positions = \
         tape positions"
    (List.length runs1 = List.length tape1 + 1);

  (* ---- 3. the refusal: the decision at the stop is the one never applied ---- *)
  print_endline "";
  print_endline "== the refusal ==";
  (* WHERE A REFUSAL COMES FROM.  `Stuck` has three constructors -- unknownFiber,
     unknownScope, unknownRace (Fibers.lean:382-385) -- and none of them is reachable from the
     DECISION alphabet: `stepDecisionState` (:1962-1982) either drives a command loop or, for
     `interruptFrom` on an id the machine never minted, answers `(m, true)` and changes
     nothing.  The six candidates below are measured and every one of them answers `finished`.
     A refusal comes from a COMMAND: `join` on a fiber that does not exist
     (Fibers.lean:1508-1512) halts the machine with `unknownFiber`.  So the refusal is
     exhibited by a PROGRAM that awaits a fiber id nothing minted, and the tape that reaches
     it is the ordinary one. *)
  let unknown = 97 in
  let decision_candidates =
    [ ("evaluate 97", [ En.evaluate 0; En.evaluate unknown; En.flush; En.flush ]);
      ("fire 97", [ En.evaluate 0; En.fire unknown; En.flush; En.flush ]);
      ("yieldVerdict 97", [ En.evaluate 0; En.yield_verdict unknown true; En.flush; En.flush ]);
      ( "answerAsync 97",
        [ En.evaluate 0; En.answer_async_success unknown 3 1; En.flush; En.flush ] );
      ("interruptFrom 97", [ En.evaluate 0; En.interrupt_from (Some 0) unknown; En.flush; En.flush ]);
      ( "answerAsync 0/unknown token",
        [ En.evaluate 0; En.answer_async_success 0 unknown 1; En.flush; En.flush ] ) ]
  in
  let t_fork = En.load p_fork ~fuel:1000 in
  List.iter
    (fun (l, tp) ->
      let pos, m, _ = L_fast.stop t_fork tp in
      Printf.printf "  pFork + %-26s -> stop at %d of %d, answer %s\n" l pos (List.length tp)
        (En.outcome m))
    decision_candidates;
  check "R0 no decision of the alphabet can refuse on its own: all six candidates answer \
         `finished` (the refusal is a COMMAND's, not a decision's)"
    (List.for_all
       (fun (_, tp) -> let _, m, _ = L_fast.stop t_fork tp in not (L_fast.is_refused m))
       decision_candidates);
  let t2 = En.load p_await_unknown ~fuel:1000 in
  let tape2 = [ En.evaluate 0; En.flush; En.flush; En.fire 0 ] in
  let pos2, m2, _ = L_fast.stop t2 tape2 in
  Printf.printf "  awaitFiber (lit 99) + [evaluate; flush; flush; fire 0] -> stop at %d of %d, \
                 answer %s, root %s\n" pos2 (List.length tape2) (En.outcome m2)
    (match En.root_exit m2 with None -> "<live>" | Some e -> e);
  check
    "R1 nor can a PROGRAM refuse on its own here: `join` on a fiber the machine never minted \
     is Fibers.lean:1508-1512's `unknownFiber`, but no term of this alphabet builds a fiber \
     handle -- `Lit_nat 99` dies with `badName` and the run FINISHES"
    ((not (L_fast.is_refused m2))
    && En.outcome m2 = "finished"
    && En.root_exit m2 = Some "failure [die(badName)]");
  Printf.printf
    "  NOTE the `Refused` arm has NO witness in this alphabet: every `Stuck` constructor \
     (unknownFiber,\n       unknownScope, unknownRace -- Fibers.lean:382-385) names an \
     identity the MACHINE mints, and neither\n       `Eff_types`' terms nor the decision \
     alphabet can spell one it did not.  Lane X's 74 306-position\n       differential found \
     no stuck machine either.  So the stuck half of the stop is `halted`'s first\n       \
     disjunct, licensed by inspection against Fibers.lean:2036, and the half this file \
     MEASURES\n       is the fuel half -- which is the half lane P6 met.\n";
  (* the "not applied" law, on the half that has a witness: at the stop the machine is the
     replay of the decisions BEFORE it, so nothing in the residue has touched it *)
  let t3 = En.load (chain 2000) ~fuel:200 in
  let tape3 = List.init 16 (fun _ -> En.evaluate 0) in
  let pos3, m3, residue3 = L_fast.stop t3 tape3 in
  check
    "R2 at the stop, nothing in the residue has been applied: the machine there is exactly \
     the replay of the decisions before it, and the residue is the tape's OWN suffix"
    (L_fast.same m3 (En.replay t3 (L_fast.prefix_of_tape tape3 pos3))
    && residue3 == L_fast.nth_tail tape3 pos3
    && List.length residue3 = List.length tape3 - pos3
    && List.length residue3 > 0);

  print_endline "";
  Printf.printf "== %s: %d failure(s) in %d checks ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures !checks;
  exit (if !failures = 0 then 0 else 1)
