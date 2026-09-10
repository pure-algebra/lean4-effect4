(* test_diff.ml -- lane X: the differential over every corpus, three engines.

   The claim of the whole engine effort is that substituting the carriers under the
   generated Lean machine changes nothing that can be observed.  A claim is not a result;
   a differential is (brief §2.1).  This binary runs THREE engines over THREE corpora and
   many tapes and compares thirteen projections at every position of every replay.

   The three engines, and what each pair isolates (A1 §5.2's table):

     Gen   `E4_engine.Make (Api_gen)` -- the UNTOUCHED generated file `ocaml/gen/api_gen.ml`
           with Lean's own List carriers and NO externs at all.  The oracle.
     Ref   `Api_engine.Make (E4_table_list) (E4_trace_list) (E4_memo_list) (E4_buckets_list)`
           -- the seam's generated file over list twins of the four carriers.
     Fast  the same generated file over the substituted carriers.

     Gen vs Ref   catches a wrong EXTERN ROW: the two files differ only in that 35 rows of
                  `ocaml/engine/externs.txt` replaced generated bodies with hand ones.
                  This is lane G's owed N1 and lane D's N2.
     Ref vs Fast  catches a wrong CARRIER LAW: the two are one generated file applied to
                  two carrier sets.  This is lane D's check 2, widened to every corpus and
                  every tape.

   The corpora (`Corpora`): the 37 byte goldens, the truth corpus (the Lean-cut wire
   goldens of harness/truth/corpus.json plus its two members that only have a `.bin`), and
   500 generated well-typed `Eff` programs with random ADMISSIBLE tapes (owner default
   A1-Q4).  Every tape names only fiber ids and park tokens the machine has shown, so a
   `Stuck` answer is always a fact about the program.

   Run: cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note s = Printf.printf "  NOTE %s\n" s

(* ==================================================================== the third engine *)

(* `Api_gen` is not an `E4_engine.INSTANCE` as it stands: the drive loop needs the fully
   applied type abbreviations and the 38 free-row projections.  They are one line each and
   they are the ONLY lines that name a carrier, exactly as `api_engine_inst.ml` says --
   here every carrier is Lean's own list, so each projection is a `List` operation.  The
   ascription `E4_engine.Make (Api_gen_inst)` is itself a check: `ocamlopt` compares the
   hand transcriptions of `E4_program.PROGRAM_TYPES` and `E4_engine.INSTANCE` against the
   generated file of the OTHER route, so a constructor that drifted between
   `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml` is a compile error here. *)
module Api_gen_inst = struct
  include Effect4_gen.Api_gen

  let name = "Gen"
  let carriers = "ocaml/gen/api_gen.ml as generated: List everywhere, no externs"

  type nu = eff_name
  type s = eff_thunk
  type prim_ = (nu, s, val_, err, defect, fiber_id, unit) prim
  type ffiber = (nu, s, val_, err, defect, fiber_id, unit) frame_fiber
  type fevent = (nu, s, val_, err, defect, fiber_id, unit) frame_event

  type machine =
    (nu, s, val_, err, defect, fiber_id, unit, ctx, stores, prim_, ffiber, fevent) run_machine

  type fiber = (nu, s, val_, err, defect, fiber_id, unit, ctx, prim_, ffiber) run_fiber
  type event = (nu, s, val_, err, defect, fiber_id, unit, ctx, prim_, fevent) run_event
  type decision = (nu, s, val_, err, defect, fiber_id, unit) run_decision

  type interp =
    (nu, s, val_, err, defect, fiber_id, unit, ctx, stores, prim_) run_interp

  type program = native_op eff

  let interp_of (p : program) : interp = program_interp_of p []
  let load (p : program) ~(fuel : int) ~(choices : bool list) : machine =
    api_load p fuel choices []

  (* `Effect4.Machine.stepDecisionState` at `Api.replay`'s specialisation
     (api_gen.ml); the bool is `Effect4.Machine.settled`. *)
  let step (p : program) (i : interp) ~(fuel : int) (m : machine) (d : decision)
    : machine * bool =
    step_decision_state_at_program_replay_checked_from_spec_1 p [] i fuel m d

  let run_api (p : program) ~(fuel : int) ~(choices : bool list) : outcome * machine =
    let r = api_run p fuel choices [] [] in
    (r.outcome, r.machine)

  let fibers (m : machine) : (fiber_id * fiber) list =
    List.map (fun (f : fiber) -> (f.id, f)) m.fibers

  let fiber_count (m : machine) : int = List.length m.fibers
  let trace (m : machine) : event list = m.trace
  let trace_length (m : machine) : int = List.length m.trace
  let stuck_of (m : machine) : stuck option = m.stuck
  let armed_of (m : machine) : fiber_id list = m.armed
  let next_id (m : machine) : int = m.next_id
  let next_token (m : machine) : int = m.next_token
  let race_count (m : machine) : int = List.length m.races
  let middleware (m : machine) : bool = m.middleware_installed
  let finished (m : machine) : bool = run_machine_finished m

  let completed_exits (m : machine)
    : (fiber_id * (val_, err, defect, fiber_id, unit) exit_) list =
    run_machine_completed_exits m

  let stores_of (m : machine) : stores = m.state
  let refs (m : machine) : val_ list = (stores_of m).refs
  let next_name (m : machine) : int = (stores_of m).next_name
  let due_count (m : machine) : int = List.length (stores_of m).deferreds.due
  let cell_count (m : machine) : int = List.length (stores_of m).deferreds.cells
  let scope_count (m : machine) : int = List.length (stores_of m).scopes
  let memo_map_count (m : machine) : int = List.length (stores_of m).memo

  let memo_paths (m : machine) : (int * int list list) list =
    List.map
      (fun (mm : memo_map) -> (mm.id, List.map fst mm.entries))
      (stores_of m).memo

  let f_id (f : fiber) : fiber_id = f.id
  let f_exit (f : fiber) : (val_, err, defect, fiber_id, unit) exit_ option = f.exit_
  let f_parked (f : fiber) : parked = f.parked
  let f_running (f : fiber) : bool = f.running
  let f_finalizing (f : fiber) : bool = Option.is_some f.finalizing

  let f_pending_tokens (f : fiber) : int list =
    List.map (fun (p : (_, _, _, _, _, _) pending) -> p.token) f.pending

  let f_observers (f : fiber) : observer list = f.observers
  let f_children (f : fiber) : fiber_id list = f.children
  let f_op_count (f : fiber) : int = f.current_op_count
  let f_max_ops (f : fiber) : int = f.max_ops_before_yield
  let f_prevent_yield (f : fiber) : bool = f.prevent_yield
  let f_yield_override (f : fiber) : bool option = f.yield_override
  let f_context (f : fiber) : ctx = f.context
  let f_dispatcher_armed (f : fiber) : bool = f.dispatcher.armed

  let f_dispatcher (f : fiber) : (int * int) list =
    List.map
      (fun (b : (_, _, _, _, _, _, _, _) bucket) -> (b.priority, List.length b.tasks))
      f.dispatcher.buckets
end

module Gen_engine = E4_engine.Make (Api_gen_inst)

module S_gen = E4_diff.Of (Gen_engine)
module S_ref = E4_diff.Of (E4_engine.Ref)
module S_fast = E4_diff.Of (E4_engine.Fast)

(* ==================================================================== the comparison *)

type tally = {
  mutable t_programs : int;
  mutable t_tapes : int;
  mutable t_positions : int;
  mutable t_pairs : int;  (** projection-vs-projection comparisons made *)
  mutable t_div : int;
  mutable t_errors : int;
  mutable t_maxlen : int;
}

let fresh () = { t_programs = 0; t_tapes = 0; t_positions = 0; t_pairs = 0; t_div = 0;
                 t_errors = 0; t_maxlen = 0 }

let shown = ref 0

let report_divergence corpus pname pair tape pos (ds : E4_diff.divergence list) =
  incr shown;
  if !shown <= 5 then begin
    Printf.printf "  DIVERGENCE %s/%s  pair=%s  position=%d\n" corpus pname pair pos;
    Printf.printf "    tape = %s\n" (E4_diff.show_tape tape);
    List.iter (fun d -> Printf.printf "    %s\n" (E4_diff.show_divergence d)) ds
  end

(* One (program, tape): the three engines' projections at every position, compared
   pairwise in the order that isolates the extern rows first and the carriers second. *)
let one_pair (t : tally) (corpus : string) (p : Corpora.program)
    (tape : E4_diff.decision list) ~(fuel : int) : unit =
  t.t_tapes <- t.t_tapes + 1;
  if List.length tape > t.t_maxlen then t.t_maxlen <- List.length tape;
  match
    ( (try Ok (S_gen.positions p.Corpora.eff ~fuel tape) with e -> Error e),
      (try Ok (S_ref.positions p.Corpora.eff ~fuel tape) with e -> Error e),
      (try Ok (S_fast.positions p.Corpora.eff ~fuel tape) with e -> Error e) )
  with
  | Ok g, Ok r, Ok f ->
    let n = List.length g in
    if n <> List.length tape + 1 then begin
      t.t_div <- t.t_div + 1;
      Printf.printf "  DIVERGENCE %s/%s: replay_steps gave %d machines for a tape of %d\n"
        corpus p.Corpora.name n (List.length tape)
    end;
    if List.length r <> n || List.length f <> n then begin
      t.t_div <- t.t_div + 1;
      Printf.printf "  DIVERGENCE %s/%s: position counts %d/%d/%d\n" corpus p.Corpora.name n
        (List.length r) (List.length f)
    end
    else begin
      t.t_positions <- t.t_positions + n;
      List.iteri
        (fun i gi ->
           let ri = List.nth r i and fi = List.nth f i in
           t.t_pairs <- t.t_pairs + 2;
           let d1 = E4_diff.compare gi ri in
           if d1 <> [] then begin
             t.t_div <- t.t_div + 1;
             report_divergence corpus p.Corpora.name "Gen-vs-Ref" tape i d1
           end;
           let d2 = E4_diff.compare ri fi in
           if d2 <> [] then begin
             t.t_div <- t.t_div + 1;
             report_divergence corpus p.Corpora.name "Ref-vs-Fast" tape i d2
           end)
        g
    end
  | g, r, f ->
    (* An engine that RAISES where another answers is itself a divergence, and one that
       raises where all three raise is a fact about the program, reported not hidden. *)
    let sh = function Ok _ -> "ok" | Error e -> Printexc.to_string e in
    t.t_errors <- t.t_errors + 1;
    let all_err = match g, r, f with Error _, Error _, Error _ -> true | _ -> false in
    if not all_err then t.t_div <- t.t_div + 1;
    if !shown <= 5 then begin
      incr shown;
      Printf.printf "  RAISED %s/%s  Gen=%s Ref=%s Fast=%s\n    tape = %s\n" corpus
        p.Corpora.name (sh g) (sh r) (sh f) (E4_diff.show_tape tape)
    end

let run_corpus (corpus : string) (progs : Corpora.program list)
    (tapes_of : Corpora.program -> (int * E4_diff.decision list) list) : tally * float =
  let t = fresh () in
  let t0 = Sys.time () in
  List.iter
    (fun p ->
       t.t_programs <- t.t_programs + 1;
       List.iter (fun (fuel, tape) -> one_pair t corpus p tape ~fuel) (tapes_of p))
    progs;
  (t, Sys.time () -. t0)

let verdict (corpus : string) ((t, secs) : tally * float) =
  Printf.printf
    "  %s: %d programs x %d tapes (longest %d decisions), %d positions, %d projection \
     comparisons (2 pairs each position), %d raised, %.2f s\n"
    corpus t.t_programs t.t_tapes t.t_maxlen t.t_positions t.t_pairs t.t_errors secs;
  check (Printf.sprintf "%s: 0 divergences" corpus) (t.t_div = 0)

(* ==================================================================== the corpora *)

let show_report (r : Corpora.load_report) =
  Printf.printf "  %s: %d files, %d decoded%s\n" r.Corpora.lr_dir r.Corpora.lr_found
    r.Corpora.lr_decoded
    (if r.Corpora.lr_refused = [] then ""
     else " -- REFUSED: " ^ String.concat " " r.Corpora.lr_refused)

(* Every corpus gets the `Api.run` tape; the generated corpus also gets random admissible
   tapes drawn from the machine as it runs (A1 §6.3's T5, made admissible by construction).
   The tape is drawn on ONE engine and applied to all three: if the engines disagree about
   what is admissible, the projections diverge and the differential says so. *)
(* THE FUEL SWEEP is what exercises `Delay` (E4_engine EN-Delay, A1 §5.1): at fuel 10 the
   drive loop returns with a NON-EMPTY command residue, `settled = false`, and the answer
   is the letter `Api.Outcome` does not have.  p3_settled and p4_answer of the projection
   are exactly that discriminator, so a fuel-starved run compares something the fuel-1000
   run cannot. *)
let gen_tape_seed = ref 0

let tapes_for_generated (p : Corpora.program) : (int * E4_diff.decision list) list =
  incr gen_tape_seed;
  let s = !gen_tape_seed in
  [ (1000, E4_diff.drive_tape);
    (20, E4_diff.drive_tape);
    (1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(20260908 + s) ~max_len:64);
    (1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(51000 + (s * 3)) ~max_len:32);
    (100, S_ref.gen_tape p.Corpora.eff ~fuel:100 ~seed:(77000 + (s * 7)) ~max_len:16);
    (10, S_ref.gen_tape p.Corpora.eff ~fuel:10 ~seed:(99000 + (s * 11)) ~max_len:8) ]

(* Random tapes on the byte corpora too: the same drawing -- these are the real programs,
   so the tapes reach real frontiers, real park tokens and real armed dispatchers. *)
let bytes_tape_seed = ref 0

let tapes_for_bytes_random (p : Corpora.program) : (int * E4_diff.decision list) list =
  incr bytes_tape_seed;
  let s = !bytes_tape_seed in
  [ (1000, E4_diff.drive_tape);
    (100, E4_diff.drive_tape);
    (10, E4_diff.drive_tape);
    (1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(31337 + s) ~max_len:64);
    (1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(90210 + (s * 13)) ~max_len:48);
    (1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(60613 + (s * 17)) ~max_len:32);
    (100, S_ref.gen_tape p.Corpora.eff ~fuel:100 ~seed:(11235 + (s * 5)) ~max_len:24);
    (10, S_ref.gen_tape p.Corpora.eff ~fuel:10 ~seed:(4242 + (s * 3)) ~max_len:16) ]

(* ==================================================================== the cross face *)

(* D4 of A1 §6.3: the truth corpus records what LEAN answered for each program at fuel
   1000.  The engines are compared with that, not only with each other.  It is reported,
   not gated: 2 of the 8 Lean-cut goldens are different programs that carry the same name
   as a `.bin` golden (eff/README.md), so a disagreement here is a fact to name, not a
   failure of the engine. *)
let cross_face (progs : Corpora.program list) =
  print_endline "";
  print_endline "== the cross face: the engines against harness/truth/corpus.json ==";
  match Corpora.truth_expectations () with
  | Error m -> note ("corpus.json not read: " ^ m)
  | Ok es ->
    Printf.printf "  corpus.json: %d programs recorded at fuel 1000\n" (List.length es);
    let agree = ref 0 and disagree = ref 0 and absent = ref 0 in
    List.iter
      (fun (p : Corpora.program) ->
         match List.find_opt (fun e -> e.Corpora.te_name = p.Corpora.name) es with
         | None -> incr absent
         | Some e -> (
           match (try Some (Gen_engine.run p.Corpora.eff ~fuel:1000) with _ -> None) with
           | None -> incr disagree
           | Some t ->
             let outcome = Gen_engine.outcome t in
             let fibers = Gen_engine.fiber_count t in
             let root = Gen_engine.root_exit t in
             let kind =
               match root with
               | None -> "none"
               | Some s ->
                 if String.length s >= 7 && String.sub s 0 7 = "success" then "success"
                 else "failure"
             in
             let want_kind = if e.Corpora.te_exit_kind = "success" then "success" else "failure" in
             let ok =
               outcome = e.Corpora.te_outcome && fibers = e.Corpora.te_fibers
               && (outcome <> "finished" || kind = want_kind)
             in
             if ok then incr agree
             else begin
               incr disagree;
               Printf.printf
                 "  DIFFERS %-14s engine: outcome=%s fibers=%d exit=%s | lean: outcome=%s \
                  fibers=%d exitKind=%s\n"
                 p.Corpora.name outcome fibers
                 (match root with None -> "-" | Some s -> s)
                 e.Corpora.te_outcome e.Corpora.te_fibers e.Corpora.te_exit_kind
             end))
      progs;
    Printf.printf "  agree=%d  differ=%d  not in corpus.json=%d\n" !agree !disagree !absent;
    note
      (Printf.sprintf
         "reported, not gated: %d of the truth programs agree with Lean's recorded run"
         !agree)

(* ==================================================================== main *)

let () =
  print_endline "== lane X: the differential over every corpus, three engines ==";
  Printf.printf "  Gen  = %s\n" Gen_engine.carriers;
  Printf.printf "  Ref  = %s\n" E4_engine.Ref.carriers;
  Printf.printf "  Fast = %s\n" E4_engine.Fast.carriers;
  print_endline "";

  (* -------------------------------------------------------------- 1. the byte goldens *)
  print_endline "== 1. ocaml/eff/goldens: the 37 byte goldens (fuel 1000) ==";
  let goldens, grep = Corpora.goldens () in
  show_report grep;
  check "the byte corpus decodes: 48 programs" (List.length goldens = 48);
  let tg = run_corpus "goldens" goldens tapes_for_bytes_random in
  verdict "goldens" tg;

  (* -------------------------------------------------------------- 2. the truth corpus *)
  print_endline "";
  print_endline "== 2. the truth corpus: the Lean-cut wire goldens (fuel 1000) ==";
  let truth, trep, missing = Corpora.truth () in
  show_report trep;
  Printf.printf "  truth programs with canonical bytes: %d of %d (%s)\n"
    (List.length truth) (List.length Corpora.truth_names)
    (String.concat "," (List.map (fun (p : Corpora.program) -> p.Corpora.name) truth));
  if missing <> [] then
    note
      ("no canonical bytes anywhere in the tree for: " ^ String.concat " " missing
     ^ " -- they are TypeScript declarations in corpus.json and Lean has not cut their \
        wire, so they cannot enter a byte-driven differential");
  check "the truth corpus has at least the 8 Lean-cut goldens" (List.length truth >= 8);
  let tt = run_corpus "truth" truth tapes_for_bytes_random in
  verdict "truth" tt;

  (* -------------------------------------------------------------- 3. the generator *)
  print_endline "";
  print_endline "== 3. the generated corpus: 500 well-typed random Eff programs ==";
  let gen, grpt = Corpora.generate ~seed:20260908 ~count:500 ~max_depth:12 () in
  Printf.printf
    "  seed=%d asked=%d drawn=%d refused-by-the-net=%d (%.2f%%) deepest=%d produced=%d\n"
    grpt.Corpora.gr_seed grpt.Corpora.gr_asked grpt.Corpora.gr_draws
    grpt.Corpora.gr_refused
    (100.0 *. float_of_int grpt.Corpora.gr_refused
    /. float_of_int (max 1 grpt.Corpora.gr_draws))
    grpt.Corpora.gr_max_depth (List.length gen);
  check "the generator produced 500 well-typed programs" (List.length gen = 500);
  check "every generated program satisfies Eff_typing.well_typed"
    (List.for_all (fun (p : Corpora.program) -> Eff_typing.well_typed p.Corpora.eff) gen);
  (* The generated corpus is a real corpus, not an in-memory artefact: every program has
     canonical bytes and comes back from them unchanged (brief §2.2, identity IS the
     bytes).  Anything the generator can build, the wire can carry. *)
  check "every generated program round-trips through the canonical wire"
    (List.for_all
       (fun (p : Corpora.program) ->
          match p.Corpora.bytes with
          | Some b -> Eff_wire.decode_program_exact b = Some p.Corpora.eff
          | None -> false)
       gen);
  let cen = Corpora.census gen in
  print_endline "  coverage (constructor occurrences over the 500 programs):";
  List.iter (fun (k, v) -> Printf.printf "    %-32s %d\n" k v) cen;
  let miss = Corpora.census_missing cen in
  if miss = [] then print_endline "  every Eff / ActionTerm / Stmt / NativeOp constructor appears"
  else note ("never generated: " ^ String.concat " " miss);
  let tgen = run_corpus "generated" gen tapes_for_generated in
  verdict "generated" tgen;

  (* -------------------------------------------------------------- 4. FB1 and DF-2 *)
  print_endline "";
  print_endline "== 4. the owed rows ==";
  (* Lane C's OWED FB1: `E4_fibers.to_list` = api_gen's `m.fibers` over the corpus.  The
     fiber-table projection is p6 (ids, in machine order) and p9 (the rows) of every
     comparison above, so FB1 is discharged by the goldens tally -- but say it in its own
     words, over the 37 goldens at the `Api.run` tape. *)
  let fb1 = ref 0 and fb1_bad = ref 0 in
  List.iter
    (fun (p : Corpora.program) ->
       match
         ( (try Some (S_gen.positions p.Corpora.eff ~fuel:1000 E4_diff.drive_tape) with _ -> None),
           (try Some (S_fast.positions p.Corpora.eff ~fuel:1000 E4_diff.drive_tape) with _ -> None) )
       with
       | Some g, Some f ->
         let gl = List.nth g (List.length g - 1) and fl = List.nth f (List.length f - 1) in
         incr fb1;
         if
           gl.E4_diff.p6_fiber_ids <> fl.E4_diff.p6_fiber_ids
           || gl.E4_diff.p9_fiber_rows <> fl.E4_diff.p9_fiber_rows
         then incr fb1_bad
       | _ -> incr fb1_bad)
    goldens;
  check
    (Printf.sprintf
       "FB1 (lane C, owed): E4_fibers.to_list = api_gen's m.fibers, ids AND rows, on %d/%d \
        goldens"
       (!fb1 - !fb1_bad) (List.length goldens))
    (!fb1_bad = 0 && !fb1 = List.length goldens);
  note
    "DF-2 (A3 §4.2, the family order byte-identical with only Deferred owing) is NOT \
     RUN: `E4_due` is not wired into the engine. ocaml/engine/externs.txt has no row for \
     `Effect4.Machine.DeferredStore.due` and none for E4_due's drain, so the due list in \
     `api_engine.ml` is still the generated one and the substitution DF-2 is about does \
     not exist yet. What stands in its place today is lane Q1's own \
     due-family-order-mutation test, and the fact that every machine in all three corpora \
     above owes only Deferred resumes (there is no Timer/Queue/Semaphore family in the \
     Lean machine yet), so ORD-FAM is vacuous here by construction.";
  note
    "DF-3 (query agreement, `E4_query.at s i` = `api_replay` of the first i) waits on lane \
     Q3 and is out of this lane's scope. The half of it that exists -- `replay_steps` at \
     position i equals a replay of the first i decisions -- is what every position of \
     every tape above compares, on three engines.";

  (* -------------------------------------------------------------- 5. the mutations *)
  print_endline "";
  print_endline "== 5. the comparison has teeth: one mutation per field ==";
  (match List.find_opt (fun (p : Corpora.program) -> p.Corpora.name = "pFork") goldens with
   | None -> note "pFork is not in the byte corpus; the mutation check did not run"
   | Some pf ->
     let ps = S_fast.positions pf.Corpora.eff ~fuel:1000 E4_diff.drive_tape in
     let b = List.nth ps (List.length ps - 1) in
     check "compare p p = [] (the projection is equal to itself)" (E4_diff.compare b b = []);
     let bump s = s ^ "!" in
     let at i f xs = List.mapi (fun j x -> if j = i then f x else x) xs in
     let muts : (string * int option * (E4_diff.projection -> E4_diff.projection)) list =
       [ ("p1_outcome", None, fun p -> { p with E4_diff.p1_outcome = bump p.E4_diff.p1_outcome });
         ("p2_stuck", None, fun p -> { p with E4_diff.p2_stuck = Some "unknownFiber 9" });
         ("p3_settled", None, fun p -> { p with E4_diff.p3_settled = not p.E4_diff.p3_settled });
         ("p4_answer", None, fun p -> { p with E4_diff.p4_answer = bump p.E4_diff.p4_answer });
         ("p5_fiber_count", None,
          fun p -> { p with E4_diff.p5_fiber_count = p.E4_diff.p5_fiber_count + 1 });
         ("p6_fiber_ids", Some 0,
          fun p -> { p with E4_diff.p6_fiber_ids = at 0 (fun i -> i + 100) p.E4_diff.p6_fiber_ids });
         ("p7_exits", Some 0,
          fun p -> { p with E4_diff.p7_exits = at 0 (fun (i, s) -> (i, bump s)) p.E4_diff.p7_exits });
         ("p8_root_exit", None, fun p -> { p with E4_diff.p8_root_exit = Some "success 999" });
         ("p9_fiber_rows", Some 1,
          fun p ->
            { p with E4_diff.p9_fiber_rows = at 1 (fun (i, s) -> (i, bump s)) p.E4_diff.p9_fiber_rows });
         ("p10_armed", None, fun p -> { p with E4_diff.p10_armed = bump p.E4_diff.p10_armed });
         ("p11_trace_length", None,
          fun p -> { p with E4_diff.p11_trace_length = p.E4_diff.p11_trace_length + 1 });
         ("p12_trace_rows", Some 7,
          fun p -> { p with E4_diff.p12_trace_rows = at 7 bump p.E4_diff.p12_trace_rows });
         ("p13_store_row", None,
          fun p -> { p with E4_diff.p13_store_row = bump p.E4_diff.p13_store_row }) ]
     in
     Printf.printf "  base = pFork at the end of [evaluate 0; flush], fuel 1000: %d fibers, \
                    %d trace rows\n"
       b.E4_diff.p5_fiber_count b.E4_diff.p11_trace_length;
     List.iter
       (fun (field, idx, mut) ->
          let d = E4_diff.compare b (mut b) in
          let ok =
            match d with
            | [ x ] -> x.E4_diff.d_field = field && x.E4_diff.d_index = idx
            | _ -> false
          in
          check
            (Printf.sprintf "mutating %s is caught, and only it%s" field
               (match idx with None -> "" | Some i -> Printf.sprintf " (at index %d)" i))
            ok)
       muts);

  (* -------------------------------------------------------------- 6. the cross face *)
  cross_face truth;

  (* -------------------------------------------------------------- the totals *)
  let tot f = f (fst tg) + f (fst tt) + f (fst tgen) in
  print_endline "";
  Printf.printf
    "== totals: %d programs, %d tapes, %d positions, %d projection comparisons, %d \
     divergences, %.2f s ==\n"
    (tot (fun t -> t.t_programs))
    (tot (fun t -> t.t_tapes))
    (tot (fun t -> t.t_positions))
    (tot (fun t -> t.t_pairs))
    (tot (fun t -> t.t_div))
    (snd tg +. snd tt +. snd tgen);
  if !failures = 0 then
    Printf.printf "== ALL PASS: 0 failure(s) == (%d checks)\n" !checks
  else Printf.printf "== FAILED: %d failure(s) in %d checks ==\n" !failures !checks;
  if !failures > 0 then exit 1
