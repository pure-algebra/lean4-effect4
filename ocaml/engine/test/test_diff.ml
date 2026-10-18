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
   the Lean corpus -- the programs `make corpus` prints under `.lake/corpus` from Lean's
   own seeded generator (`Test.Program.Gen`, 400 at depth 4, plus the wire corpus), as the
   bytes `Wire.encodeProgram` cut, well typed and ill-typed alike with Lean's verdict
   beside each.  The random tapes are ADMISSIBLE by construction: every tape names only
   fiber ids and park tokens the machine has shown, so a `Stuck` answer is always a fact
   about the program.

   Properties (tested by the classification controls below): profile refusals and
   unexpected exceptions prevent successful differential validation, including when
   all three engines refuse; neither is counted as a semantic divergence. Every
   refusal/exception report retains the named engine and its diagnostic.

   Run: make check-ocaml (which writes the Lean corpus first), or by hand
        make corpus && cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures
;;

let note s = Printf.printf "  NOTE %s\n" s

(* ==================================================================== the third engine *)

(* The third engine is `Api_gen_inst` (api_gen_inst.ml, beside this file): the generated machine
   as an `E4_engine.INSTANCE`. *)

module Gen_engine = E4_engine.Make (Api_gen_inst)
module S_gen = E4_diff.Of (Gen_engine)
module S_ref = E4_diff.Of (E4_engine.Ref)
module S_fast = E4_diff.Of (E4_engine.Fast)

(* ==================================================================== the comparison *)

type tally =
  { mutable t_programs : int
  ; mutable t_tapes : int
  ; mutable t_positions : int
  ; mutable t_pairs : int (** projection-vs-projection comparisons made *)
  ; mutable t_div : int
  ; mutable t_errors : int (** tapes with an unexpected exception *)
  ; mutable t_profile_refusals : int (** tapes refused by at least one profile *)
  ; mutable t_maxlen : int
  }

let fresh () =
  { t_programs = 0
  ; t_tapes = 0
  ; t_positions = 0
  ; t_pairs = 0
  ; t_div = 0
  ; t_errors = 0
  ; t_profile_refusals = 0
  ; t_maxlen = 0
  }
;;

(* Refusing a target profile is not an observed machine result. A mixed refusal
   and unexpected exception records both reasons that this tape was not compared. *)
type 'a run_classification =
  | Comparable of 'a * 'a * 'a
  | Incomplete of
      { profile_refused : bool
      ; raised : bool
      }

let classify_runs (t : tally) (g, r, f) =
  match g, r, f with
  | Ok g, Ok r, Ok f -> Comparable (g, r, f)
  | _ ->
    let profile_refused, raised =
      List.fold_left
        (fun (profile, raised) -> function
           | Ok _ -> profile, raised
           | Error (E4_clock.Profile_refusal _) -> true, raised
           | Error _ -> profile, true)
        (false, false)
        [ g; r; f ]
    in
    if profile_refused then t.t_profile_refusals <- t.t_profile_refusals + 1;
    if raised then t.t_errors <- t.t_errors + 1;
    Incomplete { profile_refused; raised }
;;

let differential_valid (t : tally) =
  t.t_div = 0 && t.t_profile_refusals = 0 && t.t_errors = 0
;;

let classification_controls () =
  let refused =
    Error
      (E4_clock.Profile_refusal
         { E4_clock.crossing = E4_clock.Reply; reason = "classification control" })
  in
  let raised = Error (Failure "classification control") in
  let incomplete name runs ~profile ~error =
    let t = fresh () in
    let classified =
      match classify_runs t runs with
      | Comparable _ -> false
      | Incomplete { profile_refused; raised } ->
        profile_refused = profile && raised = error
    in
    check
      ("DF-classification: " ^ name)
      (classified
       && (not (differential_valid t))
       && (t.t_profile_refusals = if profile then 1 else 0)
       && (t.t_errors = if error then 1 else 0)
       && t.t_div = 0
       && t.t_pairs = 0
       && t.t_positions = 0)
  in
  incomplete
    "all three profile refusals are not agreement"
    (refused, refused, refused)
    ~profile:true
    ~error:false;
  incomplete
    "Gen profile refusal with two answers is not agreement"
    (refused, Ok (), Ok ())
    ~profile:true
    ~error:false;
  incomplete
    "Ref profile refusal with two answers is not agreement"
    (Ok (), refused, Ok ())
    ~profile:true
    ~error:false;
  incomplete
    "Fast profile refusal with two answers is not agreement"
    (Ok (), Ok (), refused)
    ~profile:true
    ~error:false;
  incomplete
    "profile refusal and unexpected exception remain distinct"
    (refused, raised, Ok ())
    ~profile:true
    ~error:true;
  incomplete
    "three unexpected exceptions are not agreement"
    (raised, raised, raised)
    ~profile:false
    ~error:true;
  incomplete
    "unexpected exception with two answers is not agreement"
    (Ok (), raised, Ok ())
    ~profile:false
    ~error:true;
  let t = fresh () in
  check
    "DF-classification: three answers remain comparable"
    (match classify_runs t (Ok 1, Ok 2, Ok 3) with
     | Comparable (1, 2, 3) -> differential_valid t
     | _ -> false);
  t.t_div <- 1;
  check
    "DF-classification: semantic divergence fails independently"
    ((not (differential_valid t)) && t.t_profile_refusals = 0 && t.t_errors = 0)
;;

let shown = ref 0

let report_divergence corpus pname pair tape pos (ds : E4_diff.divergence list) =
  incr shown;
  if !shown <= 5
  then (
    Printf.printf "  DIVERGENCE %s/%s  pair=%s  position=%d\n" corpus pname pair pos;
    Printf.printf "    tape = %s\n" (E4_diff.show_tape tape);
    List.iter (fun d -> Printf.printf "    %s\n" (E4_diff.show_divergence d)) ds)
;;

(* One (program, tape): the three engines' projections at every position, compared
   pairwise in the order that isolates the extern rows first and the carriers second. *)
let one_pair
      (t : tally)
      (corpus : string)
      (p : Corpora.program)
      (tape : E4_diff.decision list)
      ~(fuel : int)
  : unit
  =
  t.t_tapes <- t.t_tapes + 1;
  if List.length tape > t.t_maxlen then t.t_maxlen <- List.length tape;
  let runs =
    ( (try Ok (S_gen.positions p.Corpora.eff ~fuel tape) with
       | e -> Error e)
    , (try Ok (S_ref.positions p.Corpora.eff ~fuel tape) with
       | e -> Error e)
    , try Ok (S_fast.positions p.Corpora.eff ~fuel tape) with
      | e -> Error e )
  in
  match classify_runs t runs with
  | Comparable (g, r, f) ->
    let n = List.length g in
    if n <> List.length tape + 1
    then (
      t.t_div <- t.t_div + 1;
      Printf.printf
        "  DIVERGENCE %s/%s: replay_steps gave %d machines for a tape of %d\n"
        corpus
        p.Corpora.name
        n
        (List.length tape));
    if List.length r <> n || List.length f <> n
    then (
      t.t_div <- t.t_div + 1;
      Printf.printf
        "  DIVERGENCE %s/%s: position counts %d/%d/%d\n"
        corpus
        p.Corpora.name
        n
        (List.length r)
        (List.length f))
    else (
      t.t_positions <- t.t_positions + n;
      List.iteri
        (fun i gi ->
           let ri = List.nth r i
           and fi = List.nth f i in
           t.t_pairs <- t.t_pairs + 2;
           let d1 = E4_diff.compare gi ri in
           if d1 <> []
           then (
             t.t_div <- t.t_div + 1;
             report_divergence corpus p.Corpora.name "Gen-vs-Ref" tape i d1);
           let d2 = E4_diff.compare ri fi in
           if d2 <> []
           then (
             t.t_div <- t.t_div + 1;
             report_divergence corpus p.Corpora.name "Ref-vs-Fast" tape i d2))
        g)
  | Incomplete { profile_refused; raised } ->
    let g, r, f = runs in
    let sh = function
      | Ok _ -> "ok"
      | Error e -> Printexc.to_string e
    in
    let label =
      if profile_refused && raised
      then "PROFILE REFUSAL + RAISED"
      else if profile_refused
      then "PROFILE REFUSAL"
      else "RAISED"
    in
    if !shown <= 5
    then (
      incr shown;
      Printf.printf
        "  %s %s/%s  Gen=%s Ref=%s Fast=%s\n    tape = %s\n"
        label
        corpus
        p.Corpora.name
        (sh g)
        (sh r)
        (sh f)
        (E4_diff.show_tape tape))
;;

let run_corpus
      (corpus : string)
      (progs : Corpora.program list)
      (tapes_of : Corpora.program -> (int * E4_diff.decision list) list)
  : tally * float
  =
  let t = fresh () in
  let t0 = Sys.time () in
  List.iter
    (fun p ->
       t.t_programs <- t.t_programs + 1;
       List.iter (fun (fuel, tape) -> one_pair t corpus p tape ~fuel) (tapes_of p))
    progs;
  t, Sys.time () -. t0
;;

let verdict (corpus : string) ((t, secs) : tally * float) =
  Printf.printf
    "  %s: %d programs x %d tapes (longest %d decisions), %d positions, %d projection \
     comparisons (2 pairs each position), %d profile-refused tapes, %d raised tapes, \
     %.2f s\n"
    corpus
    t.t_programs
    t.t_tapes
    t.t_maxlen
    t.t_positions
    t.t_pairs
    t.t_profile_refusals
    t.t_errors
    secs;
  check
    (Printf.sprintf "%s: 0 divergences and no unvalidated tapes" corpus)
    (differential_valid t)
;;

(* ==================================================================== the corpora *)

let show_report (r : Corpora.load_report) =
  Printf.printf
    "  %s: %d files, %d decoded%s\n"
    r.Corpora.lr_dir
    r.Corpora.lr_found
    r.Corpora.lr_decoded
    (if r.Corpora.lr_refused = []
     then ""
     else " -- REFUSED: " ^ String.concat " " r.Corpora.lr_refused)
;;

(* Every corpus gets the `Api.run` tape; the Lean corpus also gets random admissible
   tapes drawn from the machine as it runs (A1 §6.3's T5, made admissible by construction).
   The tape is drawn on ONE engine and applied to all three: if the engines disagree about
   what is admissible, the projections diverge and the differential says so. *)
(* THE FUEL SWEEP is what exercises `Delay` (E4_engine EN-Delay, A1 §5.1): at fuel 10 the
   drive loop returns with a NON-EMPTY command residue, `settled = false`, and the answer
   is the letter `Api.Outcome` does not have.  p3_settled and p4_answer of the projection
   are exactly that discriminator, so a fuel-starved run compares something the fuel-1000
   run cannot. *)
let gen_tape_seed = ref 0

let tapes_for_lean (p : Corpora.program) : (int * E4_diff.decision list) list =
  incr gen_tape_seed;
  let s = !gen_tape_seed in
  [ 1000, E4_diff.drive_tape
  ; 20, E4_diff.drive_tape
  ; 1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(20260908 + s) ~max_len:64
  ; 1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(51000 + (s * 3)) ~max_len:32
  ; 100, S_ref.gen_tape p.Corpora.eff ~fuel:100 ~seed:(77000 + (s * 7)) ~max_len:16
  ; 10, S_ref.gen_tape p.Corpora.eff ~fuel:10 ~seed:(99000 + (s * 11)) ~max_len:8
  ]
;;

(* Random tapes on the byte corpora too: the same drawing -- these are the real programs,
   so the tapes reach real frontiers, real park tokens and real armed dispatchers. *)
let bytes_tape_seed = ref 0

let tapes_for_bytes_random (p : Corpora.program) : (int * E4_diff.decision list) list =
  incr bytes_tape_seed;
  let s = !bytes_tape_seed in
  [ 1000, E4_diff.drive_tape
  ; 100, E4_diff.drive_tape
  ; 10, E4_diff.drive_tape
  ; 1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(31337 + s) ~max_len:64
  ; 1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(90210 + (s * 13)) ~max_len:48
  ; 1000, S_ref.gen_tape p.Corpora.eff ~fuel:1000 ~seed:(60613 + (s * 17)) ~max_len:32
  ; 100, S_ref.gen_tape p.Corpora.eff ~fuel:100 ~seed:(11235 + (s * 5)) ~max_len:24
  ; 10, S_ref.gen_tape p.Corpora.eff ~fuel:10 ~seed:(4242 + (s * 3)) ~max_len:16
  ]
;;

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
    let agree = ref 0
    and disagree = ref 0
    and absent = ref 0 in
    List.iter
      (fun (p : Corpora.program) ->
         match List.find_opt (fun e -> e.Corpora.te_name = p.Corpora.name) es with
         | None -> incr absent
         | Some e ->
           (match
              try Some (Gen_engine.run p.Corpora.eff ~fuel:1000) with
              | _ -> None
            with
            | None -> incr disagree
            | Some t ->
              let outcome = Gen_engine.outcome t in
              let fibers = Gen_engine.fiber_count t in
              let root = Gen_engine.root_exit t in
              let kind =
                match root with
                | None -> "none"
                | Some s ->
                  if String.length s >= 7 && String.sub s 0 7 = "success"
                  then "success"
                  else "failure"
              in
              let want_kind =
                if e.Corpora.te_exit_kind = "success" then "success" else "failure"
              in
              let ok =
                outcome = e.Corpora.te_outcome
                && fibers = e.Corpora.te_fibers
                && (outcome <> "finished" || kind = want_kind)
              in
              if ok
              then incr agree
              else (
                incr disagree;
                Printf.printf
                  "  DIFFERS %-14s engine: outcome=%s fibers=%d exit=%s | lean: \
                   outcome=%s fibers=%d exitKind=%s\n"
                  p.Corpora.name
                  outcome
                  fibers
                  (match root with
                   | None -> "-"
                   | Some s -> s)
                  e.Corpora.te_outcome
                  e.Corpora.te_fibers
                  e.Corpora.te_exit_kind)))
      progs;
    Printf.printf
      "  agree=%d  differ=%d  not in corpus.json=%d\n"
      !agree
      !disagree
      !absent;
    note
      (Printf.sprintf
         "reported, not gated: %d of the truth programs agree with Lean's recorded run"
         !agree)
;;

(* ==================================================================== main *)

let () =
  print_endline "== lane X: the differential over every corpus, three engines ==";
  Printf.printf "  Gen  = %s\n" Gen_engine.carriers;
  Printf.printf "  Ref  = %s\n" E4_engine.Ref.carriers;
  Printf.printf "  Fast = %s\n" E4_engine.Fast.carriers;
  print_endline "";
  classification_controls ();
  (* -------------------------------------------------------------- 1. the byte goldens *)
  print_endline "== 1. ocaml/eff/goldens: the byte goldens (fuel 1000) ==";
  let goldens, grep = Corpora.goldens () in
  show_report grep;
  (* no pinned count: every byte golden found decodes, and there is at least one *)
  check
    (Printf.sprintf
       "the byte corpus decodes: all %d programs found"
       grep.Corpora.lr_found)
    (goldens <> [] && List.length goldens = grep.Corpora.lr_found);
  let tg = run_corpus "goldens" goldens tapes_for_bytes_random in
  verdict "goldens" tg;
  (* -------------------------------------------------------------- 2. the truth corpus *)
  print_endline "";
  print_endline "== 2. the truth corpus: the Lean-cut wire goldens (fuel 1000) ==";
  let truth, trep, missing = Corpora.truth () in
  show_report trep;
  Printf.printf
    "  truth programs with canonical bytes: %d of %d (%s)\n"
    (List.length truth)
    (List.length Corpora.truth_names)
    (String.concat "," (List.map (fun (p : Corpora.program) -> p.Corpora.name) truth));
  if missing <> []
  then
    note
      ("no canonical bytes anywhere in the tree for: "
       ^ String.concat " " missing
       ^ " -- they are TypeScript declarations in corpus.json and Lean has not cut their \
          wire, so they cannot enter a byte-driven differential");
  check "the truth corpus has at least the 8 Lean-cut goldens" (List.length truth >= 8);
  let tt = run_corpus "truth" truth tapes_for_bytes_random in
  verdict "truth" tt;
  (* -------------------------------------------------------------- 3. the Lean corpus *)
  print_endline "";
  print_endline
    "== 3. the Lean corpus: the programs `make corpus` printed (random tapes, fuel \
     sweep) ==";
  let lean, lrep = Corpora.lean_corpus () in
  show_report lrep;
  check
    "the Lean corpus is present (`make corpus` writes it under .lake/corpus)"
    (lrep.Corpora.lr_found > 0);
  (* Lean cut every one of these byte strings with `Wire.encodeProgram`.  That this
     library's decoder accepts them all and its encoder gives them back is test_lean_wire's
     L2/L3 over four hundred programs instead of eight, and the constructor coverage is
     the generator's own (`Test/Program/Gen.lean` pins it), not re-counted here. *)
  check "every program of the Lean corpus decodes exactly" (lrep.Corpora.lr_refused = []);
  check
    "every program of the Lean corpus re-encodes to Lean's bytes"
    (List.for_all
       (fun (p : Corpora.program) ->
          match p.Corpora.bytes with
          | Some b -> Eff_wire.encode_program p.Corpora.eff = b
          | None -> false)
       lean);
  let typed =
    List.length
      (List.filter (fun (p : Corpora.program) -> p.Corpora.typed = Some true) lean)
  in
  Printf.printf
    "  %d programs: %d well typed by Lean (Api.wellTyped), %d ill-typed -- the machine's \
     answer to both is semantics\n"
    (List.length lean)
    typed
    (List.length lean - typed);
  let tl = run_corpus "lean" lean tapes_for_lean in
  verdict "lean" tl;
  (* -------------------------------------------------------------- 4. FB1 and DF-3 *)
  print_endline "";
  print_endline "== 4. the owed rows ==";
  (* Lane C's OWED FB1: the Fast instance's fiber table (`E4_fibers_view.bindings`) = api_gen's
     `m.fibers` over the corpus.  The fiber-table projection is p6 (ids, in machine order) and
     p9 (the rows) of every comparison above, so FB1 is discharged by the goldens tally -- but
     say it in its own words, over the 37 goldens at the `Api.run` tape. *)
  let fb1 = ref 0
  and fb1_bad = ref 0 in
  List.iter
    (fun (p : Corpora.program) ->
       match
         ( (try Some (S_gen.positions p.Corpora.eff ~fuel:1000 E4_diff.drive_tape) with
            | _ -> None)
         , try Some (S_fast.positions p.Corpora.eff ~fuel:1000 E4_diff.drive_tape) with
           | _ -> None )
       with
       | Some g, Some f ->
         let gl = List.nth g (List.length g - 1)
         and fl = List.nth f (List.length f - 1) in
         incr fb1;
         if
           gl.E4_diff.p6_fiber_ids <> fl.E4_diff.p6_fiber_ids
           || gl.E4_diff.p9_fiber_rows <> fl.E4_diff.p9_fiber_rows
         then incr fb1_bad
       | _ -> incr fb1_bad)
    goldens;
  check
    (Printf.sprintf
       "FB1 (lane C, owed): the Fast fiber table = api_gen's m.fibers, ids AND rows, on \
        %d/%d goldens"
       (!fb1 - !fb1_bad)
       (List.length goldens))
    (!fb1_bad = 0 && !fb1 = List.length goldens);
  note
    "DF-3 (query agreement, `E4_query.at s i` = `api_replay` of the first i) waits on \
     lane Q3 and is out of this lane's scope. The half of it that exists -- \
     `replay_steps` at position i equals a replay of the first i decisions -- is what \
     every position of every tape above compares, on three engines.";
  (* -------------------------------------------------------------- 5. the mutations *)
  print_endline "";
  print_endline "== 5. the comparison has teeth: one mutation per field ==";
  (match
     List.find_opt (fun (p : Corpora.program) -> p.Corpora.name = "pFork") goldens
   with
   | None -> note "pFork is not in the byte corpus; the mutation check did not run"
   | Some pf ->
     let ps = S_fast.positions pf.Corpora.eff ~fuel:1000 E4_diff.drive_tape in
     let b = List.nth ps (List.length ps - 1) in
     check
       "compare p p = [] (the projection is equal to itself)"
       (E4_diff.compare b b = []);
     let bump s = s ^ "!" in
     let at i f xs = List.mapi (fun j x -> if j = i then f x else x) xs in
     let muts : (string * int option * (E4_diff.projection -> E4_diff.projection)) list =
       [ ( "p1_outcome"
         , None
         , fun p -> { p with E4_diff.p1_outcome = bump p.E4_diff.p1_outcome } )
       ; ("p2_stuck", None, fun p -> { p with E4_diff.p2_stuck = Some "unknownFiber 9" })
       ; ( "p3_settled"
         , None
         , fun p -> { p with E4_diff.p3_settled = not p.E4_diff.p3_settled } )
       ; ( "p4_answer"
         , None
         , fun p -> { p with E4_diff.p4_answer = bump p.E4_diff.p4_answer } )
       ; ( "p5_fiber_count"
         , None
         , fun p -> { p with E4_diff.p5_fiber_count = p.E4_diff.p5_fiber_count + 1 } )
       ; ( "p6_fiber_ids"
         , Some 0
         , fun p ->
             { p with
               E4_diff.p6_fiber_ids = at 0 (fun i -> i + 100) p.E4_diff.p6_fiber_ids
             } )
       ; ( "p7_exits"
         , Some 0
         , fun p ->
             { p with
               E4_diff.p7_exits = at 0 (fun (i, s) -> i, bump s) p.E4_diff.p7_exits
             } )
       ; ( "p8_root_exit"
         , None
         , fun p -> { p with E4_diff.p8_root_exit = Some "success 999" } )
       ; ( "p9_fiber_rows"
         , Some 1
         , fun p ->
             { p with
               E4_diff.p9_fiber_rows =
                 at 1 (fun (i, s) -> i, bump s) p.E4_diff.p9_fiber_rows
             } )
       ; ( "p10_armed"
         , None
         , fun p -> { p with E4_diff.p10_armed = bump p.E4_diff.p10_armed } )
       ; ( "p11_trace_length"
         , None
         , fun p -> { p with E4_diff.p11_trace_length = p.E4_diff.p11_trace_length + 1 }
         )
       ; ( "p12_trace_rows"
         , Some 7
         , fun p -> { p with E4_diff.p12_trace_rows = at 7 bump p.E4_diff.p12_trace_rows }
         )
       ; ( "p13_store_row"
         , None
         , fun p -> { p with E4_diff.p13_store_row = bump p.E4_diff.p13_store_row } )
       ]
     in
     Printf.printf
       "  base = pFork at the end of [evaluate 0; flush], fuel 1000: %d fibers, %d trace \
        rows\n"
       b.E4_diff.p5_fiber_count
       b.E4_diff.p11_trace_length;
     List.iter
       (fun (field, idx, mut) ->
          let d = E4_diff.compare b (mut b) in
          let ok =
            match d with
            | [ x ] -> x.E4_diff.d_field = field && x.E4_diff.d_index = idx
            | _ -> false
          in
          check
            (Printf.sprintf
               "mutating %s is caught, and only it%s"
               field
               (match idx with
                | None -> ""
                | Some i -> Printf.sprintf " (at index %d)" i))
            ok)
       muts);
  (* -------------------------------------------------------------- 6. the cross face *)
  cross_face truth;
  (* -------------------------------------------------------------- the totals *)
  let tot f = f (fst tg) + f (fst tt) + f (fst tl) in
  print_endline "";
  Printf.printf
    "== totals: %d programs, %d tapes, %d positions, %d projection comparisons, %d \
     divergences, %d profile-refused tapes, %d raised tapes, %.2f s ==\n"
    (tot (fun t -> t.t_programs))
    (tot (fun t -> t.t_tapes))
    (tot (fun t -> t.t_positions))
    (tot (fun t -> t.t_pairs))
    (tot (fun t -> t.t_div))
    (tot (fun t -> t.t_profile_refusals))
    (tot (fun t -> t.t_errors))
    (snd tg +. snd tt +. snd tl);
  if !failures = 0
  then Printf.printf "== ALL PASS: 0 failure(s) == (%d checks)\n" !checks
  else Printf.printf "== FAILED: %d failure(s) in %d checks ==\n" !failures !checks;
  if !failures > 0 then exit 1
;;
