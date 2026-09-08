(* test_query.ml -- lane Q3, second half: the query API over a run.

   What it checks (2026-09-08-engine-a3-queue-query.md §2.6, §4.1, §4.2 DF-3):

     query-inv-tape-1  Q1, AS A REPO GATE.  `e4_query.mli` is parsed -- comments stripped,
                       every `val` split at its top-level arrows -- and the RESULT type of
                       every signature but `of_run`'s must not mention `source` or a tape
                       type; neither file may mention `E4_sched`.  This is the mechanical
                       half of INV-TAPE-1(query): a caller cannot thread a mutated source
                       or a new tape out of this module because no signature lets it.
     query-free        Q1, AS A FACT.  Every entry point is called and the source's
                       observables are compared before and after.
     query-idempotent  Q3.  Two calls with the same argument, equal answers, on all
                       thirteen projections for the ones that return a machine.
     query-complete    Q4.  `rows 0 length` is the whole log with no gap, the segments
                       cover it exactly, and `row` agrees with `rows` at every index.
     query-cost-exact  `cost ~from ~upto` is the number of times the source's `replay` is
                       ACTUALLY called -- counted, at k in {1, 8, 1024, infinity}.
     DF-3              QUERY AGREEMENT.  For the 37 byte goldens of ocaml/eff/goldens
                       (`Eff_wire` + `E4_program`, the loader copied from lane D's
                       test_engine.ml) driven with no choices at fuel 1000: for every
                       i <= |tape|, `E4_query.at s i` equals what replaying the first i
                       decisions produces, on all thirteen `E4_diff` projections.  Two
                       tapes per program -- `Api.run`'s own `[evaluate 0; flush]` and an
                       admissible generated tape (`E4_diff.gen_tape`, which only names ids
                       the machine has shown) -- at k = 1024 and at k = 8, so the
                       checkpoint arithmetic is exercised and not just bypassed.  The ten
                       longest tapes are checked at EVERY i; the rest are sampled.
     the mutation      an `at` built from a DIFFERENT tape prefix must go red: the tape is
                       rebuilt without its first decision and the comparison against the
                       true prefix must diverge for every program whose tape does anything
                       at all.

   THE HOLD SEMANTICS.  `E4_engine.replay` is `fold_left step_or_hold`: a stuck or unsettled
   machine REPEATS instead of consuming the tape (e4_engine.ml:311-316), which is what makes
   position i defined for every i.  The source's `replay` is therefore
   `fun m d -> E4_engine.Fast.replay m [d]` and NOT the raw `step`, so that "the machine at
   position i" means the same thing here and in `E4_engine`.

   Run: cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine

module E = Eff_types
module F = E4_engine.Fast
module S = E4_diff.Of (E4_engine.Fast)

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let fail_note name why =
  incr checks;
  Printf.printf "FAIL %s -- %s\n" name why;
  incr failures

(* ================================================================ locating the corpus *)

let ancestors d n =
  let rec go d n acc =
    if n = 0 then List.rev acc else go (Filename.dirname d) (n - 1) (d :: acc)
  in
  go d n []

let find_path (suffix : string list) (env : string) : string option =
  let rel = List.fold_left Filename.concat (List.hd suffix) (List.tl suffix) in
  let from_env = try [ Sys.getenv env ] with Not_found -> [] in
  let cands =
    from_env
    @ List.concat_map
        (fun a -> [ Filename.concat a rel; Filename.concat a (Filename.concat "ocaml" rel) ])
        (ancestors (Sys.getcwd ()) 9)
  in
  List.find_opt Sys.file_exists cands

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* ==================================================== the source over a run *)

let dec_of (d : E4_diff.decision) : F.decision =
  match d with
  | E4_diff.Evaluate k -> F.evaluate k
  | E4_diff.Flush -> F.flush
  | E4_diff.Fire k -> F.fire k
  | E4_diff.Yield_verdict (k, b) -> F.yield_verdict k b
  | E4_diff.Answer_async (f, tk, n) -> F.answer_async_success f tk n
  | E4_diff.Interrupt_from (w, tg) -> F.interrupt_from w tg
  | E4_diff.Install_middleware -> F.install_middleware

let hold (m : F.t) (d : F.decision) : F.t = F.replay m [ d ]

let status_of (t : F.t) : E4_query.status =
  match F.answer t with
  | E4_engine.Finished -> { E4_query.finished = true; stuck = None; fuel_left = F.fuel t }
  | E4_engine.Refused r ->
    { E4_query.finished = false; stuck = Some r; fuel_left = F.fuel t }
  | E4_engine.Suspended _ | E4_engine.Delay _ ->
    { E4_query.finished = false; stuck = None; fuel_left = F.fuel t }

(* The log is the FINAL machine's trace, stamped with the decision whose step appended each
   row.  `trace_length` is O(1) (e4_trace.mli TR4), so the stamps cost one int per decision
   and the rows are rendered ONCE, at the end -- never once per position. *)
let build ?(replay = hold) (p : E.eff) ~(fuel : int) (dtape : E4_diff.decision list) ~(k : int)
  : (F.t, F.decision) E4_query.source =
  let arr = Array.of_list (List.map dec_of dtape) in
  let n = Array.length arr in
  let t0 = F.load p ~fuel in
  let lens = Array.make (n + 1) 0 in
  lens.(0) <- F.trace_length t0;
  let m = ref t0 in
  for j = 0 to n - 1 do
    m := replay !m arr.(j);
    lens.(j + 1) <- F.trace_length !m
  done;
  let final_rows = F.trace_rows !m in
  let log = ref E4_log.empty and idx = ref E4_logindex.empty in
  let j = ref 0 in
  List.iteri
    (fun i r ->
       while !j < n && lens.(!j + 1) <= i do
         incr j
       done;
       let d = if i < lens.(0) then -1 else !j in
       log := E4_log.append !log r;
       idx := E4_logindex.add !idx (E4_logindex.parse_run_event_row ~decision:d i r))
    final_rows;
  E4_query.of_run ~log:!log ~index:!idx ~tape:arr ~replay ~initial:t0 ~checkpoint_every:k
    ~status:status_of

(* ============================================== the INV-TAPE-1(query) repo gate *)

(* OCaml comments nest, so the depth is counted; there is no string literal outside a
   comment in an .mli of this shape. *)
let strip_comments (s : string) : string =
  let n = String.length s in
  let b = Buffer.create n in
  let depth = ref 0 and i = ref 0 in
  while !i < n do
    if !i + 1 < n && s.[!i] = '(' && s.[!i + 1] = '*' then begin
      incr depth;
      i := !i + 2
    end
    else if !i + 1 < n && s.[!i] = '*' && s.[!i + 1] = ')' && !depth > 0 then begin
      decr depth;
      i := !i + 2;
      Buffer.add_char b ' '
    end
    else begin
      if !depth = 0 then Buffer.add_char b s.[!i];
      incr i
    end
  done;
  Buffer.contents b

(* every `val NAME : TYPE` of a flat signature, TYPE with its newlines squeezed *)
let val_decls (src : string) : (string * string) list =
  let text = strip_comments src in
  let lines = String.split_on_char '\n' text in
  let out = ref [] and cur = ref None and buf = Buffer.create 128 in
  let flush () =
    match !cur with
    | None -> ()
    | Some name ->
      out := (name, String.trim (Buffer.contents buf)) :: !out;
      Buffer.clear buf;
      cur := None
  in
  List.iter
    (fun line ->
       let t = String.trim line in
       let starts p = String.length t >= String.length p && String.sub t 0 (String.length p) = p in
       if starts "val " then begin
         flush ();
         let rest = String.sub t 4 (String.length t - 4) in
         match String.index_opt rest ':' with
         | None -> ()
         | Some c ->
           cur := Some (String.trim (String.sub rest 0 c));
           Buffer.add_string buf (String.sub rest (c + 1) (String.length rest - c - 1))
       end
       else if starts "type " || starts "module " || starts "end" || t = "" then flush ()
       else if !cur <> None then begin
         Buffer.add_char buf ' ';
         Buffer.add_string buf t
       end)
    lines;
  flush ();
  List.rev !out

(* the part after the LAST arrow at paren depth 0 *)
let result_type (ty : string) : string =
  let n = String.length ty in
  let depth = ref 0 and last = ref (-1) and i = ref 0 in
  while !i < n do
    (match ty.[!i] with
     | '(' | '[' -> incr depth
     | ')' | ']' -> decr depth
     | '-' when !depth = 0 && !i + 1 < n && ty.[!i + 1] = '>' -> last := !i + 2
     | _ -> ());
    incr i
  done;
  String.trim (if !last < 0 then ty else String.sub ty !last (n - !last))

let mentions hay needle =
  let m = String.length needle and h = String.length hay in
  let rec go i = i + m <= h && (String.sub hay i m = needle || go (i + 1)) in
  m > 0 && go 0

let gate () =
  print_endline "== the INV-TAPE-1(query) repo gate ==";
  match (find_path [ "engine"; "e4_query.mli" ] "E4_QUERY_MLI",
         find_path [ "engine"; "e4_query.ml" ] "E4_QUERY_ML")
  with
  | None, _ | _, None -> fail_note "query-inv-tape-1" "engine/e4_query.mli not found from the cwd"
  | Some mli_path, Some ml_path ->
    let mli = read_file mli_path in
    let ml = read_file ml_path in
    let decls = val_decls mli in
    Printf.printf "  %s: %d signatures\n" mli_path (List.length decls);
    let offenders =
      List.filter
        (fun (name, ty) ->
           let r = result_type ty in
           name <> "of_run" && (mentions r "source" || mentions r "tape"))
        decls
    in
    List.iter
      (fun (n, ty) -> Printf.printf "    OFFENDER %s : ... -> %s\n" n (result_type ty))
      offenders;
    check
      (Printf.sprintf
         "query-inv-tape-1: no signature but of_run RETURNS a source or a tape (%d checked)"
         (List.length decls))
      (offenders = [] && List.length decls > 20);
    check "query-inv-tape-1: of_run is the single constructor and it does return a source"
      (match List.assoc_opt "of_run" decls with
       | None -> false
       | Some ty -> mentions (result_type ty) "source");
    (* the CODE, not the prose: this file's own header names `E4_sched.send` to say what the
       gate forbids, so the check is on the comment-stripped text of both halves *)
    check "query-inv-tape-1: neither e4_query.mli nor e4_query.ml refers to E4_sched"
      ((not (mentions (strip_comments mli) "E4_sched"))
      && not (mentions (strip_comments ml) "E4_sched"));
    (* the gate has teeth: a signature that DID return a source must be caught *)
    let planted = val_decls (mli ^ "\nval evil : ('m, 'd) source -> ('m, 'd) source\n") in
    check "query-inv-tape-1: the gate catches a planted `-> source` signature (mutation)"
      (List.exists
         (fun (name, ty) -> name = "evil" && mentions (result_type ty) "source")
         planted)

(* ============================================================ Q1, Q3, Q4 and the cost *)

let show_divs ds = String.concat "; " (List.map E4_diff.show_divergence ds)

let laws (p : E.eff) (name : string) (dtape : E4_diff.decision list) =
  print_endline "";
  Printf.printf "== the query laws on %s (|tape| = %d) ==\n" name (List.length dtape);
  let k = 8 in
  let s = build p ~fuel:1000 dtape ~k in
  let n = E4_query.tape_length s in
  let len = E4_query.length s in
  Printf.printf "  %d log rows, %d decisions, %d fibers, %d tokens, %d scopes, k = %d\n" len n
    (List.length (E4_query.fibers s))
    (List.length (E4_query.tokens s))
    (List.length (E4_query.scopes s))
    (E4_query.checkpoint_every s);
  (* Q4 *)
  let all = E4_query.rows s ~from:0 ~upto:len in
  check "query-complete (Q4): rows 0..length is the whole log, no gap"
    (List.length all = len
    && List.for_all (fun i -> E4_query.row s i = Some (List.nth all i)) (List.init len Fun.id)
    && E4_query.row s len = None
    && E4_query.row s (-1) = None);
  check "query-complete (Q4): the decision segments partition the log"
    (let segs =
       List.filter_map
         (fun d -> E4_query.segment_of_decision s d)
         (List.init (n + 2) (fun i -> i - 1))
     in
     let cover =
       List.concat_map (fun (a, z) -> List.init (z - a) (fun i -> a + i)) segs
     in
     List.sort compare cover = List.init len Fun.id);
  check "query-complete (Q4): decision_of_row lands inside that row's own segment"
    (List.for_all
       (fun i ->
          match E4_query.decision_of_row s i with
          | None -> false
          | Some d -> (
            match E4_query.segment_of_decision s d with
            | None -> false
            | Some (a, z) -> a <= i && i < z))
       (List.init len Fun.id));
  (* Q3 *)
  let proj i = S.project (E4_query.at s i) in
  check "query-idempotent (Q3): two `at i` agree on all thirteen projections"
    (List.for_all (fun i -> E4_diff.compare (proj i) (proj i) = []) (List.init (n + 1) Fun.id));
  check "query-idempotent (Q3): rows / fibers / outcome / cost repeat"
    (E4_query.rows s ~from:0 ~upto:len = all
    && E4_query.fibers s = E4_query.fibers s
    && E4_query.checkpoints s = E4_query.checkpoints s
    && E4_query.cost s ~from:0 ~upto:n = E4_query.cost s ~from:0 ~upto:n
    && E4_query.outcome s = E4_query.outcome s);
  (* Q1: every entry point called, then every observable compared *)
  let observables () =
    ( E4_query.length s,
      E4_query.tape_length s,
      E4_query.checkpoints s,
      E4_query.rows s ~from:0 ~upto:(E4_query.length s),
      E4_query.fibers s,
      E4_query.tokens s,
      E4_query.scopes s )
  in
  let before = observables () in
  let touch () =
    ignore (E4_query.row s 0);
    ignore (E4_query.rows s ~from:0 ~upto:len);
    ignore (E4_query.segment_of_decision s 0);
    ignore (E4_query.decision_of_row s 0);
    ignore (List.map (fun f -> E4_query.fiber_rows s f) (E4_query.fibers s));
    ignore (List.map (fun k -> E4_query.scope_rows s k) (E4_query.scopes s));
    ignore (List.map (fun k -> E4_query.token_rows s k) (E4_query.tokens s));
    ignore (List.map (fun f -> E4_query.task_rows s ~owner:f) (E4_query.fibers s));
    ignore (E4_query.open_scopes s);
    ignore (E4_query.by_cid s ~cid:"program:deadbeef");
    ignore (E4_query.by_occurrence s ~program:"program:deadbeef" ~path:[ 1; 0 ]);
    ignore (E4_query.by_path s ~path:[ 1; 0 ]);
    ignore (E4_query.tape s);
    ignore (E4_query.outcome s);
    ignore (E4_query.at s (n / 2));
    ignore (E4_query.replay_steps s ~from:0 ~upto:n);
    ignore (E4_query.cost s ~from:0 ~upto:n);
    ignore (E4_query.checkpoints s);
    let c = ref (E4_query.cursor s ~from:0) in
    let go = ref true in
    while !go do
      match E4_query.next !c with None -> go := false | Some (_, c') -> c := c'
    done;
    ignore (E4_query.position !c);
    ignore (E4_query.current !c)
  in
  touch ();
  check "query-free (Q1): every entry point called, every observable unchanged"
    (observables () = before);
  check "query-free (Q1): by_cid refuses the empty address (it would match every row)"
    (try
       ignore (E4_query.by_cid s ~cid:"");
       false
     with Invalid_argument _ -> true);
  (* the cursor is the primary entry point: a full walk must be `replay_steps` *)
  let walked =
    let c = ref (E4_query.cursor s ~from:0) and acc = ref [] and go = ref true in
    while !go do
      match E4_query.next !c with
      | None -> go := false
      | Some (m, c') ->
        acc := m :: !acc;
        c := c'
    done;
    List.rev !acc
  in
  let stepped = List.tl (E4_query.replay_steps s ~from:0 ~upto:n) in
  check "query: the cursor walk is replay_steps, machine for machine"
    (List.length walked = n
    && List.for_all2 (fun a b -> E4_diff.compare (S.project a) (S.project b) = []) walked
         stepped);
  check "query: replay_steps from..upto is inclusive and its ends are `at`"
    (List.length (E4_query.replay_steps s ~from:0 ~upto:n) = n + 1
    && (n = 0
       || E4_diff.compare
            (S.project (List.hd (E4_query.replay_steps s ~from:1 ~upto:n)))
            (S.project (E4_query.at s 1))
          = []));
  (* the cost model, counted *)
  let counted k =
    let calls = ref 0 in
    let replay m d =
      incr calls;
      hold m d
    in
    let s = build ~replay p ~fuel:1000 dtape ~k in
    let exact = ref true and worst = ref 0 and total = ref 0 in
    for i = 0 to n do
      calls := 0;
      ignore (E4_query.at s i);
      let predicted = E4_query.cost s ~from:i ~upto:i in
      if !calls <> predicted then exact := false;
      if !calls > !worst then worst := !calls;
      total := !total + !calls
    done;
    (!exact, !worst, !total)
  in
  let cells = List.map (fun k -> (k, counted k)) [ 1; 8; 1024; max_int ] in
  List.iter
    (fun (k, (ok, worst, total)) ->
       Printf.printf "  k = %-11s cost exact: %-5b  worst `at` = %d replays, %d over the walk\n"
         (if k = max_int then "infinity" else string_of_int k)
         ok worst total)
    cells;
  check "query-cost-exact: `cost` is the number of replays actually made, at every k"
    (List.for_all (fun (_, (ok, _, _)) -> ok) cells);
  check "query-cost-exact: k = 1 replays nothing, k = infinity replays i, k = 8 bounded by 7"
    (match cells with
     | [ (_, (_, w1, _)); (_, (_, w8, _)); _; (_, (_, winf, _)) ] ->
       w1 = 0 && w8 <= 7 && winf = n
     | _ -> false)

(* =========================================================== DF-3: query agreement *)

let df3 () =
  print_endline "";
  print_endline "== DF-3: query agreement over the 37 byte goldens (fuel 1000, no choices) ==";
  match find_path [ "eff"; "goldens"; "p42.bin" ] "E4_EFF_GOLDENS" with
  | None -> fail_note "DF-3" "ocaml/eff/goldens not found from the cwd"
  | Some marker ->
    let dir = Filename.dirname marker in
    let names =
      List.sort compare
        (List.filter
           (fun f -> Filename.check_suffix f ".bin")
           (Array.to_list (Sys.readdir dir)))
    in
    let progs =
      List.filter_map
        (fun f ->
           match Eff_wire.decode_program_exact (read_file (Filename.concat dir f)) with
           | None -> None
           | Some p -> Some (Filename.remove_extension f, p))
        names
    in
    Printf.printf "  %s: %d/%d programs decoded\n" dir (List.length progs) (List.length names);
    (* two tapes per program: `Api.run`'s own, and an admissible generated one whose length
       varies with the program so that "the ten longest" is a real selection *)
    let cases =
      List.concat
        (List.mapi
           (fun i (name, p) ->
              let gen tag seed max_len =
                (name ^ tag, p, S.gen_tape p ~fuel:1000 ~seed ~max_len)
              in
              [ (name ^ "/drive", p, E4_diff.drive_tape);
                gen "/gen16" (20260908 + i) 16;
                gen "/gen40" (20261908 + i) 40;
                gen "/gen64" (20262908 + i) 64 ])
           progs)
    in
    let by_len = List.sort (fun (_, _, a) (_, _, b) -> compare (List.length b) (List.length a)) cases in
    let longest =
      List.filteri (fun i _ -> i < 10) by_len |> List.map (fun (n, _, _) -> n)
    in
    (* §4.2 DF-3 asks for "i sampled every 1, and the ten longest tapes at every i".  Every
       case here is cheap enough to run at EVERY i, so nothing is sampled and the ten
       longest are only named for the record. *)
    Printf.printf "  %d cases, EVERY i on all of them; the ten longest tapes are: %s\n"
      (List.length cases)
      (String.concat " " longest);
    let positions_total = ref 0 and compared = ref 0 and diverged = ref 0 and shown = ref 0 in
    let mutation_expected = ref 0 and mutation_caught = ref 0 in
    List.iter
      (fun (name, p, dtape) ->
         let n = List.length dtape in
         let truth = S.positions p ~fuel:1000 dtape in
         positions_total := !positions_total + n + 1;
         (* §4.2 DF-3 asks for "i sampled every 1, and the ten longest tapes at every i".
            Every case here turned out cheap enough to run at EVERY i, so the sample step is
            1 for all of them and `longest` only labels the report -- said plainly rather
            than dressed up as a sample. *)
         let indices = List.init (n + 1) Fun.id in
         List.iter
           (fun k ->
              let s = build p ~fuel:1000 dtape ~k in
              List.iter
                (fun i ->
                   incr compared;
                   let ds = E4_diff.compare (S.project (E4_query.at s i)) (List.nth truth i) in
                   if ds <> [] then begin
                     incr diverged;
                     if !shown < 5 then begin
                       incr shown;
                       Printf.printf "  DIVERGENCE %s k=%d i=%d: %s\n" name k i (show_divs ds)
                     end
                   end)
                indices)
           [ 1024; 8 ];
         (* the mutation: the same comparison against a source built from a DIFFERENT tape
            prefix.  It must go red whenever the true tape does anything at all. *)
         if n >= 2 then begin
           let distinct =
             List.exists (fun q -> E4_diff.compare q (List.hd truth) <> []) truth
           in
           if distinct then begin
             incr mutation_expected;
             let s' = build p ~fuel:1000 (List.tl dtape) ~k:1024 in
             let caught =
               List.exists
                 (fun i -> E4_diff.compare (S.project (E4_query.at s' i)) (List.nth truth i) <> [])
                 (List.init n Fun.id)
             in
             if caught then incr mutation_caught
           end
         end)
      cases;
    Printf.printf
      "  %d comparisons over %d positions, two checkpoint intervals, %d divergences\n"
      !compared !positions_total !diverged;
    check
      (Printf.sprintf "DF-3: `at s i` = the tape prefix's machine, %d comparisons, 0 divergences"
         !compared)
      (!diverged = 0 && !compared > 1000);
    Printf.printf "  mutation: %d/%d tapes whose dropped-first-decision source goes red\n"
      !mutation_caught !mutation_expected;
    check "DF-3 mutation: an `at` built from a different tape prefix is caught, every time"
      (!mutation_expected > 10 && !mutation_caught = !mutation_expected)

(* ====================================================== the three addresses, honestly *)

let addresses () =
  print_endline "";
  print_endline "== by_cid / by_occurrence / by_path: what they answer today ==";
  let seal = "program:2ddd3ccc83" in
  let rows =
    [ "started(0)";
      Printf.sprintf "frame(0,popped(success 1)) %s/%s" seal (E4_query.path_text [ 1; 0 ]);
      "parkedOn(0,0)";
      Printf.sprintf "exited(0,success unit) %s" seal;
      "childrenInterrupted(0,[1,2])" ]
  in
  let log = E4_log.of_list rows in
  let idx = E4_logindex.of_log log ~parse:(E4_logindex.parse_run_event_row ~decision:0) in
  let s =
    E4_query.of_run ~log ~index:idx ~tape:[||] ~replay:(fun m () -> m) ~initial:()
      ~checkpoint_every:1024
      ~status:(fun () -> { E4_query.finished = true; stuck = None; fuel_left = 0 })
  in
  check "query: by_cid finds the seal the writer put in the row, and computes none"
    (List.map fst (E4_query.by_cid s ~cid:seal) = [ 1; 3 ]);
  check "query: by_occurrence is program/[path], by_path is the path alone"
    (List.map fst (E4_query.by_occurrence s ~program:seal ~path:[ 1; 0 ]) = [ 1 ]
    && List.map fst (E4_query.by_path s ~path:[ 1; 0 ]) = [ 1 ]
    && E4_query.by_occurrence s ~program:seal ~path:[ 9 ] = []);
  check "query: the path glyph is space-separated, so an id list is not mistaken for a path"
    (E4_query.path_text [ 1; 1; 0 ] = "[1 1 0]"
    && E4_query.by_path s ~path:[ 1; 2 ] = []
    && E4_query.occurrence_text ~program:seal ~path:[ 1; 0 ] = seal ^ "/[1 0]");
  check "query: outcome reads the caller's status and the log's open scopes"
    (E4_query.outcome s = `Finished)

let () =
  print_endline "== lane Q3b: the query API over a run (Q1, Q3, Q4, the cost model, DF-3) ==";
  print_endline "";
  gate ();
  addresses ();
  (match find_path [ "eff"; "goldens"; "pFork.bin" ] "E4_EFF_GOLDENS" with
   | None -> fail_note "the query laws" "ocaml/eff/goldens/pFork.bin not found"
   | Some path -> (
     match Eff_wire.decode_program_exact (read_file path) with
     | None -> fail_note "the query laws" "pFork.bin did not decode"
     | Some p ->
       let tape = S.gen_tape p ~fuel:1000 ~seed:20260908 ~max_len:40 in
       laws p "pFork" tape));
  df3 ();
  print_endline "";
  Printf.printf "== %s: %d failure(s) in %d checks ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures !checks;
  exit (if !failures = 0 then 0 else 1)
