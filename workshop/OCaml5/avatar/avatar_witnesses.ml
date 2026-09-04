(* The witness and clause report: run every witness of `deep_witnesses.ml` under the clause
   probe, evaluate every clause of `deep_clauses.ml` it exercises (the census join of
   `deep_census.ml`), and print one deterministic report -- the same bytes on the three
   hosts, which `run-witnesses.sh` checks.

   Seat F1, 2026-09-04. *)

open Deep_fibers
open Deep_clauses

let census_of_witness (name : string) : Deep_census.row list =
  List.filter (fun (r : Deep_census.row) -> List.mem ("Effect4.Deep.Witnesses." ^ name) r.deep) Deep_census.rows

let clauses_of_rows (rows : Deep_census.row list) : (string * clause option) list =
  let names =
    List.sort_uniq compare
      (List.concat_map
         (fun (r : Deep_census.row) ->
           List.filter (fun n -> not (String.length n > 24 && String.sub n 0 24 = "Effect4.Deep.Witnesses.")) r.deep)
         rows)
  in
  List.map
    (fun n ->
      let short = if String.length n > 13 && String.sub n 0 13 = "Effect4.Deep." then String.sub n 13 (String.length n - 13) else n in
      (n, find short))
    names

let verdict_string = function
  | Holds -> "HOLDS"
  | Fails msg -> "FAILS: " ^ msg
  | Not_portable why -> "NOT PORTABLE: " ^ why

let () =
  print_endline "== deep_clauses: one entry per `Effect4/Deep/Clauses.lean` theorem, evaluated on the avatar";
  let holds = ref 0 and fails = ref 0 and refused = ref 0 in
  List.iter
    (fun c ->
      let v = evaluate c in
      (match v with Holds -> incr holds | Fails _ -> incr fails | Not_portable _ -> incr refused);
      Printf.printf "clause\t%s\t%s\t%s\t%s\n" c.name c.lean (String.concat "," c.census) (verdict_string v))
    clauses;
  Printf.printf "clauses\t%d\tholds\t%d\tfails\t%d\tnot-portable\t%d\n" count !holds !fails !refused;
  print_endline "";
  print_endline "== deep_witnesses: one entry per `Effect4/Deep/Witnesses.lean` theorem, run through the avatar";
  let w_ok = ref 0 and w_bad = ref 0 and w_refused = ref 0 in
  let run_holds = ref 0 and run_fails = ref 0 in
  List.iter
    (fun (w : Deep_witnesses.witness) ->
      let rows = census_of_witness w.name in
      let declared = clauses_of_rows rows in
      Printf.printf "witness\t%s\t%s\trows\t%s\n" w.name w.lean
        (String.concat "," (List.map (fun (r : Deep_census.row) -> r.id) rows));
      match w.portable with
      | Some why ->
        incr w_refused;
        Printf.printf "  statement\tNOT PORTABLE: %s\n" why
      | None ->
        (* The step checks the declared clauses carry, each with its first violation. *)
        let probes =
          List.filter_map
            (fun (n, c) -> match c with Some c -> (match step_check c with Some s -> Some (n, s, ref None) | None -> None) | None -> None)
            declared
        in
        let sweep = List.filter_map (fun c -> match step_check c with Some s -> Some (c.name, s, ref None) | None -> None) clauses in
        let index = ref 0 in
        let current_def = ref "" in
        on_event :=
          (fun m e ->
            let i = !index in
            incr index;
            let visit (n, s, first) =
              match !first with
              | Some _ -> ()
              | None -> (
                match (try s m i e with ex -> Some ("raised " ^ Printexc.to_string ex)) with
                | Some msg -> first := Some (Printf.sprintf "%s step %d (%s): %s" !current_def i (Avatar_trace.render_event e) msg)
                | None -> ())
            in
            List.iter visit probes;
            List.iter visit sweep);
        let snaps =
          List.map
            (fun (n, f) ->
              current_def := n;
              index := 0;
              let s = try Ok (f ()) with ex -> Error (Printexc.to_string ex) in
              (n, s))
            w.defs
        in
        on_event := (fun _ _ -> ());
        let lookup n =
          match List.assoc_opt n snaps with
          | Some (Ok s) -> s
          | Some (Error e) -> failwith (n ^ " raised " ^ e)
          | None -> failwith ("no def " ^ n)
        in
        let statement =
          try (match w.state lookup with None -> "HOLDS" | Some msg -> "FAILS: " ^ msg)
          with ex -> "FAILS: raised " ^ Printexc.to_string ex
        in
        (match statement with "HOLDS" -> incr w_ok | _ -> incr w_bad);
        Printf.printf "  statement\t%s\n" statement;
        List.iter
          (fun (n, c) ->
            match c with
            | None -> Printf.printf "  clause\t%s\tnot transferred (not a `Clauses.lean` theorem)\n" n
            | Some c -> (
              match c.check with
              | Refused why -> Printf.printf "  clause\t%s\tNOT PORTABLE: %s\n" n why
              | Pure _ -> Printf.printf "  clause\t%s\t%s (pure, evaluated once above)\n" n (verdict_string (evaluate c))
              | Run _ | Both _ -> (
                match List.find_opt (fun (pn, _, _) -> pn = n) probes with
                | Some (_, _, first) -> (
                  match !first with
                  | None -> incr run_holds; Printf.printf "  clause\t%s\tHOLDS on this run\n" n
                  | Some v -> incr run_fails; Printf.printf "  clause\t%s\tFAILS on this run at %s\n" n v)
                | None -> ())))
          declared;
        let swept_bad = List.filter_map (fun (n, _, first) -> Option.map (fun v -> (n, v)) !first) sweep in
        Printf.printf "  sweep\t%d step clauses over every event\t%s\n" (List.length sweep)
          (if swept_bad = [] then "all hold"
           else String.concat "; " (List.map (fun (n, v) -> n ^ " FAILS at " ^ v) swept_bad)))
    Deep_witnesses.witnesses;
  Printf.printf "witnesses\t%d\tholds\t%d\tfails\t%d\tnot-portable\t%d\n" Deep_witnesses.count !w_ok !w_bad !w_refused;
  Printf.printf "run-clauses\tholds\t%d\tfails\t%d\n" !run_holds !run_fails
