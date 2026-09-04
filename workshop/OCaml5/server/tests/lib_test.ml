(* Deliverable 4, the OCaml half: the daemon's handlers used as a plain library, with no
   wire in between.

   Prints one line per check. Every line begins `PASS` or `FAIL`; the process exits 1 if any
   line is a `FAIL`. Run on every host by `tests/test_client.py`'s sibling
   `tests/run-tests.sh`. *)

let failures = ref 0

let check name ok detail =
  if ok then Printf.printf "PASS %-42s %s\n" name detail
  else begin
    incr failures;
    Printf.printf "FAIL %-42s %s\n" name detail
  end

let () =
  (* --- the call the brief names: program -> tape -> masks -> result --------- *)
  let masks = Effect4_daemon.masks () in
  check "masks-from-the-committed-table" (List.length masks = 3)
    (String.concat "," (List.map (fun (m : E4d_wire.mask) -> m.name) masks));

  let program = Effect4_daemon.program_of_fixture "ref" "makeGet" in
  let result = Effect4_daemon.run_program program "" masks in
  check "run_program-rows"
    (result.Effect4_daemon.result_rows
     = [ "op\tmake\t7"; "answer\tmake\t0"; "op\tget\t0"; "answer\tget\t7";
         "done\t{\"success\":7}" ])
    (String.concat " | " result.Effect4_daemon.result_rows);
  check "run_program-header-has-the-golden-fields"
    (List.exists (fun l -> l = "face\tocaml") result.Effect4_daemon.result_header
     && List.exists
          (fun l -> String.length l > 4 && String.sub l 0 4 = "pin\t")
          result.Effect4_daemon.result_header)
    (string_of_int (List.length result.Effect4_daemon.result_header) ^ " header lines");
  check "run_program-projections"
    (List.length result.Effect4_daemon.result_projections = 3
     && List.assoc "outcome" result.Effect4_daemon.result_projections
        = [ "done\t{\"success\":7}" ])
    (String.concat ","
       (List.map
          (fun (name, rows) -> Printf.sprintf "%s=%d" name (List.length rows))
          result.Effect4_daemon.result_projections));
  check "run_program-outcome"
    (match result.Effect4_daemon.result_outcome with
     | Effect4_daemon.Finished (Deep_fibers.Esuccess (Deep_fibers.Vnat 7)) -> true
     | _ -> false)
    "success 7";
  check "run_program-machine-is-the-avatar's"
    (List.length result.Effect4_daemon.result_machine.Deep_fibers.fibers = 1)
    (string_of_int (List.length result.Effect4_daemon.result_machine.Deep_fibers.fibers)
     ^ " fibers");
  check "run_program-events"
    (result.Effect4_daemon.result_events <> [])
    (string_of_int (List.length result.Effect4_daemon.result_events) ^ " RunEvents");

  (* --- a corpus program, whose root table the library installs for itself ---- *)
  let corpus = Effect4_daemon.program_of_corpus "aIntDaemon" in
  let corpus_result = Effect4_daemon.run_program corpus "" masks in
  check "run_program-corpus" (corpus_result.Effect4_daemon.result_rows <> [])
    (string_of_int (List.length corpus_result.Effect4_daemon.result_rows) ^ " rows");

  (* --- running twice in one process gives the same answer -------------------- *)
  let again = Effect4_daemon.run_program program "" masks in
  check "state-is-reset-between-calls"
    (again.Effect4_daemon.result_rows = result.Effect4_daemon.result_rows)
    "identical rows";

  (* --- the whole protocol, without the wire --------------------------------- *)
  let answer =
    Effect4_daemon.handle
      (E4d_json.Obj
         [ ("request", Str "run"); ("source", Str "fixture"); ("family", Str "scope");
           ("program", Str "lifo") ])
  in
  check "handle-json-in-json-out"
    (E4d_json.bool_ "ok" answer && E4d_json.strings "rows" answer <> [])
    (String.concat " | " (E4d_json.strings "rows" answer));

  let explained =
    Effect4_daemon.handle
      (E4d_json.Obj
         [ ("request", Str "explain"); ("source", Str "fixture"); ("family", Str "ref");
           ("program", Str "makeGet") ])
  in
  let rows = E4d_json.to_list (E4d_json.member "rows" explained) in
  let armed =
    List.filter
      (fun row ->
        E4d_json.str "kind" row = "op" && E4d_json.to_list (E4d_json.member "arms" row) <> [])
      rows
  in
  check "explain-names-the-avatar-handler" (List.length armed = 2)
    (String.concat ","
       (List.concat_map
          (fun row ->
            List.map (fun a -> E4d_json.str "arm" a) (E4d_json.to_list (E4d_json.member "arms" row)))
          armed));

  let versioned = Effect4_daemon.handle (E4d_json.Obj [ ("request", Str "version") ]) in
  check "version-names-the-host"
    (E4d_json.str "host" versioned = Effect4_daemon.host_name ())
    (E4d_json.str "host" versioned);

  Printf.printf "%s: %d failures\n" (if !failures = 0 then "PASS" else "FAIL") !failures;
  if !failures > 0 then exit 1
