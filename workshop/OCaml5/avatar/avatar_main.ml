(* The avatar's entry point: one program, one tape, one TSV on stdout.

   Reads `EFFECT4_PROGRAM`, `EFFECT4_TAPE`, `EFFECT4_RULES`, `EFFECT4_PIN` and
   `EFFECT4_SHA` from the environment the way `harness/trace/fiber-tail.ts` does, and prints
   the estate's golden shape with `face ocaml`. `EFFECT4_EVENTS=1` prints the machine's own
   `RunEvent` trace after the rows, commented out with a leading `#`. *)

open Deep_fibers

let getenv name default = match Sys.getenv_opt name with Some v -> v | None -> default

let () =
  let name = getenv "EFFECT4_PROGRAM" "raceImmediateSuccessStopsLaunch" in
  let tape = getenv "EFFECT4_TAPE" "" in
  let rules = getenv "EFFECT4_RULES" "" in
  let pin = getenv "EFFECT4_PIN" "" in
  let sha = getenv "EFFECT4_SHA" "" in
  let family = getenv "EFFECT4_FAMILY" "fiber" in
  let table =
    match family with
    | "fiber" -> Fibers_fixture.programs
    | "ref" -> Store_fixtures.ref_programs
    | "deferred" -> Store_fixtures.deferred_programs
    | "scope" -> Store_fixtures.scope_programs
    | "layer" -> Store_fixtures.layer_programs
    | "extra" -> Extra_fixture.programs
    | other -> failwith ("unknown family " ^ other)
  in
  let program =
    match List.assoc_opt name table with
    | Some p -> p
    | None -> failwith ("unknown program " ^ name)
  in
  Tape.load tape;
  max_ops_before_yield := int_of_string (getenv "EFFECT4_MAX_OPS" (string_of_int max_int));
  let m = machine_empty state in
  let fuel = int_of_string (getenv "EFFECT4_FUEL" (string_of_int default_fuel)) in
  (match run_program m fuel program with
   | Rfinished e -> push_row (Rdone e)
   | Rfrontier -> push_row Rfrontier
   | Rstuck _ -> push_row Rfrontier);
  let head =
    Avatar_trace.header ~generator_sha:sha
      ~inputs:
        [ ("workshop/OCaml5/avatar/deep_fibers.ml", sha);
          ("workshop/OCaml5/avatar/avatar_trace.ml", sha);
          ("workshop/OCaml5/avatar/fibers_fixture.ml", sha);
          ("workshop/OCaml5/avatar/store_fixtures.ml", sha);
          ("workshop/OCaml5/avatar/extra_fixture.ml", sha) ]
      ~pin ~program:(family ^ "." ^ name) ~tape ~rules
  in
  List.iter print_endline head;
  List.iter (fun r -> print_endline (Avatar_trace.render_row r)) !sink;
  (* The yield count the host tails report (`EFFECT4_EXPECT_YIELDS`): one per injection. *)
  let yields =
    List.length (List.filter (function YieldInjected _ -> true | _ -> false) m.trace)
  in
  if getenv "EFFECT4_YIELDS" "" = "1" then
    print_endline (Printf.sprintf "#\tyields\t%d" yields);
  if getenv "EFFECT4_EVENTS" "" = "1" then
    List.iter (fun e -> print_endline ("#\t" ^ Avatar_trace.render_event e)) m.trace;
  if getenv "EFFECT4_STATUS" "" = "1" then begin
    print_endline
      (Printf.sprintf "#\tfinished\t%b\tstuck\t%s" (machine_finished m)
         (match m.stuck with
          | None -> "-"
          | Some (UnknownFiber f) -> Printf.sprintf "unknownFiber(%d)" f
          | Some (UnknownScope s) -> Printf.sprintf "unknownScope(%d)" s));
    List.iter
      (fun f ->
        print_endline
          (Printf.sprintf "#\tfiber\t%d\tstatus\t%s\tobservers\t%d\tchildren\t[%s]" f.id
             (match run_fiber_status f with
              | Sdone -> "done"
              | Sfinalizing -> "finalizing"
              | Srunning -> "running"
              | Swaiting t -> Printf.sprintf "waiting(%d)" t
              | Srunnable -> "runnable")
             (List.length f.observers)
             (String.concat ";" (List.map string_of_int f.children))))
      m.fibers
  end
