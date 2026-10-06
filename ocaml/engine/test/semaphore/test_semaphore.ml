(* test_semaphore.ml -- three of Semaphore's cases on the generated engine, through the wire.

   What it is: decisions rows 259, 265 and 276.  Semaphore's operations are library programs
   of src/Effect4/Modules/Semaphore/Ops.lean, over the step terms of Steps.lean beside it.
   Test/Program/SemaphoreScenarios.lean runs the host probe's cases over them on Lean's
   machine.  This test runs three of those programs on the generated engine: P1, the
   protected case; P3, the overtaking case; and P9, which is P1's program under another tape.
   Decisions row 259 rests on these three: a waiter runs inside the task that resolves its
   hint, and a waiter that yields at its resume checks the count again.

   The fixture is semaphore.txt, beside this file.  Lean writes it from the programs that
   `Api.Author.build` admits (write.lean, beside this file).  A run of the fixture holds the
   fuel, the program's canonical bytes, and the root's exit of Lean's machine in the spelling
   of `show_exit` (ocaml/engine/e4_engine.ml).  A run may hold its tape as data: one line of
   decisions.  A run with no tape is the engine's own drive loop, the root evaluated and then
   one flush.  A root's exit holds the cell's counts before the release, the counts after the
   walk, and the marks of the fibers that took.

   Properties:
   S1  Each program crosses as its canonical bytes: `of_bytes` reads exactly one program, on
       BOTH instances (Fast and Ref).                                     tested (three runs)
   S2  On each instance the run finishes, and the root's exit is the exit Lean wrote.
                                                                          tested (three runs)
   S3  The two instances give one report: outcome, exits, fiber rows, trace rows, store row.
                                                                          tested (three runs)
   S4  The red controls.  The three runs' exits are three texts.  A program cut by one byte is
       refused, never repaired.  At a small fuel the run does not finish, and it has no root
       exit.                                                              tested
   S5  A run with a tape is replayed from that tape, and the tape is spent: the replay reads
       every decision.  The red controls of P9's one decision: under the engine's own drive
       loop, and under the same tape with the verdict `false`, P9's program gives P1's exit
       and not its own.                                                   tested (one run)

   What it does not establish: any schedule but the fixture's, a host run, the steps'
   agreement with the abstract model (proved in Lean, on the term's value), or delivery under
   another dispatcher.  The tape is three decisions: it is no law of the engine's replay.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine *)

open Effect4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ================================================================ the fixture's text *)

type run = {
  name : string;
  fuel : int;
  tape : string list;  (* the decisions, one word each; empty for the engine's own drive loop *)
  program : string;
  exit_text : string;
}

let words (line : string) : string list =
  List.filter (fun w -> w <> "") (String.split_on_char ' ' line)

let bytes_of_hex (hex : string) : string =
  match E4_hex.to_bytes hex with
  | Some b -> b
  | None -> failwith "fixture: the program is not hexadecimal"

(* The text after a line's first word and one space. *)
let after_word (line : string) (word : string) : string =
  let n = String.length word + 1 in
  String.sub line n (String.length line - n)

(* The fixture into its runs.  Any line this reader does not know is a failure: a fixture is
   never read loosely. *)
let read_fixture (path : string) : run list =
  let ic = open_in path in
  let rec lines acc =
    match input_line ic with
    | line -> lines (line :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  let rec runs acc = function
    | [] -> List.rev acc
    | line :: rest when line = "" || line.[0] = '#' -> runs acc rest
    | line :: rest ->
      (match words line with
       | [ "run"; name ] ->
         let run, rest =
           body { name; fuel = 0; tape = []; program = ""; exit_text = "" } rest
         in
         runs (run :: acc) rest
       | _ -> failwith (Printf.sprintf "fixture %s: expected `run`, read %S" path line))
  and body r = function
    | [] -> failwith (Printf.sprintf "fixture %s: run %s has no `end`" path r.name)
    | line :: rest ->
      (match words line with
       | [ "fuel"; n ] -> body { r with fuel = int_of_string n } rest
       | "tape" :: (_ :: _ as decisions) -> body { r with tape = decisions } rest
       | [ "program"; hex ] -> body { r with program = bytes_of_hex hex } rest
       | "exit" :: _ -> body { r with exit_text = after_word line "exit" } rest
       | [ "end" ] -> (r, rest)
       | _ -> failwith (Printf.sprintf "fixture %s: run %s, unknown line %S" path r.name line))
  in
  runs [] (lines [])

(* ================================================================ one report per run *)

type report = {
  outcome : string;
  root : string option;
  exits : (int * string) list;
  fibers : (int * string) list;
  trace : string list;
  store : string;
  unread : int;  (* the decisions of the tape that the replay did not read *)
}

module Rep (En : E4_engine.ENGINE) = struct
  (* One decision of a fixture's tape.  A word this reader does not know is a failure. *)
  let decision (word : string) : En.decision =
    match String.split_on_char ':' word with
    | [ "evaluate"; fiber ] -> En.evaluate (int_of_string fiber)
    | [ "flush" ] -> En.flush
    | [ "yieldVerdict"; fiber; verdict ] ->
      En.yield_verdict (int_of_string fiber) (bool_of_string verdict)
    | _ -> failwith (Printf.sprintf "fixture: unknown decision %S" word)

  (* The program from its bytes.  With no tape: the engine's own drive loop.  With a tape:
     that tape replayed from the loaded machine. *)
  let report (bytes : string) ~(fuel : int) ~(tape : string list) : report option =
    match En.of_bytes bytes with
    | None -> None
    | Some p ->
      let t, unread =
        match tape with
        | [] -> (En.run_program p ~fuel, [])
        | decisions -> En.replay_to (En.load_program p ~fuel) (List.map decision decisions)
      in
      Some
        { outcome = En.outcome t;
          root = En.root_exit t;
          exits = En.exits t;
          fibers = En.fiber_rows t;
          trace = En.trace_rows t;
          store = En.store_row t;
          unread = List.length unread }
end

module RF = Rep (E4_engine.Fast)
module RR = Rep (E4_engine.Ref)

let find_fixture () : string =
  let candidates =
    [ "semaphore.txt"; "engine/test/semaphore/semaphore.txt";
      "ocaml/engine/test/semaphore/semaphore.txt" ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith "semaphore.txt not found from the cwd"

(* The fixture's runs, in the order Lean writes them
   (Test.Program.SemaphoreScenarios.engineRuns). *)
let expected_names = [ "p1"; "p3"; "p9" ]

(* The fuel of the red control: no run of the fixture finishes at it
   (Test/Program/SemaphoreScenarios.lean guards the same on Lean's machine). *)
let small_fuel = 3

(* A tape with each verdict turned to `false`: the red control of P9's one decision. *)
let without_verdict (tape : string list) : string list =
  List.map
    (fun word ->
       match String.split_on_char ':' word with
       | [ "yieldVerdict"; fiber; _ ] -> String.concat ":" [ "yieldVerdict"; fiber; "false" ]
       | _ -> word)
    tape

let () =
  let runs = read_fixture (find_fixture ()) in
  check
    (Printf.sprintf "the fixture holds the three runs, in order (%d)" (List.length runs))
    (List.map (fun (r : run) -> r.name) runs = expected_names);
  List.iter
    (fun (r : run) ->
       Printf.printf "== run %s: %d bytes, fuel %d, tape [%s] ==\n" r.name
         (String.length r.program) r.fuel (String.concat " " r.tape);
       match
         (RF.report r.program ~fuel:r.fuel ~tape:r.tape,
          RR.report r.program ~fuel:r.fuel ~tape:r.tape)
       with
       | Some fast, Some slow ->
         check (r.name ^ ": S1 the program's bytes decode on both instances") true;
         check (r.name ^ ": S2 Fast finishes") (fast.outcome = "finished");
         check (r.name ^ ": S2 Ref finishes") (slow.outcome = "finished");
         Printf.printf "  Lean's exit: %s\n  Fast's exit: %s\n  Ref's exit:  %s\n" r.exit_text
           (Option.value fast.root ~default:"-") (Option.value slow.root ~default:"-");
         check (r.name ^ ": S2 Fast's root exit is the exit Lean wrote") (fast.root = Some r.exit_text);
         check (r.name ^ ": S2 Ref's root exit is the exit Lean wrote") (slow.root = Some r.exit_text);
         check (r.name ^ ": S3 Fast = Ref: outcome, exits, fibers, trace, store") (fast = slow);
         (* S4: a program cut by one byte is refused *)
         let cut = String.sub r.program 0 (String.length r.program - 1) in
         check (r.name ^ ": S4 a program cut by one byte is refused on both instances")
           (RF.report cut ~fuel:r.fuel ~tape:r.tape = None
            && RR.report cut ~fuel:r.fuel ~tape:r.tape = None);
         (* S4: at a small fuel the run does not finish *)
         (match
            (RF.report r.program ~fuel:small_fuel ~tape:r.tape,
             RR.report r.program ~fuel:small_fuel ~tape:r.tape)
          with
          | Some f, Some s ->
            check
              (Printf.sprintf "%s: S4 at fuel %d neither instance finishes, and none has a root exit"
                 r.name small_fuel)
              (f.outcome <> "finished" && s.outcome <> "finished" && f.root = None && s.root = None)
          | _ -> check (r.name ^ ": S4 the program decodes at the small fuel") false);
         (* S5: a run with a tape *)
         if r.tape <> [] then begin
           check (r.name ^ ": S5 the tape is spent on both instances: no decision is unread")
             (fast.unread = 0 && slow.unread = 0);
           let first = List.hd runs in
           (match
              (RF.report r.program ~fuel:r.fuel ~tape:[], RR.report r.program ~fuel:r.fuel ~tape:[])
            with
            | Some f, Some s ->
              check
                (r.name
                 ^ ": S5 under the engine's own drive loop the program gives the first run's exit, not its own")
                (f.root = Some first.exit_text && s.root = Some first.exit_text
                 && first.exit_text <> r.exit_text)
            | _ -> check (r.name ^ ": S5 the program decodes with no tape") false);
           (match
              (RF.report r.program ~fuel:r.fuel ~tape:(without_verdict r.tape),
               RR.report r.program ~fuel:r.fuel ~tape:(without_verdict r.tape))
            with
            | Some f, Some s ->
              check
                (r.name
                 ^ ": S5 with the verdict false the tape gives the first run's exit, not its own")
                (f.root = Some first.exit_text && s.root = Some first.exit_text
                 && f.unread = 0 && s.unread = 0)
            | _ -> check (r.name ^ ": S5 the program decodes with the other verdict") false)
         end
       | _ -> check (r.name ^ ": S1 the program's bytes decode on both instances") false)
    runs;
  (* S4: the three runs answer three exits, so each run's check can fail. *)
  (match runs with
   | [ a; b; c ] ->
     check "S4 the three runs' exits are three texts"
       (a.exit_text <> b.exit_text && a.exit_text <> c.exit_text && b.exit_text <> c.exit_text);
     check "S4 the first and the last run hold one program, under two tapes"
       (a.program = c.program && a.tape <> c.tape);
     (match
        (RF.report a.program ~fuel:a.fuel ~tape:a.tape,
         RR.report a.program ~fuel:a.fuel ~tape:a.tape)
      with
      | Some fast, Some slow ->
        check "S4 the first run's exit is not the second run's, on both instances"
          (fast.root <> Some b.exit_text && slow.root <> Some b.exit_text)
      | _ -> check "S4 the first run decodes" false)
   | _ -> check "S4 three runs to compare" false);
  Printf.printf "test_semaphore: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
