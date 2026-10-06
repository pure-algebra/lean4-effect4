(* test_queue.ml -- five of the Queue's programs on the generated engine, through the wire.

   What it is: decisions row 255.  The Queue's steps are terms of
   src/Effect4/Modules/Queue/Steps.lean, and its operations are the library programs of
   src/Effect4/Modules/Queue/Ops.lean.  Test/Program/QueueScenarios.lean and
   Test/Program/QueueMask.lean run nine programs over them on Lean's machine.  This test runs
   five of those programs on the generated engine:
     r1      a queue is filled and emptied;
     r4      a second offer waits at capacity one;
     r2      a taker waits, and an offer's posted helper wakes it;
     r5      a waiting taker is interrupted, and its withdrawal removes the request;
     masked  a taker under a masked caller keeps its request (decisions row 222).

   The fixture is queue.txt, beside this file.  Lean writes it from the programs that
   `Api.Author.build` admits (write.lean, beside this file).  A run of the fixture holds the
   fuel, the program's canonical bytes, and the root's exit of Lean's machine in the spelling
   of `show_exit` (ocaml/engine/e4_engine.ml).

   Properties:
   Q1  Each program crosses as its canonical bytes: `of_bytes` reads exactly one program, on
       BOTH instances (Fast and Ref).                                       tested
   Q2  On each instance the run finishes, and the root's exit is the exit Lean wrote.
                                                                            tested (five runs)
   Q3  The two instances give one report: outcome, exits, fiber rows, trace rows, store row.
                                                                            tested (five runs)
   Q4  The red controls.  The five exits are five texts, and a run's exit is not the next
       run's.  A program cut by one byte is refused, never repaired.  At a small fuel the run
       does not finish, and it has no root exit.                            tested

   What it does not establish: any schedule but the engine's own drive loop, a host run, the
   steps' agreement with the abstract model (proved in Lean, on the term's value), or
   delivery under another dispatcher.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine *)

open Effect4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ================================================================ the fixture's text *)

type run = { name : string; fuel : int; program : string; exit_text : string }

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
         let run, rest = body { name; fuel = 0; program = ""; exit_text = "" } rest in
         runs (run :: acc) rest
       | _ -> failwith (Printf.sprintf "fixture %s: expected `run`, read %S" path line))
  and body r = function
    | [] -> failwith (Printf.sprintf "fixture %s: run %s has no `end`" path r.name)
    | line :: rest ->
      (match words line with
       | [ "fuel"; n ] -> body { r with fuel = int_of_string n } rest
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
}

module Rep (En : E4_engine.ENGINE) = struct
  (* The program from its bytes, then the engine's own drive loop. *)
  let report (bytes : string) ~(fuel : int) : report option =
    match En.of_bytes bytes with
    | None -> None
    | Some p ->
      let t = En.run_program p ~fuel in
      Some
        { outcome = En.outcome t;
          root = En.root_exit t;
          exits = En.exits t;
          fibers = En.fiber_rows t;
          trace = En.trace_rows t;
          store = En.store_row t }
end

module RF = Rep (E4_engine.Fast)
module RR = Rep (E4_engine.Ref)

let find_fixture () : string =
  let candidates = [ "queue.txt"; "engine/test/queue/queue.txt"; "ocaml/engine/test/queue/queue.txt" ] in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith "queue.txt not found from the cwd"

let () =
  let runs = read_fixture (find_fixture ()) in
  check (Printf.sprintf "the fixture holds five runs (%d)" (List.length runs)) (List.length runs = 5);
  check "the fixture's runs are r1, r4, r2, r5 and masked, in that order"
    (List.map (fun (r : run) -> r.name) runs = [ "r1"; "r4"; "r2"; "r5"; "masked" ]);
  List.iter
    (fun (r : run) ->
       Printf.printf "== run %s: %d bytes, fuel %d ==\n" r.name (String.length r.program) r.fuel;
       match (RF.report r.program ~fuel:r.fuel, RR.report r.program ~fuel:r.fuel) with
       | Some fast, Some slow ->
         check (r.name ^ ": Q1 the program's bytes decode on both instances") true;
         check (r.name ^ ": Q2 Fast finishes") (fast.outcome = "finished");
         check (r.name ^ ": Q2 Ref finishes") (slow.outcome = "finished");
         Printf.printf "  Lean's exit: %s\n  Fast's exit: %s\n" r.exit_text
           (Option.value fast.root ~default:"-");
         check (r.name ^ ": Q2 Fast's root exit is the exit Lean wrote") (fast.root = Some r.exit_text);
         check (r.name ^ ": Q2 Ref's root exit is the exit Lean wrote") (slow.root = Some r.exit_text);
         check (r.name ^ ": Q3 Fast = Ref: outcome, exits, fibers, trace, store") (fast = slow);
         (* Q4: a program cut by one byte is refused *)
         let cut = String.sub r.program 0 (String.length r.program - 1) in
         check (r.name ^ ": Q4 a program cut by one byte is refused on both instances")
           (RF.report cut ~fuel:r.fuel = None && RR.report cut ~fuel:r.fuel = None);
         (* Q4: at a small fuel the run does not finish *)
         (match (RF.report r.program ~fuel:5, RR.report r.program ~fuel:5) with
          | Some f, Some s ->
            check (r.name ^ ": Q4 at fuel 5 neither instance finishes, and none has a root exit")
              (f.outcome <> "finished" && s.outcome <> "finished" && f.root = None && s.root = None)
          | _ -> check (r.name ^ ": Q4 the program decodes at fuel 5") false)
       | _ -> check (r.name ^ ": Q1 the program's bytes decode on both instances") false)
    runs;
  (* Q4: the runs answer pairwise different exits, so each run's check can fail. *)
  let texts = List.sort_uniq compare (List.map (fun (r : run) -> r.exit_text) runs) in
  check (Printf.sprintf "Q4 the runs' exits are %d texts for %d runs" (List.length texts) (List.length runs))
    (List.length texts = List.length runs);
  let rec neighbours = function
    | (a : run) :: ((b : run) :: _ as rest) ->
      (match RF.report a.program ~fuel:a.fuel with
       | Some fast -> check (a.name ^ ": Q4 its exit is not " ^ b.name ^ "'s") (fast.root <> Some b.exit_text)
       | None -> check (a.name ^ ": Q4 the run decodes") false);
      neighbours rest
    | _ -> ()
  in
  neighbours runs;
  Printf.printf "test_queue: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
