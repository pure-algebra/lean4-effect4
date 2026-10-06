(* test_mask.ml -- the mask that restores, on the generated engine, through the wire.

   What it is: decisions rows 244 to 246.  The mask is the getter `getInterruptible`, a fiber
   action, and the node `restore saved body`.  Test/Program/MaskContract.lean runs the host
   probe's scenarios over them on Lean's machine.  This test runs ten of those programs on the
   generated engine: the getter's two answers (s1), a masked wait that is interrupted at a
   restore site (s2), the same wait under a masked caller (s3), a body with no restore site
   (s4), nested masks (s5inner, s5outer), a saved value that a fork captures (s6), the flag
   after each exit (s7), the flag at five places of a body (s9), and a saved value applied
   after its mask (s10).

   The fixture is mask.txt, beside this file.  Lean writes it from the programs that
   `Api.Author.build` admits (write.lean, beside this file).  A run of the fixture holds the
   fuel, the program's canonical bytes, and the root's exit of Lean's machine in the spelling
   of `show_exit` (ocaml/engine/e4_engine.ml).

   Properties:
   M1  Each program crosses as its canonical bytes: `of_bytes` reads exactly one program, on
       BOTH instances (Fast and Ref).                                       tested (ten runs)
   M2  On each instance the run finishes, and the root's exit is the exit Lean wrote.
                                                                            tested (ten runs)
   M3  The two instances give one report: outcome, exits, fiber rows, trace rows, store row.
                                                                            tested (ten runs)
   M4  The red controls.  The interrupted wait's exit is not the masked caller's.  A program
       cut by one byte is refused, never repaired.  At a small fuel the run does not finish,
       and it has no root exit.                                             tested

   What it does not establish: any schedule but the engine's own drive loop, a host run, the
   laws of the mask (proved in Lean, on the machine), or the behaviour of the printed form on
   a target.

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
  let candidates = [ "mask.txt"; "engine/test/mask/mask.txt"; "ocaml/engine/test/mask/mask.txt" ] in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith "mask.txt not found from the cwd"

(* The fixture's runs, in the order Lean writes them (Test.Program.MaskContract.engineRuns). *)
let expected_names =
  [ "s1"; "s2"; "s3"; "s4"; "s5inner"; "s5outer"; "s6"; "s7"; "s9"; "s10" ]

(* The fuel of the red control: no run of the fixture finishes at it
   (Test/Program/MaskContract.lean guards the same on Lean's machine). *)
let small_fuel = 3

let () =
  let runs = read_fixture (find_fixture ()) in
  check
    (Printf.sprintf "the fixture holds the ten runs, in order (%d)" (List.length runs))
    (List.map (fun (r : run) -> r.name) runs = expected_names);
  List.iter
    (fun (r : run) ->
       Printf.printf "== run %s: %d bytes, fuel %d ==\n" r.name (String.length r.program) r.fuel;
       match (RF.report r.program ~fuel:r.fuel, RR.report r.program ~fuel:r.fuel) with
       | Some fast, Some slow ->
         check (r.name ^ ": M1 the program's bytes decode on both instances") true;
         check (r.name ^ ": M2 Fast finishes") (fast.outcome = "finished");
         check (r.name ^ ": M2 Ref finishes") (slow.outcome = "finished");
         Printf.printf "  Lean's exit: %s\n  Fast's exit: %s\n  Ref's exit:  %s\n" r.exit_text
           (Option.value fast.root ~default:"-") (Option.value slow.root ~default:"-");
         check (r.name ^ ": M2 Fast's root exit is the exit Lean wrote") (fast.root = Some r.exit_text);
         check (r.name ^ ": M2 Ref's root exit is the exit Lean wrote") (slow.root = Some r.exit_text);
         check (r.name ^ ": M3 Fast = Ref: outcome, exits, fibers, trace, store") (fast = slow);
         (* M4: a program cut by one byte is refused *)
         let cut = String.sub r.program 0 (String.length r.program - 1) in
         check (r.name ^ ": M4 a program cut by one byte is refused on both instances")
           (RF.report cut ~fuel:r.fuel = None && RR.report cut ~fuel:r.fuel = None);
         (* M4: at a small fuel the run does not finish *)
         (match (RF.report r.program ~fuel:small_fuel, RR.report r.program ~fuel:small_fuel) with
          | Some f, Some s ->
            check
              (Printf.sprintf "%s: M4 at fuel %d neither instance finishes, and none has a root exit"
                 r.name small_fuel)
              (f.outcome <> "finished" && s.outcome <> "finished" && f.root = None && s.root = None)
          | _ -> check (r.name ^ ": M4 the program decodes at the small fuel") false)
       | _ -> check (r.name ^ ": M1 the program's bytes decode on both instances") false)
    runs;
  (* M4: the interrupted wait and the masked caller's wait answer two exits, so each run's
     check can fail. *)
  (match
     ( List.find_opt (fun (r : run) -> r.name = "s2") runs,
       List.find_opt (fun (r : run) -> r.name = "s3") runs )
   with
   | Some a, Some b ->
     check "M4 the exits of s2 and s3 are two texts" (a.exit_text <> b.exit_text);
     (match (RF.report a.program ~fuel:a.fuel, RR.report a.program ~fuel:a.fuel) with
      | Some fast, Some slow ->
        check "M4 the exit of s2 is not the exit of s3, on both instances"
          (fast.root <> Some b.exit_text && slow.root <> Some b.exit_text)
      | _ -> check "M4 the run s2 decodes" false)
   | _ -> check "M4 the runs s2 and s3 are in the fixture" false);
  Printf.printf "test_mask: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
