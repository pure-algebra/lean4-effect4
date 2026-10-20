(* test_scenarios.ml -- the machine clause of the dogfood scenarios, on the generated engine.

   What it is: decisions row 254.  A scenario of Test/Dogfood/Scenario/ compares one named
   observation.  The generated engine holds no session, so the observation lands as two
   clauses: the session clause, checked in Lean, and the machine clause, checked here.  The
   machine clause is `Effect4.Run.machineView`: the root's exit, the cells, the calls
   the machine waits on, the armed owners, the runnable fibers and the timers.

   The fixtures are the *.txt files beside this one, written by Lean from the programs
   `Api.Author.build` admits (Test/Dogfood/Scenario/Lowered.lean; the writer is write.lean,
   beside this file).  A run of a fixture holds the program's canonical bytes, each row's
   canonical bytes, the budgets, and the machine tape: each decision that moved Lean's session
   machine, with the view after it.

   The adapter lives here and changes no production interface.  `E4_engine.INSTANCE` takes the
   row table, but it steps one decision at a time; this test reads a view after every prefix
   of a tape, so it calls the generated `api_replay` itself, with the program, the command
   fuel, the tape, the row table and the compile fuel.

   Properties:
   S1  The row table is read from its rows' canonical bytes (`Eff_codec.decode_rows`, Lean's
       reading, lowered). The row type is `Eff_types`', which the generated engine opens, so no
       conversion stands between the bytes and the engine. A row with trailing arguments is
       refused.                                                          by construction
   S2  At every position of every run, on the engine's instance (Fast), the view of
       `api_replay` on the tape's prefix is the view Lean wrote for its session machine.
                                                                 tested (finite runs)
   S3  A value crosses as its canonical bytes: `Eff_val.decode` reads Lean's `Val.encode`, and
       `Eff_val.emit` writes the engine's value back in the same frames.  For every value a
       fixture's tape carries, `emit (decode bytes) = bytes`.               tested
   S4  The table, and the red controls.  A fixture's line `table differs` or `table same`
       is one observed difference, in one projection: whether Lean's raw replay with the
       empty table (what the production wrappers supply) shows another machine view
       (`machineViewOf`) at some position than its replay with the built table.  The engine
       must show the same answer, in both directions.  `table same` does NOT say that the
       replay reads no row: `prepareExternalAnswer` (src/Effect4/Program/Compile.lean)
       consults a nonempty table for each successful reply, and an answer with no handle can
       come out the same.  A tape cut before its last decision that moves the view ends at
       another view than the full tape's.  The cut is Lean's: the last position at which two
       neighbouring view lines of the fixture differ.  The engine's own views choose nothing.
       A run of two or more decisions in which no decision moves the view fails: it is not
       skipped.  The decisions after the cut move nothing, and S2 compares each of their
       positions, so they get no second comparison.  A row whose bytes are cut is refused,
       never repaired.                                                     tested
   S5  A run whose fixture ends at a frontier is compared up to that position only, and its
       unread rows are reported: a frontier is never read as a reply application.
                                                                 by construction

   What it does not establish: the session clause on the engine (the engine has no stored
   reply, no retired call, no consumed call), any schedule but the fixtures', or the host run.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine *)

open Effect4_engine
open Eff_types

let check = E4_check.check

(* ================================================================ the fixture's text *)

type run =
  { name : string
  ; fuel : int
  ; compile : int
  ; program : string (* canonical bytes *)
  ; rows : string list (* canonical bytes, in table order *)
  ; observed_table_difference : bool
    (* whether Lean's raw replay with the empty table shows another machine view on this run *)
  ; first : string (* the view line of the loaded machine *)
  ; steps : (string list * string) list
    (* a decision's words, and the view line after it *)
  ; ending : string list (* ["tape"], or ["frontier"; rows left] *)
  }

let words (line : string) : string list =
  List.filter (fun w -> w <> "") (String.split_on_char ' ' line)
;;

let bytes_of_hex (what : string) (hex : string) : string =
  match E4_hex.to_bytes hex with
  | Some b -> b
  | None -> failwith (Printf.sprintf "fixture: %s is not hexadecimal" what)
;;

(* One fixture file into its runs.  Any line this reader does not know is a failure: a fixture
   is never read loosely. *)
let read_fixture (path : string) : run list =
  let ic = open_in path in
  let rec lines acc =
    match input_line ic with
    | line -> lines (line :: acc)
    | exception End_of_file ->
      close_in ic;
      List.rev acc
  in
  let rec runs acc = function
    | [] -> List.rev acc
    | line :: rest when line = "" || line.[0] = '#' -> runs acc rest
    | line :: rest ->
      (match words line with
       | [ "run"; name ] ->
         let run, rest =
           body
             { name
             ; fuel = 0
             ; compile = 0
             ; program = ""
             ; rows = []
             ; observed_table_difference = false
             ; first = ""
             ; steps = []
             ; ending = []
             }
             rest
         in
         runs (run :: acc) rest
       | _ -> failwith (Printf.sprintf "fixture %s: expected `run`, read %S" path line))
  and body r = function
    | [] -> failwith (Printf.sprintf "fixture %s: run %s has no `end`" path r.name)
    | line :: rest ->
      (match words line with
       | [ "fuel"; n ] -> body { r with fuel = int_of_string n } rest
       | [ "compile"; n ] -> body { r with compile = int_of_string n } rest
       | [ "program"; hex ] ->
         body { r with program = bytes_of_hex "the program" hex } rest
       | [ "row"; hex ] ->
         body { r with rows = r.rows @ [ bytes_of_hex "a row" hex ] } rest
       | [ "table"; "differs" ] -> body { r with observed_table_difference = true } rest
       | [ "table"; "same" ] -> body { r with observed_table_difference = false } rest
       | "view" :: _ when r.first = "" -> body { r with first = line } rest
       | "step" :: decision ->
         (match rest with
          | view :: rest'
            when match words view with
                 | "view" :: _ -> true
                 | _ -> false ->
            body { r with steps = r.steps @ [ decision, view ] } rest'
          | _ ->
            failwith (Printf.sprintf "fixture %s: a step of %s has no view" path r.name))
       | "end" :: ending -> { r with ending }, rest
       | _ ->
         failwith (Printf.sprintf "fixture %s: run %s, unknown line %S" path r.name line))
  in
  runs [] (lines [])
;;

(* ================================================================ the generated engine *)

(* What the adapter reads of a generated instance beyond `E4_engine.INSTANCE`: the replay with
   its table, and the declarations of the generated type group it names.  `ocamlopt` checks each
   against both instances, so a field or a constructor that moves in api_engine.ml is a build
   error here. *)
module type GEN = sig
  include E4_engine.INSTANCE

  type key =
    { fiber : fiber_id
    ; token : int
    }

  type frontier_reason =
    | FrontierReason_commandFuel
    | FrontierReason_compileFuel of fiber_id
    | FrontierReason_awaitHost of key
    | FrontierReason_awaitTimer of fiber_id * E4_clock.t
    | FrontierReason_awaitDecision

  type inspection =
    { outcome : outcome
    ; machine : machine
    ; reasons : frontier_reason list
    }

  val api_replay : program -> int -> api_decision list -> Row.t list -> int -> inspection
end

(* The one reading that must name a carrier: the timer store's waiters. *)
module type TIMERS = sig
  type machine

  val timers : machine -> (int * E4_clock.t) list
end

module Adapter (A : GEN) (T : TIMERS with type machine = A.machine) = struct
  (* The table from its wire bytes. A row that is not exactly one row is refused, and so is a
     row with trailing arguments: the engine reads none. The row is `Eff_types`', the one
     program type the engine opens, so nothing converts. *)
  let table_of (rows : string list) : (Row.t list, string) result =
    match Eff_codec.decode_rows rows with
    | None -> Error "a row's bytes are not exactly one row"
    | Some table ->
      (match List.find_opt (fun (r : Row.t) -> r.Row.trailing <> []) table with
       | Some r -> Error (r.Row.spelling ^ ": trailing arguments")
       | None -> Ok table)
  ;;

  (* ------------------------------------------------------------ S3: values as bytes *)

  (* The value frames are Eff_val's, the lanes' one writer and reader of `Val.encode`. *)
  let hex_of_val (v : Eff_types.Val.t) : string = E4_hex.of_bytes (Eff_val.to_bytes v)

  let val_of_hex (hex : string) : Val.t =
    match Eff_val.decode_exact (bytes_of_hex "a value" hex) with
    | Some v -> v
    | None -> failwith "fixture: a value's bytes are not exactly one value"
  ;;

  let text_of_word (word : string) : string =
    if String.length word > 0 && word.[0] = 's'
    then bytes_of_hex "a text" (String.sub word 1 (String.length word - 1))
    else failwith "fixture: a text does not start with `s`"
  ;;

  (* ------------------------------------------------------------ the tape's decisions *)

  let decision_of (ws : string list) : A.api_decision =
    match ws with
    | [ "fire"; f ] -> A.RunDecision_fire (int_of_string f)
    | [ "flush" ] -> A.RunDecision_flush
    | [ "evaluate"; f ] -> A.RunDecision_evaluate (int_of_string f)
    | [ "yield"; f; verdict ] ->
      A.RunDecision_yieldVerdict (int_of_string f, verdict = "1")
    | [ "answer"; f; token; "ok"; hex ] ->
      A.RunDecision_answerAsync
        ( int_of_string f
        , int_of_string token
        , Eff_types.Completion.OfExit (Eff_types.Exit.Success (val_of_hex hex)) )
    | [ "answer"; f; token; "failed"; tag; message ] ->
      A.RunDecision_answerAsync
        ( int_of_string f
        , int_of_string token
        , Eff_types.Completion.OfExit
            (Eff_types.Exit.Failure
               [ Eff_types.Reason.Fail
                   (Eff_types.Err.Tagged (text_of_word tag, text_of_word message), [])
               ]) )
    | [ "interrupt"; who; target ] ->
      A.RunDecision_interruptFrom
        ((if who = "-" then None else Some (int_of_string who)), [], int_of_string target)
    | [ "middleware" ] -> A.RunDecision_installMiddleware
    | [ "advance"; millis ] ->
      (match E4_clock.of_decimal millis with
       | Some t -> A.RunDecision_advance t
       | None -> failwith "fixture: a clock step is not a canonical decimal")
    | _ -> failwith ("fixture: unknown decision " ^ String.concat " " ws)
  ;;

  (* ------------------------------------------------------------ S2: the view *)

  let items (texts : string list) : string =
    if texts = [] then "-" else String.concat "," texts
  ;;

  let outcome_word : A.outcome -> string = function
    | A.Outcome_finished -> "finished"
    | A.Outcome_frontier -> "frontier"
    | A.Outcome_stuck _ -> "stuck"
  ;;

  (* The view line of an inspection: the same seven readings, in the same spelling, as
     `Test.Dogfood.Scenario.Lowered.viewText`. *)
  let view_of (r : A.inspection) : string =
    let m = r.A.machine in
    let fibers = A.fibers m in
    let root =
      match List.assoc_opt 0 fibers with
      | None -> "-"
      | Some f ->
        (match A.f_exit f with
         | None -> "-"
         | Some e -> hex_of_val (A.reify_exit_val e))
    in
    let cells = items (List.map hex_of_val (A.refs m)) in
    let awaiting =
      items
        (List.map
           (fun (a : A.await) ->
              Printf.sprintf
                "%d.%d.%s.%s"
                a.A.fiber
                a.A.token
                (match a.A.op with
                 | Eff_types.NativeOp.External i -> string_of_int i
                 | _ -> "x")
                (hex_of_val a.A.request))
           (A.program_awaits m))
    in
    let queued = items (List.map string_of_int (A.armed_of m)) in
    let runnable =
      items
        (List.filter_map
           (fun (id, f) ->
              if A.f_exit f = None && A.f_parked f = A.Parked_notParked
              then Some (string_of_int id)
              else None)
           fibers)
    in
    let timers =
      items
        (List.map
           (fun (f, at) -> Printf.sprintf "%d@%s" f (E4_clock.to_decimal at))
           (T.timers m))
    in
    String.concat
      " "
      [ "view"
      ; outcome_word r.A.outcome
      ; root
      ; cells
      ; awaiting
      ; queued
      ; runnable
      ; timers
      ]
  ;;

  (* ------------------------------------------------------------ one run *)

  let rec take n = function
    | [] -> []
    | x :: xs -> if n = 0 then [] else x :: take (n - 1) xs
  ;;

  (* The views of `api_replay` on every prefix of a tape, the loaded machine first. *)
  let views
        (program : A.program)
        (r : run)
        (table : Row.t list)
        (tape : A.api_decision list)
    : string list
    =
    List.init
      (List.length tape + 1)
      (fun count ->
         view_of (A.api_replay program r.fuel (take count tape) table r.compile))
  ;;

  (* The positions at which the engine's view is not the fixture's; `-1` for another length. *)
  let differs (expected : string list) (got : string list) : int list =
    if List.length expected <> List.length got
    then [ -1 ]
    else
      List.filter
        (fun i -> List.nth expected i <> List.nth got i)
        (List.init (List.length got) Fun.id)
  ;;

  let run_one (r : run) : unit =
    let label what = Printf.sprintf "%s %s: %s" A.name r.name what in
    match Eff_codec.decode_program r.program with
    | None -> check (label "the program's bytes are exactly one program") false
    | Some program ->
      (match table_of r.rows with
       | Error m -> check (label ("the row table converts: " ^ m)) false
       | Ok table ->
         let tape = List.map (fun (ws, _) -> decision_of ws) r.steps in
         let expected = r.first :: List.map snd r.steps in
         let got = views program r table tape in
         let bad = differs expected got in
         check
           (label
              (Printf.sprintf
                 "the engine's view is Lean's at each of %d positions"
                 (List.length expected)))
           (bad = []);
         List.iter
           (fun i ->
              if i >= 0
              then
                Printf.printf
                  "  position %d\n    Lean   %s\n    engine %s\n"
                  i
                  (List.nth expected i)
                  (List.nth got i))
           bad;
         (* S5: a fixture that ends at a frontier names the rows it left unread. *)
         (match r.ending with
          | [ "tape" ] -> ()
          | [ "frontier"; left ] ->
            Printf.printf
              "  %s stops at a frontier: %s rows of the journal are not replayed\n"
              r.name
              left
          | _ ->
            check (label "the run's last line is `end tape` or `end frontier n`") false);
         (* S3: every value of the tape re-encodes to its own bytes. *)
         let values =
           List.filter_map
             (fun (ws, _) ->
                match ws with
                | [ "answer"; _; _; "ok"; hex ] -> Some hex
                | _ -> None)
             r.steps
         in
         check
           (label
              (Printf.sprintf
                 "%d answer values re-encode to their own bytes"
                 (List.length values)))
           (List.for_all (fun hex -> hex_of_val (val_of_hex hex) = hex) values);
         (* S4: the red control of every run with two decisions or more.  The cut is Lean's: the
            last position at which two neighbouring view lines of the fixture differ.  The
            engine's replay of the tape before that decision must end at another view than the
            fixture's last.  A run in which no decision moves the view has no cut, and it
            fails. *)
         if List.length tape >= 2
         then (
           let moving =
             List.filter
               (fun i -> List.nth expected i <> List.nth expected (i + 1))
               (List.init (List.length tape) Fun.id)
           in
           check
             (label
                "the tape cut before its last decision that moves the view ends at \
                 another view (red control)")
             (match List.rev moving with
              | [] -> false
              | cut :: _ ->
                view_of (A.api_replay program r.fuel (take cut tape) table r.compile)
                <> List.nth expected (List.length tape)));
         (* S4: the table and its red control, on a run with a host row. *)
         if r.rows <> []
         then (
           check
             (label
                (if r.observed_table_difference
                 then "with the empty table some machine view differs, as in Lean"
                 else "with the empty table every machine view is the same, as in Lean"))
             (differs expected (views program r [] tape)
              <> []
              = r.observed_table_difference);
           check
             (label "a row whose bytes are cut is refused (red control)")
             (match
                table_of (List.map (fun b -> String.sub b 0 (String.length b - 1)) r.rows)
              with
              | Error _ -> true
              | Ok _ -> false)))
  ;;
end

module Fast =
  Adapter
    (Api_engine_inst)
    (struct
      type machine = Api_engine_inst.machine

      let timers (m : machine) : (int * E4_clock.t) list =
        List.map
          (fun (w : E4_clock.t Api_engine_inst.waiter) ->
             w.Api_engine_inst.fiber, w.Api_engine_inst.payload)
          (Api_engine_inst.stores_of m).Api_engine_inst.timers.Api_engine_inst.wake
            .Api_engine_inst.waiters
      ;;
    end)

(* ================================================================ main *)

let () =
  let dir = "." in
  let files =
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".txt")
    |> List.sort compare
  in
  check "the scenario fixtures are present" (files <> []);
  let positions = ref 0 in
  List.iter
    (fun file ->
       let runs = read_fixture (Filename.concat dir file) in
       Printf.printf "== %s: %d runs ==\n" file (List.length runs);
       check (Printf.sprintf "%s holds at least one run" file) (runs <> []);
       List.iter
         (fun r ->
            positions := !positions + List.length r.steps + 1;
            Fast.run_one r)
         runs)
    files;
  Printf.printf "%d positions compared on the engine's instance\n" !positions;
  E4_check.finish ()
;;
