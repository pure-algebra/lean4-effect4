(* Properties: qcheck-stm compares actual owned-writer command lists to transitions emitted
   by Lean Cas. Unknown or missing oracle transitions refuse before disk operations.
   The finite observation is ordered node bytes and complete roots; each image separately
   checks its durable boundary and retained snapshots. No copied store interpreter appears. *)
open Effect4_engine_cas
open Disk_test_support

let action_count = 14
let command_bound = 40
let table = Hashtbl.create 128

let load_oracle path =
  let channel = open_in path in
  let states = Hashtbl.create 16 in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () ->
       let rec loop () =
         match input_line channel with
         | exception End_of_file -> ()
         | line when String.length line > 0 && line.[0] = '#' -> loop ()
         | line ->
           (match String.split_on_char '\t' line with
            | [ state; command; next; answer; image ] ->
              let state = int_of_string state
              and command = int_of_string command
              and next = int_of_string next in
              require (command >= 0 && command < action_count) "unknown oracle action";
              require
                (not (Hashtbl.mem table (state, command)))
                "duplicate oracle transition";
              Hashtbl.add table (state, command) (next, answer, image);
              Hashtbl.replace states state ();
              Hashtbl.replace states next ();
              loop ()
            | _ -> failwith "malformed oracle transition")
       in
       loop ());
  require (Hashtbl.mem states 0) "oracle has no initial state";
  Hashtbl.iter
    (fun state () ->
       for command = 0 to action_count - 1 do
         require (Hashtbl.mem table (state, command)) "missing oracle transition"
       done)
    states;
  Printf.printf
    "actual Cas oracle: %d states, %d actions, %d transitions, command-list bound %d\n%!"
    (Hashtbl.length states)
    action_count
    (Hashtbl.length table)
    command_bound
;;

let lookup state command =
  if command < 0 || command >= action_count
  then Error "unknown oracle action"
  else (
    match Hashtbl.find_opt table (state, command) with
    | Some value -> Ok value
    | None -> Error "missing oracle transition")
;;

module Spec = struct
  type cmd = int
  type state = int

  type sut =
    { directory : string
    ; mutable disk : E4_disk.t
    ; mutable state : int
    ; mutable retained : (E4_disk.image * string * (int * int)) list
    }

  let init_state = 0
  let show_cmd = string_of_int
  let arb_cmd _ = QCheck.make ~print:show_cmd (QCheck.Gen.int_bound (action_count - 1))

  let next_state command state =
    match lookup state command with
    | Ok (next, _, _) -> next
    | Error reason -> failwith reason
  ;;

  let precond _ _ = true

  let init_sut () =
    let directory = temp () in
    { directory; disk = open_ directory; state = 0; retained = [] }
  ;;

  let cleanup sut =
    E4_disk.close sut.disk;
    remove sut.directory
  ;;

  let operate command sut =
    let commit nodes moves =
      transaction_observation (E4_disk.commit sut.disk (transaction nodes moves))
    in
    match command with
    | 0 -> commit [ schema; a; b ] []
    | 1 -> commit [] [ E4_control.Create ("docs/a", E4_control.Swap, target aa) ]
    | 2 ->
      commit
        []
        [ E4_control.Advance ("docs/a", { digest = aa; generation = Z.one }, target ba) ]
    | 3 ->
      commit
        []
        [ E4_control.Advance
            ("docs/a", { digest = ba; generation = Z.of_int 2 }, target aa)
        ]
    | 4 ->
      commit
        []
        [ E4_control.Advance
            ("docs/a", { digest = aa; generation = Z.of_int 3 }, target aa)
        ]
    | 5 ->
      commit
        []
        [ E4_control.Advance
            ( "docs/a"
            , { digest = aa; generation = Z.one }
            , { kind = E4_kind.Schema; digest = s } )
        ]
    | 6 ->
      commit
        [ t; u ]
        [ E4_control.Advance ("missing", { digest = aa; generation = Z.one }, target ua) ]
    | 7 -> commit [ t; u ] [ E4_control.Create ("docs/b", E4_control.Swap, target ua) ]
    | 8 ->
      "read:"
      ^
        (match get (E4_disk.read sut.disk aa) with
        | None -> "none"
        | Some bytes -> E4_hex.of_bytes bytes)
    | 9 ->
      let image = snapshot sut.disk in
      sut.retained <- (image, observation image, E4_disk.boundary image) :: sut.retained;
      "snapshot"
    | 10 ->
      E4_disk.close sut.disk;
      let cache = Filename.concat sut.directory "index/000000.idx" in
      if Sys.file_exists cache then Sys.remove cache;
      sut.disk <- open_ sut.directory;
      "reopen"
    | 11 | 12 ->
      let raw =
        (if command = 12 then "\001" else "\000")
        ^ String.make 1 (Char.chr (E4_kind.byte E4_kind.Export))
        ^ E4_node.zero_digest
        ^ E4_be.framed 253 ""
      in
      transaction_observation
        (E4_disk.commit sut.disk { txn_nodes = [ raw ]; txn_moves = [] })
    | 13 -> commit [ node E4_kind.Export E4_node.zero_digest (vstr "missing-spec") ] []
    | _ -> failwith "unknown oracle action"
  ;;

  let run command sut =
    match lookup sut.state command with
    | Error reason -> STM.Res (STM.string, "oracle-refused:" ^ reason)
    | Ok (next, _, _) ->
      let retained_ok () =
        List.for_all
          (fun (image, before, boundary) ->
             String.equal (observation image) before && E4_disk.boundary image = boundary)
          sut.retained
      in
      let answer = operate command sut in
      sut.state <- next;
      let actual = answer ^ "\t" ^ observation (snapshot sut.disk) in
      STM.Res (STM.string, if retained_ok () then actual else "retained snapshot changed")
  ;;

  let postcond command state = function
    | STM.Res ((STM.String, _), actual) ->
      (match lookup state command with
       | Ok (_, answer, image) -> String.equal actual (answer ^ "\t" ^ image)
       | Error _ -> false)
    | _ -> false
  ;;
end

module Machine = STM_sequential.Make (Spec)

let rec take count = function
  | [] -> []
  | _ when count = 0 -> []
  | value :: rest -> value :: take (count - 1) rest
;;

let () =
  let path =
    match Sys.getenv_opt "E4_DISK_ORACLE" with
    | Some path -> path
    | None -> golden_path "disk-oracle.tsv"
  in
  load_oracle path;
  let sut = Spec.init_sut () in
  let before = observation (snapshot sut.disk) in
  require
    (match Spec.run 99 sut with
     | STM.Res ((STM.String, _), value) ->
       String.equal value "oracle-refused:unknown oracle action"
     | _ -> false)
    "unknown action did not refuse";
  require
    (String.equal before (observation (snapshot sut.disk)))
    "unknown action wrote disk";
  Spec.cleanup sut;
  let commands = QCheck.map (take command_bound) (Machine.arb_cmds Spec.init_state) in
  let test =
    QCheck.Test.make
      ~count:300
      ~name:"owned disk against actual Cas transitions"
      commands
      Machine.agree_prop
  in
  exit
    (QCheck_base_runner.run_tests
       ~verbose:true
       ~rand:(Random.State.make [| 1739 |])
       [ test ])
;;
