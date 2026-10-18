(* ok -- an outside project checks and runs one program with the installed kit (plan E1).

   What it is: the outside consumer's executable. ../../check_install.sh builds it from a copy of
   this project outside ocaml/, with OCAMLPATH set to a scratch prefix that `dune install` filled,
   so it links the installed effect4_kit and its installed dependencies alone.
   Usage: ok.exe PROGRAM.json, a program's JSON print (the session tool's form).
   Depends on: Effect4_kit.Kit (installed).

   Behaviours:
   O1 It prints two lines: Kit's check answer, then Kit's run report under the host that answers
      no call. A program that does not read is reported on stderr with exit code 2.
                                                                         by construction
   O2 The two lines equal ok.expected, and the installed `eff check` and `eff run` print the same
      two lines.                                                          tested (check_install.sh) *)

open Effect4_kit

let () =
  let path = if Array.length Sys.argv = 2 then Sys.argv.(1) else (prerr_endline "usage: ok.exe PROGRAM.json"; exit 2) in
  let text = In_channel.with_open_bin path In_channel.input_all in
  match Kit.Json.parse text with
  | Error why -> prerr_endline ("ok: " ^ path ^ " is not JSON: " ^ why); exit 2
  | Ok json -> (
    match Kit.Json.program json with
    | None -> prerr_endline ("ok: " ^ path ^ " does not read as a program"); exit 2
    | Some program ->
      let app = Kit.app () in
      print_endline (Kit.Json.render (Kit.Json.check_json app program));
      print_endline (Kit.Json.render (Kit.Json.report_json app (Kit.run app Kit.Reactor.silent () program))))
