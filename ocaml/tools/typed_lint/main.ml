(* Thin driver for Typed_lint. Dependencies: its library and the standard library.
   Usage: main [--raises] FILE.cmt... from the build context's root (the dune rules chdir there).
   Properties: prints nothing on a clean run; prints each finding on one line; exits 1 on a
   rule-7 finding, 2 on a refusal or a bad command line, 0 otherwise. Rule 6's findings
   (--raises) are a report and change no exit status. Tested by test/dune. *)

let () =
  let raises, files =
    match Array.to_list Sys.argv with
    | _ :: "--raises" :: files -> true, files
    | _ :: files -> false, files
    | [] -> false, [] in
  (match files with
   | [] -> prerr_endline "usage: main [--raises] FILE.cmt..."; exit 2
   | _ :: _ -> ());
  let compares = ref 0 and raised = ref 0 and refused = ref false in
  List.iter (fun file ->
    match Typed_lint.check ~raises file with
    | Error why -> prerr_endline (Typed_lint.message why); refused := true
    | Ok findings ->
        List.iter (fun (finding : Typed_lint.finding) ->
          print_endline (Typed_lint.render finding);
          match finding.rule with Compare -> incr compares | Raise -> incr raised) findings)
    files;
  if raises then Printf.printf "%d rule-6 finding(s), a report\n" !raised;
  if !compares > 0 then Printf.printf "%d rule-7 finding(s)\n" !compares;
  if !refused then exit 2 else if !compares > 0 then exit 1
