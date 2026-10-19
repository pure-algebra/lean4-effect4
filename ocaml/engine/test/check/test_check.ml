(* test_check.ml -- E4_check against its behaviours C1-C4 (e4_check.mli).

   What it checks: the PASS and FAIL lines with both gaps (C1); the summary line and the exit
   code, read from this executable run as a child, once with every check passing and once, the
   red control, with one check failing (C2); two scratch directories, never one path (C3); and
   a tree with a directory and a file the owner cannot write, removed whole, then removed again
   with no error (C4).
   Depends on: E4_check, unix.
   Evidence: finite runs on this host.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/support *)

(* The child's two scripts: [green] passes every check, [red] fails one. *)
let child_script = function
  | "green" ->
    E4_check.check "one" true;
    E4_check.check ~gap:Two "two" true;
    E4_check.finish ()
  | "red" ->
    E4_check.check "kept" true;
    E4_check.check ~gap:Two "broken" false;
    E4_check.finish ()
  | other -> failwith ("test_check: no child script " ^ other)
;;

(* Runs this executable on one script; answers its exit code and its lines. *)
let run_child (script : string) : int * string list =
  let input =
    Unix.open_process_args_in Sys.executable_name [| Sys.executable_name; script |]
  in
  let rec lines acc =
    match input_line input with
    | line -> lines (line :: acc)
    | exception End_of_file -> List.rev acc
  in
  let out = lines [] in
  match Unix.close_process_in input with
  | Unix.WEXITED code -> code, out
  | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1, out
;;

let main () =
  let check = E4_check.check in
  (* C1 and C2: the green child *)
  let code, out = run_child "green" in
  check
    "C1 a passing check prints PASS, a space and its name; with gap Two, two spaces"
    (List.equal
       String.equal
       (List.filteri (fun i _ -> i < 2) out)
       [ "PASS one"; "PASS  two" ]);
  check
    "C2 with no failure the summary is ALL PASS with the count, and the code is 0"
    (code = 0
     && List.equal
          String.equal
          (List.filteri (fun i _ -> i = 2) out)
          [ "== ALL PASS: 0 failure(s) in 2 checks ==" ]);
  (* C2's red control: one failing check *)
  let code, out = run_child "red" in
  check
    "C2 red control: one failing check prints FAIL, the summary FAILED, and the code is 1"
    (code = 1
     && List.equal
          String.equal
          out
          [ "PASS kept"; "FAIL  broken"; "== FAILED: 1 failure(s) in 2 checks ==" ]);
  (* C3 *)
  let a = E4_check.temp_dir "e4check-" in
  let b = E4_check.temp_dir "e4check-" in
  let inner = E4_check.temp_dir ~under:a "s" in
  check
    "C3 two scratch directories are two paths, both directories, named from the prefix"
    ((not (String.equal a b))
     && Sys.is_directory a
     && Sys.is_directory b
     && Sys.is_directory inner
     && String.equal (Filename.dirname inner) a
     && String.starts_with ~prefix:"e4check-" (Filename.basename a));
  (* C4: a sealed directory holding a read-only file *)
  let sealed = Filename.concat inner "sealed" in
  Unix.mkdir sealed 0o700;
  let file = Filename.concat sealed "segment" in
  Out_channel.with_open_bin file (fun oc -> Out_channel.output_string oc "bytes");
  Unix.chmod file 0o400;
  Unix.chmod sealed 0o500;
  E4_check.remove_tree a;
  E4_check.remove_tree b;
  check
    "C4 a tree with a directory and a file the owner cannot write is removed whole"
    ((not (Sys.file_exists a)) && not (Sys.file_exists b));
  check
    "C4 removing an absent path raises nothing"
    (match E4_check.remove_tree a with
     | () -> true
     | exception _ -> false);
  E4_check.finish ()
;;

let () =
  match Sys.argv with
  | [| _; script |] -> child_script script
  | _ -> main ()
;;
