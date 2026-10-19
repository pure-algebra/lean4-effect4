(* E4_check -- see e4_check.mli. *)

type gap =
  | One
  | Two

let counted = ref 0
let failed = ref 0

let spaces = function
  | One -> " "
  | Two -> "  "
;;

let check ?(gap = One) (name : string) (ok : bool) : unit =
  incr counted;
  if not ok then incr failed;
  Printf.printf "%s%s%s\n%!" (if ok then "PASS" else "FAIL") (spaces gap) name
;;

let checks () = !counted
let failures () = !failed

let finish () =
  if !failed = 0
  then Printf.printf "== ALL PASS: 0 failure(s) in %d checks ==\n%!" !counted
  else Printf.printf "== FAILED: %d failure(s) in %d checks ==\n%!" !failed !counted;
  exit (if !failed = 0 then 0 else 1)
;;

let temp_dir ?under (prefix : string) : string =
  Filename.temp_dir ?temp_dir:under prefix ""
;;

(* A sealed store leaves directories without write permission, so each directory is opened up
   before its entries go. Every failure is swallowed: what the host keeps, stays (C4). *)
let rec remove_tree (path : string) : unit =
  match Unix.lstat path with
  | exception Unix.Unix_error _ -> ()
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    (try Unix.chmod path 0o700 with
     | Unix.Unix_error _ -> ());
    (match Sys.readdir path with
     | names -> Array.iter (fun name -> remove_tree (Filename.concat path name)) names
     | exception Sys_error _ -> ());
    (try Unix.rmdir path with
     | Unix.Unix_error _ -> ())
  | _ ->
    (try Sys.remove path with
     | Sys_error _ -> ())
;;
