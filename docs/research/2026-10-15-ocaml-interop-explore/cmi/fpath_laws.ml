(* The realization premise of the generated Fpath rows, tested: is the string image an exact
   embedding? Retraction: of_string (to_string p) = Ok p. Exactness: of_string s = Ok p implies
   to_string p = s. Exploration probe (2026-10-15), Fpath on OCaml 5.1.1. *)
let samples = [ "a/b"; "/usr/lib/"; "a//b"; "./x"; "a/./b"; "../.."; "a/b/"; "/"; "//net/share";
                "C:\\x"; "x.tar.gz"; " spaced name"; "\xce\xb1/\xce\xb2"; ""; "a\000b" ]
let () =
  List.iter (fun s ->
      match Fpath.of_string s with
      | Error (`Msg m) -> Printf.printf "%-16S refused by of_string: %s\n" s m
      | Ok p ->
        let back = Fpath.to_string p in
        let retract = (match Fpath.of_string back with Ok q -> Fpath.equal p q | Error _ -> false) in
        Printf.printf "%-16S retraction %b, exactness %b%s\n" s retract (back = s)
          (if back = s then "" else Printf.sprintf " (to_string gives %S)" back)) samples
