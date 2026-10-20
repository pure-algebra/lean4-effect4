(* test_lean_wire — the lowering's finite check on Lean's own bytes (hand-written).

   What it is: `ocaml/goldens/eff/` holds the canonical bytes of a corpus of Eff programs as
   hex, written by `src/OCaml5/Tools/EffWire.lean` through `Effect4.Program.Wire` — Lean's
   own encoder, run by Lean. This library reads and writes a program by the same definition,
   lowered (Eff_codec: `Canonical.toVal` and `Canonical.ofVal` in Eff_image, over the framing
   kernel). This test reads Lean's bytes with the lowered reader and re-encodes them with the
   lowered writer, so a lowering or a kernel that departs from Lean shows up as a decode
   refusal or a byte difference (decisions row 391 (1): the finite checks stay).

   Checks:
   L1  the Lean manifest's constructor order is this library's, family by family, and its
       tag numbers are Eff_frame's;
   L1b wire-tags.txt, the wire tag Lean's own codec states for every constructor of every
       inductive family, is this library's table (Eff_layout.wire_tags, cut from
       tools/Effect4Gen/wire-tags.json), and no family gives one tag to two constructors;
   L2  every <name>.hex decodes exactly (no trailing bytes, no repairs), and a trailing byte, a
       truncation, a wrong tag and a length past the end are refused;
   L3  re-encoding the decoded program reproduces Lean's bytes exactly;
   L4  its JSON print as the tools print it (Lean's `ShapeDoc.printTree`, lowered) reads back to
       it under Lean's located reader (`ShapeDoc.readLocated`, lowered), or is refused for a
       natural above the profile's limit.

   The Lean goldens live in a directory the dune project builds no rule in (ocaml/goldens/eff,
   a sibling of ocaml/eff), so they cannot be a tracked dune dependency: the path is reached
   relatively or given as argv(1), and when the directory is
   absent the test says so and passes rather than pretending. Regenerate them with
   `lake env lean -M4096 --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff`. *)

module G = Effect4_gen.Api_gen

let checks = ref 0
let failures = ref 0

let check (name : string) (ok : bool) : unit =
  incr checks;
  if not ok
  then (
    incr failures;
    Printf.printf "FAIL: %s\n%!" name)
;;

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s
;;

(* _build/default/test and _build/default/eff/test are both four levels below ocaml/. *)
let default_dir = "../../../../goldens/eff"

let dir =
  let d = if Array.length Sys.argv > 1 then Sys.argv.(1) else default_dir in
  if String.length d > 0 && d.[String.length d - 1] = '/'
  then String.sub d 0 (String.length d - 1)
  else d
;;

let unhex (s : string) : string =
  let digit c =
    match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
    | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
    | _ -> invalid_arg "unhex: not a hex digit"
  in
  let clean = Buffer.create (String.length s) in
  String.iter
    (fun c ->
       if c <> '\n' && c <> '\r' && c <> ' ' && c <> '\t' then Buffer.add_char clean c)
    s;
  let clean = Buffer.contents clean in
  if String.length clean mod 2 <> 0 then invalid_arg "unhex: odd number of digits";
  let out = Buffer.create (String.length clean / 2) in
  let i = ref 0 in
  while !i < String.length clean do
    Buffer.add_char out (Char.chr ((digit clean.[!i] * 16) + digit clean.[!i + 1]));
    i := !i + 2
  done;
  Buffer.contents out
;;

let words (s : string) : string list =
  String.split_on_char ' ' s |> List.filter (fun w -> w <> "")
;;

let () =
  if not (Sys.file_exists dir && Sys.is_directory dir)
  then
    Printf.printf
      "test_lean_wire: SKIPPED — %s is absent. Regenerate it with `lake env lean -M4096 \
       --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff`, or pass the directory as \
       argv(1).\n\
       %!"
      dir
  else (
    (* ---- L1: the manifest ---- *)
    let manifest =
      read_file (Filename.concat dir "manifest.txt")
      |> String.split_on_char '\n'
      |> List.filter (fun l -> String.trim l <> "")
    in
    let line (key : string) : string list option =
      let k = key ^ ":" in
      let n = String.length k in
      match
        List.find_opt (fun l -> String.length l >= n && String.sub l 0 n = k) manifest
      with
      | None -> None
      | Some l -> Some (words (String.sub l n (String.length l - n)))
    in
    let family key names =
      check
        (Printf.sprintf "manifest %s is this library's constructor order" key)
        (line key = Some names)
    in
    check
      "manifest covers the shared selected description"
      (List.length manifest = List.length Eff_layout.wire_families + 1);
    List.iter (fun (name, fields) -> family name fields) Eff_layout.wire_families;
    let tags =
      match line "tags" with
      | None -> []
      | Some ws ->
        List.filter_map
          (fun w ->
             match String.split_on_char '=' w with
             | [ n; v ] -> Some (n, int_of_string v)
             | _ -> None)
          ws
    in
    let open Eff_frame in
    check
      "the manifest's tag numbers are Eff_frame's"
      (tags
       = [ "bool", tag_bool
         ; "nat", tag_nat
         ; "string", tag_string
         ; "list", tag_list
         ; "pair", tag_pair
         ; "none", tag_none
         ; "some", tag_some
         ; "bytes", tag_bytes
         ; "unit", tag_unit
         ; "ctor", tag_ctor
         ; "ref", tag_ref
         ; "handle", tag_handle
         ; "int", tag_int
         ; "float", tag_float
         ]);
    (* ---- L1b: the wire tags ---- *)
    let tag_lines =
      read_file (Filename.concat dir "wire-tags.txt")
      |> String.split_on_char '\n'
      |> List.filter (fun l -> String.trim l <> "")
    in
    let tag_line (key : string) : (string * int) list option =
      let k = key ^ ":" in
      let n = String.length k in
      match
        List.find_opt (fun l -> String.length l >= n && String.sub l 0 n = k) tag_lines
      with
      | None -> None
      | Some l ->
        Some
          (List.filter_map
             (fun w ->
                match String.split_on_char '=' w with
                | [ c; v ] -> Some (c, int_of_string v)
                | _ -> None)
             (words (String.sub l n (String.length l - n))))
    in
    check
      "wire-tags.txt covers every inductive family of this library"
      (List.length tag_lines = List.length Eff_layout.wire_tags);
    List.iter
      (fun (name, rows) ->
         check
           (Printf.sprintf "wire tags of %s are Lean's" name)
           (tag_line name = Some rows);
         let tags = List.map snd rows in
         check
           (Printf.sprintf "wire tags of %s are pairwise distinct" name)
           (List.length (List.sort_uniq compare tags) = List.length tags))
      Eff_layout.wire_tags;
    (* ---- L2..L5: the programs ---- *)
    let names =
      Sys.readdir dir
      |> Array.to_list
      |> List.filter (fun f -> Filename.check_suffix f ".hex")
      |> List.map (fun f -> Filename.chop_suffix f ".hex")
      |> List.sort compare
    in
    check "the Lean corpus is not empty" (names <> []);
    Printf.printf
      "  %-12s %6s  %-9s %-10s %s\n"
      "program"
      "bytes"
      "decode"
      "re-encode"
      "JSON";
    List.iter
      (fun name ->
         let bytes = unhex (read_file (Filename.concat dir (name ^ ".hex"))) in
         match Eff_codec.decode_program bytes with
         | None ->
           check (name ^ ": Lean's bytes decode exactly") false;
           Printf.printf
             "  %-12s %6d  %-9s %-10s %s\n"
             name
             (String.length bytes)
             "REFUSED"
             "-"
             "-"
         | Some p ->
           check (name ^ ": Lean's bytes decode exactly") true;
           let re = Eff_codec.encode_program p in
           check (name ^ ": re-encoding reproduces Lean's bytes") (re = bytes);
           let json =
             match
               G.store_shape_doc_read_located
                 G.run_kit_program_shape
                 (G.store_shape_doc_print_tree
                    G.run_kit_program_shape
                    (G.run_kit_program_to_val p))
             with
             | Ok v -> G.run_kit_program_of_val v = Some p
             | Error
                 { Eff_types.Located.reason = G.JsonReason_naturalOutsideProfile _; _ } ->
               true
             | Error _ -> false
           in
           check (name ^ ": Lean's JSON print reads back") json;
           check
             (name ^ ": a trailing byte is refused")
             (Eff_codec.decode_program (bytes ^ "\000") = None);
           check
             (name ^ ": truncation is refused")
             (Eff_codec.decode_program (String.sub bytes 0 (String.length bytes - 1))
              = None);
           let flipped = Bytes.of_string bytes in
           Bytes.set flipped 0 '\004';
           check
             (name ^ ": a wrong tag is refused")
             (Eff_codec.decode_program (Bytes.to_string flipped) = None);
           let longer = Bytes.of_string bytes in
           Bytes.set longer 8 (Char.chr (Char.code (Bytes.get longer 8) + 1));
           check
             (name ^ ": a length past the end is refused")
             (Eff_codec.decode_program (Bytes.to_string longer) = None);
           Printf.printf
             "  %-12s %6d  %-9s %-10s %s\n"
             name
             (String.length bytes)
             "ok"
             (if re = bytes then "identical" else "DIFFERS")
             (if json then "reads" else "DIFFERS"))
      names;
    Printf.printf "test_lean_wire: %d checks, %d failures\n%!" !checks !failures;
    if !failures > 0 then exit 1)
;;
