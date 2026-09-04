(* test_lean_wire — the differential against Lean's own wire (hand-written).

   What it is: `ocaml/goldens/eff/` holds the canonical bytes of a corpus of Eff programs as
   hex, written by `src/OCaml5/Tools/EffWire.lean` through `Effect4.Program.Wire` — Lean's
   own encoder, an implementation of the byte rule independent of the one `EffGen.lean`
   generates this library from. This test reads those bytes with THIS library's decoder and
   re-encodes them, so a disagreement between the two implementations of the rule shows up
   as a decode refusal or a byte difference.

   Checks:
   L1  the Lean manifest's constructor order is this library's, family by family, and its
       tag numbers are Eff_frame's;
   L2  every <name>.hex decodes exactly (no trailing bytes, no repairs);
   L3  re-encoding the decoded program reproduces Lean's bytes exactly;
   L4  the JSON printer and the checker run on it (the type is printed for the record);
   L5  for the programs the two corpora define identically (p42, pBind, pFork, pAwait — read
       off src/Effect4/Program/Wire.lean §Corpus against src/OCaml5/Tools/EffGen.lean
       §Corpus), Lean's bytes are byte for byte this library's goldens/<name>.bin. Where a
       name is shared but the Lean definition differs (pGen, pCatch), the comparison is
       reported, not asserted.

   The Lean goldens live outside this dune project (ocaml/goldens/eff, a sibling of
   ocaml/eff), so they cannot be a tracked dune dependency: the path is reached relatively
   (it is the same from either build root) or given as argv(1), and when the directory is
   absent the test says so and passes rather than pretending. Regenerate them with
   `lake env lean -M4096 --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff`. *)

let checks = ref 0
let failures = ref 0

let check (name : string) (ok : bool) : unit =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "FAIL: %s\n%!" name
  end

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* _build/default/test and _build/default/eff/test are both four levels below ocaml/. *)
let default_dir = "../../../../goldens/eff"

let dir =
  let d = if Array.length Sys.argv > 1 then Sys.argv.(1) else default_dir in
  if String.length d > 0 && d.[String.length d - 1] = '/' then String.sub d 0 (String.length d - 1) else d

let unhex (s : string) : string =
  let digit c =
    match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
    | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
    | _ -> invalid_arg "unhex: not a hex digit"
  in
  let clean = Buffer.create (String.length s) in
  String.iter (fun c -> if c <> '\n' && c <> '\r' && c <> ' ' && c <> '\t' then Buffer.add_char clean c) s;
  let clean = Buffer.contents clean in
  if String.length clean mod 2 <> 0 then invalid_arg "unhex: odd number of digits";
  let out = Buffer.create (String.length clean / 2) in
  let i = ref 0 in
  while !i < String.length clean do
    Buffer.add_char out (Char.chr ((digit clean.[!i] * 16) + digit clean.[!i + 1]));
    i := !i + 2
  done;
  Buffer.contents out

(* The first index where two byte strings differ, or where the shorter one ends. *)
let first_diff (a : string) (b : string) : int option =
  let n = min (String.length a) (String.length b) in
  let rec go i =
    if i >= n then if String.length a = String.length b then None else Some i
    else if a.[i] <> b.[i] then Some i
    else go (i + 1)
  in
  go 0

let byte_at (s : string) (i : int) : string =
  if i < String.length s then Printf.sprintf "%02x" (Char.code s.[i]) else "<end>"

(* The names whose Lean definition in Wire.lean §Corpus is the same term as the one
   EffGen.lean §Corpus writes to goldens/<name>.bin. *)
let same_program = [ "p42"; "pBind"; "pFork"; "pAwait" ]

let words (s : string) : string list =
  String.split_on_char ' ' s |> List.filter (fun w -> w <> "")

(* This library's own golden of the same name, if the corpus has one. *)
let ours_bin (name : string) : string option =
  let p = "../goldens/" ^ name ^ ".bin" in
  if Sys.file_exists p then Some (read_file p) else None

let () =
  if not (Sys.file_exists dir && Sys.is_directory dir) then
    Printf.printf
      "test_lean_wire: SKIPPED — %s is absent. Regenerate it with `lake env lean -M4096 --run \
       src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff`, or pass the directory as argv(1).\n%!"
      dir
  else begin
    (* ---- L1: the manifest ---- *)
    let manifest =
      read_file (Filename.concat dir "manifest.txt")
      |> String.split_on_char '\n'
      |> List.filter (fun l -> String.trim l <> "")
    in
    let line (key : string) : string list option =
      let k = key ^ ":" in
      let n = String.length k in
      match List.find_opt (fun l -> String.length l >= n && String.sub l 0 n = k) manifest with
      | None -> None
      | Some l -> Some (words (String.sub l n (String.length l - n)))
    in
    let family key names =
      check (Printf.sprintf "manifest %s is this library's constructor order" key) (line key = Some names)
    in
    check "the Lean manifest has 16 lines" (List.length manifest = 16);
    family "Lit" Eff_types.ctor_names_lit;
    family "Term" Eff_types.ctor_names_term;
    family "Terms" Eff_types.ctor_names_terms;
    family "CauseTerm" Eff_types.ctor_names_cause_term;
    family "FnName" Eff_types.ctor_names_fn_name;
    family "FinalizerStrategy" Eff_types.ctor_names_finalizer_strategy;
    family "NativeOp" Eff_types.ctor_names_native_op;
    family "MaskMode" Eff_types.ctor_names_mask_mode;
    family "ObserverMode" Eff_types.ctor_names_observer_mode;
    family "ForkOptions" Eff_types.field_names_fork_options;
    family "Eff" Eff_types.ctor_names_eff;
    family "Stmt" Eff_types.ctor_names_stmt;
    family "Stmts" Eff_types.ctor_names_stmts;
    family "Effs" Eff_types.ctor_names_effs;
    family "ActionTerm" Eff_types.ctor_names_action_term;
    let tags =
      match line "tags" with
      | None -> []
      | Some ws ->
        List.filter_map
          (fun w -> match String.split_on_char '=' w with [ n; v ] -> Some (n, int_of_string v) | _ -> None)
          ws
    in
    let open Eff_frame in
    check "the manifest's tag numbers are Eff_frame's"
      (tags
       = [ ("bool", tag_bool); ("nat", tag_nat); ("string", tag_string); ("list", tag_list);
           ("pair", tag_pair); ("none", tag_none); ("some", tag_some); ("bytes", tag_bytes);
           ("unit", tag_unit); ("ctor", tag_ctor) ]);

    (* ---- L2..L5: the programs ---- *)
    let names =
      Sys.readdir dir |> Array.to_list
      |> List.filter (fun f -> Filename.check_suffix f ".hex")
      |> List.map (fun f -> Filename.chop_suffix f ".hex")
      |> List.sort compare
    in
    check "the Lean corpus is not empty" (names <> []);
    Printf.printf "  %-12s %6s  %-9s %-10s %s\n" "program" "bytes" "decode" "re-encode" "vs goldens/<name>.bin";
    List.iter
      (fun name ->
        let bytes = unhex (read_file (Filename.concat dir (name ^ ".hex"))) in
        match Eff_wire.decode_program_exact bytes with
        | None ->
          check (name ^ ": Lean's bytes decode exactly") false;
          Printf.printf "  %-12s %6d  %-9s %-10s %s\n" name (String.length bytes) "REFUSED" "-" "-"
        | Some p ->
          check (name ^ ": Lean's bytes decode exactly") true;
          let re = Eff_wire.encode_program p in
          check (name ^ ": re-encoding reproduces Lean's bytes") (re = bytes);
          check (name ^ ": the JSON printer runs") (String.length (Eff_json.print_eff p) > 0);
          check (name ^ ": the checker runs") (String.length (Eff_typing.print_type p) > 0);
          check (name ^ ": a trailing byte is refused") (Eff_wire.decode_program_exact (bytes ^ "\000") = None);
          let ours = ours_bin name in
          let verdict =
            match ours with
            | None -> "(no golden of that name)"
            | Some b ->
              let same = List.mem name same_program in
              if same then check (name ^ ": Lean's bytes are this library's golden") (b = bytes);
              (match first_diff b bytes with
               | None -> "identical"
               | Some i ->
                 (* A byte difference is only ever allowed to be a program difference: the
                    two decoded programs must then differ too, which rules out the wire. *)
                 check (name ^ ": a byte difference is a program difference, not a wire one")
                   (Eff_wire.decode_program_exact b <> Some p);
                 Printf.sprintf "differs at %d (%s vs %s)%s" i (byte_at b i) (byte_at bytes i)
                   (if same then "" else " — different programs, same name"))
          in
          Printf.printf "  %-12s %6d  %-9s %-10s %s\n" name (String.length bytes) "ok"
            (if re = bytes then "identical" else "DIFFERS") verdict)
      names;
    Printf.printf "test_lean_wire: %d checks, %d failures\n%!" !checks !failures;
    if !failures > 0 then exit 1
  end
