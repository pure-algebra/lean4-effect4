(* Corpora -- the programs the differential runs, from three sources, as data.

   What it is: build lane X of the engine team (docs/research/2026-09-08-engine-brief.md
   §2.1 "a differential is the evidence"; the corpus table of
   2026-09-08-engine-a1-state.md §6.3).  Every source is reduced to ONE shape --
   {!program}, an `Eff_types.eff` with a name and the corpus it came from -- so the three
   engines can be driven through `E4_engine.ENGINE.compile` with no per-corpus code.

   The three sources, and what each is worth:

     goldens   ocaml/eff/goldens/*.bin -- 37 programs in the EXACT wire, decoded by
               `Eff_wire.decode_program_exact`.  27 well-typed and 10 `pIll*`; the
               ill-typed ones are part of the corpus because the machine's answer to
               them is also semantics.
     truth     ocaml/goldens/eff/*.hex -- 8 programs whose bytes were cut by LEAN's own
               `Program.Wire` (eff/README.md), i.e. the cross-face oracle, plus the two
               members of harness/truth/corpus.json that have a `.bin` under
               ocaml/eff/goldens and no `.hex` (pTwo, pAcquire).  The recorded
               `run`/`runSync` of harness/truth/corpus.json is read beside them
               ({!truth_expectations}) so the engines can be compared with the LEAN side
               and not only with each other.
     lean      {!lean_corpus} -- the printed corpus `make corpus` writes under
               `.lake/corpus` (tools/Tools/Corpus.lean): 400 programs of Lean's seeded
               generator `Test.Program.Gen` plus the wire corpus, each as the canonical
               bytes `Wire.encodeProgram` cut, with Lean's own `Api.wellTyped` verdict
               beside it in `index.tsv`.  Since 2026-09-13 this replaces the OCaml
               generator that was built on the hand-written checker: the programs come
               from Lean as bytes, and the verdicts ride along as data.

   Depends on: effect4_eff (Eff_types, Eff_wire, Eff_json_text), stdlib.  Nothing in this
   module touches an engine: it is programs, not runs.

   Behaviours:
   X1  Nothing here derives a typing verdict: {!program.typed} is Lean's, read from
       `index.tsv`, or `None` where the source records none.              by construction
   X2  The Lean corpus is deterministic: `Test.Program.Gen.program i depth` is a pure
       function of `i`, so `make corpus` writes one program list.          by construction
   X3  Loading is total and lossless: a `.bin`/`.hex`/`.eff` that
       `Eff_wire.decode_program_exact` refuses is REPORTED, never skipped silently
       ({!load_report}).                                                   by construction
   X4  No program is invented for a name: {!truth} contains exactly the corpus.json
       members whose canonical bytes exist in the tree, and {!truth_missing} names the
       rest; {!lean_corpus} contains exactly the rows of `index.tsv`.      by construction *)

open Eff_types

(* ==================================================================== the shape *)

type program = {
  name : string;  (** the golden's basename, or `g<NNN>` for a generated program *)
  corpus : string;  (** "goldens" | "truth" | "lean" *)
  eff : eff;
  bytes : string option;  (** the canonical wire bytes, when the program came from them *)
  typed : bool option;  (** Lean's `Api.wellTyped` verdict, when the source records it *)
}

type load_report = {
  lr_dir : string;
  lr_found : int;
  lr_decoded : int;
  lr_refused : string list;  (** the file names `decode_program_exact` refused *)
}

(* ==================================================================== finding files *)

let ancestors (d : string) (n : int) : string list =
  let rec go d n acc =
    if n = 0 then List.rev acc else go (Filename.dirname d) (n - 1) (d :: acc)
  in
  go d n []

(* The same ancestor walk `test/test_engine.ml` uses: from the cwd (in dune,
   `_build/default/engine/test`) upwards, trying both `<a>/<rel>` and `<a>/ocaml/<rel>`,
   with an environment override (the path of the file itself) first. *)
let find_path ?(env : string option) (suffix : string list) : string option =
  let rel = List.fold_left Filename.concat (List.hd suffix) (List.tl suffix) in
  let from_env =
    match env with
    | None -> []
    | Some e -> (try [ Sys.getenv e ] with Not_found -> [])
  in
  let cands =
    from_env
    @ List.concat_map
        (fun a -> [ Filename.concat a rel; Filename.concat a (Filename.concat "ocaml" rel) ])
        (ancestors (Sys.getcwd ()) 9)
  in
  List.find_opt Sys.file_exists cands

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let hex_decode (s : string) : string option =
  let b = Buffer.create (String.length s / 2) in
  let v c =
    match c with
    | '0' .. '9' -> Some (Char.code c - Char.code '0')
    | 'a' .. 'f' -> Some (Char.code c - Char.code 'a' + 10)
    | 'A' .. 'F' -> Some (Char.code c - Char.code 'A' + 10)
    | _ -> None
  in
  let digits = List.filter_map v (List.of_seq (String.to_seq s)) in
  let rec go = function
    | [] -> true
    | [ _ ] -> false
    | hi :: lo :: rest ->
      Buffer.add_char b (Char.chr ((hi * 16) + lo));
      go rest
  in
  if go digits then Some (Buffer.contents b) else None

(* ==================================================================== the byte goldens *)

let files_with (dir : string) (ext : string) : string list =
  List.sort compare
    (List.filter (fun f -> Filename.check_suffix f ext) (Array.to_list (Sys.readdir dir)))

let load_dir (dir : string) (ext : string) (corpus : string) (decode : string -> string option)
  : program list * load_report =
  let names = files_with dir ext in
  let refused = ref [] and progs = ref [] in
  List.iter
    (fun f ->
       let raw = read_file (Filename.concat dir f) in
       match decode raw with
       | None -> refused := f :: !refused
       | Some wire ->
         (match Eff_wire.decode_program_exact wire with
          | None -> refused := f :: !refused
          | Some e ->
            progs :=
              { name = Filename.remove_extension f; corpus; eff = e; bytes = Some wire;
                typed = None }
              :: !progs))
    names;
  ( List.rev !progs,
    { lr_dir = dir;
      lr_found = List.length names;
      lr_decoded = List.length !progs;
      lr_refused = List.rev !refused } )

let goldens () : program list * load_report =
  match find_path ~env:"E4_EFF_GOLDENS" [ "eff"; "goldens"; "p42.bin" ] with
  | None ->
    ([], { lr_dir = "<not found: ocaml/eff/goldens>"; lr_found = 0; lr_decoded = 0;
           lr_refused = [] })
  | Some marker ->
    load_dir (Filename.dirname marker) ".bin" "goldens" (fun s -> Some s)

(* ==================================================================== the truth corpus *)

(* The members of harness/truth/corpus.json, in its order.  A program of that corpus is a
   TypeScript declaration; its canonical bytes live elsewhere, so this list is the index
   and {!truth} is the join with the two byte sources. *)
let truth_names : string list =
  [ "p42"; "pBind"; "pFork"; "pAwait"; "pGen"; "pLoop"; "pCatch"; "pScope"; "pTwo";
    "pAcquire"; "pAcquireClosed"; "pProvide"; "pProvideMerge"; "pProvideTwice" ]

let truth () : program list * load_report * string list =
  let hex_dir =
    Option.map Filename.dirname (find_path ~env:"E4_HEX_GOLDENS" [ "goldens"; "eff"; "p42.hex" ])
  in
  let bin_dir =
    Option.map Filename.dirname (find_path ~env:"E4_EFF_GOLDENS" [ "eff"; "goldens"; "p42.bin" ])
  in
  let from_hex, rep =
    match hex_dir with
    | None ->
      ([], { lr_dir = "<not found: ocaml/goldens/eff>"; lr_found = 0; lr_decoded = 0;
             lr_refused = [] })
    | Some d -> load_dir d ".hex" "truth" hex_decode
  in
  let have = List.map (fun p -> p.name) from_hex in
  (* the corpus members with no Lean-cut hex but a byte golden of the same name *)
  let extra =
    match bin_dir with
    | None -> []
    | Some d ->
      List.filter_map
        (fun n ->
           if List.mem n have then None
           else
             let f = Filename.concat d (n ^ ".bin") in
             if not (Sys.file_exists f) then None
             else
               let wire = read_file f in
               Option.map
                 (fun e ->
                    { name = n; corpus = "truth"; eff = e; bytes = Some wire; typed = None })
                 (Eff_wire.decode_program_exact wire))
        truth_names
  in
  let got = have @ List.map (fun p -> p.name) extra in
  let missing = List.filter (fun n -> not (List.mem n got)) truth_names in
  (from_hex @ extra, rep, missing)

(* -------------------------------------------------------- corpus.json, as an oracle *)

(* A minimal JSON reader.  `Eff_json_text` is a printer with no parser anywhere in the
   library (its own header says so), and corpus.json is the only JSON this lane reads. *)
exception Json_error of string

let json_parse (s : string) : Eff_json_text.t =
  let n = String.length s in
  let i = ref 0 in
  let fail m = raise (Json_error (Printf.sprintf "%s at byte %d" m !i)) in
  let peek () = if !i < n then s.[!i] else '\000' in
  let rec skip () =
    if !i < n then
      match s.[!i] with ' ' | '\t' | '\n' | '\r' -> incr i; skip () | _ -> ()
  in
  let lit w v =
    let l = String.length w in
    if !i + l <= n && String.sub s !i l = w then (i := !i + l; v) else fail ("expected " ^ w)
  in
  let string_ () =
    if peek () <> '"' then fail "expected a string";
    incr i;
    let b = Buffer.create 16 in
    let rec go () =
      if !i >= n then fail "unterminated string"
      else
        match s.[!i] with
        | '"' -> incr i
        | '\\' ->
          incr i;
          (if !i >= n then fail "unterminated escape");
          (match s.[!i] with
           | 'n' -> Buffer.add_char b '\n'; incr i
           | 't' -> Buffer.add_char b '\t'; incr i
           | 'r' -> Buffer.add_char b '\r'; incr i
           | 'b' -> Buffer.add_char b '\b'; incr i
           | 'f' -> Buffer.add_char b '\012'; incr i
           | 'u' ->
             if !i + 4 >= n then fail "short \\u";
             let h = String.sub s (!i + 1) 4 in
             i := !i + 5;
             Buffer.add_char b (Char.chr (int_of_string ("0x" ^ h) land 0xff))
           | c -> Buffer.add_char b c; incr i);
          go ()
        | c -> Buffer.add_char b c; incr i; go ()
    in
    go ();
    Buffer.contents b
  in
  let number () =
    let start = !i in
    let ok c = (c >= '0' && c <= '9') || c = '-' || c = '+' || c = '.' || c = 'e' || c = 'E' in
    while !i < n && ok s.[!i] do incr i done;
    let t = String.sub s start (!i - start) in
    match int_of_string_opt t with
    | Some k -> Eff_json_text.Int k
    | None -> Eff_json_text.String t
  in
  let rec value () =
    skip ();
    match peek () with
    | '{' ->
      incr i;
      skip ();
      if peek () = '}' then (incr i; Eff_json_text.Object [])
      else
        let acc = ref [] in
        let rec go () =
          skip ();
          let k = string_ () in
          skip ();
          if peek () <> ':' then fail "expected :";
          incr i;
          let v = value () in
          acc := (k, v) :: !acc;
          skip ();
          match peek () with
          | ',' -> incr i; go ()
          | '}' -> incr i
          | _ -> fail "expected , or }"
        in
        go ();
        Eff_json_text.Object (List.rev !acc)
    | '[' ->
      incr i;
      skip ();
      if peek () = ']' then (incr i; Eff_json_text.Array [])
      else
        let acc = ref [] in
        let rec go () =
          let v = value () in
          acc := v :: !acc;
          skip ();
          match peek () with
          | ',' -> incr i; go ()
          | ']' -> incr i
          | _ -> fail "expected , or ]"
        in
        go ();
        Eff_json_text.Array (List.rev !acc)
    | '"' -> Eff_json_text.String (string_ ())
    | 't' -> lit "true" (Eff_json_text.Bool true)
    | 'f' -> lit "false" (Eff_json_text.Bool false)
    | 'n' -> lit "null" Eff_json_text.Null
    | _ -> number ()
  in
  let v = value () in
  skip ();
  v

let jfield (k : string) (v : Eff_json_text.t) : Eff_json_text.t option =
  match v with Eff_json_text.Object kvs -> List.assoc_opt k kvs | _ -> None

let jstr (v : Eff_json_text.t option) : string option =
  match v with Some (Eff_json_text.String s) -> Some s | _ -> None

let jint (v : Eff_json_text.t option) : int option =
  match v with Some (Eff_json_text.Int k) -> Some k | _ -> None

type truth_expect = {
  te_name : string;
  te_outcome : string;  (** `run.outcome`: "finished" | "frontier" | "stuck …" *)
  te_fibers : int;
  te_exit_kind : string;  (** `run.exitKind`: "success" | "fail" | "die" | "interrupt" *)
  te_success_nat : int option;  (** `run.exit.success` when it is a plain number *)
}

let truth_expectations () : (truth_expect list, string) result =
  match find_path ~env:"E4_TRUTH_CORPUS" [ "harness"; "truth"; "corpus.json" ] with
  | None -> Error "harness/truth/corpus.json not found from the cwd"
  | Some path -> (
    match json_parse (read_file path) with
    | exception Json_error m -> Error m
    | j -> (
      match jfield "programs" j with
      | Some (Eff_json_text.Array ps) ->
        Ok
          (List.filter_map
             (fun p ->
                let run = jfield "run" p in
                match jstr (jfield "name" p), run with
                | Some name, Some r ->
                  Some
                    { te_name = name;
                      te_outcome = Option.value (jstr (jfield "outcome" r)) ~default:"?";
                      te_fibers = Option.value (jint (jfield "fiberCount" r)) ~default:(-1);
                      te_exit_kind = Option.value (jstr (jfield "exitKind" r)) ~default:"?";
                      te_success_nat =
                        (match jfield "exit" r with
                         | Some e -> jint (jfield "success" e)
                         | None -> None) }
                | _ -> None)
             ps)
      | _ -> Error "corpus.json has no `programs` array"))


(* ==================================================================== the Lean corpus *)

(* `make corpus` runs tools/Tools/Corpus.lean into `.lake/corpus`: `index.tsv` has one
   `name  wellTyped  readable  chars` row per program Lean printed, and beside it
   `<name>.eff` is `Wire.encodeProgram` of the program Lean's own reader kept after the
   printer.  `E4_LEAN_CORPUS` names the directory; otherwise the ancestor walk finds
   `.lake/corpus` above the cwd.  A row whose bytes are missing or refused by
   `Eff_wire.decode_program_exact` is reported (X3); the verdict column is carried as
   {!program.typed} and never re-derived (X1). *)
let lean_corpus () : program list * load_report =
  let from_env =
    match Sys.getenv_opt "E4_LEAN_CORPUS" with
    | Some d when Sys.file_exists (Filename.concat d "index.tsv") ->
      Some (Filename.concat d "index.tsv")
    | _ -> None
  in
  let index =
    match from_env with
    | Some i -> Some i
    | None -> find_path [ ".lake"; "corpus"; "index.tsv" ]
  in
  match index with
  | None ->
    ([], { lr_dir = "<not found: .lake/corpus -- run `make corpus`>"; lr_found = 0;
           lr_decoded = 0; lr_refused = [] })
  | Some index ->
    let dir = Filename.dirname index in
    let rows =
      List.filter (fun l -> l <> "") (String.split_on_char '\n' (read_file index))
    in
    let refused = ref [] and progs = ref [] in
    List.iter
      (fun row ->
         match String.split_on_char '\t' row with
         | name :: verdict :: _ ->
           let file = Filename.concat dir (name ^ ".eff") in
           if not (Sys.file_exists file) then refused := (name ^ ".eff") :: !refused
           else begin
             let wire = read_file file in
             match Eff_wire.decode_program_exact wire with
             | None -> refused := (name ^ ".eff") :: !refused
             | Some e ->
               progs :=
                 { name; corpus = "lean"; eff = e; bytes = Some wire;
                   typed = Some (verdict = "true") }
                 :: !progs
           end
         | _ -> refused := ("index row: " ^ row) :: !refused)
      rows;
    ( List.rev !progs,
      { lr_dir = dir;
        lr_found = List.length rows;
        lr_decoded = List.length !progs;
        lr_refused = List.rev !refused } )
