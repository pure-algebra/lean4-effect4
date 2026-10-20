(* Corpora -- see corpora.mli. *)

open Eff_types

(* ==================================================================== the shape *)

type program =
  { name : string (** the golden's basename, or `g<NNN>` for a generated program *)
  ; corpus : string (** "goldens" | "truth" | "lean" *)
  ; eff : NativeOp.t Eff.t
  ; bytes : string option (** the canonical wire bytes, when the program came from them *)
  ; typed : bool option (** Lean's `Api.wellTyped` verdict, when the source records it *)
  }

type load_report =
  { lr_dir : string
  ; lr_found : int
  ; lr_decoded : int
  ; lr_refused : string list (** the file names `decode_program_exact` refused *)
  }

(* ==================================================================== finding files *)

let ancestors (d : string) (n : int) : string list =
  let rec go d n acc =
    if n = 0 then List.rev acc else go (Filename.dirname d) (n - 1) (d :: acc)
  in
  go d n []
;;

(* The same ancestor walk `test/test_engine.ml` uses: from the cwd (in dune,
   `_build/default/engine/test`) upwards, trying both `<a>/<rel>` and `<a>/ocaml/<rel>`,
   with an environment override (the path of the file itself) first. *)
let find_path ?(env : string option) (suffix : string list) : string option =
  let rel = List.fold_left Filename.concat (List.hd suffix) (List.tl suffix) in
  let from_env =
    match env with
    | None -> []
    | Some e ->
      (try [ Sys.getenv e ] with
       | Not_found -> [])
  in
  let cands =
    from_env
    @ List.concat_map
        (fun a ->
           [ Filename.concat a rel; Filename.concat a (Filename.concat "ocaml" rel) ])
        (ancestors (Sys.getcwd ()) 9)
  in
  List.find_opt Sys.file_exists cands
;;

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s
;;

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
;;

(* ==================================================================== the byte goldens *)

let files_with (dir : string) (ext : string) : string list =
  List.sort
    compare
    (List.filter (fun f -> Filename.check_suffix f ext) (Array.to_list (Sys.readdir dir)))
;;

let load_dir
      (dir : string)
      (ext : string)
      (corpus : string)
      (decode : string -> string option)
  : program list * load_report
  =
  let names = files_with dir ext in
  let refused = ref []
  and progs = ref [] in
  List.iter
    (fun f ->
       let raw = read_file (Filename.concat dir f) in
       match decode raw with
       | None -> refused := f :: !refused
       | Some wire ->
         (match Eff_codec.decode_program wire with
          | None -> refused := f :: !refused
          | Some e ->
            progs
            := { name = Filename.remove_extension f
               ; corpus
               ; eff = e
               ; bytes = Some wire
               ; typed = None
               }
               :: !progs))
    names;
  ( List.rev !progs
  , { lr_dir = dir
    ; lr_found = List.length names
    ; lr_decoded = List.length !progs
    ; lr_refused = List.rev !refused
    } )
;;

let goldens () : program list * load_report =
  match find_path ~env:"E4_EFF_GOLDENS" [ "eff"; "goldens"; "p42.bin" ] with
  | None ->
    ( []
    , { lr_dir = "<not found: ocaml/eff/goldens>"
      ; lr_found = 0
      ; lr_decoded = 0
      ; lr_refused = []
      } )
  | Some marker -> load_dir (Filename.dirname marker) ".bin" "goldens" (fun s -> Some s)
;;

(* ==================================================================== the truth corpus *)

(* The members of harness/truth/corpus.json, in its order.  A program of that corpus is a
   TypeScript declaration; its canonical bytes live elsewhere, so this list is the index
   and {!truth} is the join with the two byte sources. *)
let truth_names : string list =
  [ "p42"
  ; "pBind"
  ; "pFork"
  ; "pAwait"
  ; "pGen"
  ; "pLoop"
  ; "pCatch"
  ; "pScope"
  ; "pTwo"
  ; "pAcquire"
  ; "pAcquireClosed"
  ; "pProvide"
  ; "pProvideMerge"
  ; "pProvideTwice"
  ]
;;

let truth () : program list * load_report * string list =
  let hex_dir =
    Option.map
      Filename.dirname
      (find_path ~env:"E4_HEX_GOLDENS" [ "goldens"; "eff"; "p42.hex" ])
  in
  let bin_dir =
    Option.map
      Filename.dirname
      (find_path ~env:"E4_EFF_GOLDENS" [ "eff"; "goldens"; "p42.bin" ])
  in
  let from_hex, rep =
    match hex_dir with
    | None ->
      ( []
      , { lr_dir = "<not found: ocaml/goldens/eff>"
        ; lr_found = 0
        ; lr_decoded = 0
        ; lr_refused = []
        } )
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
           if List.mem n have
           then None
           else (
             let f = Filename.concat d (n ^ ".bin") in
             if not (Sys.file_exists f)
             then None
             else (
               let wire = read_file f in
               Option.map
                 (fun e ->
                    { name = n
                    ; corpus = "truth"
                    ; eff = e
                    ; bytes = Some wire
                    ; typed = None
                    })
                 (Eff_codec.decode_program wire))))
        truth_names
  in
  let got = have @ List.map (fun p -> p.name) extra in
  let missing = List.filter (fun n -> not (List.mem n got)) truth_names in
  from_hex @ extra, rep, missing
;;

(* -------------------------------------------------------- corpus.json, as an oracle *)

(* corpus.json is this lane's one JSON input, and no carrier reads it: yojson parses it, and
   three projections read the fields the oracle needs. *)
let jfield (k : string) (v : Yojson.Safe.t) : Yojson.Safe.t option =
  match v with
  | `Assoc kvs -> List.assoc_opt k kvs
  | _ -> None
;;

let jstr (v : Yojson.Safe.t option) : string option =
  match v with
  | Some (`String s) -> Some s
  | _ -> None
;;

let jint (v : Yojson.Safe.t option) : int option =
  match v with
  | Some (`Int k) -> Some k
  | _ -> None
;;

type truth_expect =
  { te_name : string
  ; te_outcome : string (** `run.outcome`: "finished" | "frontier" | "stuck …" *)
  ; te_fibers : int
  ; te_exit_kind : string (** `run.exitKind`: "success" | "fail" | "die" | "interrupt" *)
  ; te_success_nat : int option (** `run.exit.success` when it is a plain number *)
  }

let truth_expectations () : (truth_expect list, string) result =
  match find_path ~env:"E4_TRUTH_CORPUS" [ "Test"; "Corpus"; "corpus.json" ] with
  | None -> Error "harness/truth/corpus.json not found from the cwd"
  | Some path ->
    (match Yojson.Safe.from_string (read_file path) with
     | exception Yojson.Json_error m -> Error m
     | j ->
       (match jfield "programs" j with
        | Some (`List ps) ->
          Ok
            (List.filter_map
               (fun p ->
                  let run = jfield "run" p in
                  match jstr (jfield "name" p), run with
                  | Some name, Some r ->
                    Some
                      { te_name = name
                      ; te_outcome = Option.value (jstr (jfield "outcome" r)) ~default:"?"
                      ; te_fibers =
                          Option.value (jint (jfield "fiberCount" r)) ~default:(-1)
                      ; te_exit_kind =
                          Option.value (jstr (jfield "exitKind" r)) ~default:"?"
                      ; te_success_nat =
                          (match jfield "exit" r with
                           | Some e -> jint (jfield "success" e)
                           | None -> None)
                      }
                  | _ -> None)
               ps)
        | _ -> Error "corpus.json has no `programs` array"))
;;

(* ==================================================================== the Lean corpus *)

(* `make corpus` runs tools/Tools/Corpus.lean into `.lake/corpus`: `index.tsv` has one
   `name  wellTyped  readable  chars` row per program Lean printed, and beside it
   `<name>.eff` is `Wire.encodeProgram` of the program Lean's own reader kept after the
   printer.  `E4_LEAN_CORPUS` names the directory; otherwise the ancestor walk finds
   `.lake/corpus` above the cwd.  A row whose bytes are missing or refused by
   `Eff_codec.decode_program` is reported (X3); the verdict column is carried as
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
    ( []
    , { lr_dir = "<not found: .lake/corpus -- run `make corpus`>"
      ; lr_found = 0
      ; lr_decoded = 0
      ; lr_refused = []
      } )
  | Some index ->
    let dir = Filename.dirname index in
    let rows =
      List.filter (fun l -> l <> "") (String.split_on_char '\n' (read_file index))
    in
    let refused = ref []
    and progs = ref [] in
    List.iter
      (fun row ->
         match String.split_on_char '\t' row with
         | name :: verdict :: _ ->
           let file = Filename.concat dir (name ^ ".eff") in
           if not (Sys.file_exists file)
           then refused := (name ^ ".eff") :: !refused
           else (
             let wire = read_file file in
             match Eff_codec.decode_program wire with
             | None -> refused := (name ^ ".eff") :: !refused
             | Some e ->
               progs
               := { name
                  ; corpus = "lean"
                  ; eff = e
                  ; bytes = Some wire
                  ; typed = Some (verdict = "true")
                  }
                  :: !progs)
         | _ -> refused := ("index row: " ^ row) :: !refused)
      rows;
    ( List.rev !progs
    , { lr_dir = dir
      ; lr_found = List.length rows
      ; lr_decoded = List.length !progs
      ; lr_refused = List.rev !refused
      } )
;;
