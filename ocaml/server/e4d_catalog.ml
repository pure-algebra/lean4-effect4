(* The programs the daemon can load, and what it can say about one without running it.

   Three source forms, which is what the estate has:

     `fixture`  one of the avatar's committed program tables -- the five families whose
                fixtures are `fibers_fixture.ml`, `store_fixtures.ml` and `extra_fixture.ml`,
                which are the OCaml transcription of the generated `harness/trace/*-fixture.ts`
                modules the goldens are produced from;
     `corpus`   a program of the adversarial corpus DSL (`avatar/corpus/programs.txt`,
                grammar in `avatar/corpus_dsl.ml`), either by name out of the compiled-in
                corpus text or from a text the request carries;
     `golden`   a golden's own wire header block, from which the family, the program name,
                the tape and the rules are read; the program itself is then resolved as a
                `fixture`.

   Nothing here evaluates a program. `prepare` returns the thunk and the defaults the
   avatar's own `avatar_main.ml` would have synthesised, and installs the corpus root table
   when the source is a corpus program -- that install is a write to `Deep_fibers.body_of_code`
   and is therefore undone by `E4d_reset.all` before the next request. *)

open Deep_fibers

type source =
  | Fixture of { family : string; program : string }
  | Corpus of { text : string option; name : string }

type program = {
  source : source;
  (* The name a response's `program` header field carries: `<family>.<name>`, exactly what
     `avatar_main.ml` writes. *)
  label : string;
  family : string;
  name : string;
}

exception Unknown of string

(* ------------------------------------------------------------------ the fixture tables *)

let fixture_families =
  [ ("fiber", "ocaml/avatar/fibers_fixture.ml");
    ("ref", "ocaml/avatar/store_fixtures.ml");
    ("deferred", "ocaml/avatar/store_fixtures.ml");
    ("scope", "ocaml/avatar/store_fixtures.ml");
    ("layer", "ocaml/avatar/store_fixtures.ml");
    ("extra", "ocaml/avatar/extra_fixture.ml") ]

(* The same `match family with` `avatar_main.ml:20-33` has, minus the `fuzz` arm, whose
   table is filled by a corpus another spike regenerates and is empty in this binary. *)
let fixture_table (family : string) : (string * (unit -> value)) list =
  match family with
  | "fiber" -> Fibers_fixture.programs
  | "ref" -> Store_fixtures.ref_programs
  | "deferred" -> Store_fixtures.deferred_programs
  | "scope" -> Store_fixtures.scope_programs
  | "layer" -> Store_fixtures.layer_programs
  | "extra" -> Extra_fixture.programs
  | other -> raise (Unknown ("unknown family " ^ other))

let fixture_names family = List.map fst (fixture_table family)

(* ------------------------------------------------------------------------- the corpus *)

let builtin_corpus : Corpus_dsl.prog list Lazy.t =
  lazy (Corpus_dsl.parse Corpus_data.text)

let corpus_of ~(text : string option) : Corpus_dsl.prog list =
  match text with None -> Lazy.force builtin_corpus | Some t -> Corpus_dsl.parse t

let corpus_names ?text () = List.map (fun (p : Corpus_dsl.prog) -> p.Corpus_dsl.name) (corpus_of ~text)

let corpus_find ~text name : Corpus_dsl.prog =
  match List.find_opt (fun (p : Corpus_dsl.prog) -> p.Corpus_dsl.name = name) (corpus_of ~text) with
  | Some p -> p
  | None -> raise (Unknown ("unknown corpus program " ^ name))

(* --------------------------------------------------------------------------- resolving *)

let of_fixture family program =
  if not (List.mem_assoc family fixture_families) then
    raise (Unknown ("unknown family " ^ family));
  if not (List.mem_assoc program (fixture_table family)) then
    raise (Unknown (Printf.sprintf "unknown program %s in family %s" program family));
  { source = Fixture { family; program };
    label = family ^ "." ^ program;
    family;
    name = program }

let of_corpus ?text name =
  ignore (corpus_find ~text name);
  { source = Corpus { text; name }; label = "corpus." ^ name; family = "corpus"; name }

(* A golden's header block. `program` in a committed golden is the bare program name (the
   goldens carry `program\t<name>`); the family is the caller's, or is inferred from the
   fixture tables when exactly one family declares that name. *)
let of_golden_header ?family (header_text : string) =
  let t = E4d_wire.parse_trace header_text in
  let program =
    match E4d_wire.header_field t "program" with
    | Some p -> p
    | None -> raise (Unknown "golden header has no `program` row")
  in
  (* A daemon answer carries `<family>.<name>`; a Lean golden carries `<name>`. *)
  let program, inferred_family =
    match String.index_opt program '.' with
    | Some i ->
      ( String.sub program (i + 1) (String.length program - i - 1),
        Some (String.sub program 0 i) )
    | None -> (program, None)
  in
  let family =
    match (family, inferred_family) with
    | Some f, _ -> f
    | None, Some f -> f
    | None, None -> (
      match
        List.filter
          (fun (f, _) -> List.mem_assoc program (fixture_table f))
          fixture_families
      with
      | [ (f, _) ] -> f
      | [] -> raise (Unknown ("no family declares the program " ^ program))
      | many ->
        raise
          (Unknown
             (Printf.sprintf "the program %s is declared by %s; name the family" program
                (String.concat ", " (List.map fst many)))))
  in
  ( of_fixture family program,
    (match E4d_wire.header_field t "tape" with Some s -> s | None -> ""),
    (match E4d_wire.header_field t "rules" with Some s -> s | None -> ""),
    (match E4d_wire.header_field t "pin" with
     | Some s -> ( match String.index_opt s '\t' with
                   | Some i -> String.sub s (i + 1) (String.length s - i - 1)
                   | None -> s)
     | None -> "") )

(* ------------------------------------------------------------------------- preparing *)

(* The default tape and op budget a program gets when the request names none. This is
   `avatar_main.ml:43-59`: a fixture program gets the caller's tape and no budget; a corpus
   program gets its own `tape` line, or 32 all-`false` entries so a fork never hands the
   processor over unless the program says so, and its own `maxops` line. *)
let defaults (p : program) : string * int =
  match p.source with
  | Fixture _ -> ("", max_int)
  | Corpus { text; name } ->
    let prog = corpus_find ~text name in
    ( (if prog.Corpus_dsl.tape = "" then
         String.concat "," (List.init 32 (fun i -> string_of_int i ^ ":0"))
       else prog.Corpus_dsl.tape),
      match prog.Corpus_dsl.maxops with Some n -> n | None -> max_int )

(* The thunk, plus the root-table install a corpus program needs. Call `E4d_reset.all ()`
   first: `Corpus_run.install` overwrites `Deep_fibers.body_of_code`. *)
let thunk (p : program) : unit -> value =
  match p.source with
  | Fixture { family; program } -> List.assoc program (fixture_table family)
  | Corpus { text; name } ->
    let prog = corpus_find ~text name in
    Corpus_run.install prog;
    Corpus_run.program prog

(* --------------------------------------------------------------------------- inspect *)

(* What a program declares, read off its source rather than off a run: the roots a fork can
   name, the operations its steps perform, and the family alphabet those operations come
   from. A fixture program is an OCaml closure and has no readable body, so its roots are the
   numeric body table `fibers_fixture.ml:body` declares and its operations are the family's
   `OpSpec` rows. *)

let corpus_ops (prog : Corpus_dsl.prog) : string list =
  let ops = ref [] in
  let add (s : Corpus_dsl.step) = if not (List.mem s.Corpus_dsl.op !ops) then ops := !ops @ [ s.Corpus_dsl.op ] in
  List.iter add prog.Corpus_dsl.main;
  List.iter (fun (_, steps) -> List.iter add steps) prog.Corpus_dsl.roots;
  !ops

(* The DSL step names a corpus program uses; empty for a fixture program, whose body is an
   OCaml closure. `Effect4_daemon.arms_for_row` uses it to narrow a row name that two arms
   could have produced. *)
let step_ops (p : program) : string list =
  match p.source with
  | Fixture _ -> []
  | Corpus { text; name } -> corpus_ops (corpus_find ~text name)

let json_of_step (s : Corpus_dsl.step) : E4d_json.t =
  let rec arg (a : Corpus_dsl.arg) : E4d_json.t =
    match a with
    | Corpus_dsl.Lit n -> Obj [ ("lit", Int n) ]
    | Corpus_dsl.Local i -> Obj [ ("local", Int i) ]
    | Corpus_dsl.Global g -> Obj [ ("global", Int g) ]
    | Corpus_dsl.List xs -> Obj [ ("list", List (List.map arg xs)) ]
  in
  Obj
    [ ("op", Str s.Corpus_dsl.op);
      ("args", List (List.map arg s.Corpus_dsl.args));
      ("publish", match s.Corpus_dsl.publish with Some g -> Int g | None -> Null) ]

(* The value alphabet the wire describes (`avatar_trace.ml:9-19`, transcribed from
   `git:c407ab7:Effect4/Target/TypeScript/Trace.lean:60-75`). One list, so `inspect` can say what a row's
   request or answer can be without the caller reading the OCaml. *)
let value_alphabet =
  [ ("unit", "[]"); ("nat", "an integer"); ("bool", "true / false");
    ("string", "a quoted string"); ("handle", "its index in first-seen order");
    ("pair", "[a, b]"); ("none", "{\"none\":true}"); ("some", "{\"some\":v}");
    ("list", "right-nested pairs closed by unit") ]

let row_alphabet = E4d_wire.event_kinds

let inspect (p : program) : E4d_json.t =
  let family_rows =
    match List.assoc_opt p.family E4d_families_data.families with Some rows -> rows | None -> []
  in
  let common =
    [ ("program", E4d_json.Str p.name);
      ("family", E4d_json.Str p.family);
      ("label", E4d_json.Str p.label);
      ( "operations",
        E4d_json.List
          (List.map
             (fun (name, params, answer) ->
               E4d_json.Obj
                 [ ("name", Str name); ("params", Int params); ("answer", Str answer) ])
             family_rows) );
      ( "alphabet",
        E4d_json.Obj
          [ ("rowKinds", E4d_json.of_strings row_alphabet);
            ( "values",
              E4d_json.List
                (List.map
                   (fun (k, v) -> E4d_json.Obj [ ("tag", E4d_json.Str k); ("wire", E4d_json.Str v) ])
                   value_alphabet) ) ] ) ]
  in
  match p.source with
  | Fixture { family; _ } ->
    E4d_json.Obj
      (common
      @ [ ("form", Str "fixture");
          ("source", Str (try List.assoc family fixture_families with Not_found -> "?"));
          (* `fibers_fixture.ml:body`: the numeric root table a fork names. *)
          ( "roots",
            List
              (List.map
                 (fun (code, what) -> E4d_json.Obj [ ("code", Int code); ("body", Str what) ])
                 [ (0, "succeeds with 11"); (1, "succeeds with 22"); (2, "fails with 1");
                   (3, "fails with 2"); (4, "never"); (5, "masks across a yield");
                   (6, "completes the Deferred at handle 0") ]) );
          ("body", Null) ])
  | Corpus { text; name } ->
    let prog = corpus_find ~text name in
    E4d_json.Obj
      (common
      @ [ ("form", Str "corpus");
          ("source", Str "ocaml/avatar/corpus/programs.txt");
          ("notes", E4d_json.of_strings prog.Corpus_dsl.notes);
          ("tape", Str prog.Corpus_dsl.tape);
          ("maxops", match prog.Corpus_dsl.maxops with Some n -> Int n | None -> Null);
          ( "roots",
            List
              (List.map
                 (fun (code, steps) ->
                   E4d_json.Obj
                     [ ("code", Int code); ("steps", List (List.map json_of_step steps)) ])
                 prog.Corpus_dsl.roots) );
          ("main", List (List.map json_of_step prog.Corpus_dsl.main));
          ("usedOperations", E4d_json.of_strings (corpus_ops prog)) ])
