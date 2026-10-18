(* test_shapes.ml -- the carriers' shapes, pinned (phase 5 of the OCaml estate refactor, 5.2).

   What it is: a SHA-256 digest of each shape document of Effect4.Run.Kit
   (src/Effect4/Run/Kit.lean, `admitShape` to `valShape`), as Lean lowers it into
   Effect4_gen.Api_gen (`run_kit_*_shape`), against a pin taken at Kit.format_version. Kit.Json
   prints and reads every carrier by these documents, so a changed shape is a changed format:
   this test fails until its pin and Kit.format_version move together (the rule in kit.mli).
   Depends on: Effect4_gen.Api_gen (the shapes), Effect4_kit.Kit (the version), E4_sha256.

   Properties:
   S1  Each of the nine shapes' digest equals its pin.                          tested
   S2  The pins were taken at the current version: `pinned_version` is Kit.format_version.
                                                                                tested
   S3  Red control: a shape changed in its root, in one definition's name or in one field's
       name no longer matches its pin, so S1 tells a change from no change.     tested
   S4  The rendering is total over `shape` and quotes every name, so a constructor added to
       the generated type is a compile error here, and two different documents render
       differently.                                                    by construction

   What it does not establish: Api_gen's `kind` is a placeholder (`Placeholder_kind`), so a
   reference's kind is not in the OCaml image of a shape, and not in its digest.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/kit *)

module G = Effect4_gen.Api_gen
module Kit = Effect4_kit.Kit

(* The rule: when S1 fails, a shape has changed. Take the digests this test prints as the new
   pins, and move [pinned_version] and Kit.format_version up by one, in the same commit. *)
let pinned_version = 2

let pins =
  [ ("admit", "fece61a8e4b0cec24350afeea5a9b63d4e28b14a2ed3e7487738141b81f8ee7f");
    ("program", "1c64c460235b36677a1c5cc62a6aa2bc5a8eb4bd17a969ce7c4bef929954633f");
    ("rows", "8bb28dafc37d3d6c4b6c344684f3b0d8b65fe0c4378e3944e9264044386e147a");
    ("services", "6cf93867e4469d6394f62acfed9cf19a48c83ab6bf9ff9989c4b440b5603bd8e");
    ("ty", "a326c1d8b4416d0c12708fdc6fb57710eb2774e8515a889148b787ba90d672d3");
    ("eff_ty", "398dd55b90392c4a595beff164ab1ac76f6c13f9abdf2c1bf964cb43ed6534a3");
    ("refusal", "27dc1facbfc1308441beb99940201e98d7ac0f26558d53d8fb91739b2efadfac");
    ("exit", "a6db7d6c97fef76407f7259345de9aa85e3edaef4bf5f888ef92496b23bfc17a");
    ("val", "5af72e029939913e205454540e86ed7b6e965492ee5c18fc8449873e07451cc8") ]

let shapes =
  [ ("admit", G.run_kit_admit_shape);
    ("program", G.run_kit_program_shape);
    ("rows", G.run_kit_rows_shape);
    ("services", G.run_kit_services_shape);
    ("ty", G.run_kit_ty_shape);
    ("eff_ty", G.run_kit_eff_ty_shape);
    ("refusal", G.run_kit_refusal_shape);
    ("exit", G.run_kit_exit_shape);
    ("val", G.run_kit_val_shape) ]

(* S4: one clause per constructor, every name quoted. *)
let rec render (s : G.shape) : string =
  let fields fs = String.concat " " (List.map (fun (n, s) -> Printf.sprintf "(%S %s)" n (render s)) fs) in
  match s with
  | G.Shape_unit -> "unit"
  | G.Shape_bool -> "bool"
  | G.Shape_nat -> "nat"
  | G.Shape_string -> "string"
  | G.Shape_bytes -> "bytes"
  | G.Shape_digest -> "digest"
  | G.Shape_list a -> Printf.sprintf "(list %s)" (render a)
  | G.Shape_option a -> Printf.sprintf "(option %s)" (render a)
  | G.Shape_pair (a, b) -> Printf.sprintf "(pair %s %s)" (render a) (render b)
  | G.Shape_struct (name, fs) -> Printf.sprintf "(struct %S (%s))" name (fields fs)
  | G.Shape_sum (name, cases) ->
    Printf.sprintf "(sum %S (%s))" name
      (String.concat " " (List.map (fun (n, (i, fs)) -> Printf.sprintf "(%S %d (%s))" n i (fields fs)) cases))
  | G.Shape_ref _ -> "(ref)"
  | G.Shape_anyRef -> "anyRef"
  | G.Shape_named n -> Printf.sprintf "(named %S)" n
  | G.Shape_value -> "value"

let render_doc (d : G.shape_doc) : string =
  Printf.sprintf "(doc %s (%s))" (render d.root)
    (String.concat " " (List.map (fun (n, s) -> Printf.sprintf "(%S %s)" n (render s)) d.defs))

let digest (d : G.shape_doc) : string = E4_sha256.hex (E4_sha256.digest (render_doc d))

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* S3's changes: the root wrapped, the first definition renamed, the first field renamed. *)
let rec rename_first_field (s : G.shape) : G.shape option =
  let rename fs =
    match fs with (n, t) :: rest -> Some ((n ^ "'", t) :: rest) | [] -> None
  in
  match s with
  | G.Shape_struct (name, fs) -> Option.map (fun fs -> G.Shape_struct (name, fs)) (rename fs)
  | G.Shape_sum (name, cases) ->
    let rec first = function
      | [] -> None
      | (n, (i, fs)) :: rest -> (
        match rename fs with
        | Some fs -> Some ((n, (i, fs)) :: rest)
        | None -> Option.map (fun rest -> (n, (i, fs)) :: rest) (first rest))
    in
    Option.map (fun cases -> G.Shape_sum (name, cases)) (first cases)
  | G.Shape_list a -> Option.map (fun a -> G.Shape_list a) (rename_first_field a)
  | G.Shape_option a -> Option.map (fun a -> G.Shape_option a) (rename_first_field a)
  | G.Shape_pair (a, b) -> (
    match rename_first_field a with
    | Some a -> Some (G.Shape_pair (a, b))
    | None -> Option.map (fun b -> G.Shape_pair (a, b)) (rename_first_field b))
  | G.Shape_unit | G.Shape_bool | G.Shape_nat | G.Shape_string | G.Shape_bytes | G.Shape_digest
  | G.Shape_ref _ | G.Shape_anyRef | G.Shape_named _ | G.Shape_value -> None

let field_renamed (d : G.shape_doc) : G.shape_doc option =
  match rename_first_field d.root with
  | Some root -> Some { d with root }
  | None ->
    let rec first = function
      | [] -> None
      | (n, s) :: rest -> (
        match rename_first_field s with
        | Some s -> Some ((n, s) :: rest)
        | None -> Option.map (fun rest -> (n, s) :: rest) (first rest))
    in
    Option.map (fun defs -> { d with defs }) (first d.defs)

let () =
  check
    (Printf.sprintf "S2 the pins were taken at the current format version (%d)" Kit.format_version)
    (pinned_version = Kit.format_version);
  List.iter
    (fun (name, doc) ->
      let pin = List.assoc name pins and now = digest doc in
      check (Printf.sprintf "S1 %s's shape is its pin (%s)" name now) (String.equal now pin);
      check (Printf.sprintf "S3 red control: %s's shape with its root wrapped misses the pin" name)
        (not (String.equal (digest { doc with root = G.Shape_option doc.root }) pin));
      (match doc.defs with
       | (n, s) :: rest ->
         check (Printf.sprintf "S3 red control: %s's shape with its first definition renamed misses the pin" name)
           (not (String.equal (digest { doc with defs = (n ^ "'", s) :: rest }) pin))
       | [] -> ());
      match field_renamed doc with
      | Some changed ->
        check (Printf.sprintf "S3 red control: %s's shape with one field renamed misses the pin" name)
          (not (String.equal (digest changed) pin))
      | None -> ())
    shapes;
  Printf.printf "%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
