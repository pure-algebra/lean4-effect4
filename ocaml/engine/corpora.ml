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
     generated {!generate} -- well-typed random `Eff` programs (owner default A1-Q4: the
               158-program avatar corpus is dropped from the differential because 7 of its
               41 ops have no `Eff` constructor, and a generator replaces it).

   THE GENERATOR IS TYPE-DIRECTED, NOT REJECTION-BASED.  `gen_eff` carries the `eff_ty` of
   every subterm it builds -- the same judgement `Eff_typing.check_eff` computes, applied
   as a constructor rather than as a filter -- so the environment a binder extends is known
   exactly and `Term_var` never points past it.  Where a rule needs a join that a random
   draw can miss (`catchCause`, `matchCause`, `branch`, `choose`, `raceAll`, `ifElse`) the
   losing side is replaced by an arm whose answer is `never`, which joins with everything.
   `Eff_typing.well_typed` is then run on every finished program as a NET, not as the
   mechanism: {!generate} reports how many draws it refused, and that number is a
   measurement of the generator, not of the corpus.

   Depends on: effect4_eff (Eff_types, Eff_typing, Eff_native, Eff_wire, Eff_json_text),
   stdlib.  Nothing in this module touches an engine: it is programs, not runs.

   Behaviours:
   X1  Every program {!generate} returns satisfies `Eff_typing.well_typed`.  Checked on
       every one, not sampled.                                            by construction
   X2  The generator is deterministic: one seed, one 48-bit LCG (the constants lane C
       measured to fit a 63-bit OCaml int), one program list.             by construction
   X3  Loading is total and lossless: a `.bin`/`.hex` that `Eff_wire.decode_program_exact`
       refuses is REPORTED, never skipped silently ({!load_report}).      by construction
   X4  No program is invented for a name: {!truth} contains exactly the corpus.json
       members whose canonical bytes exist in the tree, and {!truth_missing} names the
       rest.                                                              by construction
   X5  {!census} counts constructor occurrences by the GENERATED alphabet's own names
       (`Eff_types.ctor_name_*`), so a coverage claim is a count of Lean constructors.
                                                                          by construction *)

open Eff_types

(* ==================================================================== the shape *)

type program = {
  name : string;  (** the golden's basename, or `g<NNN>` for a generated program *)
  corpus : string;  (** "goldens" | "truth" | "generated" *)
  eff : eff;
  bytes : string option;  (** the canonical wire bytes, when the program came from them *)
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
   with an environment override first. *)
let find_path (suffix : string list) (env : string) : string option =
  let rel = List.fold_left Filename.concat (List.hd suffix) (List.tl suffix) in
  let from_env = try [ Sys.getenv env ] with Not_found -> [] in
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
              { name = Filename.remove_extension f; corpus; eff = e; bytes = Some wire }
              :: !progs))
    names;
  ( List.rev !progs,
    { lr_dir = dir;
      lr_found = List.length names;
      lr_decoded = List.length !progs;
      lr_refused = List.rev !refused } )

let goldens () : program list * load_report =
  match find_path [ "eff"; "goldens"; "p42.bin" ] "E4_EFF_GOLDENS" with
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
    Option.map Filename.dirname (find_path [ "goldens"; "eff"; "p42.hex" ] "E4_HEX_GOLDENS")
  in
  let bin_dir =
    Option.map Filename.dirname (find_path [ "eff"; "goldens"; "p42.bin" ] "E4_EFF_GOLDENS")
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
                 (fun e -> { name = n; corpus = "truth"; eff = e; bytes = Some wire })
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
  match find_path [ "harness"; "truth"; "corpus.json" ] "E4_TRUTH_CORPUS" with
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

(* ==================================================================== the generator *)

(* Java's 48-bit LCG, the one lane C settled on: the 64-bit constant A1's note implied does
   not fit a 63-bit OCaml int, so the multiplier is 25214903917 and the top bits are taken.
   Deterministic, cheap, and identical on every host with `Sys.int_size >= 48`. *)
type rng = { mutable st : int }

let rng_make (seed : int) : rng = { st = (seed lxor 25214903917) land 0xFFFFFFFFFFFF }

let bits (r : rng) (k : int) : int =
  r.st <- ((r.st * 25214903917) + 11) land 0xFFFFFFFFFFFF;
  r.st lsr (48 - k)

let rnd (r : rng) (n : int) : int = if n <= 1 then 0 else bits r 31 mod n
let rbool (r : rng) : bool = rnd r 2 = 0
let pick (r : rng) (xs : 'a list) : 'a = List.nth xs (rnd r (List.length xs))

(* -------------------------------------------------------------------- types as data *)

let ref_ty = Eff_native.ref_ty
let deferred_ty = Eff_native.deferred_ty
let scope_ty = Eff_native.scope_ty
let context_ty = Eff_native.context_ty
let children_ty = Ty_list (Ty_fiberOf (Ty_handle "unknown", Ty_handle "unknown"))

let vars_of (env : ty list) (t : ty) : int list =
  let rec go i = function
    | [] -> []
    | x :: xs -> if x = t then i :: go (i + 1) xs else go (i + 1) xs
  in
  go 0 env

let fiber_vars (env : ty list) : (int * ty * ty) list =
  let rec go i = function
    | [] -> []
    | Ty_fiberOf (a, b) :: xs -> (i, a, b) :: go (i + 1) xs
    | _ :: xs -> go (i + 1) xs
  in
  go 0 env

let exit_vars (env : ty list) : int list =
  let rec go i = function
    | [] -> []
    | Ty_exitOf _ :: xs -> i :: go (i + 1) xs
    | _ :: xs -> go (i + 1) xs
  in
  go 0 env

(* A term of exactly [t] in [env]: a variable of that type, a literal when [t] is a base
   type, or one of the ten native atoms applied to smaller terms.  `None` when the type is
   not inhabited by anything this environment can spell -- which is how the generator
   avoids `Term_var` past the end of the environment (rule `term_ty`, eff_typing.ml:139). *)
let rec term_of_ty (r : rng) (env : ty list) (t : ty) (fuel : int) : term option =
  let vs = List.map (fun i -> Term_var i) (vars_of env t) in
  let lits =
    match t with
    | Ty_unit -> [ Term_lit Lit_unit ]
    | Ty_nat -> [ Term_lit (Lit_nat (rnd r 8)) ]
    | Ty_bool -> [ Term_lit (Lit_bool (rbool r)) ]
    | Ty_string -> [ Term_lit (Lit_str (pick r [ "a"; "bb"; "" ])) ]
    | _ -> []
  in
  let one atom a = Term_app (atom, Terms_cons (a, Terms_nil)) in
  let two atom a b = Term_app (atom, Terms_cons (a, Terms_cons (b, Terms_nil))) in
  let apps =
    if fuel <= 0 then []
    else
      match t with
      | Ty_nat ->
        (match term_of_ty r env Ty_nat (fuel - 1) with
         | Some a -> [ one "succ" a; one "pred" a ]
         | None -> [])
      | Ty_bool ->
        (match term_of_ty r env Ty_nat (fuel - 1) with
         | Some a ->
           [ one "isZero" a ]
           @ (match term_of_ty r env Ty_nat (fuel - 1) with
              | Some b -> [ two "lt" a b; two "eq" a b ]
              | None -> [])
         | None -> [])
      | Ty_prod (a, b) ->
        (match term_of_ty r env a (fuel - 1), term_of_ty r env b (fuel - 1) with
         | Some x, Some y -> [ two "pair" x y ]
         | _ -> [])
      | _ -> []
  in
  match vs @ lits @ apps with [] -> None | cs -> Some (pick r cs)

(* A term of SOME type: a variable when the environment has one, else a literal. *)
let gen_term (r : rng) (env : ty list) : term * ty =
  if env <> [] && rnd r 3 <> 0 then
    let i = rnd r (List.length env) in
    (Term_var i, List.nth env i)
  else
    match rnd r 4 with
    | 0 -> (Term_lit Lit_unit, Ty_unit)
    | 1 -> (Term_lit (Lit_nat (rnd r 8)), Ty_nat)
    | 2 -> (Term_lit (Lit_bool (rbool r)), Ty_bool)
    | _ -> (Term_lit (Lit_str "s"), Ty_string)

let gen_cause (r : rng) (env : ty list) : cause_term * ty =
  match rnd r 4 with
  | 0 -> let t, ty = gen_term r env in (Cause_term_fail t, ty)
  | 1 -> let t, _ = gen_term r env in (Cause_term_die t, Ty_never)
  | 2 -> (Cause_term_interrupt None, Ty_never)
  | _ ->
    (match term_of_ty r env Ty_nat 1 with
     | Some w -> (Cause_term_interrupt (Some w), Ty_never)
     | None -> (Cause_term_interrupt None, Ty_never))

let gen_fork_options (r : rng) : fork_options =
  { fork_options_startImmediately = rbool r;
    fork_options_daemon = rbool r;
    fork_options_maskMode =
      pick r [ Mask_mode_interruptible; Mask_mode_uninterruptible; Mask_mode_inherit ] }

(* the arm whose answer is `never`, so `join_answer` succeeds against anything *)
let never_arm (r : rng) : eff * eff_ty =
  (Eff_fail (Term_lit (Lit_nat (rnd r 4))), Eff_typing.mk Ty_never Ty_nat Eff_typing.req_empty)

let bind_ty (a : eff_ty) (b : eff_ty) : eff_ty =
  Eff_typing.mk b.eff_ty_answer
    (Eff_typing.join a.eff_ty_error b.eff_ty_error)
    (Eff_typing.req_union a.eff_ty_requires b.eff_ty_requires)

let nil_gen : Eff_typing.gen_ty =
  { Eff_typing.gen_answer = None; gen_error = Ty_never; gen_requires = Eff_typing.req_empty }

let merge_or (a : Eff_typing.gen_ty) (b : Eff_typing.gen_ty) : Eff_typing.gen_ty option =
  match Eff_typing.gen_join_answer a.Eff_typing.gen_answer b.Eff_typing.gen_answer with
  | None -> None
  | Some ans ->
    Some
      { Eff_typing.gen_answer = ans;
        gen_error = Eff_typing.join a.Eff_typing.gen_error b.Eff_typing.gen_error;
        gen_requires =
          Eff_typing.req_union a.Eff_typing.gen_requires b.Eff_typing.gen_requires }

(* -------------------------------------------------------------------- the recursion *)

let rec gen_eff (r : rng) (env : ty list) (b : int) : eff * eff_ty =
  if b <= 1 then gen_leaf r env
  else
    let rec attempt k =
      if k = 0 then gen_leaf r env
      else match gen_node r env b (rnd r 19) with Some x -> x | None -> attempt (k - 1)
    in
    attempt 8

and gen_leaf (r : rng) (env : ty list) : eff * eff_ty =
  let rec attempt k =
    if k = 0 then (Eff_succeed (Term_lit Lit_unit), Eff_typing.pure Ty_unit)
    else
      match rnd r 9 with
      | 0 -> let t, ty = gen_term r env in (Eff_succeed t, Eff_typing.pure ty)
      | 1 -> let t, ty = gen_term r env in (Eff_sync t, Eff_typing.pure ty)
      | 2 ->
        let t, ty = gen_term r env in
        (Eff_fail t, Eff_typing.mk Ty_never ty Eff_typing.req_empty)
      | 3 ->
        let t, ty = gen_term r env in
        (Eff_yieldError t, Eff_typing.mk Ty_never ty Eff_typing.req_empty)
      | 4 ->
        let c, ty = gen_cause r env in
        (Eff_failCause c, Eff_typing.mk Ty_never ty Eff_typing.req_empty)
      | 5 -> (Eff_yieldNow (rnd r 3), Eff_typing.pure Ty_unit)
      | 6 -> (
        match gen_perform r env with Some x -> x | None -> attempt (k - 1))
      | 7 -> (
        match rnd r 3 with
        | 0 -> (Eff_withFiber Action_term_getId, Eff_typing.pure Ty_nat)
        | 1 -> (Eff_withFiber Action_term_getContext, Eff_typing.pure context_ty)
        | _ -> (Eff_withFiber Action_term_snapshotChildren, Eff_typing.pure children_ty))
      | _ ->
        let t, ty = gen_term r env in
        ( Eff_gen (Stmts_cons (Stmt_ret t, Stmts_nil)),
          Eff_typing.mk ty Ty_never Eff_typing.req_empty )
  in
  attempt 6

(* `perform op request`: the row's request type must be spelled exactly (rule `perform`,
   eff_typing.ml:198), so the op is drawn from the ops this environment can serve. *)
and gen_perform (r : rng) (env : ty list) : (eff * eff_ty) option =
  let servable =
    List.filter_map
      (fun op ->
         let row = Eff_native.row_of op in
         match term_of_ty r env row.row_request 1 with
         | Some t -> Some (op, t, Eff_typing.row_answer row)
         | None -> None)
      Eff_native.all_ops
  in
  match servable with
  | [] -> None
  | xs ->
    let op, t, ty = pick r xs in
    Some (Eff_perform (op, t), ty)

and gen_node (r : rng) (env : ty list) (b : int) (tag : int) : (eff * eff_ty) option =
  let half = if b / 2 < 1 then 1 else b / 2 in
  match tag with
  | 0 ->
    let a, ta = gen_eff r env half in
    let c, tc = gen_eff r (env @ [ ta.eff_ty_answer ]) half in
    Some (Eff_bind (a, c), bind_ty ta tc)
  | 1 -> let a, ta = gen_eff r env (b - 1) in Some (Eff_suspend a, ta)
  | 2 -> let a, ta = gen_eff r env (b - 1) in Some (Eff_uninterruptible a, ta)
  | 3 -> let a, ta = gen_eff r env (b - 1) in Some (Eff_interruptible a, ta)
  | 4 -> let a, ta = gen_eff r env (b - 1) in Some (Eff_scoped a, ta)
  | 5 ->
    let a, ta = gen_eff r env (b - 1) in
    Some
      ( Eff_exit a,
        Eff_typing.mk (Ty_exitOf (ta.eff_ty_answer, ta.eff_ty_error)) Ty_never
          ta.eff_ty_requires )
  | 6 ->
    let x, tx = gen_eff r env half in
    let henv = env @ [ Ty_causeOf tx.eff_ty_error ] in
    let h, th = gen_eff r henv half in
    let h, th =
      match Eff_typing.join_answer tx.eff_ty_answer th.eff_ty_answer with
      | Some _ -> (h, th)
      | None -> never_arm r
    in
    let answer =
      match Eff_typing.join_answer tx.eff_ty_answer th.eff_ty_answer with
      | Some a -> a
      | None -> tx.eff_ty_answer
    in
    Some
      ( Eff_catchCause (x, h),
        Eff_typing.mk answer th.eff_ty_error
          (Eff_typing.req_union tx.eff_ty_requires th.eff_ty_requires) )
  | 7 ->
    let x, tx = gen_eff r env half in
    let v, tv = gen_eff r (env @ [ tx.eff_ty_answer ]) half in
    let c, tc = gen_eff r (env @ [ Ty_causeOf tx.eff_ty_error ]) half in
    let c, tc =
      match Eff_typing.join_answer tv.eff_ty_answer tc.eff_ty_answer with
      | Some _ -> (c, tc)
      | None -> never_arm r
    in
    let answer =
      match Eff_typing.join_answer tv.eff_ty_answer tc.eff_ty_answer with
      | Some a -> a
      | None -> tv.eff_ty_answer
    in
    Some
      ( Eff_matchCause (x, v, c),
        Eff_typing.mk answer
          (Eff_typing.join tv.eff_ty_error tc.eff_ty_error)
          (Eff_typing.req_union
             (Eff_typing.req_union tx.eff_ty_requires tv.eff_ty_requires)
             tc.eff_ty_requires) )
  | 8 ->
    let x, tx = gen_eff r env half in
    let f, tf =
      gen_eff r (env @ [ Ty_exitOf (tx.eff_ty_answer, tx.eff_ty_error) ]) half
    in
    Some
      ( Eff_onExit (x, f),
        Eff_typing.mk tx.eff_ty_answer
          (Eff_typing.join tx.eff_ty_error tf.eff_ty_error)
          (Eff_typing.req_union tx.eff_ty_requires tf.eff_ty_requires) )
  | 9 -> (
    match term_of_ty r env Ty_bool 1 with
    | None -> None
    | Some test ->
      let x, tx = gen_eff r env half in
      let y, ty_ = gen_eff r env half in
      let y, ty_ =
        match Eff_typing.join_answer tx.eff_ty_answer ty_.eff_ty_answer with
        | Some _ -> (y, ty_)
        | None -> never_arm r
      in
      let answer =
        match Eff_typing.join_answer tx.eff_ty_answer ty_.eff_ty_answer with
        | Some a -> a
        | None -> tx.eff_ty_answer
      in
      Some
        ( Eff_branch (test, x, y),
          Eff_typing.mk answer
            (Eff_typing.join tx.eff_ty_error ty_.eff_ty_error)
            (Eff_typing.req_union tx.eff_ty_requires ty_.eff_ty_requires) ))
  | 10 ->
    (* whileLoop: the cursor is a nat, the test `lt cursor k`, the step `succ cursor`, so
       the loop actually turns (rule `whileLoop`, eff_typing.ml:244). *)
    let idx = List.length env in
    let initial = Term_lit (Lit_nat 0) in
    let test =
      Term_app
        ( "lt",
          Terms_cons (Term_var idx, Terms_cons (Term_lit (Lit_nat (1 + rnd r 3)), Terms_nil)) )
    in
    let body, tb = gen_eff r (env @ [ Ty_nat ]) (b - 1) in
    let step = Term_app ("succ", Terms_cons (Term_var idx, Terms_nil)) in
    Some
      ( Eff_whileLoop (initial, test, step, body),
        Eff_typing.mk Ty_unit tb.eff_ty_error tb.eff_ty_requires )
  | 11 ->
    let a, ta = gen_eff r env half in
    let rel, tr =
      gen_eff r
        (env @ [ ta.eff_ty_answer; Ty_exitOf (ta.eff_ty_answer, ta.eff_ty_error) ])
        half
    in
    Some
      ( Eff_acquireRelease (a, rel),
        Eff_typing.mk ta.eff_ty_answer ta.eff_ty_error
          (Eff_typing.req_union
             (Eff_typing.req_union ta.eff_ty_requires tr.eff_ty_requires)
             (Eff_typing.req_single Eff_native.scope_key)) )
  | 12 ->
    let body, g = gen_stmts r env false (b - 1) in
    Some
      ( Eff_gen body,
        Eff_typing.mk
          (match g.Eff_typing.gen_answer with Some a -> a | None -> Ty_unit)
          g.Eff_typing.gen_error g.Eff_typing.gen_requires )
  | 13 ->
    let p, tp = gen_eff r env (b - 1) in
    let opts = gen_fork_options r in
    if rbool r then
      Some
        ( Eff_withFiber (Action_term_fork (p, opts)),
          Eff_typing.mk
            (Ty_fiberOf (tp.eff_ty_answer, tp.eff_ty_error))
            Ty_never tp.eff_ty_requires )
    else
      Some
        ( Eff_withFiber (Action_term_forkScoped (p, opts)),
          Eff_typing.mk
            (Ty_fiberOf (tp.eff_ty_answer, tp.eff_ty_error))
            Ty_never
            (Eff_typing.req_union tp.eff_ty_requires
               (Eff_typing.req_single Eff_native.scope_key)) )
  | 14 -> Some (shape_fork r env b)
  | 15 -> Some (shape_deferred r env b)
  | 16 -> Some (shape_ref r env b)
  | 17 -> Some (shape_scope r env b)
  | _ -> shape_actions r env b

(* -------------------------------------------------------------------- the shapes *)

(* The constructors whose typing rule needs a value of a specific shape in the environment
   (`awaitFiber` a fiber handle, `closeScope` a scope AND an exit, `awaitNewChildren` a
   children snapshot) are unreachable by a uniform draw: nothing binds one by accident.
   Each shape below BINDS what its head needs and then uses it, which is how the corpus
   reaches fork/await, the deferred cells, the ref heap, scopes and the child actions. *)

and shape_fork (r : rng) (env : ty list) (b : int) : eff * eff_ty =
  let p, tp = gen_eff r env (if b / 2 < 1 then 1 else b / 2) in
  let idx = List.length env in
  let opts = gen_fork_options r in
  let mode = if rbool r then Observer_mode_awaitValue else Observer_mode_joinEffect in
  let k, tk =
    match rnd r 4 with
    | 0 -> (Eff_withFiber (Action_term_interrupt (Term_var idx)), Eff_typing.pure Ty_unit)
    | 1 ->
      (Eff_withFiber (Action_term_interruptScoped (Term_var idx)), Eff_typing.pure Ty_unit)
    | _ -> (
      ( Eff_awaitFiber (Term_var idx, mode),
        match mode with
        | Observer_mode_joinEffect ->
          Eff_typing.mk tp.eff_ty_answer tp.eff_ty_error Eff_typing.req_empty
        | Observer_mode_awaitValue ->
          Eff_typing.pure (Ty_exitOf (tp.eff_ty_answer, tp.eff_ty_error)) ))
  in
  let head = Eff_withFiber (Action_term_fork (p, opts)) in
  let thead =
    Eff_typing.mk (Ty_fiberOf (tp.eff_ty_answer, tp.eff_ty_error)) Ty_never tp.eff_ty_requires
  in
  (Eff_bind (head, k), bind_ty thead tk)

and shape_deferred (r : rng) (env : ty list) (b : int) : eff * eff_ty =
  let idx = List.length env in
  let head = Eff_perform (Native_op_deferredMake, Term_lit Lit_unit) in
  let thead = Eff_typing.row_answer (Eff_native.row_of Native_op_deferredMake) in
  let inner = env @ [ deferred_ty ] in
  let k, tk =
    match rnd r 6 with
    | 0 ->
      ( Eff_perform (Native_op_deferredAwait, Term_var idx),
        Eff_typing.row_answer (Eff_native.row_of Native_op_deferredAwait) )
    | 1 ->
      ( Eff_callback (Native_op_deferredAwait, Term_var idx),
        Eff_typing.row_answer (Eff_native.row_of Native_op_deferredAwait) )
    | 2 ->
      let op = if rbool r then Native_op_deferredSucceed else Native_op_deferredFail in
      ( Eff_perform
          ( op,
            Term_app
              ( "pair",
                Terms_cons (Term_var idx, Terms_cons (Term_lit (Lit_nat (rnd r 5)), Terms_nil))
              ) ),
        Eff_typing.row_answer (Eff_native.row_of op) )
    | 3 ->
      let op = if rbool r then Native_op_deferredIsDone else Native_op_deferredPoll in
      (Eff_perform (op, Term_var idx), Eff_typing.row_answer (Eff_native.row_of op))
    | _ -> gen_eff r inner (b - 1)
  in
  (Eff_bind (head, k), bind_ty thead tk)

and shape_ref (r : rng) (env : ty list) (b : int) : eff * eff_ty =
  let idx = List.length env in
  let head = Eff_perform (Native_op_refMake, Term_lit (Lit_nat (rnd r 8))) in
  let thead = Eff_typing.row_answer (Eff_native.row_of Native_op_refMake) in
  let pair a c = Term_app ("pair", Terms_cons (a, Terms_cons (c, Terms_nil))) in
  let fn () = pick r [ Fn_name_incr; Fn_name_double; Fn_name_zeroWhenPositive;
                       Fn_name_noChange; Fn_name_takeAndBump ] in
  let k, tk =
    (* mostly an explicit operation on the ref just bound, so all TWELVE ref rows are
       reached and not only the arms a uniform draw over the 53 native ops happens to pick *)
    if rnd r 4 <> 0 then
      let op, req =
        match rnd r 12 with
        | 0 -> (Native_op_refGet, Term_var idx)
        | 1 -> (Native_op_refSet, pair (Term_var idx) (Term_lit (Lit_nat (rnd r 5))))
        | 2 -> (Native_op_refGetAndSet, pair (Term_var idx) (Term_lit (Lit_nat (rnd r 5))))
        | 3 -> (Native_op_refSetAndGet, pair (Term_var idx) (Term_lit (Lit_nat (rnd r 5))))
        | 4 -> (Native_op_refUpdate (fn ()), Term_var idx)
        | 5 -> (Native_op_refGetAndUpdate (fn ()), Term_var idx)
        | 6 -> (Native_op_refUpdateAndGet (fn ()), Term_var idx)
        | 7 -> (Native_op_refUpdateSome (fn ()), Term_var idx)
        | 8 -> (Native_op_refGetAndUpdateSome (fn ()), Term_var idx)
        | 9 -> (Native_op_refUpdateSomeAndGet (fn ()), Term_var idx)
        | 10 -> (Native_op_refModify (fn ()), Term_var idx)
        | _ -> (Native_op_refModifySome (fn ()), Term_var idx)
      in
      (Eff_perform (op, req), Eff_typing.row_answer (Eff_native.row_of op))
    else gen_eff r (env @ [ ref_ty ]) (b - 1)
  in
  (Eff_bind (head, k), bind_ty thead tk)

and shape_scope (r : rng) (env : ty list) (b : int) : eff * eff_ty =
  let strat = if rbool r then Finalizer_strategy_sequential else Finalizer_strategy_parallel in
  let idx = List.length env in
  let head = Eff_perform (Native_op_scopeMake strat, Term_lit Lit_unit) in
  let thead = Eff_typing.row_answer (Eff_native.row_of (Native_op_scopeMake strat)) in
  let inner = env @ [ scope_ty ] in
  let k, tk =
    match rnd r 4 with
    | 0 ->
      let p, tp = gen_eff r inner (if b / 2 < 1 then 1 else b / 2) in
      ( Eff_withFiber (Action_term_forkIn (p, gen_fork_options r, Term_var idx)),
        Eff_typing.mk
          (Ty_fiberOf (tp.eff_ty_answer, tp.eff_ty_error))
          Ty_never tp.eff_ty_requires )
    | 2 ->
      (* runIn is the one action that needs a fiber AND a scope at once: fork into the
         scope first, then run the child in it *)
      let p, tp = gen_eff r inner (if b / 2 < 1 then 1 else b / 2) in
      let fork = Eff_withFiber (Action_term_forkIn (p, gen_fork_options r, Term_var idx)) in
      let tfork =
        Eff_typing.mk (Ty_fiberOf (tp.eff_ty_answer, tp.eff_ty_error)) Ty_never
          tp.eff_ty_requires
      in
      let run =
        Eff_withFiber (Action_term_runIn (Term_var (List.length inner), Term_var idx))
      in
      (Eff_bind (fork, run), bind_ty tfork (Eff_typing.pure Ty_unit))
    | 1 ->
      (* closeScope needs an exitOf term as well, so bind one first *)
      let p, tp = gen_eff r inner (if b / 2 < 1 then 1 else b / 2) in
      let einner = inner @ [ Ty_exitOf (tp.eff_ty_answer, tp.eff_ty_error) ] in
      let close =
        Eff_withFiber (Action_term_closeScope (Term_var idx, Term_var (List.length inner)))
      in
      let texit =
        Eff_typing.mk (Ty_exitOf (tp.eff_ty_answer, tp.eff_ty_error)) Ty_never
          tp.eff_ty_requires
      in
      ignore einner;
      (Eff_bind (Eff_exit p, close), bind_ty texit (Eff_typing.pure Ty_unit))
    | _ -> gen_eff r inner (b - 1)
  in
  (Eff_bind (head, k), bind_ty thead tk)

and shape_actions (r : rng) (env : ty list) (b : int) : (eff * eff_ty) option =
  let idx = List.length env in
  match rnd r 4 with
  | 0 ->
    let k, tk =
      match rnd r 4 with
      | 0 ->
        ( Eff_withFiber (Action_term_awaitAll (Term_var idx)),
          Eff_typing.pure (Ty_list (Ty_exitOf (Ty_handle "unknown", Ty_handle "unknown"))) )
      | 1 ->
        ( Eff_withFiber (Action_term_awaitAllFailFast (Term_var idx)),
          Eff_typing.pure (Ty_list (Ty_exitOf (Ty_handle "unknown", Ty_handle "unknown"))) )
      | 2 ->
        ( Eff_withFiber (Action_term_awaitNewChildren (Term_var idx)),
          Eff_typing.pure Ty_unit )
      | _ ->
        let who = if rbool r then Some (Term_lit (Lit_nat 0)) else None in
        (Eff_withFiber (Action_term_interruptAll (Term_var idx, who)), Eff_typing.pure Ty_unit)
    in
    Some
      ( Eff_bind (Eff_withFiber Action_term_snapshotChildren, k),
        bind_ty (Eff_typing.pure children_ty) tk )
  | 1 ->
    Some
      ( Eff_bind
          ( Eff_withFiber Action_term_getContext,
            Eff_withFiber (Action_term_setContext (Term_var idx)) ),
        bind_ty (Eff_typing.pure context_ty) (Eff_typing.pure Ty_unit) )
  | 2 ->
    let x, tx = gen_eff r env (if b / 2 < 1 then 1 else b / 2) in
    let y, ty_ = gen_eff r env (if b / 2 < 1 then 1 else b / 2) in
    let y, ty_ =
      match Eff_typing.join_answer tx.eff_ty_answer ty_.eff_ty_answer with
      | Some _ -> (y, ty_)
      | None -> never_arm r
    in
    let answer =
      match Eff_typing.join_answer tx.eff_ty_answer ty_.eff_ty_answer with
      | Some a -> a
      | None -> tx.eff_ty_answer
    in
    Some
      ( Eff_withFiber
          (Action_term_raceAll (Effs_cons (x, Effs_cons (y, Effs_nil)))),
        Eff_typing.mk answer
          (Eff_typing.join tx.eff_ty_error ty_.eff_ty_error)
          (Eff_typing.req_union tx.eff_ty_requires ty_.eff_ty_requires) )
  | _ -> (
    (* runIn needs a fiber AND a scope already in scope; only take it when both are there *)
    match fiber_vars env, vars_of env scope_ty with
    | (fi, _, _) :: _, si :: _ ->
      Some
        ( Eff_withFiber (Action_term_runIn (Term_var fi, Term_var si)),
          Eff_typing.pure Ty_unit )
    | _ -> (
      match exit_vars env, vars_of env scope_ty with
      | ei :: _, si :: _ ->
        Some
          ( Eff_withFiber (Action_term_closeScope (Term_var si, Term_var ei)),
            Eff_typing.pure Ty_unit )
      | _ -> None))

and gen_stmts (r : rng) (env : ty list) (in_loop : bool) (b : int)
  : stmts * Eff_typing.gen_ty =
  if b <= 0 then (Stmts_nil, nil_gen)
  else
    let half = if b / 2 < 1 then 1 else b / 2 in
    match rnd r (if in_loop then 8 else 7) with
    | 0 -> (Stmts_nil, nil_gen)
    | 1 ->
      let e, te = gen_eff r env half in
      let rest, tr = gen_stmts r (env @ [ te.eff_ty_answer ]) in_loop half in
      ( Stmts_cons (Stmt_bindYield e, rest),
        { Eff_typing.gen_answer = tr.Eff_typing.gen_answer;
          gen_error = Eff_typing.join te.eff_ty_error tr.Eff_typing.gen_error;
          gen_requires =
            Eff_typing.req_union te.eff_ty_requires tr.Eff_typing.gen_requires } )
    | 2 ->
      let e, te = gen_eff r env half in
      let rest, tr = gen_stmts r env in_loop half in
      ( Stmts_cons (Stmt_yieldDiscard e, rest),
        { Eff_typing.gen_answer = tr.Eff_typing.gen_answer;
          gen_error = Eff_typing.join te.eff_ty_error tr.Eff_typing.gen_error;
          gen_requires =
            Eff_typing.req_union te.eff_ty_requires tr.Eff_typing.gen_requires } )
    | 3 ->
      let t, ty_ = gen_term r env in
      ( Stmts_cons (Stmt_ret t, Stmts_nil),
        { Eff_typing.gen_answer = Some ty_; gen_error = Ty_never;
          gen_requires = Eff_typing.req_empty } )
    | 4 -> (
      match term_of_ty r env Ty_bool 1 with
      | None -> (Stmts_nil, nil_gen)
      | Some test ->
        let a, ta = gen_stmts r env in_loop half in
        let c, tc = gen_stmts r env in_loop half in
        let c, tc = match merge_or ta tc with Some _ -> (c, tc) | None -> (Stmts_nil, nil_gen) in
        let ab = match merge_or ta tc with Some m -> m | None -> ta in
        let rest, trr = gen_stmts r env in_loop half in
        let rest, trr =
          match merge_or ab trr with Some _ -> (rest, trr) | None -> (Stmts_nil, nil_gen)
        in
        let all = match merge_or ab trr with Some m -> m | None -> ab in
        (Stmts_cons (Stmt_ifElse (test, a, c), rest), all))
    | 5 ->
      let body, tb = gen_stmts r env true half in
      let rest, tr = gen_stmts r env in_loop half in
      let rest, tr =
        match merge_or tb tr with Some _ -> (rest, tr) | None -> (Stmts_nil, nil_gen)
      in
      let all = match merge_or tb tr with Some m -> m | None -> tb in
      (Stmts_cons (Stmt_whileTrue body, rest), all)
    | 6 -> (Stmts_nil, nil_gen)
    | _ ->
      let rest, tr = gen_stmts r env in_loop half in
      (Stmts_cons (Stmt_breakLoop, rest), tr)

(* -------------------------------------------------------------------- the face *)

type gen_report = {
  gr_seed : int;
  gr_asked : int;
  gr_draws : int;  (** draws made, including the ones the net refused *)
  gr_refused : int;  (** draws `Eff_typing.well_typed` refused: X1's measurement *)
  gr_max_depth : int;
}

let rec depth_of (e : eff) : int =
  let s = depth_stmts and es = depth_effs in
  1
  +
  match e with
  | Eff_succeed _ | Eff_fail _ | Eff_failCause _ | Eff_yieldError _ | Eff_sync _
  | Eff_yieldNow _ | Eff_callback _ | Eff_awaitFiber _ | Eff_perform _ ->
    0
  | Eff_suspend a | Eff_exit a | Eff_uninterruptible a | Eff_interruptible a | Eff_scoped a ->
    depth_of a
  | Eff_bind (a, c) | Eff_catchCause (a, c) | Eff_onExit (a, c) | Eff_acquireRelease (a, c)
  | Eff_catchIf (_, a, c) ->
    max (depth_of a) (depth_of c)
  | Eff_matchCause (a, c, d) -> max (depth_of a) (max (depth_of c) (depth_of d))
  | Eff_branch (_, a, c) -> max (depth_of a) (depth_of c)
  | Eff_whileLoop (_, _, _, a) -> depth_of a
  | Eff_provideLayer (l, _, e) -> max (depth_layer l) (depth_of e)
  | Eff_service _ -> 0
  | Eff_provideService (_, _, e) -> depth_of e
  | Eff_gen b -> s b
  | Eff_withFiber a -> (
    match a with
    | Action_term_fork (p, _) | Action_term_forkScoped (p, _) | Action_term_forkIn (p, _, _) ->
      depth_of p
    | Action_term_raceAll xs -> es xs
    | _ -> 0)

and depth_layer (l : layer_term) : int =
  1 +
  match l with
  | Layer_term_succeed _ -> 0
  | Layer_term_effect (_, e) | Layer_term_effectDiscard e -> depth_of e
  | Layer_term_provide (a, b) | Layer_term_provideMerge (a, b) | Layer_term_merge (a, b) ->
    max (depth_layer a) (depth_layer b)
  | Layer_term_fresh l | Layer_term_orDie l -> depth_layer l
  | Layer_term_ref _ -> 0
  | Layer_term_mergeAll ls -> depth_layers ls

and depth_layers (ls : layer_terms) : int =
  match ls with
  | Layer_terms_nil -> 0
  | Layer_terms_cons (h, t) -> max (depth_layer h) (depth_layers t)

and depth_stmts (s : stmts) : int =
  match s with
  | Stmts_nil -> 0
  | Stmts_cons (h, t) ->
    max
      (match h with
       | Stmt_bindYield e | Stmt_yieldDiscard e -> depth_of e
       | Stmt_ifElse (_, a, c) -> max (depth_stmts a) (depth_stmts c)
       | Stmt_whileTrue a -> depth_stmts a
       | Stmt_ret _ | Stmt_breakLoop -> 0)
      (depth_stmts t)

and depth_effs (e : effs) : int =
  match e with Effs_nil -> 0 | Effs_cons (h, t) -> max (depth_of h) (depth_effs t)

(* [generate ~seed ~count ~max_depth] draws [count] well-typed programs.  The size budget
   is drawn per program so the corpus mixes trivia with depth; [max_depth] bounds the
   budget, and the DEPTH of what came out is reported, not assumed. *)
let generate ?(seed = 20260908) ?(count = 500) ?(max_depth = 12) () :
  program list * gen_report =
  let r = rng_make seed in
  let out = ref [] and draws = ref 0 and refused = ref 0 and deepest = ref 0 in
  let i = ref 0 in
  while List.length !out < count && !draws < count * 40 do
    incr draws;
    let budget = 2 + rnd r (max_depth - 1) in
    let e, _ = gen_eff r [] budget in
    if Eff_typing.well_typed e then begin
      let d = depth_of e in
      if d > !deepest then deepest := d;
      incr i;
      out :=
        { name = Printf.sprintf "g%03d" !i;
          corpus = "generated";
          eff = e;
          bytes = (try Some (Eff_wire.encode_program e) with _ -> None) }
        :: !out
    end
    else incr refused
  done;
  ( List.rev !out,
    { gr_seed = seed; gr_asked = count; gr_draws = !draws; gr_refused = !refused;
      gr_max_depth = !deepest } )

(* ==================================================================== the census *)

let census (ps : program list) : (string * int) list =
  let tbl : (string, int) Hashtbl.t = Hashtbl.create 128 in
  let bump k = Hashtbl.replace tbl k (1 + Option.value (Hashtbl.find_opt tbl k) ~default:0) in
  let rec e_ (x : eff) =
    bump ("eff." ^ ctor_name_eff x);
    match x with
    | Eff_succeed _ | Eff_fail _ | Eff_failCause _ | Eff_yieldError _ | Eff_sync _
    | Eff_yieldNow _ | Eff_awaitFiber _ ->
      ()
    | Eff_perform (op, _) | Eff_callback (op, _) -> bump ("op." ^ ctor_name_native_op op)
    | Eff_suspend a | Eff_exit a | Eff_uninterruptible a | Eff_interruptible a | Eff_scoped a
      ->
      e_ a
    | Eff_bind (a, c) | Eff_catchCause (a, c) | Eff_onExit (a, c) | Eff_acquireRelease (a, c)
    | Eff_catchIf (_, a, c)
      ->
      e_ a; e_ c
    | Eff_matchCause (a, c, d) -> e_ a; e_ c; e_ d
    | Eff_branch (_, a, c) -> e_ a; e_ c
    | Eff_whileLoop (_, _, _, a) -> e_ a
    | Eff_gen b -> s_ b
    | Eff_withFiber a -> a_ a
    | Eff_provideLayer (l, _, e) -> l_ l; e_ e
    | Eff_service _ -> ()
    | Eff_provideService (_, _, e) -> e_ e
  and l_ (x : layer_term) =
    bump ("layer." ^ ctor_name_layer_term x);
    match x with
    | Layer_term_succeed _ -> ()
    | Layer_term_effect (_, e) | Layer_term_effectDiscard e -> e_ e
    | Layer_term_provide (a, b) | Layer_term_provideMerge (a, b) | Layer_term_merge (a, b) ->
      l_ a; l_ b
    | Layer_term_fresh l | Layer_term_orDie l -> l_ l
    | Layer_term_ref _ -> ()
    | Layer_term_mergeAll ls -> ls_ ls
  and ls_ (x : layer_terms) =
    match x with
    | Layer_terms_nil -> ()
    | Layer_terms_cons (h, t) -> l_ h; ls_ t
  and a_ (x : action_term) =
    bump ("action." ^ ctor_name_action_term x);
    match x with
    | Action_term_fork (p, _) | Action_term_forkScoped (p, _) | Action_term_forkIn (p, _, _) ->
      e_ p
    | Action_term_raceAll xs -> es_ xs
    | _ -> ()
  and s_ (x : stmts) =
    match x with
    | Stmts_nil -> ()
    | Stmts_cons (h, t) ->
      bump ("stmt." ^ ctor_name_stmt h);
      (match h with
       | Stmt_bindYield e | Stmt_yieldDiscard e -> e_ e
       | Stmt_ifElse (_, a, c) -> s_ a; s_ c
       | Stmt_whileTrue a -> s_ a
       | Stmt_ret _ | Stmt_breakLoop -> ());
      s_ t
  and es_ (x : effs) = match x with Effs_nil -> () | Effs_cons (h, t) -> e_ h; es_ t in
  List.iter (fun p -> e_ p.eff) ps;
  List.sort
    (fun (a, x) (b, y) -> if x = y then compare a b else compare y x)
    (Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl [])

(* The constructors of `Eff_types.eff` / `action_term` / `stmt` / `native_op` that the
   census did NOT see -- the honest half of a coverage claim. *)
let census_missing (c : (string * int) list) : string list =
  let seen k = List.mem_assoc k c in
  List.filter_map
    (fun k -> if seen k then None else Some k)
    (List.map (fun n -> "eff." ^ n) ctor_names_eff
    @ List.map (fun n -> "action." ^ n) ctor_names_action_term
    @ List.map (fun n -> "stmt." ^ n) ctor_names_stmt
    @ List.map (fun n -> "op." ^ n) ctor_names_native_op)
