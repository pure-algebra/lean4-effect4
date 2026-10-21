(* test_rocq.ml -- the generated Rocq skeleton against Lean's lowered call tree.

   Rocq_run extracts rocq/Skeleton.v, printed from Effect4.Run.Tree by make gen-rocq.
   SkeletonApprox.v proves budget monotonicity of that generated skeleton.
   Both trees use the same lowered evaluator and Tree.run, with one host and one observer.
   The observation is the host calls and replies, cell answers, and stop, as at the base.
   This finite comparison checks the control skeleton, not the shared evaluator or runner.
   It proves neither lowering correctness nor the open ofProgram_eq_denoteRowsB statement.

   Properties:
   R1  The adapter copies the four tree constructors and composes each continuation with
       itself. It evaluates no term and handles no operation.                 by construction
   R2  The kit examples, including caught failure and context read, agree at budgets 0 to 12.
                                                                             tested
   R3  Every to-do request agrees under its typed record host at budgets 0 to 8. tested
   R4  The typed corpus programs selected by InRocq agree under the silent host and four
       unit replies at budgets 0 to 8. Refused programs are measured separately. tested
   R5  A wrong budget and an altered evaluator each produce a detected difference. tested *)

open Eff_types

(* The internal type owner: Api_gen seals these types for installed clients. *)
module G = Closure_gen
module A = Effect4_kit.Kit_author
module R = Rocq_run

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if not ok
  then (
    incr failures;
    Printf.printf "FAIL %s\n%!" name)
;;

type exit = (Val.t, Err.t, Defect.t, Z.t, unit) Exit.t

(* R1: no execution in the adapter; the shared lowered runner observes each tree. *)
module Adapt (E : R.Eval with type sync_op = Rocq_gen.sync_op and type ctx = Rocq_gen.ctx) =
struct
  module T = R.Skeleton (E)

  let rec tree : T.tree -> G.tree = function
    | T.Tree_done ex -> G.Tree_done ex
    | T.Tree_cut -> G.Tree_cut
    | T.Tree_call (i, v, resume) -> G.Tree_call (i, v, fun ex -> tree (resume ex))
    | T.Tree_cell (op, resume) -> G.Tree_cell (op, fun v -> tree (resume v))
  ;;

  let of_program rows k p = tree (T.ofProgram rows k p)
end

module Original = Adapt (R.Lean)

module Wrong_eval = struct
  include R.Lean

  let eval_value _ _ = Exit.Success Val.Unit
end

module Wrong = Adapt (Wrong_eval)

type stop =
  | Finished of exit
  | Cut
  | Waiting of Z.t * Val.t

type run =
  { calls : (Z.t * Val.t * exit) list
  ; cells : Val.t list
  ; stop : stop
  }

let observe (o : 's G.effect4_run_tree_outcome) : run =
  { calls =
      List.filter_map
        (function
          | G.Step_called (i, v, ex) -> Some (i, v, ex)
          | _ -> None)
        o.steps
  ; cells =
      List.filter_map
        (function
          | G.Step_celled (_, v) -> Some v
          | _ -> None)
        o.steps
  ; stop =
      (match o.stop with
       | G.Stop_finished ex -> Finished ex
       | G.Stop_cut -> Cut
       | G.Stop_waiting (i, v) -> Waiting (i, v))
  }
;;

let equal_exit a b =
  Eff_val.equal
    (Effect4_gen.Api_gen.run_kit_exit_to_val a)
    (Effect4_gen.Api_gen.run_kit_exit_to_val b)
;;

let equal_run a b =
  List.equal
    (fun (i, v, ex) (j, w, ey) -> Z.equal i j && Eff_val.equal v w && equal_exit ex ey)
    a.calls
    b.calls
  && List.equal Eff_val.equal a.cells b.cells
  &&
  match a.stop, b.stop with
  | Finished x, Finished y -> equal_exit x y
  | Cut, Cut -> true
  | Waiting (i, v), Waiting (j, w) -> Z.equal i j && Eff_val.equal v w
  | _ -> false
;;

let lean_run rows k host st p = observe (G.run_tree_probe rows (Z.of_int k) host st p)

let rocq_run rows k host st p =
  observe (G.run_tree_run host (Original.of_program rows k p) st)
;;

let value_text v = Effect4_kit.Kit.Json.(render (value_json v))
let exit_text ex = value_text (Effect4_gen.Api_gen.run_kit_exit_to_val ex)

let run_text (r : run) =
  Printf.sprintf
    "calls [%s] cells [%s] %s"
    (String.concat
       "; "
       (List.map
          (fun (i, v, a) ->
             Printf.sprintf "%s %s -> %s" (Z.to_string i) (value_text v) (exit_text a))
          r.calls))
    (String.concat "; " (List.map value_text r.cells))
    (match r.stop with
     | Finished ex -> "finished " ^ exit_text ex
     | Cut -> "cut"
     | Waiting (i, v) -> Printf.sprintf "waiting %s %s" (Z.to_string i) (value_text v))
;;

let shown = ref 0

(* The first budget up to [upto] at which the runs differ; the first few differences print both
   runs. *)
let first_difference ?(name = "") ~upto rows host st p =
  let rec go k =
    if k > upto
    then None
    else (
      let l = lean_run rows k host st p
      and r = rocq_run rows k host st p in
      if equal_run l r
      then go (k + 1)
      else (
        if !shown < 12
        then (
          incr shown;
          Printf.printf
            "  %s at budget %d\n    Lean %s\n    Rocq %s\n"
            name
            k
            (run_text l)
            (run_text r));
        Some k))
  in
  go 0
;;

let tape : Z.t -> Val.t -> exit list -> (exit * exit list) option =
  fun _ _ t ->
  match t with
  | ex :: rest -> Some (ex, rest)
  | [] -> None
;;

let silent : Z.t -> Val.t -> unit -> (exit * unit) option = fun _ _ () -> None
let unit_ok : exit = Exit.Success Val.Unit
let units n = List.init n (fun _ -> unit_ok)

let r2 () =
  let echo = A.row "echo" ~request:Ty.Nat ~answer:Ty.Unit () in
  let app = Effect4_kit.Kit.app ~rows:[ echo ] () in
  let rows = [ echo ] in
  let build ?defs p =
    match A.build ~app ?defs p with
    | Ok e -> e
    | Error r -> failwith (A.refusal_text r)
  in
  let doubling =
    build
      (A.loop
         ~init:(A.nat 1)
         ~test:(fun c -> A.(c < nat 16))
         ~step:(fun c _ -> A.(c * nat 2))
         ~result:(fun c -> c)
         (fun c -> A.perform "echo" c))
  in
  let cells =
    build
      A.(
        let* c = cell (nat 0) in
        loop
          ~init:(nat 1)
          ~test:(fun i -> i < nat 8)
          ~step:(fun i _ -> i * nat 2)
          ~result:(fun _ -> unit)
          (fun i -> set c i)
        >> get c)
  in
  let caught = build A.(catch (fail (str "boom")) (fun _ -> succeed (nat 7))) in
  let self_call =
    build
      ~defs:[ A.def "f" ~request:Ty.Nat ~answer:Ty.Nat (fun r -> A.call "f" r) ]
      (A.call "f" (A.nat 0))
  in
  let twice =
    build
      ~defs:
        [ A.def "twice" ~request:Ty.Nat ~answer:Ty.Nat (fun r ->
            A.(
              let* _ = perform "echo" r in
              succeed (r * nat 2)))
        ]
      A.(
        let* a = call "twice" (nat 3) in
        call "twice" a)
  in
  let same name host st p =
    check
      (Printf.sprintf "R2 %s: equal at budgets 0 to 12" name)
      (first_difference ~name ~upto:12 rows host st p = None)
  in
  same "doubling, four replies" tape (units 4) doubling;
  same "doubling, three replies" tape (units 3) doubling;
  same
    "doubling, a refused-looking reply"
    tape
    [ unit_ok; Exit.Success (Val.Str "oops") ]
    doubling;
  same "a cell written in a loop" silent () cells;
  same "a caught failure" silent () caught;
  let context = Eff.WithFiber (ActionTerm.Context []) in
  same "a context read" silent () context;
  check
    "R5 a wrong budget is detected"
    (not
       (equal_run
          (lean_run rows 2 tape (units 4) doubling)
          (rocq_run rows 1 tape (units 4) doubling)));
  let changed = observe (G.run_tree_run silent (Wrong.of_program rows 0 caught) ()) in
  check
    "R5 an altered evaluator is detected"
    (not (equal_run (lean_run rows 0 silent () caught) changed));
  same "a definition that calls itself" silent () self_call;
  same "a definition called twice" tape (units 2) twice
;;

let r3 () =
  let requests = Todo_fixture.read_fixture "../todo/todo-host.txt" in
  let provider = Native_todo.provider Native_todo.record in
  let differ =
    List.filter_map
      (fun (r : Todo_fixture.request) ->
         let built = Todo_fixture.built_of r in
         let state =
           Todo_fixture.repo_of
             (Todo_fixture.exactly "the state" Eff_val.decode_exact r.state)
         in
         let rows = built.app.rows in
         let host = G.run_tree_host_of_reactor rows provider in
         match first_difference ~name:r.entry ~upto:8 rows host state built.program with
         | None -> None
         | Some k -> Some (Printf.sprintf "%s at %d" r.entry k))
      requests
  in
  Printf.printf
    "R3 to-do fixture: %d requests, %d differ%s\n"
    (List.length requests)
    (List.length differ)
    (if differ = []
     then ""
     else ": " ^ String.concat ", " (List.filteri (fun i _ -> i < 8) differ));
  check
    "R3 the to-do fixture: equal at budgets 0 to 8"
    (List.length requests = 7 && differ = [])
;;

(* The printed corpus: verdicts.txt of the kit's lane, one program a line. *)
let corpus () =
  let bytes_of_hex h =
    String.init
      (String.length h / 2)
      (fun i -> Char.chr (int_of_string ("0x" ^ String.sub h (2 * i) 2)))
  in
  In_channel.with_open_bin "../kit/verdicts.txt" In_channel.input_all
  |> String.split_on_char '\n'
  |> List.filter_map (fun l ->
    match String.split_on_char '\t' l with
    | name :: hex :: _ :: _ ->
      Option.map (fun p -> name, p) (Eff_codec.decode_program (bytes_of_hex hex))
    | _ -> None)
;;

let r4 () =
  let empty = Effect4_kit.Kit.app () in
  let fragment = List.filter (fun (_, p) -> Rocq_gen.run_tree_in_rocq p) (corpus ()) in
  let typed, refused =
    List.partition (fun (_, p) -> Result.is_ok (Effect4_kit.Kit.check empty p)) fragment
  in
  let differ host st programs =
    List.filter_map
      (fun (name, p) ->
         Option.map
           (fun k -> Printf.sprintf "%s at %d" name k)
           (first_difference ~name ~upto:8 [] host st p))
      programs
  in
  let names xs =
    if xs = []
    then ""
    else " (" ^ String.concat ", " (List.filteri (fun i _ -> i < 8) xs) ^ ")"
  in
  let silent_differ = differ silent () typed
  and tape_differ = differ tape (units 4) typed in
  let refused_differ = differ silent () refused in
  Printf.printf
    "R4 corpus: %d programs in InRocq, %d of them typed; %d differ under the silent \
     host%s, %d under four units%s\n"
    (List.length fragment)
    (List.length typed)
    (List.length silent_differ)
    (names silent_differ)
    (List.length tape_differ)
    (names tape_differ);
  Printf.printf
    "R4 the %d the checker refuses, a measurement: %d differ under the silent host%s\n"
    (List.length refused)
    (List.length refused_differ)
    (names refused_differ);
  check
    "R4 the corpus, the silent host: equal at budgets 0 to 8"
    (List.length fragment = 51 && List.length typed = 36 && silent_differ = []);
  check "R4 the corpus, four units: equal at budgets 0 to 8" (tape_differ = [])
;;

let () =
  r2 ();
  r3 ();
  r4 ();
  Printf.printf "test_rocq: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
;;
