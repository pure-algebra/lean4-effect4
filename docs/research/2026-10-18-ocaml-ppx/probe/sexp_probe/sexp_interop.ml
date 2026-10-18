(* sexp_interop.ml -- probe: a Lean carrier under Jane Street's names, so hand types holding it
   use the derivers as they are. Every function below is Lean's, lowered; this module only names
   them as ppx_sexp_conv, ppx_compare and ppx_hash expect. *)

module G = Effect4_gen.Api_gen
open! Sexplib0.Sexp_conv
open! Ppx_compare_lib.Builtin
open! Ppx_hash_lib.Std.Hash.Builtin

module Request = struct
  type t = G.request G.envelope

  let sexp_of_t = G.test_probe_sexp_lane_request_to_sexp

  let t_of_sexp x =
    match G.test_probe_sexp_lane_request_of_sexp x with
    | Some r -> r
    | None -> Sexplib0.Sexp_conv.of_sexp_error "Request.t_of_sexp: not a request's print" x

  let equal = G.test_probe_sexp_lane_request_equal

  let compare a b =
    match G.test_probe_sexp_lane_request_compare a b with
    | G.Ordering_lt -> -1
    | G.Ordering_eq -> 0
    | G.Ordering_gt -> 1

  (* Equal carriers have equal canonical bytes, so hashing the machine text respects [equal]. *)
  let hash_fold_t st x = Base.Hash.fold_string st (Sexplib0.Sexp.to_string_mach (sexp_of_t x))
  let hash x = Base.Hash.get_hash_value (hash_fold_t (Base.Hash.create ()) x)

  include Base.Comparator.Make (struct
    type nonrec t = t

    let compare = compare
    let sexp_of_t = sexp_of_t
  end)
end

(* A hand type that holds a Lean carrier, derived as any Jane Street type is. *)
type logged = { at : int; request : Request.t; note : string option }
[@@deriving sexp, equal, compare, hash]

let history : Request.t = Request.t_of_sexp (Parsexp.Single.parse_string_exn "((method history)(version 1)(payload(ask(q history))))")
let table : Request.t = Request.t_of_sexp (Parsexp.Single.parse_string_exn "((method table)(version 1)(payload(ask(q table))))")

let%expect_test "a logged request prints through Lean's face" =
  print_endline (Sexplib0.Sexp.to_string_hum (sexp_of_logged { at = 3; request = history; note = None }));
  [%expect {|
    ((at 3) (request ((method history) (version 1) (payload (ask (q history)))))
     (note ())) |}]

let%test_unit "derived equality, order and hash agree with Lean's" =
  let a = { at = 1; request = history; note = Some "x" } and b = { at = 1; request = table; note = Some "x" } in
  [%test_eq: logged] a (logged_of_sexp (sexp_of_logged a));
  [%test_result: bool] (equal_logged a b) ~expect:false;
  [%test_result: int] (Int.compare (compare_logged a b) 0 |> Int.abs) ~expect:1;
  [%test_result: bool] (hash_logged a = hash_logged (logged_of_sexp (sexp_of_logged a))) ~expect:true

let%test_unit "a Base map keyed by a Lean carrier" =
  let m = Base.Map.of_alist_exn (module Request) [ (history, "h"); (table, "t") ] in
  [%test_result: string option] (Base.Map.find m history) ~expect:(Some "h")
