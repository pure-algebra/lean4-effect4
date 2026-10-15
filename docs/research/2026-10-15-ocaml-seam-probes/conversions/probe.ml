(* Research probe over copied generated carriers and installed libraries.
   Depends on Eff_types, Eff_wire, Sexplib, Base_quickcheck and E4_clock.
   Properties: every assertion has a printed case identifier [tested].
   Scope: finite host observations; no compiler or universal conversion theorem. *)
open Sexplib.Std

let passed = ref 0
let check name condition =
  if not condition then failwith ("FAIL " ^ name);
  incr passed;
  Printf.printf "PASS %s\n%!" name

let raises f = try ignore (f ()); false with _ -> true
let sexp = Sexplib.Sexp.of_string
let show = Sexplib.Sexp.to_string_mach

module Payload = struct
  open Base
  open Base_quickcheck.Export
  type t = { count : int; note : string option; flags : bool list }
  [@@deriving sexp, sexp_grammar, compare, quickcheck]
end

module Capability = struct
  type t = { serial : int }
  let make serial = { serial }
end

type capability_view = { label : string; resource : (Capability.t [@sexp.opaque]) }
[@@deriving sexp]

(* Host facade: exact decimal is distinct from a bounded observation. *)
module Nat : sig
  type t
  val of_decimal : string -> t option
  val to_decimal : t -> string
end = struct
  type t = E4_clock.t
  let of_decimal = E4_clock.of_decimal
  let to_decimal = E4_clock.to_decimal
end

let () =
  let open Eff_types in
  let tys = [
    Ty_never; Ty_unit; Ty_nat; Ty_int; Ty_string; Ty_bool; Ty_handle "File";
    Ty_option Ty_nat; Ty_list Ty_bool; Ty_prod (Ty_nat, Ty_string);
    Ty_except (Ty_string, Ty_nat); Ty_exitOf (Ty_nat, Ty_string);
    Ty_causeOf Ty_string; Ty_fiberOf (Ty_nat, Ty_string);
    Ty_union (Ty_nat, Ty_int); Ty_lit "Ready"; Ty_refOf Ty_nat;
    Ty_deferredOf (Ty_nat, Ty_string); Ty_var 0; Ty_unknown;
    Ty_record [("count", (false, Ty_nat)); ("note", (true, Ty_string))];
    Ty_map (Ty_string, Ty_nat); Ty_tuple [Ty_nat; Ty_bool; Ty_string];
    Ty_app ("Box", [Ty_nat]); Ty_null; Ty_undefined; Ty_number; Ty_bytes;
    Ty_contextOf [{ name = 1; service = 2 }]
  ] in
  List.iteri (fun i ty ->
    let tree = sexp_of_ty ty in
    check (Printf.sprintf "generated_ty_%02d_sexp_roundtrip" i)
      (ty_of_sexp tree = ty);
    let bytes = Eff_wire.encode_ty ty in
    check (Printf.sprintf "generated_ty_%02d_wire_roundtrip" i)
      (Eff_wire.decode_ty_exact bytes = Some ty)) tys;
  Printf.printf "MEASURE generated_ty_cases=%d\n" (List.length tys);
  let program = Eff_bind (Eff_succeed (Term_lit (Lit_nat 7)),
    Eff_succeed (Term_record ([("value", (false, Ty_nat))], ["value"],
      Terms_cons (Term_var 0, Terms_nil)))) in
  let sx = sexp_of_eff sexp_of_native_op program in
  check "generated_eff_sexp_roundtrip" (eff_of_sexp native_op_of_sexp sx = program);
  let bytes = Eff_wire.encode_eff program in
  check "generated_eff_wire_roundtrip"
    (Eff_wire.decode_eff_exact bytes = Some program);
  Printf.printf "OBS generated_eff=%s\n" (show sx);
  let invalid_nat = lit_of_sexp (sexp "(Lit_nat -1)") in
  check "raw_sexp_accepts_negative_natural" (invalid_nat = Lit_nat (-1));
  check "wire_refuses_negative_natural" (raises (fun () -> Eff_wire.encode_lit invalid_nat));
  let bad_utf8 = Lit_str "\255" in
  check "raw_sexp_keeps_invalid_utf8_bytes"
    (lit_of_sexp (sexp_of_lit bad_utf8) = bad_utf8);
  check "wire_refuses_invalid_utf8" (raises (fun () -> Eff_wire.encode_lit bad_utf8));
  check "raw_sexp_accepts_hex_int"
    (lit_of_sexp (sexp "(Lit_nat 0x2a)") = Lit_nat 42);
  check "writer_normalizes_hex_int"
    (show (sexp_of_lit (lit_of_sexp (sexp "(Lit_nat 0x2a)"))) = "(Lit_nat 42)");
  let reverse = sexp "((service 2)(name 1))" in
  let canonical = sexp_of_service_key (service_key_of_sexp reverse) in
  check "record_decoder_accepts_reordered_fields" (service_key_of_sexp reverse = {name=1;service=2});
  check "record_writer_changes_field_order" (canonical <> reverse);
  Printf.printf "OBS record_normalization=%s -> %s\n" (show reverse) (show canonical);
  check "record_duplicate_refused"
    (raises (fun () -> service_key_of_sexp (sexp "((name 1)(name 2)(service 3))")));
  check "record_extra_field_refused"
    (raises (fun () -> service_key_of_sexp (sexp "((name 1)(service 2)(extra 3))")));
  check "record_missing_field_refused"
    (raises (fun () -> service_key_of_sexp (sexp "((name 1))")));
  check "raw_ty_union_order_retained"
    (ty_of_sexp (sexp_of_ty (Ty_union (Ty_nat, Ty_int))) = Ty_union (Ty_nat, Ty_int));
  check "raw_ty_optional_field_retained"
    (ty_of_sexp (sexp_of_ty (Ty_record [("x", (true, Ty_nat))])) =
      Ty_record [("x", (true, Ty_nat))]);
  let above_native = Z.succ (Z.of_int max_int) in
  check "native_int_converter_refuses_large_natural"
    (raises (fun () -> lit_of_sexp (Sexplib.Sexp.List [Atom "Lit_nat"; Atom (Z.to_string above_native)])));
  let huge = "18446744073709551616000000000000000000" in
  let exact = Option.get (Nat.of_decimal huge) in
  check "abstract_nat_decimal_roundtrip" (Nat.to_decimal exact = huge);
  List.iter (fun raw -> check ("canonical_nat_refuses_" ^ raw) (Nat.of_decimal raw = None))
    [""; "-1"; "+1"; "01"; "0x10"; " 1"];
  let huge_clock = E4_clock.literal huge in
  check "exact_clock_refuses_bounded_observation"
    (raises (fun () -> E4_clock.to_profile_nat huge_clock));
  check "exact_clock_value_survives_refusal" (E4_clock.to_decimal huge_clock = huge);
  let cap_a = { label = "file"; resource = Capability.make 1 } in
  let cap_b = { label = "file"; resource = Capability.make 2 } in
  check "opaque_serialization_loses_identity"
    (sexp_of_capability_view cap_a = sexp_of_capability_view cap_b);
  check "opaque_serialization_cannot_reconstruct_resource"
    (raises (fun () -> capability_view_of_sexp (sexp_of_capability_view cap_a)));
  let nan1 = Int64.float_of_bits 0x7ff8000000000001L in
  let nan2 = Int64.float_of_bits 0x7ff8000000000002L in
  check "float_sexp_loses_nan_payload"
    (sexp_of_float nan1 = sexp_of_float nan2);
  Printf.printf "OBS nan_input_bits=%Lx,%Lx sexp=%s decoded_bits=%Lx\n"
    (Int64.bits_of_float nan1) (Int64.bits_of_float nan2)
    (show (sexp_of_float nan1)) (Int64.bits_of_float (float_of_sexp (sexp_of_float nan1)));
  let trials = 256 in
  let config = { Base_quickcheck.Test.default_config with
    seed = Deterministic "effect4-conversions-2026-10-15"; test_count = trials } in
  let samples = ref 0 in
  Base_quickcheck.Test.run_exn ~config (module Payload) ~f:(fun p ->
    incr samples;
    assert (Payload.compare p (Payload.t_of_sexp (Payload.sexp_of_t p)) = 0));
  check "derived_quickcheck_roundtrips" (!samples = trials);
  Printf.printf "MEASURE quickcheck_roundtrips=%d\n" !samples;
  let mutation = Base_quickcheck.Test.result ~config
    ~examples:[{Payload.count=1;note=Some "retained";flags=[]}]
    (module Payload) ~f:(fun p ->
      let read = Payload.t_of_sexp (Payload.sexp_of_t p) in
      if Payload.compare p {read with note=None} = 0 then Ok () else Error "note discarded") in
  check "quickcheck_detects_lossy_mutation"
    (match mutation with Error _ -> true | Ok () -> false);
  (match mutation with
   | Error (p, why) -> Printf.printf "OBS mutation_counterexample=%s reason=%s\n"
       (show (Payload.sexp_of_t p)) why
   | Ok () -> assert false);
  Printf.printf "MEASURE passed=%d\n%!" !passed
