(* Installed Jane Street mechanisms at an adapter boundary.
   Depends on Core.Univ_map, Typerep, PPX derivations and Bin_prot.
   Properties: finite positive and negative controls print named results [tested].
   No new program representation, external effect, FFI, or production code. *)
open Base
open Bin_prot.Std
open Typerep_lib.Std

let passed = ref 0
let check name holds =
  if not holds then failwith name;
  Int.incr passed;
  Stdlib.Printf.printf "PASS %s\n%!" name

module Request = struct
  type t = { count : int; message : string }
  [@@deriving sexp, sexp_grammar, compare, hash, bin_io, typerep]
  let type_id = Base.Type_equal.Id.create ~name:"request" sexp_of_t
end

module Renamed = struct
  type t = { count : int; label : string } [@@deriving bin_io, typerep]
end

module Same_fields = struct
  type t = { count : int; message : string } [@@deriving typerep]
end

module Request_alias = struct
  type t = Request.t [@@deriving bin_io, typerep]
end

(* A representation re-export keeps the actual generated carrier's type identity.
   Derivations live in this adapter module, outside the minimal generated module. *)
module Service_key_view = struct
  type t = Eff_types.service_key = { name : int; service : int }
  [@@deriving sexp, sexp_grammar, compare, hash, bin_io, typerep]
end

module Asc = struct
  type t = int [@@deriving sexp_of, compare]
  include Comparator.Make (struct type nonrec t = t let compare = compare let sexp_of_t = sexp_of_t end)
end

module Desc = struct
  type t = int [@@deriving sexp_of]
  let compare a b = Int.compare b a
  include Comparator.Make (struct type nonrec t = t let compare = compare let sexp_of_t = sexp_of_t end)
end

(* A conventional first-class module closes over a carrier and its operations.
   This is a binary adapter contract, not a definition of program semantics. *)
module type PAYLOAD = sig
  type t
  val type_id : t Base.Type_equal.Id.t
  val sexp_of_t : t -> Sexp.t
  val bin_writer_t : t Bin_prot.Type_class.writer
  val bin_reader_t : t Bin_prot.Type_class.reader
end

let inspect_binary (type a) (module M : PAYLOAD with type t = a) (value : a) =
  let bytes = Bin_prot.Utils.bin_dump M.bin_writer_t value in
  let pos_ref = ref 0 in
  let decoded = M.bin_reader_t.read bytes ~pos_ref in
  M.sexp_of_t decoded, !pos_ref = Bigarray.Array1.dim bytes

let record_fields (type a) (repr : a Typerep.t) =
  match Typerep.head repr with
  | Typerep.Record record ->
    Typerep.Record.fold record ~init:[] ~f:(fun acc (Typerep.Record.Field f) ->
      Typerep.Field.label f :: acc) |> List.rev
  | _ -> []

let count_field (type a) (repr : a Typerep.t) (value : a) : int option =
  match Typerep.head repr with
  | Typerep.Record record ->
    Typerep.Record.fold record ~init:(None : int option) ~f:(fun answer (Typerep.Record.Field f) ->
      if String.equal (Typerep.Field.label f) "count" then
        match Typerep.head (Typerep.Field.traverse f) with
        | Typerep.Int -> Some (Typerep.Field.get f value)
        | _ -> answer
      else answer)
  | _ -> None

let () =
  let original : Eff_types.service_key = {name=11;service=22} in
  let view : Service_key_view.t = original in
  check "ppx_reexport_is_the_existing_generated_type"
    (Service_key_view.compare original view = 0);
  let restored : Eff_types.service_key = Service_key_view.t_of_sexp (Service_key_view.sexp_of_t original) in
  check "ppx_reexport_converters_return_existing_generated_type"
    (Int.equal restored.name 11 && Int.equal restored.service 22);
  let request = { Request.count = 42; message = "hello" } in
  let text_id = Base.Type_equal.Id.create ~name:"request" String.sexp_of_t in
  let recreated_id = Base.Type_equal.Id.create ~name:"request" Request.sexp_of_t in
  let map = Core.Univ_map.set Core.Univ_map.empty ~key:Request.type_id ~data:request in
  check "univ_map_recovers_same_typed_key"
    (Option.value_map (Core.Univ_map.find map Request.type_id) ~default:false
      ~f:(fun r -> Request.compare request r = 0));
  check "univ_map_rejects_same_text_wrong_type" (Option.is_none (Core.Univ_map.find map text_id));
  check "univ_map_rejects_recreated_same_type_key" (Option.is_none (Core.Univ_map.find map recreated_id));
  check "univ_map_detects_duplicate"
    (match Core.Univ_map.add map ~key:Request.type_id ~data:request with `Duplicate -> true | `Ok _ -> false);
  check "type_id_same_key_witness"
    (Option.is_some (Base.Type_equal.Id.same_witness Request.type_id Request.type_id));
  check "type_id_different_key_no_witness"
    (Option.is_none (Base.Type_equal.Id.same_witness Request.type_id text_id));
  let observed, filled = inspect_binary (module Request) request in
  check "first_class_module_keeps_matching_carrier_and_operations"
    (Sexp.equal observed (Request.sexp_of_t request) && filled);
  check "typerep_reflects_record_fields"
    (List.equal String.equal (record_fields Request.typerep_of_t) ["count";"message"]);
  check "typerep_typed_field_accessor" (Option.equal Int.equal (count_field Request.typerep_of_t request) (Some 42));
  check "typerep_wrong_shape_has_no_count" (Option.is_none (count_field typerep_of_string "hello"));
  check "typerep_alias_has_same_type" (Typerep.same Request.typerep_of_t Request_alias.typerep_of_t);
  check "typerep_same_record_shape_is_not_same_type"
    (not (Typerep.same Request.typerep_of_t Same_fields.typerep_of_t));
  let digest_a = Bin_prot.Shape.eval_to_digest_string Request.bin_shape_t in
  let digest_alias = Bin_prot.Shape.eval_to_digest_string Request_alias.bin_shape_t in
  let digest_renamed = Bin_prot.Shape.eval_to_digest_string Renamed.bin_shape_t in
  check "bin_shape_alias_same_digest" (String.equal digest_a digest_alias);
  check "bin_shape_detects_field_rename" (not (String.equal digest_a digest_renamed));
  let bytes = Bin_prot.Utils.bin_dump Request.bin_writer_t request in
  let pos_ref = ref 0 in
  let renamed = Renamed.bin_read_t bytes ~pos_ref in
  check "bin_bytes_alone_do_not_enforce_shape"
    (Int.equal renamed.count 42 && String.equal renamed.label "hello");
  Stdlib.Printf.printf "OBS shape_request=%s shape_alias=%s shape_renamed=%s\n" digest_a digest_alias digest_renamed;
  let negative = {Request.count = -1; message = "not a natural"} in
  let negative_bytes = Bin_prot.Utils.bin_dump Request.bin_writer_t negative in
  let decoded_negative = Request.bin_read_t negative_bytes ~pos_ref:(ref 0) in
  check "bin_io_does_not_admit_program_natural" (Int.equal decoded_negative.count (-1));
  let grammar : int Sexplib0.Sexp_grammar.t = [%sexp_grammar: int] in
  check "sexp_integer_grammar_has_no_native_bit_bound"
    (match grammar.untyped with Sexplib0.Sexp_grammar.Integer -> true | _ -> false);
  let huge = Sexp.Atom "18446744073709551616" in
  check "sexp_int_converter_still_refuses_overflow"
    (Result.is_error (Result.try_with (fun () -> Int.t_of_sexp huge)));
  check "compare_generated_on_concrete_record" (Request.compare request request = 0);
  check "hash_agrees_after_alias_roundtrip"
    (Int.equal (Request.hash request) (Request.hash (Request.t_of_sexp (Request.sexp_of_t request))));
  let asc = Set.of_list (module Asc) [3;1;2] in
  let desc = Set.of_list (module Desc) [3;1;2] in
  check "comparator_witness_selects_ascending_order" (List.equal Int.equal (Set.to_list asc) [1;2;3]);
  check "comparator_witness_selects_descending_order" (List.equal Int.equal (Set.to_list desc) [3;2;1]);
  Stdlib.Printf.printf "MEASURE ecosystem_passed=%d\n%!" !passed
