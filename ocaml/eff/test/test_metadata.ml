(* Selected metadata boundary: Lean bytes decode/re-encode exactly; hand JSON
   agrees; malformed framing and noncanonical requirement lists are refused. *)
let read path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in close_in ic; s
let unhex s = String.init (String.length s / 2)
  (fun i -> Char.chr (int_of_string ("0x" ^ String.sub s (2 * i) 2)))
let checks = ref 0
let check label ok = incr checks; if not ok then failwith label
let exercise name bytes expected decode encode print =
  match decode bytes with
  | None -> failwith (name ^ ": exact decoder refused Lean fixture")
  | Some value ->
    check (name ^ ": bytes") (encode value = bytes);
    check (name ^ ": JSON") (print value = expected);
    check (name ^ ": trailing") (decode (bytes ^ "\000") = None);
    check (name ^ ": truncated") (decode (String.sub bytes 0 (String.length bytes - 1)) = None);
    check (name ^ ": wrong tag") (decode ("\009" ^ String.sub bytes 1 (String.length bytes - 1)) = None)
let () =
  let open Eff_wire in
  let open Eff_json in
  let families = ref [] in
  read "../goldens/metadata.tsv" |> String.split_on_char '\n' |> List.iter (function
    | "" -> ()
    | line -> match String.split_on_char '\t' line with
      | [name; family; hex; json; _node] ->
        families := family :: !families;
        let bytes = unhex hex in
        (match family with
        | "Ty" -> exercise name bytes json decode_ty_exact encode_ty print_ty
        | "RowKind" -> exercise name bytes json decode_row_kind_exact encode_row_kind print_row_kind
        | "RowShape" -> exercise name bytes json decode_row_shape_exact encode_row_shape print_row_shape
        | "Registration" -> exercise name bytes json decode_registration_exact encode_registration print_registration
        | "Row" -> exercise name bytes json decode_row_exact encode_row print_row
        | "EffTy" -> exercise name bytes json decode_eff_ty_exact encode_eff_ty print_eff_ty
        | _ -> failwith ("unsupported metadata family " ^ family))
      | _ -> failwith "metadata TSV arity");
  check "all selected families exercised" (List.length (List.sort_uniq compare !families) = 6);
  let open Eff_types in
  let key n s = { service_key_name = { service_name_value = n };
    service_key_service = { service_type_code_value = s } } in
  let invalid xs =
    let value = { eff_ty_answer = Ty_nat; eff_ty_error = Ty_never; eff_ty_requires = xs } in
    let bytes = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b 0 (fun b ->
      emit_ty b value.eff_ty_answer; emit_ty b value.eff_ty_error;
      Eff_frame.emit_list b emit_service_key xs)) () in
    check "unordered requirements decoder" (decode_eff_ty_exact bytes = None);
    check "unordered requirements encoder" (try ignore (encode_eff_ty value); false with Invalid_argument _ -> true)
  in
  invalid [key 1 2; key 1 2]; invalid [key 2 0; key 1 3]; invalid [key 1 3; key 1 2];
  Printf.printf "metadata: %d checks passed\n" !checks
