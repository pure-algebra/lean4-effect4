(* Thin driver for Lcnf_interface. Dependencies: its library and the standard library.
   Properties: library refusals exit nonzero; output is written only after inference succeeds;
   a sixth argument, "reachable", keeps only the types the exported values name (a consumer's
   facade). Tested by test_interface and scripts/lib/lcnf_interfaces.py's staging controls. *)

let split text =
  String.split_on_char ',' text |> List.filter (fun x -> not (String.equal x ""))
;;

let infer ~types cmt output roots abstract_types prelude =
  match
    Lcnf_interface.generate
      ~types
      ~cmt
      ~roots:(split roots)
      ~abstract_types:(split abstract_types)
      ~prelude:(if String.equal prelude "" then None else Some prelude)
  with
  | Error why ->
    prerr_endline (Lcnf_interface.message why);
    exit 1
  | Ok text ->
    let channel = open_out output in
    Fun.protect
      ~finally:(fun () -> close_out channel)
      (fun () -> output_string channel text)
;;

let () =
  let arguments = Array.to_list Sys.argv |> List.tl in
  match arguments with
  | [ cmt; output; roots; abstract_types; prelude ] ->
    infer ~types:Lcnf_interface.All cmt output roots abstract_types prelude
  | [ cmt; output; roots; abstract_types; prelude; "reachable" ] ->
    infer ~types:Lcnf_interface.Reachable cmt output roots abstract_types prelude
  | _ ->
    prerr_endline "usage: main CMT OUTPUT ROOTS ABSTRACT_TYPES PRELUDE [reachable]";
    exit 2
;;
