(* Eff_codec — a program's canonical bytes, by Lean's own definition (hand-written).

   What it is: `Canonical.encode` and `Canonical.decode` (src/Effect4/Store/Domain/Canonical.lean)
   at the carriers this library reads and writes as bytes: a program (`Wire.encodeProgram`,
   `Wire.decodeProgram`, src/Effect4/Store/Domain/ProgramWire.lean), a row table, a program type
   and each node sort of a program. A carrier's bytes are `Val.encode` of its value tree. The tree
   is Lean's exact embedding (`Canonical.toVal`, `Canonical.ofVal`), lowered into Eff_image
   (GENERATED, ocaml/gen/roots.json), and the frames are the one framing kernel's (Eff_val over
   Eff_frame). This module composes the two and decides nothing of its own.
   Depends on: Eff_types, Eff_image (GENERATED), Eff_subterm (GENERATED), Eff_val.

   Behaviours it holds itself to:
   C1  Encoding is Lean's: `encode_program p` is the frames of `programToVal p`, which are
       `Wire.encodeProgram p`'s bytes wherever Eff_val writes Lean's frames (Eff_val V1).
                                 by construction; tested (test_lean_wire L3, prop_wire P1)
   C2  Decoding is Lean's exact reading: the whole string is one value tree (Eff_val.decode_exact)
       and the tree is a program's image (`programOfVal`, which re-encodes what it read and
       compares). Trailing bytes, a frame no program carries (raw bytes, a reference, a handle,
       a float) and a tree that is no program's image are refusals, never repairs.
                                 by construction; tested (test_eff, prop_wire P2 P3,
                                 test_val_frames V4)
   C3  The domain is Lean's image. A value outside it either raises Invalid_argument at encoding
       (a negative natural, a string that is not UTF-8: Eff_frame F4) or encodes to bytes that
       `decode_program` refuses: a requirement row out of order, whose order Lean's row type
       carries and the OCaml list does not.            by construction; tested (test_eff)
   C4  A node's bytes are the frames of its sort's image (`Run.Kit.stmtsToVal` to `layersToVal`,
       and `programToVal` for a program), the sub-tree its parent's image holds at its argument.
                                 by construction; tested (test_cache S1, S2)
   C5  No bound: the framing kernel reads every natural exactly (Eff_frame F2, Zarith's `Z.t`
       since M4), as Lean reads it. Until M4 a natural above 2^62 - 1 was refused at decoding.
                                                                      by construction *)

open Eff_types

type program = NativeOp.t Eff.t

let encode_program (p : program) : string =
  Eff_val.to_bytes (Eff_image.run_kit_program_to_val p)
;;

let decode_program (s : string) : program option =
  Option.bind (Eff_val.decode_exact s) Eff_image.run_kit_program_of_val
;;

(* Each row's tree, in order, or the first that does not read; the table is Lean's reading of
   their list. *)
let decode_rows (rows : string list) : Row.t list option =
  let rec trees acc = function
    | [] -> Some (List.rev acc)
    | bytes :: rest ->
      (match Eff_val.decode_exact bytes with
       | None -> None
       | Some v -> trees (v :: acc) rest)
  in
  Option.bind (trees [] rows) (fun vs -> Eff_image.run_kit_rows_of_val (Val.List vs))
;;

let decode_eff_ty (s : string) : EffTy.t option =
  Option.bind (Eff_val.decode_exact s) Eff_image.run_kit_eff_ty_of_val
;;

(* C4: one arm per node sort; a sort added to `Effect4.Program.Node` is a non-exhaustive match
   here until its image is lowered. *)
let encode_node (n : Eff_subterm.node) : string =
  Eff_val.to_bytes
    (match n with
     | Eff_subterm.N_eff v -> Eff_image.run_kit_program_to_val v
     | Eff_subterm.N_stmts v -> Eff_image.run_kit_stmts_to_val v
     | Eff_subterm.N_stmt v -> Eff_image.run_kit_stmt_to_val v
     | Eff_subterm.N_action v -> Eff_image.run_kit_action_to_val v
     | Eff_subterm.N_effs v -> Eff_image.run_kit_effs_to_val v
     | Eff_subterm.N_layer v -> Eff_image.run_kit_layer_to_val v
     | Eff_subterm.N_layers v -> Eff_image.run_kit_layers_to_val v)
;;
