(* Eff_codec — a program's canonical bytes, by Lean's own definition (hand-written); the
   behaviours C1-C5 are stated at the head of eff_codec.ml. *)

open Eff_types

(** The one program type: an `Eff` over the native alphabet. *)
type program = NativeOp.t Eff.t

(** A program's canonical bytes: `Wire.encodeProgram` (src/Effect4/Store/Domain/ProgramWire.lean),
    the frames of its value tree. @raise Invalid_argument on a value outside Lean's image that
    the frames refuse: a negative natural or a string that is not UTF-8 (C3). *)
val encode_program : program -> string

(** A program from its canonical bytes, exactly: `Wire.decodeProgram` (C2). *)
val decode_program : string -> program option

(** A row table from each row's canonical bytes: every row reads exactly, and the table reads as
    Lean's row table (`Run.Kit.rowsOfVal`). *)
val decode_rows : string list -> Row.t list option

(** A program type from its canonical bytes, exactly (`Run.Kit.effTyOfVal`). *)
val decode_eff_ty : string -> EffTy.t option

(** The canonical bytes of a node of the program, at its sort (`Effect4.Program.Node`): the frames
    of `Canonical.toVal` at that sort (C4). *)
val encode_node : Eff_subterm.node -> string
