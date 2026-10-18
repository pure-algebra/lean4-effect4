(* Eff_val — a value's canonical frames and its equality (hand-written); the behaviours V1-V5
   are stated at the head of eff_val.ml. *)

val emit : Eff_frame.writer -> Eff_types.Val.t -> unit
(** The frames of `Val.encode` (src/Effect4/Store/Carrier/Val.lean). *)

val to_bytes : Eff_types.Val.t -> string
(** A value's canonical bytes. *)

val decode : Eff_types.Val.t Eff_frame.decoder
(** The reader of the same frames: scalars, strings, lists, options, pairs, constructor
    applications and negative integers; every other frame refuses (V2). *)

val decode_exact : string -> Eff_types.Val.t option
(** Exactly one value: trailing bytes are a refusal. *)

val equal : Eff_types.Val.t -> Eff_types.Val.t -> bool
(** Structural equality, constructor by constructor (V5). *)
