(* Eff_val — a value's canonical frames and its equality (hand-written); the behaviours V1-V5
   are stated at the head of eff_val.ml. *)

(** The frames of `Val.encode` (src/Effect4/Store/Carrier/Val.lean). *)
val emit : Eff_frame.writer -> Eff_types.Val.t -> unit

(** A value's canonical bytes. *)
val to_bytes : Eff_types.Val.t -> string

(** The reader of the same frames: scalars, strings, lists, options, pairs, constructor
    applications and negative integers; every other frame refuses (V2). *)
val decode : Eff_types.Val.t Eff_frame.decoder

(** Exactly one value: trailing bytes are a refusal. *)
val decode_exact : string -> Eff_types.Val.t option

(** Structural equality, constructor by constructor (V5). *)
val equal : Eff_types.Val.t -> Eff_types.Val.t -> bool

(** Whether the value is the image of a Lean value (V6): every natural, negative integer's
    digits, constructor index, handle key and double's bits is nonnegative, every byte and kind
    is in 0..255, and every string is valid UTF-8. *)
val valid : Eff_types.Val.t -> bool
