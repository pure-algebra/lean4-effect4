(** Exact logical milliseconds, the target of Effect4.ClockMillis, and the refusal of a value at
    a named crossing.
    Depends on Zarith. Properties: nonnegative immutable values and exact addition/multiplication/order
    [by construction]; canonical decimal transport and checked numeric observation
    [tested in test_clock]; each refusal names its crossing [tested in test_clock]. This module
    does not read a physical clock or mutate a timer. *)
type t

(** Where a value is refused: the receipt's crossings ([OCaml5.Lcnf.Crossing],
    [src/OCaml5/Lcnf/TypeRows.lean]). A program's literals and a host's answer are no crossing
    here: Lean's profile support judges them at ingress ([Effect4.Program.ProfileData], lowered;
    E4_engine's [ingress] and [literal_refusal]). *)
type crossing =
  | Arithmetic (** an arithmetic result, against the program's profile (DI-56) *)
  | Clock (** a clock reading taken as a natural, or a natural taken as a clock *)
  | Index (** a length, an index or an index-sized word past the target's capacity *)
  | Panic (** the program's own [panic] *)

(** One refusal: the crossing whose check refused, and what it refused. *)
type refusal =
  { crossing : crossing
  ; reason : string
  }

(** Outside the target scalar profile (DI-56) or the target's capacity, never a program failure
    or a clock value. *)
exception Profile_refusal of refusal

(** The crossing's name, as the receipt spells it: ["arithmetic"], ["clock"], ["index"] or
    ["panic"]. *)
val crossing_name : crossing -> string

(** ["<crossing>: <reason>"], the text an answer that reports the refusal carries. *)
val refusal_text : refusal -> string

(** [refuse crossing reason] raises [Profile_refusal { crossing; reason }]. *)
val refuse : crossing -> string -> 'a

val zero : t
val positive : int -> t

(** A natural taken as a clock: refused at [Clock] when negative. *)
val of_nat : int -> t

(** A clock reading taken as a natural: refused at [Clock] outside the program's profile. *)
val to_profile_nat : t -> int

(** [Effect4.Program.Profile.grow]: the exact sum, refused at [Arithmetic] outside the program's
    profile. *)
val profile_add : int -> int -> int

(** [Effect4.Program.Profile.scale]: the exact product, refused at [Arithmetic] outside the
    program's profile. *)
val profile_mul : int -> int -> int

val add : t -> t -> t
val mul : t -> t -> t
val equal : t -> t -> bool
val le : t -> t -> bool
val lt : t -> t -> bool
val of_decimal : string -> t option

(** A generated clock literal. The translator writes canonical decimal, so any other text is a
    programming error: [Invalid_argument]. *)
val literal : string -> t

val to_decimal : t -> string
