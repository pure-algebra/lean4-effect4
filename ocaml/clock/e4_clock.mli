(** Exact logical milliseconds, the target of Effect4.ClockMillis.
    Depends on Zarith. Properties: nonnegative immutable values and exact addition/order
    [by construction]; canonical decimal transport and checked numeric observation
    [tested in test_clock]. This module does not read a physical clock or mutate a timer. *)
type t

exception Profile_refusal of string
(** Outside the target scalar profile (DI-56), never a program failure or a clock value. *)

val zero : t
val positive : int -> t
val of_nat : int -> t
val to_profile_nat : t -> int
val add : t -> t -> t
val equal : t -> t -> bool
val le : t -> t -> bool
val lt : t -> t -> bool
val of_decimal : string -> t option
val literal : string -> t
val to_decimal : t -> string
