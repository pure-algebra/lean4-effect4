(* E4_nat — Lean's `Nat` on a 63-bit host, exactly as ocaml/gen/NOTES.md §5 states it.

   What it is: the arithmetic profile the generated engine assumes, as a module, so that a
   hand extern (E4_shim) and the generated code cannot disagree about what `2 ^ 64` or
   `n / 0` means.  It is the SAME rule the LCNF backend inlines
   (src/OCaml5/Lcnf/Translate.lean:120-174), written once so it can be tested.

   Depends on: the OCaml standard library only.

   Behaviours:
   N1  Saturating, never wrapping: `pow`, `shift_left` and `of_lit` answer `max_int` rather
       than a wrapped value, so `Effect4.Store.Val.wf`'s `… < 2 ^ 64` (src/Effect4/Store/
       Val.lean:279-316) reads as `… < max_int` and keeps the meaning it has in Lean.
                                                                   by construction; tested
   N2  Lean's division: `div n 0 = 0` and `rem n 0 = n` (Lean v4.33.1 core; consolidation
       review R6).  OCaml's `/` and `mod` raise Division_by_zero — this is the ONE place the
       generated code is wrong today (NOTES.md:263 "still not guarded").          tested
   N3  Truncated subtraction: `sub a b = max 0 (a - b)`.                by construction
   N4  Host width: `bits` is Sys.int_size (63 native, 32 under js_of_ocaml, 31 under
       wasm_of_ocaml — ocaml/wasm/README.md:13); `max_nat` is `max_int`; `wire_limit` is the
       bound at which ocaml/eff/eff_frame.ml refuses a natural — see D1 below.
                                                                       by construction; tested
   N5  Guarded shifts: OCaml's `lsl`/`lsr` are undefined at >= 63; `shift_right` answers 0
       at or above `bits`, `shift_left` saturates.                     by construction; tested
   N6  Every operation is total: no exception escapes any function of this module.  tested
   N7  `pow` agrees with `Translate.powClamped` (Translate.lean:127-137) value for value:
       both are `f^b (1)` for `f r = if a = 0 then 0 else if r > max_int / a then max_int
       else r * a`.  This module iterates and exits at the fixed point instead of recursing
       `b` times, which is why `pow 2 (10^9)` terminates here.        tested (differential)
   Bound: Lean's Nat is unbounded.  A program whose payload is longer than max_int bytes
   cannot exist on this host, which is why saturating is sound here and wrapping is not
   (NOTES.md §5).

   Deviations from docs/research/2026-09-08-engine-a1-state.md §3.1 (lane M, 2026-09-08):
   D1  `wire_limit` is the INCLUSIVE bound `max_nat`, not the exclusive `2 ^ 62` the design
       names.  On a 63-bit host `max_int = 2 ^ 62 - 1`, so `2 ^ 62` is not an OCaml int at
       all and no `val wire_limit : t` can hold it.  `fits_wire` is added as the predicate
       the design asked for ("the refusal predicate for naturals >= 2^62 at the wire"):
       `fits_wire n = 0 <= n && n <= max_nat`, whose complement is exactly what
       eff_frame.decode_nat refuses (nine digits, or eight with a top byte >= 0x40).
   D2  `of_lit_decimal` is added.  `of_lit : int -> t` cannot see an out-of-range literal,
       because an OCaml int is already in range; the clamp of
       Translate.letValueExpr sees the literal as an arbitrary-precision Lean `Nat`, and a
       decimal string is that literal.  `of_lit` is kept for the in-range case.
   D3  `add`, `mul` and `shift_left` saturate here; the generator emits raw `+` and `*` for
       `Nat.add`/`Nat.mul` and `a * powClamped 2 b` for `Nat.shiftLeft` (Translate.lean:
       148, 166), which wrap.  Saturating is N1's rule applied to the same operations; the
       two agree on every input that does not overflow, and no corpus input overflows them. *)

type t = int
(** A Lean `Nat` on this host: 0 .. max_nat.  Negative values are outside the image and
    every constructor of this module refuses to produce one. *)

val bits : int
(** Sys.int_size: 63 native, 32 jsoo, 31 wasm. *)

val max_nat : t
(** max_int. *)

val wire_limit : t
(** max_nat: the LARGEST natural the canonical wire carries (D1).  The first natural it
    refuses is [max_nat + 1] = 2^62, which is not representable here. *)

val of_lit : int -> t
(** A Lean literal already in the host's range: the identity on 0 .. max_nat, and max_nat on
    a negative int (the only shape an overflowed literal can have). *)

val of_lit_decimal : string -> t option
(** A Lean literal as decimal digits: >= 2^62 saturates to max_nat, matching
    Translate.letValueExpr (src/OCaml5/Lcnf/Translate.lean:429).  None on an empty string or
    any character outside '0'..'9'. *)

val add : t -> t -> t          (* saturating *)
val sub : t -> t -> t          (* truncated: max 0 (a - b) *)
val mul : t -> t -> t          (* saturating *)
val div : t -> t -> t          (* Lean: div n 0 = 0 *)
val rem : t -> t -> t          (* Lean: rem n 0 = n *)
val pow : t -> t -> t          (* saturating at max_nat; Translate.powClamped's value *)
val succ : t -> t
val pred : t -> t              (* max 0 (n - 1) *)

val shift_left : t -> t -> t   (* a * 2^b, saturating *)
val shift_right : t -> t -> t  (* a lsr b, 0 when b >= bits *)
val land_ : t -> t -> t
val lor_ : t -> t -> t
val lxor_ : t -> t -> t

val is_nat : int -> bool       (* 0 <= n <= max_nat *)

val fits_wire : t -> bool
(** The naturals ocaml/eff/eff_frame.ml's decode_nat accepts: 0 .. max_nat (D1). *)

val saturates : t -> t -> bool
(** [saturates a b] is true when [mul a b] would exceed max_nat: the predicate the
    differential uses to skip inputs on which host and Lean legitimately differ. *)

val pow_reference : t -> t -> t
(** Translate.powClamped transcribed literally (recursive, no fixed-point exit), for the N7
    differential only.  Recurses [b] times: do not call it with a large [b]. *)
