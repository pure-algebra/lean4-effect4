(* Lcnf_crossing -- the refusal of a value at a named crossing, where LCNF-made code meets the
   target's capacity (decision D-2: exact, or refused at a named crossing).

   What it is: the crossings of `OCaml5.Lcnf.Crossing` (src/OCaml5/Lcnf/TypeRows.lean) at which a
   function of the runtime library refuses. `Nat`, `Int` and `UInt64` are exact over Zarith since
   M4, so two crossings remain: an exponent or a shift that the target's `int` does not hold
   (`Lcnf_nat.to_shift_exn`), and an index past the target's index capacity
   (`Lcnf_nat.to_index_exn`, `Lcnf_nat.index_add`, `Lcnf_nat.index_sub`). The program's own
   `panic` raises `Failure`, not this exception. A program's literals and a host's answer are no
   crossing here: Lean's profile support judges them at ingress (E4_engine's `ingress` and
   `literal_refusal`).

   Depends on: the standard library only.

   Properties:
   X1  `refuse c r` raises `Refused { crossing = c; reason = r }` and returns no value.
                                                                        tested (test_lcnf)
   X2  `refusal_text` is "<crossing>: <reason>", the crossing named as `OCaml5.Lcnf.Crossing`
       prints it ("arithmetic", "index").                               tested (test_lcnf)
   X3  A refusal holds no state: it is a value of `refusal`, read by its two fields.
                                                                        by construction *)

(** Where a value is refused. *)
type crossing =
  | Arithmetic (** an exponent or a shift past the target's [int] *)
  | Index
  (** a length, an index or an index-sized word past the target's index capacity *)

(** One refusal: the crossing whose check refused, and what it refused. *)
type refusal =
  { crossing : crossing
  ; reason : string
  }

(** A value outside the target's capacity at a crossing: never a program failure. *)
exception Refused of refusal

(** The crossing's name, as [OCaml5.Lcnf.Crossing] prints it: ["arithmetic"] or ["index"]. *)
val crossing_name : crossing -> string

(** ["<crossing>: <reason>"], the text an answer that reports the refusal carries. *)
val refusal_text : refusal -> string

(** [refuse crossing reason] raises [Refused { crossing; reason }]. *)
val refuse : crossing -> string -> 'a
