(* E4_trace -- the machine event log over Lcnf_array.
   Source: RunMachine.emit (src/Effect4/Machine/Fibers.lean).
   Reader: Api.Inspection.trace (src/Effect4/Api.lean).
   Depends on: Lcnf_array, Zarith (Z) and the standard library.

   Properties, checked by test/prop_trace.ml:
   TR1 to_list (emit evs t) = to_list t @ evs.
   TR2 emit [] t returns t physically, without allocation.
   TR3 emit appends each event once. Conversion delegates to Lcnf_array.to_list.
   TR4 length t = List.length (to_list t); length reads the stored count.
   TR5 emit leaves every retained sibling unchanged.
   TR6 equal event sequences produce equal lists, in emission order.
   TR7 nth_opt i t = List.nth_opt (to_list t) i for nonnegative indices.
       Indices outside the carrier return None.
   TR8 random emission sequences agree with the list-backed reference.

   The host count is bounded by max_int and available memory; `length` answers it as a Lean
   natural, Zarith's `Z.t` (M4).
   Lcnf_array owns the transient-array capacity check and its list fallback. *)

type 'e t

val empty : 'e t

(** Append, in order.  [emit [] t] returns [t] ITSELF (TR2). *)
val emit : 'e list -> 'e t -> 'e t

(** The trace in emission order.  Conversion follows the carrier owner (TR3). *)
val to_list : 'e t -> 'e list

(** O(1) (TR4). *)
val length : 'e t -> Z.t

val is_empty : 'e t -> bool

(** Row [i] of the finished trace, for A3's trace index (2026-09-08-design-language.md §3:
    the reading axis is the trace index).  O(log (length t / 256)): the substitution the old
    text promised ("A3 may substitute a finger tree behind this signature without touching
    the engine") has been made, and the substitute is A3's own `Lcnf_array`.  It is
    deliberately the only random-access operation, so that A3 needs no second seam. *)
val nth_opt : int -> 'e t -> 'e option
