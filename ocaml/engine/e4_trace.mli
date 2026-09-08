(* E4_trace — the machine's event log: a persistent chunked vector, appended per step and
   read along its own index (docs/research/2026-09-08-engine-a1-state.md §4.3, field F1 of
   §1.2; lane Q3's proposal N2).

   What it is: the OCaml half of the probe's fix D4(b) (2026-09-07-probe-stores-performance
   §1.5, §7 P2), done in OCaml only so that no Lean proof moves.  `RunMachine.emit` already
   guards the empty list on the Lean side (src/Effect4/Machine/Fibers.lean:585-587,
   direction L4: `trace := if events.isEmpty then m.trace else m.trace ++ events`); this
   module removes the O(T) copy from the NON-empty case too, which is the Θ(steps²) term
   A1 §6.1 measured (bytes/step linear in n on W2, 14 812 -> 60 233 words from n=100 to
   n=1000).

   `emit` is called 32 times in Fibers.lean, always on the innermost step (finishFrame,
   :1123), usually with []; `trace` is WRITTEN by exactly two functions (emit :587 and
   empty :621) and READ by exactly one (Api.Run.trace, Api.lean:185-186), which is outside
   api_run's closure.  So the substitution is licensed by inspection, not by an argument.

   This module satisfies the generated functor's `TRACE` signature (A1 §1.5) verbatim;
   `e4_trace_list.ml` is its list twin and satisfies the same signature.  Both ascriptions
   are checked at compile time in test/prop_trace.ml.

   Depends on: E4_log (same library) and the OCaml standard library only.

   Representation: `'e E4_log.Vec.t` — 256-row frozen arrays under a `Map` from chunk number,
   plus the open tail (e4_log.ml).  It WAS `{ rev : the events, most recent first; n }`, a
   reversed accumulator; lane Q3's N2 replaced it because `nth_opt i` cost O(T - i) there and
   a viewer walking the reading axis (2026-09-08-design-language.md §3) therefore cost
   Theta(T^2).  The length is still maintained incrementally, so `length` is O(1) — TR4
   states this, and the alternative (walking the carrier) would put an O(T) call on a
   per-step path that A3's trace index uses.

   Behaviours (each is a named PASS/FAIL line in test/prop_trace.ml):
   TR1 to_list (emit evs t) = to_list t @ evs                              tested
   TR2 emit [] t == t  (PHYSICALLY equal; no allocation, no copy)          tested
   TR3 emit is O(length evs) AMORTISED — one cons per event, plus one 256-element array and
       one Map insertion every 256 events — and never walks t; to_list is O(length t) (one
       Vec.fold, no map lookup per row) and is called at most once per run
                                                              by construction; benched
   TR4 length t = List.length (to_list t), maintained incrementally, O(1)   tested
   TR5 persistence: `t` is unchanged by any emit on it                      tested
   TR6 the reversal is stable: to_list is List.rev of the accumulator, so equal event
       sequences give equal lists                                           tested
   TR7 nth_opt i t = List.nth_opt (to_list t) i, and None outside 0 .. length t - 1.
       O(log (length t / 256)) and it does NOT build the list               tested
   TR8 agreement with the list twin on random emit sequences                tested
   Bound: the trace is unbounded in Lean; on this host it is bounded by the heap, and
   `length` is a host int (E4_nat.max_nat). *)

type 'e t

val empty : 'e t

val emit : 'e list -> 'e t -> 'e t
(** Append, in order.  [emit [] t] returns [t] ITSELF (TR2). *)

val to_list : 'e t -> 'e list
(** The trace in emission order.  One fold and one reversal; call it once per run (TR3). *)

val length : 'e t -> int
(** O(1) (TR4). *)

val is_empty : 'e t -> bool

val nth_opt : int -> 'e t -> 'e option
(** Row [i] of the finished trace, for A3's trace index (2026-09-08-design-language.md §3:
    the reading axis is the trace index).  O(log (length t / 256)): the substitution the old
    text promised ("A3 may substitute a finger tree behind this signature without touching
    the engine") has been made, and the substitute is A3's own `E4_log.Vec`.  It is
    deliberately the only random-access operation, so that A3 needs no second seam. *)
