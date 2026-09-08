(* e4_trigger.mli — the one-shot cross-domain wake, as a three-state CAS.
   Borrow: Picos' `Trigger` (survey #9, §8.1), with the closure replaced by a mailbox address,
   so signalling is "enqueue a Resume row" and never "run user code". The CAS decides only WHO
   posts, never WHAT happens: the resume is a row on the tape, so this adds no off-tape choice.
   Without it, a foreign domain signalling twice posts a duplicate row and the tape diverges
   on replay.
   Properties (Picos states these as ERRORS, not best practice -- adopted verbatim):
     TR1 Once signaled it never changes state (signal is idempotent-or-error).
     TR2 Only the owner may await, and twice is an error.
     TR3 A signaled trigger holds no value: signaled triggers must not accumulate.
     TR4 The post runs with NEITHER effect NOR exception handlers installed and must return
         fast; `post` is `E4_mailbox.push`, which is bounded and refuses. *)

type addr = { machine : int; fiber : int; token : int }
type state = Initial | Awaiting of addr | Signaled
type t

val create : unit -> t
val state : t -> state
val await : t -> addr -> [ `Awaiting | `Already_signaled ]
val signal : t -> post:(addr -> unit) -> unit
val is_signaled : t -> bool
