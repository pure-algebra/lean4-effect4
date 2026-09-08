(* e4_admit.mli — the admission predicate, consulted before popping.
   Borrow: Hack's serverMain, which computes the admissible client kind from server state
   BEFORE selecting (survey #23). Our fuel budget is the safe point and a frontier is Cancel;
   what we lacked was the admission rule -- today we accept every decision until a mailbox is
   full.
   Properties:
     A1  A pure function of the saved host state. No clock, no randomness, no atomic hint.
         [by construction; tested: admit-pure]
     A2  Monotone in room: more room never admits less. [tested: admit-monotone] *)

type t = Any | Priority_only | None_now

val of_state : mailbox_len:int -> mailbox_bound:int -> in_flight:int -> t
val admits : t -> priority:bool -> bool
