(* Stm_support -- the runner the estate's qcheck-stm model tests share (plan E2).

   What it is: the seed, the repetition and the test constructors that every model test in this
   directory uses, so each test file states only its model, its system and its controls.
   Depends on: qcheck-core (QCheck, QCheck_base_runner).

   Behaviours:
   U1 Every run draws its command lists from one fixed seed, so the lists are reproducible; the
      interleavings of a parallel run are the host's, and are not.              by construction
   U2 A parallel test assumes its precondition in every interleaving before it runs a triple, as
      qcheck-stm's own parallel tests do.                                       by construction
   U3 A red control is a negative test: it holds only when QCheck finds a counterexample.
                                                                                 by construction *)

(** The generator seed of every model test in this directory. *)
val seed : int

(** [repeat n prop x] runs [prop x] [n] times and holds when every run holds: a parallel run is
    nondeterministic, so one triple is run [n] times. *)
val repeat : int -> ('a -> bool) -> 'a -> bool

(** [par_test ~neg ~name ~count ~repeats ~ok arb prop]: [count] triples from [arb], each assumed
    to satisfy [ok] (every precondition in every interleaving), each run [repeats] times under
    [prop]. With [neg], the test is a red control and must find a counterexample. [retries]
    (default 10) multiplies the runs of each candidate while QCheck shrinks a counterexample. *)
val par_test
  :  ?retries:int
  -> neg:bool
  -> name:string
  -> count:int
  -> repeats:int
  -> ok:('t -> bool)
  -> 't QCheck.arbitrary
  -> ('t -> bool)
  -> QCheck.Test.t

(** Runs the tests from {!seed} with a verbose report and no colours, then exits: 0 when every
    test held, 1 otherwise. *)
val run : QCheck.Test.t list -> 'a
