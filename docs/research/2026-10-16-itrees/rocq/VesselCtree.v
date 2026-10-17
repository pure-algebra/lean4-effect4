(** * VesselCtree: a mock FMI host refines the FMI host's specification (choice trees)

    The FMI host is real code ([ocaml/vessel/fmi/], an OpenModelica FMU through C stubs). No
    proof reaches it. What a proof can say is relative to a specification: a host whose every
    reply is admissible. An interaction tree has one continuation per answer and no internal
    choice, so "any admissible reply" needs a choice tree (Chappe et al., Choice Trees). Here the
    specification host branches ([Br]) over every admissible reply and every failure; a mock host
    answers one reply; and [mock_refines_spec] states, for every program over the two services,
    that the run under the mock is strongly simulated ([≲], [ssim]) by the run under the
    specification. So every run a test against the mock shows is a run the specification
    allows; and a real host that meets the specification (an assumption, never proved here) has
    its runs among the specification's too.

    The hosts and the one-event lemma are in [VesselCtreeHost.v], checked with universe checking
    on. This file lifts them to every program by ctrees' [ssim_interp_h]. Its module
    [Interp.FoldStateT] is compiled by ctrees with [Unset Universe Checking], and loading it with
    universe checking on is refused as a universe inconsistency (the receipt's control). So this
    file turns universe checking off, and its theorem holds only modulo universe consistency.

    Built in the opam switch [ctree] (Coq 8.20.1, coq-ctree 2.0, coq-itree 5.2.1); ctrees 2.0
    needs Coq 8.20. *)

Unset Universe Minimization ToSet.
(* Needed to load Interp.FoldStateT, which ctrees builds with universe checking off. *)
Unset Universe Checking.

From Coq Require Import NArith String.
From ITree Require Import Basics.Basics Indexed.Sum.
From CTree Require Import CTree Eq Interp.Fold Interp.FoldCTree Interp.FoldStateT.
Require Import E4.VesselTypes E4.VesselCtreeHost.

(** **The mock refines the specification, for every program**: whatever program over the two
    services, its run under the mock host is strongly simulated by its run under the
    specification host. *)
Theorem mock_refines_spec (geo : step_host) {C X} `{C -< chooseB} (t : ctree VE C X) :
  interp (mock_host geo) t (≲eq) interp (spec_host geo) t.
Proof.
  apply ssim_interp_h.
  - split; reflexivity.
  - intros Z e. apply mock_answers_within_spec.
Qed.
