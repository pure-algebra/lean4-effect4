(* Corpora -- the programs the differential runs, from three sources, as data.

   What it is: build lane X of the engine team (docs/research/2026-09-08-engine-brief.md
   §2.1 "a differential is the evidence"; the corpus table of
   2026-09-08-engine-a1-state.md §6.3).  Every source is reduced to ONE shape --
   {!program}, an `Eff_wire.program` with a name and the corpus it came from -- so the
   engines can be driven through `E4_engine.ENGINE.compile` with no per-corpus code.  It is
   test machinery: it left the installed effect4_engine for the test library e4_reference on
   2026-10-18 (the hygiene lane's H3).

   The three sources, and what each is worth:

     goldens   ocaml/eff/goldens/*.bin -- 37 programs in the EXACT wire, decoded by
               `Eff_wire.decode_program_exact`.  27 well-typed and 10 `pIll*`; the
               ill-typed ones are part of the corpus because the machine's answer to
               them is also semantics.
     truth     ocaml/goldens/eff/*.hex -- 8 programs whose bytes were cut by LEAN's own
               `Program.Wire` (eff/README.md), i.e. the cross-face oracle, plus the two
               members of harness/truth/corpus.json that have a `.bin` under
               ocaml/eff/goldens and no `.hex` (pTwo, pAcquire).  The recorded
               `run`/`runSync` of harness/truth/corpus.json is read beside them
               ({!truth_expectations}) so the engines can be compared with the LEAN side
               and not only with each other.
     lean      {!lean_corpus} -- the printed corpus `make corpus` writes under
               `.lake/corpus` (tools/Drivers/Corpus.lean): 400 programs of Lean's seeded
               generator `Test.Program.Gen` plus the wire corpus, each as the canonical
               bytes `Wire.encodeProgram` cut, with Lean's own `Api.wellTyped` verdict
               beside it in `index.tsv`.  Since 2026-09-13 this replaces the OCaml
               generator that was built on the hand-written checker: the programs come
               from Lean as bytes, and the verdicts ride along as data.

   Each directory is found by an ancestor walk from the working directory; the variables
   E4_EFF_GOLDENS, E4_HEX_GOLDENS, E4_TRUTH_CORPUS and E4_LEAN_CORPUS name one instead.

   Depends on: effect4_eff (Eff_types, Eff_wire), yojson (corpus.json), stdlib.  Nothing in this
   module touches an engine: it is programs, not runs.

   Behaviours:
   X1  Nothing here derives a typing verdict: {!program.typed} is Lean's, read from
       `index.tsv`, or `None` where the source records none.              by construction
   X2  The Lean corpus is deterministic: `Test.Program.Gen.program i depth` is a pure
       function of `i`, so `make corpus` writes one program list.          by construction
   X3  Loading is total and lossless: a `.bin`/`.hex`/`.eff` that
       `Eff_wire.decode_program_exact` refuses is REPORTED, never skipped silently
       ({!load_report}).                                                   by construction
   X4  No program is invented for a name: {!truth} answers exactly the corpus.json members
       whose canonical bytes exist in the tree, and its third component names the rest;
       {!lean_corpus} answers exactly the rows of `index.tsv`.             by construction *)

open Eff_types

(** One program of a corpus. *)
type program =
  { name : string (** the golden's basename, or `g<NNN>` for a generated program *)
  ; corpus : string (** "goldens" | "truth" | "lean" *)
  ; eff : NativeOp.t Eff.t
  ; bytes : string option (** the canonical wire bytes, when the program came from them *)
  ; typed : bool option (** Lean's `Api.wellTyped` verdict, when the source records it *)
  }

(** What loading one directory found (X3). *)
type load_report =
  { lr_dir : string
  ; lr_found : int
  ; lr_decoded : int
  ; lr_refused : string list (** the file names `decode_program_exact` refused *)
  }

(** The byte goldens of ocaml/eff/goldens. *)
val goldens : unit -> program list * load_report

(** The members of harness/truth/corpus.json, by name. *)
val truth_names : string list

(** The truth corpus: the programs whose canonical bytes exist, the report, and the names of
    {!truth_names} with no bytes in the tree (X4). *)
val truth : unit -> program list * load_report * string list

(** What Lean recorded for one truth program at fuel 1000. *)
type truth_expect =
  { te_name : string
  ; te_outcome : string (** `run.outcome`: "finished" | "frontier" | "stuck …" *)
  ; te_fibers : int
  ; te_exit_kind : string (** `run.exitKind`: "success" | "fail" | "die" | "interrupt" *)
  ; te_success_nat : int option (** `run.exit.success` when it is a plain number *)
  }

(** harness/truth/corpus.json's recorded runs, or why the file was not read. *)
val truth_expectations : unit -> (truth_expect list, string) result

(** The printed Lean corpus with Lean's verdicts (X1, X2). *)
val lean_corpus : unit -> program list * load_report
