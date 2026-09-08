(* E4_program -- the program alphabet: `Eff_types.eff` (the wire's type) into the generated
   engine's `eff`, with the ordinal pin that licenses the conversion.

   What it is: owner default A1-Q2, option U-c (docs/research/2026-09-08-engine-a1-state.md
   §2.3).  `ocaml/eff/eff_types.ml` and `ocaml/engine/api_engine.ml` are two OCaml types for
   ONE Lean declaration (`Effect4.Program.Eff`), written by two generators (`EffGen.lean` and
   `Lcnf/Types.lean`) from the same `InductiveVal.ctors`.  This module carries the hand
   conversion between them and the gate that says the two alphabets still agree.

   Why a functor.  The engine's `eff` is declared INSIDE `Api_engine.Make`
   (api_engine.ml:427-454), because the type group mentions the carrier parameters, so
   `Api_engine.Make(fast carriers).eff` and `Api_engine.Make(list carriers).eff` are two
   distinct OCaml types.  {!PROGRAM_TYPES} is the part of that type group the program
   alphabet actually uses -- nineteen declarations, none of which mentions a carrier -- so
   ONE conversion serves every instance.

   THAT SIGNATURE IS ITSELF THE STRUCTURAL HALF OF THE PIN.  It is a hand transcription of
   api_engine.ml's declarations, and `ocamlopt` checks it against every instance the engine
   is applied to: a constructor added, removed, renamed or re-ordered in the generated file
   is a compile error here, naming the family.  The ordinal half ({!pin}, {!check_manifest})
   is what catches a re-ordering that keeps the same set of names.

   Depends on: effect4_eff (Eff_types, Eff_wire), stdlib.

   Behaviours:
   P1  Total on the source: `of_eff` is defined at every constructor of `Eff_types.eff` and
       raises nothing.  OCaml's exhaustiveness check is the evidence.     by construction
   P2  Ordinal-preserving: for every arm, `Eff_types.ctor_index_<t> v` equals
       `ctor_index_<t> (of_<t> v)`, for each of the fourteen families.  This is what closes
       the transposition hole a plain structural map leaves (two same-arity arms swapped).
                                                                          tested (test_engine
                                                                          check 3)
   P3  Append-only alphabets (brief §2.6, CAS amendment M17): the source's constructor names
       are a PREFIX of the engine's, family by family.  `eff` is the one family where they
       differ -- the engine has 27 arms and the wire 24, because `provideLayer`, `service`
       and `provideService` joined `Eff` after `eff_types.ml` was cut -- and a prefix is
       exactly what "append-only" means.  A re-order is not a prefix.     tested; {!pin}
   P4  The content table is `ocaml/eff/eff_manifest.txt`: {!check_manifest} reads it and
       compares its constructor names, family by family, with `Eff_types`'.  M17's "every
       ordinal is a position in a content table" is that comparison.      tested
   P5  Refusal at load: {!pin_exn} raises {!Ordinal_mismatch} rather than converting under a
       disagreed alphabet.  `E4_engine.load` calls it.                     by construction
   P6  No allocation beyond the converted tree; the conversion is O(program size) and runs
       once per load (A1 §2.3: `load` is 0.000 ms at chain n = 1000).      by construction *)

exception Ordinal_mismatch of string

(** {1 The alphabet the generated engine declares} *)

module type PROGRAM_TYPES = sig
  (* Transcribed from ocaml/engine/api_engine.ml; the line number of each declaration is on
     its right.  Every instance of `Api_engine.Make` satisfies this signature. *)

  type mask_mode = MaskMode_interruptible | MaskMode_uninterruptible | MaskMode_inherit
  (* :626 *)

  type fork_options = { start_immediately : bool; daemon : bool; mask_mode : mask_mode }
  (* :627 *)

  type finalizer_strategy = FinalizerStrategy_sequential | FinalizerStrategy_parallel
  (* :628 *)

  type observer_mode = ObserverMode_awaitValue | ObserverMode_joinEffect  (* :541 *)

  type fn_name =                                                          (* :221-226 *)
    | FnName_incr
    | FnName_double
    | FnName_zeroWhenPositive
    | FnName_noChange
    | FnName_takeAndBump

  type lit = Lit_unit | Lit_nat of int | Lit_bool of bool | Lit_str of string  (* :736-740 *)

  type term = Term_var of int | Term_lit of lit | Term_app of string * terms  (* :652 *)
  and terms = Terms_nil | Terms_cons of term * terms                          (* :741 *)

  type cause_term =                                                       (* :655-659 *)
    | CauseTerm_fail of term
    | CauseTerm_die of term
    | CauseTerm_interrupt of term option
    | CauseTerm_both of cause_term * cause_term

  type service_name = int                                                 (* :783 *)
  type service_type_code = int                                            (* :784 *)
  type service_key = { name : service_name; service : service_type_code }  (* :722 *)

  type native_op =                                                        (* :660-680 *)
    | NativeOp_refMake
    | NativeOp_refGet
    | NativeOp_refSet
    | NativeOp_refGetAndSet
    | NativeOp_refSetAndGet
    | NativeOp_refUpdate of fn_name
    | NativeOp_refGetAndUpdate of fn_name
    | NativeOp_refUpdateAndGet of fn_name
    | NativeOp_refUpdateSome of fn_name
    | NativeOp_refGetAndUpdateSome of fn_name
    | NativeOp_refUpdateSomeAndGet of fn_name
    | NativeOp_refModify of fn_name
    | NativeOp_refModifySome of fn_name
    | NativeOp_deferredMake
    | NativeOp_deferredIsDone
    | NativeOp_deferredPoll
    | NativeOp_deferredSucceed
    | NativeOp_deferredFail
    | NativeOp_deferredAwait
    | NativeOp_scopeMake of finalizer_strategy

  type 'op eff =                                                          (* :427-454 *)
    | Eff_succeed of term
    | Eff_fail of term
    | Eff_failCause of cause_term
    | Eff_yieldError of term
    | Eff_sync of term
    | Eff_suspend of 'op eff
    | Eff_perform of 'op * term
    | Eff_bind of 'op eff * 'op eff
    | Eff_gen of 'op stmts
    | Eff_catchCause of 'op eff * 'op eff
    | Eff_matchCause of 'op eff * 'op eff * 'op eff
    | Eff_onExit of 'op eff * 'op eff
    | Eff_exit of 'op eff
    | Eff_uninterruptible of 'op eff
    | Eff_interruptible of 'op eff
    | Eff_branch of term * 'op eff * 'op eff
    | Eff_whileLoop of term * term * term * 'op eff
    | Eff_yieldNow of int
    | Eff_callback of 'op * term
    | Eff_awaitFiber of term * observer_mode
    | Eff_withFiber of 'op action_term
    | Eff_scoped of 'op eff
    | Eff_acquireRelease of 'op eff * 'op eff
    | Eff_choose of int * 'op eff * 'op eff
    | Eff_provideLayer of 'op layer_term * bool * 'op eff
    | Eff_service of service_key
    | Eff_provideService of service_key * term * 'op eff

  and 'op stmts = Stmts_nil | Stmts_cons of 'op stmt * 'op stmts          (* :714 *)

  and 'op stmt =                                                          (* :715-721 *)
    | Stmt_bindYield of 'op eff
    | Stmt_yieldDiscard of 'op eff
    | Stmt_ret of term
    | Stmt_ifElse of term * 'op stmts * 'op stmts
    | Stmt_whileTrue of 'op stmts
    | Stmt_breakLoop

  and 'op effs = Effs_nil | Effs_cons of 'op eff * 'op effs               (* :750 *)

  and 'op action_term =                                                   (* :469-485 *)
    | ActionTerm_fork of 'op eff * fork_options
    | ActionTerm_forkIn of 'op eff * fork_options * term
    | ActionTerm_forkScoped of 'op eff * fork_options
    | ActionTerm_runIn of term * term
    | ActionTerm_interrupt of term
    | ActionTerm_interruptScoped of term
    | ActionTerm_interruptAll of term * term option
    | ActionTerm_awaitAll of term
    | ActionTerm_awaitAllFailFast of term
    | ActionTerm_snapshotChildren
    | ActionTerm_awaitNewChildren of term
    | ActionTerm_raceAll of 'op effs
    | ActionTerm_setContext of term
    | ActionTerm_getContext
    | ActionTerm_getId
    | ActionTerm_closeScope of term * term

  and 'op layer_term =                                                    (* :723-731 *)
    | LayerTerm_succeed of service_key * lit
    | LayerTerm_effect of service_key * 'op eff
    | LayerTerm_effectDiscard of 'op eff
    | LayerTerm_provide of 'op layer_term * 'op layer_term
    | LayerTerm_provideMerge of 'op layer_term * 'op layer_term
    | LayerTerm_merge of 'op layer_term * 'op layer_term
    | LayerTerm_fresh of 'op layer_term
    | LayerTerm_orDie of 'op layer_term
end

(** {1 The ordinal ledger} *)

val source_ctor_names : (string * string list) list
(** Every inductive family of `Eff_types`, in the order `eff_manifest.txt` lists it, with its
    constructor names -- i.e. `Eff_types.ctor_names_<t>` gathered into one table. *)

val engine_ctor_names : (string * string list) list
(** The same families as the GENERATED engine declares them (api_engine.ml), hand
    transcribed beside {!PROGRAM_TYPES}.  `eff` has three arms the wire does not. *)

val pin : unit -> (unit, string) result
(** P3: for every family, the source's names are a prefix of the engine's.  `Error msg` names
    the family, the position and the two names.  No file is read: this is the gate a `load`
    can afford. *)

val pin_exn : unit -> unit
(** {!pin}, raising {!Ordinal_mismatch}. *)

val parse_manifest : string -> ((string * string list) list, string) result
(** Read `ocaml/eff/eff_manifest.txt` (the path is the argument) and return one row per
    INDUCTIVE family: the OCaml type name and the constructor names, in declaration order.
    Structures are skipped -- they have one constructor and no ordinal. *)

val check_manifest : string -> (unit, string) result
(** P4: {!parse_manifest}, then every family it names must agree, name for name and position
    for position, with {!source_ctor_names}, and must be a prefix of {!engine_ctor_names}. *)

(** {1 The conversion} *)

module Make (A : PROGRAM_TYPES) : sig
  val of_lit : Eff_types.lit -> A.lit
  val of_term : Eff_types.term -> A.term
  val of_terms : Eff_types.terms -> A.terms
  val of_cause_term : Eff_types.cause_term -> A.cause_term
  val of_mask_mode : Eff_types.mask_mode -> A.mask_mode
  val of_fork_options : Eff_types.fork_options -> A.fork_options
  val of_observer_mode : Eff_types.observer_mode -> A.observer_mode
  val of_finalizer_strategy : Eff_types.finalizer_strategy -> A.finalizer_strategy
  val of_fn_name : Eff_types.fn_name -> A.fn_name
  val of_native_op : Eff_types.native_op -> A.native_op
  val of_eff : Eff_types.eff -> A.native_op A.eff
  val of_stmt : Eff_types.stmt -> A.native_op A.stmt
  val of_stmts : Eff_types.stmts -> A.native_op A.stmts
  val of_effs : Eff_types.effs -> A.native_op A.effs
  val of_action_term : Eff_types.action_term -> A.native_op A.action_term

  val load : Eff_types.eff -> A.native_op A.eff
  (** {!of_eff} after {!pin_exn}: the refusal of P5. *)

  val of_bytes : string -> A.native_op A.eff option
  (** `Eff_wire.decode_program_exact`, then {!load}.  None when the bytes are not exactly one
      program (the wire's own refusal). *)

  (** The engine side of P2.  Each is the position of the constructor in api_engine.ml's
      declaration, so `ctor_index_<t> (of_<t> v) = Eff_types.ctor_index_<t> v` is a real
      statement about two independently written tables. *)

  val ctor_index_lit : A.lit -> int
  val ctor_index_term : A.term -> int
  val ctor_index_terms : A.terms -> int
  val ctor_index_cause_term : A.cause_term -> int
  val ctor_index_mask_mode : A.mask_mode -> int
  val ctor_index_observer_mode : A.observer_mode -> int
  val ctor_index_finalizer_strategy : A.finalizer_strategy -> int
  val ctor_index_fn_name : A.fn_name -> int
  val ctor_index_native_op : A.native_op -> int
  val ctor_index_eff : 'op A.eff -> int
  val ctor_index_stmt : 'op A.stmt -> int
  val ctor_index_stmts : 'op A.stmts -> int
  val ctor_index_effs : 'op A.effs -> int
  val ctor_index_action_term : 'op A.action_term -> int
end
