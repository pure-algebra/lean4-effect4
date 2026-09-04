(* Eff_typed — Eff as a typed language: a GADT surface indexed by the Eff type (hand-written).

   The signature of the point of the exercise: one OCaml constructor per arm of `Eff`,
   `Stmt`, `Effs`, `ActionTerm`, `CauseTerm`, `Term` and `NativeOp`
   (src/Effect4/Program/{Eff,Native}.lean), with the typing rules of Typing.lean written into
   the constructor types, so that a program that does not type-check in Lean cannot be built
   here. Everything is exposed: the constructors ARE the surface. `erase` forgets the types
   and produces the untyped carrier (Eff_types), which Eff_wire encodes as Lean would.

   Behaviours (see eff_typed.ml for the argument):
   E1  for every constructible `p : (empty, 'a, 'e) eff`, `Eff_typing.well_typed (erase p)`,
       and the checker's answer and error are `to_ty` of the indices.   tested (27 programs)
   E2  `Eff_wire.encode_program (erase p)` is byte for byte what Lean encodes for the same
       program.                                                  tested (goldens/<name>.bin)
   E3  completeness is deliberately partial (unions are not canonical at the type level, a
       generator's returns must agree exactly, handle targets are a closed set); every
       refusal here is a refusal or a stricter reading of Lean's rule.       by construction *)

(* ---- the type language, as phantoms ----
   A value type is a phantom OCaml type. The compound ones are abstract, so their parameters
   are declared injective (`!`) for `ty` below to deduce an index from them. *)

type never
type nat
type int_
type ref_number
type deferred_number
type scope
type context
type unknown
type (!'e, !'a) except
type (!'a, !'e) exit
type !'e cause_of
type (!'a, !'e) fiber
type (!'a, !'b) union

(** The handle targets of the native alphabet: a handle's target is a string in Lean and a
    phantom cannot carry a string, so the targets are the closed set the native rows name. *)
type _ handle =
  | Ref_number : ref_number handle
  | Deferred_number : deferred_number handle
  | Scope : scope handle
  | Context : context handle
  | Unknown : unknown handle

(** The witness of a phantom: Lean's `Ty`, constructor for constructor.
    `Union` maps to the canonical `Ty.join`. *)
type _ ty =
  | Never : never ty
  | Unit : unit ty
  | Nat : nat ty
  | Int : int_ ty
  | String : string ty
  | Bool : bool ty
  | Handle : 'h handle -> 'h ty
  | Option : 'a ty -> 'a option ty
  | List : 'a ty -> 'a list ty
  | Prod : 'a ty * 'b ty -> ('a * 'b) ty
  | Except : 'e ty * 'a ty -> ('e, 'a) except ty
  | Exit_of : 'a ty * 'e ty -> ('a, 'e) exit ty
  | Cause_of : 'e ty -> 'e cause_of ty
  | Fiber_of : 'a ty * 'e ty -> ('a, 'e) fiber ty
  | Union : 'a ty * 'b ty -> ('a, 'b) union ty

(* ---- environments and variables ----
   An environment is a type-level snoc list `'newest * 'older`, `empty` at the root; a
   variable is a de Bruijn index counted from the newest entry. *)

type empty

type (_, _) ix =
  | Z : ('a * 'env, 'a) ix
  | S : ('env, 'a) ix -> ('b * 'env, 'a) ix

(* ---- terms: variables, literals, the native atoms (nativeAtomTy) ---- *)

type (_, _) term =
  | Var : ('env, 'a) ix -> ('env, 'a) term
  | Unit_lit : ('env, unit) term
  | Nat_lit : int -> ('env, nat) term
  | Bool_lit : bool -> ('env, bool) term
  | Str_lit : string -> ('env, string) term
  | Succ : ('env, nat) term -> ('env, nat) term
  | Pred : ('env, nat) term -> ('env, nat) term
  | Is_zero : ('env, nat) term -> ('env, bool) term
  | Not : ('env, bool) term -> ('env, bool) term
  | Add : ('env, nat) term * ('env, nat) term -> ('env, nat) term
  | Lt : ('env, nat) term * ('env, nat) term -> ('env, bool) term
  | Eq : ('env, nat) term * ('env, nat) term -> ('env, bool) term
  | Pair : ('env, 'a) term * ('env, 'b) term -> ('env, 'a * 'b) term
  | Fst : ('env, 'a * 'b) term -> ('env, 'a) term
  | Snd : ('env, 'a * 'b) term -> ('env, 'b) term

(* ---- causes (causeTy) ---- *)

type (_, _) cause =
  | C_fail : ('env, 'e) term -> ('env, 'e) cause
  | C_die : ('env, 'd) term -> ('env, never) cause
  | C_interrupt : ('env, nat) term option -> ('env, never) cause
  | C_both : ('env, 'e1) cause * ('env, 'e2) cause -> ('env, ('e1, 'e2) union) cause

(* ---- the native rows: request, answer, error, kind (NativeOp.row) ---- *)

type sync
type async

type (_, _, _, _) op =
  | Ref_make : (nat, ref_number, never, sync) op
  | Ref_get : (ref_number, nat, never, sync) op
  | Ref_set : (ref_number * nat, ref_number, never, sync) op
  | Ref_get_and_set : (ref_number * nat, nat, never, sync) op
  | Ref_set_and_get : (ref_number * nat, nat, never, sync) op
  | Ref_update : Eff_types.fn_name -> (ref_number, unit, never, sync) op
  | Ref_get_and_update : Eff_types.fn_name -> (ref_number, nat, never, sync) op
  | Ref_update_and_get : Eff_types.fn_name -> (ref_number, nat, never, sync) op
  | Ref_update_some : Eff_types.fn_name -> (ref_number, unit, never, sync) op
  | Ref_get_and_update_some : Eff_types.fn_name -> (ref_number, nat, never, sync) op
  | Ref_update_some_and_get : Eff_types.fn_name -> (ref_number, nat, never, sync) op
  | Ref_modify : Eff_types.fn_name -> (ref_number, nat, never, sync) op
  | Ref_modify_some : Eff_types.fn_name -> (ref_number, nat, never, sync) op
  | Deferred_make : (unit, deferred_number, never, sync) op
  | Deferred_is_done : (deferred_number, bool, never, sync) op
  | Deferred_poll : (deferred_number, bool, never, sync) op
  | Deferred_succeed : (deferred_number * nat, bool, never, sync) op
  | Deferred_fail : (deferred_number * nat, bool, never, sync) op
  | Deferred_await : (deferred_number, nat, nat, async) op
  | Scope_make : Eff_types.finalizer_strategy -> (unit, scope, never, sync) op

(* ---- the witnesses ---- *)

(** `EffTy.joinAnswer a b`: equal, or one of them `never`. *)
type (_, _, _) join_answer =
  | Same : ('a, 'a, 'a) join_answer
  | Left_never : (never, 'b, 'b) join_answer
  | Right_never : ('a, never, 'a) join_answer

(** No `ret` yet: `GenTy.answer = none`. *)
type no_ret

(** `GenTy.joinAnswer` on the returns seen so far: none, or equal. *)
type (_, _, _) merge_ret =
  | R_same : ('r, 'r, 'r) merge_ret
  | R_left_none : (no_ret, 'r, 'r) merge_ret
  | R_right_none : ('r, no_ret, 'r) merge_ret

(** `g.answer.getD unit`. *)
type (_, _) gen_answer =
  | G_ret : ('a, 'a) gen_answer
  | G_unit : (no_ret, unit) gen_answer

(** `awaitFiber`'s mode: join answers the value, await answers the exit. *)
type (_, _, _, _) observer =
  | Join_effect : ('a, 'e, 'a, 'e) observer
  | Await_value : ('a, 'e, ('a, 'e) exit, never) observer

type in_loop
type not_in_loop

(* ---- programs: (environment, answer, error) ---- *)

type (_, _, _) eff =
  | Succeed : ('env, 'a) term -> ('env, 'a, never) eff
  | Fail : ('env, 'e) term -> ('env, never, 'e) eff
  | Fail_cause : ('env, 'e) cause -> ('env, never, 'e) eff
  | Yield_error : ('env, 'e) term -> ('env, never, 'e) eff
  | Sync : ('env, 'a) term -> ('env, 'a, never) eff
  | Suspend : ('env, 'a, 'e) eff -> ('env, 'a, 'e) eff
  | Perform : ('req, 'ans, 'err, 'k) op * ('env, 'req) term -> ('env, 'ans, 'err) eff
  | Bind : ('env, 'a, 'e1) eff * ('a * 'env, 'b, 'e2) eff -> ('env, 'b, ('e1, 'e2) union) eff
  | Gen : ('env, 'r, 'e, not_in_loop) stmts * ('r, 'a) gen_answer -> ('env, 'a, 'e) eff
  | Catch_cause :
      ('env, 'a, 'e1) eff * ('e1 cause_of * 'env, 'b, 'e2) eff * ('a, 'b, 'c) join_answer
      -> ('env, 'c, 'e2) eff
  | Match_cause :
      ('env, 'a, 'e) eff * ('a * 'env, 'b, 'e1) eff * ('e cause_of * 'env, 'c, 'e2) eff
      * ('b, 'c, 'd) join_answer
      -> ('env, 'd, ('e1, 'e2) union) eff
  | On_exit :
      ('env, 'a, 'e) eff * (('a, 'e) exit * 'env, 'b, 'e2) eff -> ('env, 'a, ('e, 'e2) union) eff
  | Exit : ('env, 'a, 'e) eff -> ('env, ('a, 'e) exit, never) eff
  | Uninterruptible : ('env, 'a, 'e) eff -> ('env, 'a, 'e) eff
  | Interruptible : ('env, 'a, 'e) eff -> ('env, 'a, 'e) eff
  | Branch :
      ('env, bool) term * ('env, 'a, 'e1) eff * ('env, 'b, 'e2) eff * ('a, 'b, 'c) join_answer
      -> ('env, 'c, ('e1, 'e2) union) eff
  | While_loop :
      ('env, 'c) term * ('c * 'env, bool) term * ('a * ('c * 'env), 'c) term * ('c * 'env, 'a, 'e) eff
      -> ('env, unit, 'e) eff
  | Yield_now : int -> ('env, unit, never) eff
  | Callback : ('req, 'ans, 'err, async) op * ('env, 'req) term -> ('env, 'ans, 'err) eff
  | Await_fiber : ('env, ('a, 'e) fiber) term * ('a, 'e, 'ans, 'err) observer -> ('env, 'ans, 'err) eff
  | With_fiber : ('env, 'a, 'e) action -> ('env, 'a, 'e) eff
  | Scoped : ('env, 'a, 'e) eff -> ('env, 'a, 'e) eff
  | Acquire_release :
      ('env, 'a, 'e) eff * (('a, 'e) exit * ('a * 'env), 'b, 'e2) eff -> ('env, 'a, 'e) eff
  | Choose :
      int * ('env, 'a, 'e1) eff * ('env, 'b, 'e2) eff * ('a, 'b, 'c) join_answer
      -> ('env, 'c, ('e1, 'e2) union) eff

(** A generator body: environment, the return type so far (`no_ret` before the first `ret`),
    error, and whether a `breakLoop` is legal here. *)
and (_, _, _, _) stmts =
  | Nil : ('env, no_ret, never, 'l) stmts
  | Bind_yield :
      ('env, 'a, 'e1) eff * ('a * 'env, 'r, 'e2, 'l) stmts -> ('env, 'r, ('e1, 'e2) union, 'l) stmts
  | Yield_discard :
      ('env, 'a, 'e1) eff * ('env, 'r, 'e2, 'l) stmts -> ('env, 'r, ('e1, 'e2) union, 'l) stmts
  | Ret : ('env, 'r) term -> ('env, 'r, never, 'l) stmts
  | If_else :
      ('env, bool) term
      * ('env, 'r1, 'e1, 'l) stmts * ('env, 'r2, 'e2, 'l) stmts * ('r1, 'r2, 'r12) merge_ret
      * ('env, 'r3, 'e3, 'l) stmts * ('r12, 'r3, 'r) merge_ret
      -> ('env, 'r, (('e1, 'e2) union, 'e3) union, 'l) stmts
  | While_true :
      ('env, 'r1, 'e1, in_loop) stmts * ('env, 'r2, 'e2, 'l) stmts * ('r1, 'r2, 'r) merge_ret
      -> ('env, 'r, ('e1, 'e2) union, 'l) stmts
  | Break : ('env, 'r, 'e, in_loop) stmts -> ('env, 'r, 'e, in_loop) stmts

(** Race entrants: the answers join, the errors union. *)
and (_, _, _) effs =
  | Effs_nil : ('env, never, never) effs
  | Effs_cons :
      ('env, 'a, 'e1) eff * ('env, 'b, 'e2) effs * ('a, 'b, 'c) join_answer
      -> ('env, 'c, ('e1, 'e2) union) effs

(** The fiber actions (`actionTy`). *)
and (_, _, _) action =
  | Fork : ('env, 'a, 'e) eff * Eff_types.fork_options -> ('env, ('a, 'e) fiber, never) action
  | Fork_in :
      ('env, 'a, 'e) eff * Eff_types.fork_options * ('env, scope) term
      -> ('env, ('a, 'e) fiber, never) action
  | Fork_scoped : ('env, 'a, 'e) eff * Eff_types.fork_options -> ('env, ('a, 'e) fiber, never) action
  | Run_in : ('env, ('a, 'e) fiber) term * ('env, scope) term -> ('env, unit, never) action
  | Interrupt : ('env, ('a, 'e) fiber) term -> ('env, unit, never) action
  | Interrupt_scoped : ('env, ('a, 'e) fiber) term -> ('env, unit, never) action
  | Interrupt_all :
      ('env, ('a, 'e) fiber list) term * ('env, nat) term option -> ('env, unit, never) action
  | Await_all : ('env, ('a, 'e) fiber list) term -> ('env, ('a, 'e) exit list, never) action
  | Await_all_fail_fast : ('env, ('a, 'e) fiber list) term -> ('env, ('a, 'e) exit list, never) action
  | Snapshot_children : ('env, (unknown, unknown) fiber list, never) action
  | Await_new_children : ('env, (unknown, unknown) fiber list) term -> ('env, unit, never) action
  | Race_all : ('env, 'a, 'e) effs -> ('env, 'a, 'e) action
  | Set_context : ('env, context) term -> ('env, unit, never) action
  | Get_context : ('env, context, never) action
  | Get_id : ('env, nat, never) action
  | Close_scope : ('env, scope) term * ('env, ('a, 'e) exit) term -> ('env, unit, never) action

(** A closed program with its witnesses, for tables and tests. *)
type program = Program : (empty, 'a, 'e) eff * 'a ty * 'e ty -> program

(* ---- the witnesses, as Lean's Ty ---- *)

(** The handle's target string, as `Ty.handle` spells it in Lean. *)
val handle_target : 'h handle -> string

(** The phantom's Lean `Ty`. `Union` is canonicalised through `Eff_typing.join`. *)
val to_ty : 'a ty -> Eff_types.ty

(* ---- erasure ----
   `erase_*` take the depth of the environment, because an OCaml index counts from the newest
   binding and Lean's `Var` counts from the oldest: the Lean index is `depth - 1 - index`. *)

val ix_to_int : ('env, 'a) ix -> int
val terms_of : Eff_types.term list -> Eff_types.terms
val erase_term : int -> ('env, 'a) term -> Eff_types.term
val erase_cause : int -> ('env, 'e) cause -> Eff_types.cause_term
val erase_op : ('r, 'a, 'e, 'k) op -> Eff_types.native_op
val erase_observer : ('a, 'e, 'ans, 'err) observer -> Eff_types.observer_mode
val erase_eff : int -> ('env, 'a, 'e) eff -> Eff_types.eff
val erase_stmts : int -> ('env, 'r, 'e, 'l) stmts -> Eff_types.stmts
val erase_effs : int -> ('env, 'a, 'e) effs -> Eff_types.effs
val erase_action : int -> ('env, 'a, 'e) action -> Eff_types.action_term

(** A closed program, erased at the empty environment. *)
val erase : (empty, 'a, 'e) eff -> Eff_types.eff

(** Its canonical bytes: what Lean would store for the same program. *)
val encode : (empty, 'a, 'e) eff -> string

(* ---- small conveniences ---- *)

val v0 : ('a * 'b, 'a) term
val v1 : ('a * ('b * 'c), 'b) term
val v2 : ('a * ('b * ('c * 'd)), 'c) term
val v3 : ('a * ('b * ('c * ('d * 'e))), 'd) term
val nat : int -> ('a, nat) term
val unit_ : ('a, unit) term
val bool : bool -> ('a, bool) term
val str : string -> ('a, string) term

val fork_options :
  ?start_immediately:bool -> ?daemon:bool -> ?mask:Eff_types.mask_mode -> unit ->
  Eff_types.fork_options
