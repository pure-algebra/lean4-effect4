(* Eff_typed — Eff as a typed language: a GADT surface indexed by the Eff type (hand-written).

   What it is: one OCaml constructor per arm of `Eff`, `Stmt`, `Effs`, `ActionTerm`,
   `CauseTerm`, `Term` and `NativeOp` (src/Effect4/Program/{Eff,Native}.lean), with the typing
   rules of Typing.lean written into the constructor types, so that a program that does not
   type-check in Lean cannot be built here. `erase` forgets the types and produces the
   untyped carrier (Eff_types), which Eff_wire encodes as Lean would.

   The indices. A value type is a phantom OCaml type: `nat`, `unit`, `bool`, `string`,
   `int_`, `never`, `'a option`, `'a list`, `'a * 'b`, `('e, 'a) except`, `('a, 'e) exit`,
   `'e cause_of`, `('a, 'e) fiber`, `('a, 'b) union`, and one phantom per handle target of the
   native alphabet (`ref_number`, `deferred_number`, `scope`, `context`, `unknown`): a
   handle's target is a string in Lean and a phantom cannot carry a string, so the targets
   are the closed set the native rows and `actionTy` name. `'a ty` is the witness that maps
   a phantom back to Lean's `Ty` (`to_ty`); `Union` maps to the canonical `Ty.join`.
   An environment is a type-level snoc list `'newest * 'older`, `empty` at the root; a
   variable is a de Bruijn index from the newest entry (`Z`, `S`), and `erase` turns it into
   Lean's position from the oldest (`depth - 1 - index`), which is why `erase` threads the
   depth.
   Where Lean's rule joins two answers (`EffTy.joinAnswer`: equal, or one of them `never`)
   the constructor takes a `join_answer` witness; where a generator body merges its returns
   (`GenTy.joinAnswer`: none, or equal) it takes a `merge_ret` witness, and `Gen` takes the
   `gen_answer` witness for `getD unit`. The requirement row `R` is computed by the checker
   and not tracked here.

   Behaviours it holds itself to:
   E1  Soundness: for every constructible `p : (empty, 'a, 'e) eff`, `Eff_typing.well_typed
       (erase p)`, and Lean's answer and error are `to_ty` of the indices (the error up to
       `Ty.join`, which `to_ty` applies).      tested (the 27 well-typed corpus programs);
                                              the Lean theorem is stated in REPORT.md, open
   E2  Exactness of authorship: `Eff_wire.encode_program (erase p)` is byte for byte what
       Lean encodes for the same program.       tested (goldens/<name>.bin, 27 programs)
   E3  Completeness is deliberately partial: unions are not canonical at the type level
       (`(nat, never) union` is not `nat` to OCaml, it is to Lean), a generator's returns must
       agree exactly (a `never` return does not merge), handle targets are the closed set
       above. Every refusal here is also a refusal or a stricter reading of Lean's rule,
       never an acceptance Lean refuses.        by construction (see E1)
   Depends on: Eff_types, Eff_native (row data is not consulted: the op signatures below are
   written by hand from eff_native.ml and pinned against it by the tests), Eff_typing (join). *)

(* ---- the type language, as phantoms ---- *)

type never
type nat
type int_
type ref_number
type deferred_number
type scope
type context
type unknown
(* The compound phantoms are abstract, so their parameters must be declared injective
   (`!`) for the GADT below to deduce an index from `('e, 'a) except` and friends. *)
type (!'e, !'a) except
type (!'a, !'e) exit
type !'e cause_of
type (!'a, !'e) fiber
type (!'a, !'b) union

(* The handle targets of the native alphabet. *)
type _ handle =
  | Ref_number : ref_number handle          (* "Ref.Ref<number>" *)
  | Deferred_number : deferred_number handle (* "Deferred.Deferred<number, number>" *)
  | Scope : scope handle                    (* "Scope.Scope" *)
  | Context : context handle                (* "Context.Context<unknown>" *)
  | Unknown : unknown handle                (* "unknown" *)

(* The witness of a phantom: Lean's Ty, constructor for constructor. *)
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

(* ---- environments and variables ---- *)

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

(* EffTy.joinAnswer a b: equal, or one of them never. *)
type (_, _, _) join_answer =
  | Same : ('a, 'a, 'a) join_answer
  | Left_never : (never, 'b, 'b) join_answer
  | Right_never : ('a, never, 'a) join_answer

(* GenTy.joinAnswer on the returns seen so far: none, or equal. *)
type no_ret

type (_, _, _) merge_ret =
  | R_same : ('r, 'r, 'r) merge_ret
  | R_left_none : (no_ret, 'r, 'r) merge_ret
  | R_right_none : ('r, no_ret, 'r) merge_ret

(* g.answer.getD unit *)
type (_, _) gen_answer =
  | G_ret : ('a, 'a) gen_answer
  | G_unit : (no_ret, unit) gen_answer

(* awaitFiber's mode: join answers the value, await answers the exit. *)
type (_, _, _, _) observer =
  | Join_effect : ('a, 'e, 'a, 'e) observer
  | Await_value : ('a, 'e, ('a, 'e) exit, never) observer

type in_loop
type not_in_loop

(* ---- programs ---- *)

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
  | On_exit : ('env, 'a, 'e) eff * (('a, 'e) exit * 'env, 'b, 'e2) eff -> ('env, 'a, ('e, 'e2) union) eff
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

(* A generator body: env, the return type so far (no_ret before the first), error, loop. *)
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

(* Race entrants: the answers join, the errors union. *)
and (_, _, _) effs =
  | Effs_nil : ('env, never, never) effs
  | Effs_cons :
      ('env, 'a, 'e1) eff * ('env, 'b, 'e2) effs * ('a, 'b, 'c) join_answer
      -> ('env, 'c, ('e1, 'e2) union) effs

(* The fiber actions (actionTy). *)
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

(* A closed program with its witnesses, for tables and tests. *)
type program = Program : (empty, 'a, 'e) eff * 'a ty * 'e ty -> program

(* ---- the witnesses, as Lean's Ty ---- *)

let handle_target : type h. h handle -> string = function
  | Ref_number -> "Ref.Ref<number>"
  | Deferred_number -> "Deferred.Deferred<number, number>"
  | Scope -> "Scope.Scope"
  | Context -> "Context.Context<unknown>"
  | Unknown -> "unknown"

let rec to_ty : type a. a ty -> Eff_types.ty = function
  | Never -> Eff_types.Ty_never
  | Unit -> Eff_types.Ty_unit
  | Nat -> Eff_types.Ty_nat
  | Int -> Eff_types.Ty_int
  | String -> Eff_types.Ty_string
  | Bool -> Eff_types.Ty_bool
  | Handle h -> Eff_types.Ty_handle (handle_target h)
  | Option a -> Eff_types.Ty_option (to_ty a)
  | List a -> Eff_types.Ty_list (to_ty a)
  | Prod (a, b) -> Eff_types.Ty_prod (to_ty a, to_ty b)
  | Except (e, a) -> Eff_types.Ty_except (to_ty e, to_ty a)
  | Exit_of (a, e) -> Eff_types.Ty_exitOf (to_ty a, to_ty e)
  | Cause_of e -> Eff_types.Ty_causeOf (to_ty e)
  | Fiber_of (a, e) -> Eff_types.Ty_fiberOf (to_ty a, to_ty e)
  | Union (a, b) -> Eff_typing.join (to_ty a) (to_ty b)

(* ---- erasure ---- *)

let rec ix_to_int : type env a. (env, a) ix -> int = function
  | Z -> 0
  | S i -> 1 + ix_to_int i

let terms_of (xs : Eff_types.term list) : Eff_types.terms =
  List.fold_right (fun x acc -> Eff_types.Terms_cons (x, acc)) xs Eff_types.Terms_nil

let rec erase_term : type env a. int -> (env, a) term -> Eff_types.term = fun depth t ->
  let app name args = Eff_types.Term_app (name, terms_of args) in
  let e : type b. (env, b) term -> Eff_types.term = fun x -> erase_term depth x in
  match t with
  | Var i -> Eff_types.Term_var (depth - 1 - ix_to_int i)
  | Unit_lit -> Eff_types.Term_lit Eff_types.Lit_unit
  | Nat_lit n -> Eff_types.Term_lit (Eff_types.Lit_nat n)
  | Bool_lit b -> Eff_types.Term_lit (Eff_types.Lit_bool b)
  | Str_lit s -> Eff_types.Term_lit (Eff_types.Lit_str s)
  | Succ a -> app "succ" [ e a ]
  | Pred a -> app "pred" [ e a ]
  | Is_zero a -> app "isZero" [ e a ]
  | Not a -> app "not" [ e a ]
  | Add (a, b) -> app "add" [ e a; e b ]
  | Lt (a, b) -> app "lt" [ e a; e b ]
  | Eq (a, b) -> app "eq" [ e a; e b ]
  | Pair (a, b) -> app "pair" [ e a; e b ]
  | Fst a -> app "fst" [ e a ]
  | Snd a -> app "snd" [ e a ]

let rec erase_cause : type env e. int -> (env, e) cause -> Eff_types.cause_term = fun depth c ->
  match c with
  | C_fail t -> Eff_types.Cause_term_fail (erase_term depth t)
  | C_die t -> Eff_types.Cause_term_die (erase_term depth t)
  | C_interrupt who -> Eff_types.Cause_term_interrupt (Option.map (erase_term depth) who)
  | C_both (l, r) -> Eff_types.Cause_term_both (erase_cause depth l, erase_cause depth r)

let erase_op : type r a e k. (r, a, e, k) op -> Eff_types.native_op = function
  | Ref_make -> Eff_types.Native_op_refMake
  | Ref_get -> Eff_types.Native_op_refGet
  | Ref_set -> Eff_types.Native_op_refSet
  | Ref_get_and_set -> Eff_types.Native_op_refGetAndSet
  | Ref_set_and_get -> Eff_types.Native_op_refSetAndGet
  | Ref_update f -> Eff_types.Native_op_refUpdate f
  | Ref_get_and_update f -> Eff_types.Native_op_refGetAndUpdate f
  | Ref_update_and_get f -> Eff_types.Native_op_refUpdateAndGet f
  | Ref_update_some f -> Eff_types.Native_op_refUpdateSome f
  | Ref_get_and_update_some f -> Eff_types.Native_op_refGetAndUpdateSome f
  | Ref_update_some_and_get f -> Eff_types.Native_op_refUpdateSomeAndGet f
  | Ref_modify f -> Eff_types.Native_op_refModify f
  | Ref_modify_some f -> Eff_types.Native_op_refModifySome f
  | Deferred_make -> Eff_types.Native_op_deferredMake
  | Deferred_is_done -> Eff_types.Native_op_deferredIsDone
  | Deferred_poll -> Eff_types.Native_op_deferredPoll
  | Deferred_succeed -> Eff_types.Native_op_deferredSucceed
  | Deferred_fail -> Eff_types.Native_op_deferredFail
  | Deferred_await -> Eff_types.Native_op_deferredAwait
  | Scope_make s -> Eff_types.Native_op_scopeMake s

let erase_observer : type a e ans err. (a, e, ans, err) observer -> Eff_types.observer_mode = function
  | Join_effect -> Eff_types.Observer_mode_joinEffect
  | Await_value -> Eff_types.Observer_mode_awaitValue

let rec erase_eff : type env a e. int -> (env, a, e) eff -> Eff_types.eff = fun d p ->
  let t : type b. (env, b) term -> Eff_types.term = fun x -> erase_term d x in
  match p with
  | Succeed v -> Eff_types.Eff_succeed (t v)
  | Fail v -> Eff_types.Eff_fail (t v)
  | Fail_cause c -> Eff_types.Eff_failCause (erase_cause d c)
  | Yield_error v -> Eff_types.Eff_yieldError (t v)
  | Sync v -> Eff_types.Eff_sync (t v)
  | Suspend b -> Eff_types.Eff_suspend (erase_eff d b)
  | Perform (op, r) -> Eff_types.Eff_perform (erase_op op, t r)
  | Bind (f, r) -> Eff_types.Eff_bind (erase_eff d f, erase_eff (d + 1) r)
  | Gen (body, _) -> Eff_types.Eff_gen (erase_stmts d body)
  | Catch_cause (b, h, _) -> Eff_types.Eff_catchCause (erase_eff d b, erase_eff (d + 1) h)
  | Match_cause (b, v, c, _) ->
    Eff_types.Eff_matchCause (erase_eff d b, erase_eff (d + 1) v, erase_eff (d + 1) c)
  | On_exit (b, f) -> Eff_types.Eff_onExit (erase_eff d b, erase_eff (d + 1) f)
  | Exit b -> Eff_types.Eff_exit (erase_eff d b)
  | Uninterruptible b -> Eff_types.Eff_uninterruptible (erase_eff d b)
  | Interruptible b -> Eff_types.Eff_interruptible (erase_eff d b)
  | Branch (test, a, b, _) -> Eff_types.Eff_branch (t test, erase_eff d a, erase_eff d b)
  | While_loop (initial, test, step, body) ->
    Eff_types.Eff_whileLoop (t initial, erase_term (d + 1) test, erase_term (d + 2) step, erase_eff (d + 1) body)
  | Yield_now p -> Eff_types.Eff_yieldNow p
  | Callback (op, r) -> Eff_types.Eff_callback (erase_op op, t r)
  | Await_fiber (f, mode) -> Eff_types.Eff_awaitFiber (t f, erase_observer mode)
  | With_fiber a -> Eff_types.Eff_withFiber (erase_action d a)
  | Scoped b -> Eff_types.Eff_scoped (erase_eff d b)
  | Acquire_release (a, r) -> Eff_types.Eff_acquireRelease (erase_eff d a, erase_eff (d + 2) r)
  | Choose (site, l, r, _) -> Eff_types.Eff_choose (site, erase_eff d l, erase_eff d r)

and erase_stmts : type env r e l. int -> (env, r, e, l) stmts -> Eff_types.stmts = fun d s ->
  let cons st rest = Eff_types.Stmts_cons (st, rest) in
  match s with
  | Nil -> Eff_types.Stmts_nil
  | Bind_yield (e, rest) -> cons (Eff_types.Stmt_bindYield (erase_eff d e)) (erase_stmts (d + 1) rest)
  | Yield_discard (e, rest) -> cons (Eff_types.Stmt_yieldDiscard (erase_eff d e)) (erase_stmts d rest)
  | Ret v -> cons (Eff_types.Stmt_ret (erase_term d v)) Eff_types.Stmts_nil
  | If_else (test, a, b, _, rest, _) ->
    cons (Eff_types.Stmt_ifElse (erase_term d test, erase_stmts d a, erase_stmts d b)) (erase_stmts d rest)
  | While_true (body, rest, _) -> cons (Eff_types.Stmt_whileTrue (erase_stmts d body)) (erase_stmts d rest)
  | Break rest -> cons Eff_types.Stmt_breakLoop (erase_stmts d rest)

and erase_effs : type env a e. int -> (env, a, e) effs -> Eff_types.effs = fun d es ->
  match es with
  | Effs_nil -> Eff_types.Effs_nil
  | Effs_cons (h, tl, _) -> Eff_types.Effs_cons (erase_eff d h, erase_effs d tl)

and erase_action : type env a e. int -> (env, a, e) action -> Eff_types.action_term = fun d a ->
  let t : type b. (env, b) term -> Eff_types.term = fun x -> erase_term d x in
  match a with
  | Fork (p, o) -> Eff_types.Action_term_fork (erase_eff d p, o)
  | Fork_in (p, o, s) -> Eff_types.Action_term_forkIn (erase_eff d p, o, t s)
  | Fork_scoped (p, o) -> Eff_types.Action_term_forkScoped (erase_eff d p, o)
  | Run_in (target, s) -> Eff_types.Action_term_runIn (t target, t s)
  | Interrupt target -> Eff_types.Action_term_interrupt (t target)
  | Interrupt_scoped target -> Eff_types.Action_term_interruptScoped (t target)
  | Interrupt_all (targets, who) -> Eff_types.Action_term_interruptAll (t targets, Option.map t who)
  | Await_all targets -> Eff_types.Action_term_awaitAll (t targets)
  | Await_all_fail_fast targets -> Eff_types.Action_term_awaitAllFailFast (t targets)
  | Snapshot_children -> Eff_types.Action_term_snapshotChildren
  | Await_new_children s -> Eff_types.Action_term_awaitNewChildren (t s)
  | Race_all es -> Eff_types.Action_term_raceAll (erase_effs d es)
  | Set_context c -> Eff_types.Action_term_setContext (t c)
  | Get_context -> Eff_types.Action_term_getContext
  | Get_id -> Eff_types.Action_term_getId
  | Close_scope (s, e) -> Eff_types.Action_term_closeScope (t s, t e)

(* A closed program, erased at the empty environment. *)
let erase (p : (empty, 'a, 'e) eff) : Eff_types.eff = erase_eff 0 p

(* Its canonical bytes: what Lean would store for the same program. *)
let encode (p : (empty, 'a, 'e) eff) : string = Eff_wire.encode_program (erase p)

(* ---- small conveniences ---- *)

let v0 = Var Z
let v1 = Var (S Z)
let v2 = Var (S (S Z))
let v3 = Var (S (S (S Z)))
let nat n = Nat_lit n
let unit_ = Unit_lit
let bool b = Bool_lit b
let str s = Str_lit s

let fork_options ?(start_immediately = false) ?(daemon = false)
    ?(mask = Eff_types.Mask_mode_inherit) () : Eff_types.fork_options =
  { Eff_types.fork_options_startImmediately = start_immediately;
    fork_options_daemon = daemon;
    fork_options_maskMode = mask }
