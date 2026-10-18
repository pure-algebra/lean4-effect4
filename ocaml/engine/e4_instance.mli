(* E4_instance: the generated engine and its pure host adapter.
   Depends on Api_engine and Eff_types.
   Properties: its values are recipe roots or pure adapter projections, by construction.
   The engine differential tests both carrier instances through E4_engine.INSTANCE. *)
open Eff_types

module Make
    (M : Api_engine.TABLE)
    (T : Api_engine.TRACE)
    (L : Api_engine.LAYERS)
    (D : Api_engine.DISPATCHER)
    (P : Api_engine.PPATH)
    (E : Api_engine.PENV)
    (F : Api_engine.FIBERS) : sig
  include module type of Api_engine.Make (M) (T) (L) (D) (P) (E) (F)

  type nu = eff_name
  type s = eff_thunk
  type prim_ = (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) prim
  type ffiber = (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) frame_fiber
  type fevent = (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) frame_event

  type machine =
    ( nu
      , s
      , Val.t
      , Err.t
      , Defect.t
      , fiber_id
      , unit
      , ctx
      , stores
      , prim_
      , ffiber
      , fevent )
      run_machine

  type fiber =
    (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit, ctx, prim_, ffiber) run_fiber

  type event =
    (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit, ctx, prim_, fevent) run_event

  (* The tape's decision. `decision` itself is the program's `Decision` (`select`'s carrier),
     generated with the rest of the program types. *)
  type api_decision = (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) run_decision

  type interp =
    (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit, ctx, stores, prim_) run_interp

  (* No program conversion: the generated engine opens `Eff_types`, the one program type of the
     wire and every instance, so no instance names a program type of its own. *)
  type program = NativeOp.t Eff.t

  val interp_of : Row.t list -> program -> interp
  val prepare : Row.t list -> program -> prepared
  val load : program -> fuel:int -> machine
  val step : prepared -> fuel:int -> machine -> api_decision -> machine * bool
  val run_api : Row.t list -> program -> fuel:int -> outcome * machine
  val admit : prepared -> machine -> api_decision -> bool
  val fibers : machine -> (fiber_id * fiber) list
  val fiber_count : machine -> int
  val trace : machine -> event list
  val trace_length : machine -> int
  val stuck_of : machine -> stuck option
  val armed_of : machine -> fiber_id list
  val next_id : machine -> int
  val next_token : machine -> int
  val race_count : machine -> int
  val middleware : machine -> bool
  val finished : machine -> bool

  val completed_exits
    :  machine
    -> (fiber_id * (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t) list

  val stores_of : machine -> stores
  val refs : machine -> Val.t list
  val next_name : machine -> int
  val due_count : machine -> int
  val cell_count : machine -> int
  val scope_count : machine -> int
  val memo_map_count : machine -> int
  val memo_paths : machine -> (int * (int list * int list list) list) list
  val f_id : fiber -> fiber_id
  val f_exit : fiber -> (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t option
  val f_parked : fiber -> parked
  val f_running : fiber -> bool
  val f_finalizing : fiber -> bool
  val f_pending_tokens : fiber -> int list
  val f_observers : fiber -> observer list
  val f_children : fiber -> fiber_id list
  val f_op_count : fiber -> int
  val f_max_ops : fiber -> int
  val f_prevent_yield : fiber -> bool
  val f_yield_override : fiber -> bool option
  val f_context : fiber -> ctx
  val f_dispatcher : fiber -> (int * int) list
end
