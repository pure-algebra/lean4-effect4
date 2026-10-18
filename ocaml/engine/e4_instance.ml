(* E4_instance -- the generated engine over one set of carriers, with the adapter that makes
   it an `E4_engine.INSTANCE`.

     E4_instance.Make (M) (T) (L) (D) (P) (E) (F)  =  Api_engine.Make (M) (T) (L) (D) (P) (E) (F)
                                                      + the adapter

   What it is: the ADAPTER every instance of `Api_engine` needs -- the type abbreviations for
   the fully applied machine and the free-row projections of `E4_engine.INSTANCE` -- written
   once, as a functor over what varies between the instances: the seven carriers the generated
   functor takes.  A projection that reads a carrier reads it through the carrier's module type
   (`F.bindings`, `T.to_list`, `M.to_list`, `L.bindings`, `D.to_list`), so no line here names a
   carrier module, and each instance file is one application, its name and its carriers string:

     api_engine_inst.ml  Fast  E4_table, E4_trace, E4_memo, E4_buckets, E4_ppath, E4_env,
                               E4_fibers_view
     api_engine_ref.ml   Ref   the seven list twins, Lean's own carriers

   Everything else -- the drive loop, the answer alphabet, every renderer -- is written ONCE in
   `E4_engine.Make`, which ascribes `E4_engine.INSTANCE` to each instance.  The result exposes the generated roots and the adapter projections through e4_instance.mli.
   Tests also read retained prelude declarations through an instance (`sh_spawn`, `fork_record`,
   the timer store).

   The third instance, `test/api_gen_inst.ml`, is not an application of this functor.  Its
   oracle `Effect4_gen.Api_gen` is a second generated file, not `Api_engine.Make` over carriers,
   and its records hold Lean's lists directly (`fibers : run_fiber list`, `trace : run_event
   list`, `refs : val_ list`).  A functor over both would need those record types written out by
   hand, so that file keeps its own projections.

   Depends on: Api_engine (generated), Eff_types.

   Behaviours:
   I1  Every projection is a pure function of the machine value: no fuel, no tape, no
       mutation (INV-TAPE-1, brief §2.4; E4_engine EN7).            by construction
   I2  `fibers`, `completed_exits` and `refs` are ASCENDING by key: api_engine.ml's TABLE and
       FIBERS signatures ask `bindings` and `completed` ascending, and every carrier given here
       answers so -- E4_table T4 (its `to_list` is the values of `bindings`), E4_fibers_view
       FV5 and FV1 (the maintained completed view is the same ascending filterMap), and the
       twins' TL2 and TFV2 -- so the differential between two instances compares like with
       like.                                                        by construction
   I3  `trace` is in emission order: `T.to_list` is, for both trace carriers (E4_trace TR1;
       E4_trace_list TLT1 and TLT2).                                by construction
   I4  `step` is the generated `stepDecisionState`, and its second component is the
       generated `settled` -- the discriminator the answer alphabet needs (owner default
       A1-Q7).                                                      by construction *)

open Eff_types

module Make
    (M : Api_engine.TABLE)
    (T : Api_engine.TRACE)
    (L : Api_engine.LAYERS)
    (D : Api_engine.DISPATCHER)
    (P : Api_engine.PPATH)
    (E : Api_engine.PENV)
    (F : Api_engine.FIBERS) =
struct
  include Api_engine.Make (M) (T) (L) (D) (P) (E) (F)

  (* -- the fully applied machine ----------------------------------------------------- *)

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

  let prepare (table : Row.t list) (p : program) : prepared =
    program_prepared_make p table
  ;;

  (* -- loading and stepping ----------------------------------------------------------- *)

  let interp_of (table : Row.t list) (p : program) : interp = program_interp_of p table

  let load (p : program) ~(fuel : int) : machine =
    sh_api_load program_compile empty_ctx stores p fuel
  ;;

  (* The prepared package retains the interpreter and native evaluator. *)
  let step (prepared : prepared) ~(fuel : int) (m : machine) (d : api_decision)
    : machine * bool
    =
    program_prepared_step prepared fuel m d
  ;;

  let run_api (table : Row.t list) (p : program) ~(fuel : int) : outcome * machine =
    let r = api_run p fuel table fuel in
    r.outcome, r.machine
  ;;

  (* The machine's admission at the application of this row table: the wire carries no named
     type, so the application declares none (decisions row 407 (5)). *)
  let admit (prepared : prepared) (m : machine) (d : api_decision) : bool =
    Option.is_none (program_prepared_admit prepared m d)
  ;;

  (* -- the free rows ------------------------------------------------------------------ *)

  let fibers (m : machine) : (fiber_id * fiber) list = F.bindings m.fibers
  let fiber_count (m : machine) : int = F.cardinal m.fibers
  let trace (m : machine) : event list = T.to_list m.trace
  let trace_length (m : machine) : int = T.length m.trace
  let stuck_of (m : machine) : stuck option = m.stuck
  let armed_of (m : machine) : fiber_id list = m.armed
  let next_id (m : machine) : int = m.next_id
  let next_token (m : machine) : int = m.next_token
  let race_count (m : machine) : int = List.length m.races
  let middleware (m : machine) : bool = m.middleware_installed
  let finished (m : machine) : bool = sh_machine_finished m

  let completed_exits (m : machine)
    : (fiber_id * (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t) list
    =
    sh_machine_completed_exits m
  ;;

  let stores_of (m : machine) : stores = m.state
  let refs (m : machine) : Val.t list = M.to_list (stores_of m).refs
  let next_name (m : machine) : int = (stores_of m).next_name
  let due_count (m : machine) : int = List.length (stores_of m).deferreds.due
  let cell_count (m : machine) : int = M.cardinal (stores_of m).deferreds.cells
  let scope_count (m : machine) : int = M.cardinal (stores_of m).scopes
  let memo_map_count (m : machine) : int = List.length (stores_of m).memo

  let memo_paths (m : machine) : (int * (int list * int list list) list) list =
    List.map
      (fun (mm : memo_map) -> mm.id, List.map fst (L.bindings mm.entries))
      (stores_of m).memo
  ;;

  (* -- the fiber's own fields --------------------------------------------------------- *)

  let f_id (f : fiber) : fiber_id = f.id

  let f_exit (f : fiber) : (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t option =
    f.exit_
  ;;

  let f_parked (f : fiber) : parked = f.parked
  let f_running (f : fiber) : bool = f.running
  let f_finalizing (f : fiber) : bool = Option.is_some f.finalizing

  let f_pending_tokens (f : fiber) : int list =
    List.map (fun (p : (_, _, _, _, _, _) pending) -> p.token) f.pending
  ;;

  let f_observers (f : fiber) : observer list = f.observers
  let f_children (f : fiber) : fiber_id list = f.children
  let f_op_count (f : fiber) : int = f.current_op_count
  let f_max_ops (f : fiber) : int = f.max_ops_before_yield
  let f_prevent_yield (f : fiber) : bool = f.prevent_yield
  let f_yield_override (f : fiber) : bool option = f.yield_override
  let f_context (f : fiber) : ctx = f.context

  let f_dispatcher (f : fiber) : (int * int) list =
    List.map (fun (p, ts) -> p, List.length ts) (D.to_list f.dispatcher)
  ;;
end
