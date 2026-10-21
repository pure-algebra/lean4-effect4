(* PRELUDE-BEGIN -- ocaml/engine/tools/api_engine_prelude.ml, spliced verbatim *)
(* ---------------------------------------------------------------------------------------
   The hand rows of the extern table (ocaml/engine/externs.txt), spliced VERBATIM inside
   `Api_engine.Make` by `--prelude`, immediately after the type group.

   Why here and not in a module of its own: every row below applies a *builtin* to a carrier
   field (Lean writes `m.fibers ++ [child]`, `heap.length`, `trace ++ events` inline), so its
   body needs BOTH the carrier parameters `M`/`T`/`L`/`D`/`P`/`E`/`F` and the generated record
   types -- and the records only exist inside the functor.  A separate `e4_shim.ml` cannot see
   them.  `F`'s writes take `~exit_of:sh_fiber_exit` for the same reason from the other side:
   the carrier is a compilation unit and the fiber record is not visible to it (lane G3).
   This file is NOT a compilation unit: it lives under `tools/` so dune never compiles it on
   its own.  Regenerate `ocaml/engine/api_engine.ml` after editing it
   (`ocaml/engine/tools/gen-check.sh`).

   Every row cites the Lean definition it transcribes as `file:line`, and differs from it in
   exactly one way: the carrier operation stands where the list operation stood.

   Properties:
   P1  One row per `fn` row of externs.txt marked `[hand]`; no row has any other caller.
   P2  Each body is Lean's, arm for arm, with `M`/`T`/`L`/`D` for `List`.  A body that needs a
       generated helper takes it as a leading argument, because the prelude is emitted BEFORE
       the declarations (externs.txt spells the helper's name in the row).
   P3  No mutable structure and no exception, except the two `failwith`s below, which fire
       only on a construction the closure does not contain and which say so.
   P4  Record parameters carry an `(_, …, _) t` annotation wherever a field name is claimed by
       more than one generated record (`id`, `state`, `scope`, `key`, `interruptible`, …), so
       OCaml's label disambiguation never has to guess.
   P5  A Lean natural is Zarith's `Z.t` (the `Nat` type row, M4): every natural a row writes is
       `Z.zero`, `Z.one` or `Z.succ`, and every one it compares goes through `Z.equal`.
   --------------------------------------------------------------------------------------- *)

(* -- carriers of a whole store ---------------------------------------------------------- *)

(* Effect4.Machine.Stores.empty, Stores.empty (src/Effect4/Machine/Stores.lean) (`⟨[], ⟨[], []⟩, ⟨[]⟩, [], 0⟩`).
   `scope_store` is a trivial structure, so it IS the carrier; so is `external_store`, whose one
   field is the list of allocated targets (DI-23 deleted the preloaded answers). *)
let sh_stores_empty : stores =
  { refs = M.empty
  ; deferreds = { cells = M.empty; due = [] }
  ; scopes = M.empty
  ; memo = []
  ; timers =
      { now = Z.zero
      ; wake = { waiters = []; batch = None; phase = Z.zero }
      ; target = None
      }
  ; next_name = Z.zero
  ; externals = []
  }
;;

(* Effect4.Machine.RunMachine.empty, RunMachine.empty (src/Effect4/Machine/Fibers.lean), including the empty fork ledger. *)
let sh_machine_empty state =
  { fibers = F.empty
  ; races = []
  ; next_id = Z.zero
  ; next_token = Z.zero
  ; next_race = Z.zero
  ; middleware_installed = false
  ; armed = []
  ; state
  ; trace = T.empty
  ; stuck = None
  ; forks = []
  }
;;

(* A fiber's completion, as the FIBERS carrier's `~exit_of` (lane G3).  The fiber record is
   declared here, inside the functor, and `E4_fibers_view` is a compilation unit beside it, so
   the projection travels as an argument.  It is a field read: the option block it answers is
   the one stored in the record, which is what makes the sharing law FV8 hold for every
   `{ f with … }` that does not touch the exit. *)
let sh_fiber_exit (f : (_, _, _, _, _, _, _, _, _, _) run_fiber) = f.exit_

(* Effect4.Machine.RunMachine.emit, RunMachine.emit (src/Effect4/Machine/Fibers.lean).  The empty guard is
   Lean's own (direction L4); `T.emit [] t == t` makes it redundant, and it is kept so the two
   read alike. *)
let sh_machine_emit m events =
  match events with
  | [] -> m
  | _ -> { m with trace = T.emit events m.trace }
;;

(* Effect4.Machine.RunMachine.fiber?, RunMachine.fiber? (src/Effect4/Machine/Fibers.lean). *)
let sh_machine_fiber m id = F.find_opt id m.fibers

(* Effect4.Machine.RunMachine.update, RunMachine.update (src/Effect4/Machine/Fibers.lean).  Lean's
   replace-by-key map is a NO-OP on an absent id, which is exactly `F.set` (FIBERS FV2). *)
let sh_machine_update m (f : (_, _, _, _, _, _, _, _, _, _) run_fiber) =
  { m with fibers = F.set ~exit_of:sh_fiber_exit f.id f m.fibers }
;;

(* Effect4.Machine.RunMachine.finished, RunMachine.finished (src/Effect4/Machine/Fibers.lean). *)
let sh_machine_finished m =
  F.for_all
    (fun _ (f : (_, _, _, _, _, _, _, _, _, _) run_fiber) -> Option.is_some f.exit_)
    m.fibers
;;

(* Effect4.Machine.RunMachine.completedExits, completedExits (src/Effect4/Machine/Fibers.lean) --
   the ascending filterMap over the fiber table, MAINTAINED (lane G3).

   It is a field read.  The carrier keeps the exited subset as the table is written (FIBERS
   law FV1: `completed t` is that filterMap, for the `~exit_of` every write was given), so
   this row is O(1) and the `(fiber_id * exit) list` it answers is ONE list, shared by every
   step and by every `Point.completed` built from it (FV8) instead of rebuilt per step.

   NOT A MEMO, and that is the point.  Lane PROF's PROF-3 proposed a one-entry memo keyed on
   the physical identity of `m.fibers`; lane G2 built it and measured **0.0 % hits** on
   chain-1000 (3 000 calls), fork-512 (2 051) and fork-128 (520), because every call sees a
   table a `set`/`add` has already rebuilt -- even at one fiber.  The diagnosis stood
   (`filter_map` -> `Map.fold` was 62.7 % inclusive on fan-out 512, lane G2 §6); only the fix
   was wrong.  The view is not keyed on the table: it changes when a fiber's EXIT changes,
   which is at most once per fiber. *)
let sh_machine_completed_exits m = F.completed m.fibers

(* Effect4.Machine.RunFiber.make, RunFiber.make (src/Effect4/Machine/Fibers.lean), with
   `core.start current interruptible` at `frameCore` (src/Effect4/Machine/Fibers.lean), spelled out:
   `Effect4.FrameFiber.start` is `⟨current, [], true, none, false⟩` and `make` overrides
   `interruptible`.  Transcribed rather than called, because the two specialisations of
   `RunFiber.make` were callees of `Api.load` and of `spawn`, which this table deletes, and
   the generic `RunFiber.make` takes the `FiberCore` record — a `@[reducible] instance` that
   the mono phase never emits — as its first argument. *)
let sh_run_fiber_make id current interruptible (budget : Z.t * bool) context =
  { id
  ; frame =
      ({ current
       ; stack = []
       ; interruptible
       ; interrupted_cause = None
       ; deferred_interrupt = false
       }
       : (_, _, _, _, _, _, _) frame_fiber)
  ; running = false
  ; parked = Parked_notParked
  ; pending = []
  ; finalizing = None
  ; exit_ = None
  ; current_op_count = Z.zero
  ; max_ops_before_yield = fst budget
  ; prevent_yield = snd budget
  ; yield_override = None
  ; observers = []
  ; children = []
  ; dispatcher = D.empty
  ; context
  }
;;

(* Effect4.Api.load, load (src/Effect4/Api.lean):
   `{ (RunMachine.empty Stores.empty) with fibers := [RunFiber.make root (compile …) true
      (stores.budgetOf emptyCtx) emptyCtx], nextId := 1 }`; the root has no fork record.
   `compile` (`Program.compile`), `ectx` (`emptyCtx`) and `interp` (`Machine.stores`) are
   generated and come AFTER this prelude, so the row hands them in at the call site; `emit`
   adds the emission-order edge that keeps each of them above its user. *)
let sh_api_load compile ectx interp program fuel =
  let m = sh_machine_empty sh_stores_empty in
  let root =
    sh_run_fiber_make Z.zero (compile program fuel []) true (interp.budget_of ectx) ectx
  in
  { m with fibers = F.add ~exit_of:sh_fiber_exit Z.zero root F.empty; next_id = Z.one }
;;

(* Effect4.Machine.spawn, spawn (src/Effect4/Machine/Fibers.lean): the child and its fork record
   are appended in the same update. One row deletes both of
   its specialisations (`evaluatePrim.withFiber`'s and `launchEntrant`'s). *)
let sh_spawn
      interp
      m
      (parent : (_, _, _, _, _, _, _, _, _, _) run_fiber)
      program
      options
      site
  =
  let child_id = m.next_id in
  let child_interruptible =
    match options.ForkOptions.mask_mode with
    | MaskMode.Interruptible -> true
    | MaskMode.Uninterruptible -> false
    | MaskMode.Inherit ->
      (* `core.interruptible parent.frame` (spawn (src/Effect4/Machine/Fibers.lean)), which the mono phase reads off
         the frame record; the annotation is needed because `interruptible` is also a field of
         `fiber_core`, where it is a function. *)
      (parent.frame : (_, _, _, _, _, _, _) frame_fiber).interruptible
  in
  let child =
    sh_run_fiber_make
      child_id
      program
      child_interruptible
      (interp.budget_of parent.context)
      parent.context
  in
  let m =
    { m with
      fibers = F.add ~exit_of:sh_fiber_exit child_id child m.fibers
    ; next_id = Z.succ m.next_id
    ; forks =
        m.forks
        @ [ ({ child = child_id; parent = parent.id; daemon = options.daemon; site }
             : fork_record)
          ]
    }
  in
  ( sh_machine_emit m [ RunEvent_forked (parent.id, child_id, options.daemon) ]
  , (parent, child_id) )
;;

(* The same at a generic `FiberCore` (`Effect4.Machine.spawn` itself, reached from the
   `driveState`/`stepDecisionState` roots): `core.start`/`core.interruptible` are record
   fields there, and the generic `RunFiber.make` — which takes `core` — is generated, so the
   row hands it in. *)
let sh_spawn_generic
      mk_fiber
      (core : (_, _, _, _, _, _, _, _) fiber_core)
      interp
      m
      (parent : (_, _, _, _, _, _, _, _, _, _) run_fiber)
      program
      options
      site
  =
  let child_id = m.next_id in
  let child_interruptible =
    match options.ForkOptions.mask_mode with
    | MaskMode.Interruptible -> true
    | MaskMode.Uninterruptible -> false
    | MaskMode.Inherit -> core.interruptible parent.frame
  in
  let child =
    mk_fiber
      core
      child_id
      program
      child_interruptible
      (interp.budget_of parent.context)
      parent.context
  in
  let m =
    { m with
      fibers = F.add ~exit_of:sh_fiber_exit child_id child m.fibers
    ; next_id = Z.succ m.next_id
    ; forks =
        m.forks
        @ [ ({ child = child_id; parent = parent.id; daemon = options.daemon; site }
             : fork_record)
          ]
    }
  in
  ( sh_machine_emit m [ RunEvent_forked (parent.id, child_id, options.daemon) ]
  , (parent, child_id) )
;;

(* Effect4.Machine.dropObservers, dropObservers (src/Effect4/Machine/Fibers.lean): the bulk,
   id-preserving map over the fiber table.  The filter in `dropObservers` (src/Effect4/Machine/Fibers.lean) is transcribed
   here rather than called, because its own specialisation is a callee of the map's and is
   deleted with it.  The third argument is `List.mapTR.loop`'s accumulator, always `[]`. *)
let sh_drop_observer_keep token = function
  | Observer_resumeAwait (_, t, _) -> not (Z.equal t token)
  | Observer_countdown (_, t) -> not (Z.equal t token)
  | _ -> true
;;

let sh_drop_observers token fibers (_acc : 'acc list) =
  F.map
    ~exit_of:sh_fiber_exit
    (fun (g : (_, _, _, _, _, _, _, _, _, _) run_fiber) ->
       { g with observers = List.filter (sh_drop_observer_keep token) g.observers })
    fibers
;;

let sh_machine_drop_token m token =
  { m with fibers = sh_drop_observers token m.fibers [] }
;;

(* -- the ref heap ------------------------------------------------------------------------ *)

(* Effect4.Machine.refStep, refStep (src/Effect4/Machine/Stores.lean), arm for arm.
   `refPeek` (`heap[cell.index]?`) is `M.find_opt`; `refPoke` (`heap.set i v`) is `M.set`,
   with an absent index unchanged. Both declarations live in src/Effect4/Machine/Stores.lean.
   `refStep` at `SyncOp.refMake` there returns `(Val.cell ⟨heap.length⟩, heap ++ [initial])`; it
   applies `List.length` and `++` to the carrier inline.  `Val.cell k` is `Val.handle 2 k`.
   A read-modify-write row carries a binder term and its environment (decisions row 43) and
   runs the term at `env ++ [a]`: `eval_term` is `Effect4.Program.evalTerm`, generated below
   this prelude, so the row hands it in.  The row's environment is the point environment
   carrier of the node that performed it (`field Effect4.Machine.SyncOp.env E.t`, externs.txt;
   the state plan's T3b), so `env ++ [a]` is `E.snoc env a`: the term reads its outer binders
   below the current value, at the node's level.  The term's answer is read as Lean's arm
   reads it: the option frames
   (`Store.Image.ofOption Store.Image.ident`: `Val.None`, `Val.Some`) and the two-element
   tuple (`Store.Image.ofTuple2`: `Val.List [b; a]`); any other answer is a frontier. *)
let sh_ref_step eval_term op heap =
  let run env f a = eval_term (E.snoc env a) f in
  let option_of = function
    | Val.None -> Some None
    | Val.Some v -> Some (Some v)
    | _ -> None
  in
  let pair_of = function
    | Val.List [ b; v ] -> Some (b, v)
    | _ -> None
  in
  match op with
  | SyncOp_refMake initial ->
    let k = M.cardinal heap in
    Some (Val.Handle (2, k), M.add k initial heap)
  | SyncOp_refGet cell ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> Some (a, heap))
  | SyncOp_refSet (cell, value) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some _ -> Some (Val.Handle (2, cell), M.set cell value heap))
  | SyncOp_refGetAndSet (cell, value) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> Some (a, M.set cell value heap))
  | SyncOp_refSetAndGet (cell, value) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some _ -> Some (value, M.set cell value heap))
  | SyncOp_refUpdate (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match run env f a with
        | None -> None
        | Some a' -> Some (Val.Unit, M.set cell a' heap)))
  | SyncOp_refGetAndUpdate (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match run env f a with
        | None -> None
        | Some a' -> Some (a, M.set cell a' heap)))
  | SyncOp_refUpdateAndGet (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match run env f a with
        | None -> None
        | Some a' -> Some (a', M.set cell a' heap)))
  | SyncOp_refUpdateSome (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match Option.bind (run env f a) option_of with
        | None -> None
        | Some None -> Some (Val.Unit, heap)
        | Some (Some a') -> Some (Val.Unit, M.set cell a' heap)))
  | SyncOp_refGetAndUpdateSome (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match Option.bind (run env f a) option_of with
        | None -> None
        | Some None -> Some (a, heap)
        | Some (Some a') -> Some (a, M.set cell a' heap)))
  | SyncOp_refUpdateSomeAndGet (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match Option.bind (run env f a) option_of with
        | None -> None
        | Some None -> Some (a, heap)
        | Some (Some a') ->
          let heap' = M.set cell a' heap in
          (match M.find_opt cell heap' with
           | None -> None
           | Some fresh -> Some (fresh, heap'))))
  | SyncOp_refModify (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match Option.bind (run env f a) pair_of with
        | None -> None
        | Some (b, a') -> Some (b, M.set cell a' heap)))
  | SyncOp_refModifySome (cell, f, env) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match Option.bind (run env f a) pair_of with
        | None -> None
        | Some (b, o) ->
          (match option_of o with
           | None -> None
           | Some next ->
             let stored =
               match next with
               | None -> a
               | Some v -> v
             in
             Some (b, M.set cell stored heap))))
  | _ -> None
;;

(* -- the deferred cells ------------------------------------------------------------------ *)

(* Effect4.Machine.DeferredStore.make, DeferredStore.make (src/Effect4/Machine/Stores.lean). *)
let sh_deferred_make (self : _ deferred_store) =
  let k = M.cardinal self.cells in
  ( k
  , { self with
      cells =
        M.add
          k
          { completion = None; wake = { waiters = []; batch = None; phase = Z.zero } }
          self.cells
    } )
;;

(* Effect4.Machine.DeferredStore.cellAt, DeferredStore.cellAt (src/Effect4/Machine/Stores.lean). *)
let sh_deferred_cell_at (self : _ deferred_store) cell = M.find_opt cell self.cells

(* Effect4.Machine.DeferredStore.setCell, DeferredStore.setCell (src/Effect4/Machine/Stores.lean)
   (`cells.set i v`: a no-op out of range, which is `M.set`). *)
let sh_deferred_set_cell (self : _ deferred_store) cell value =
  { self with cells = M.set cell value self.cells }
;;

(* -- the scope entries -------------------------------------------------------------------- *)

(* Effect4.Machine.ScopeStore.entryAt, ScopeStore.entryAt (src/Effect4/Machine/Stores.lean) -- a `find?`
   BY KEY, so `M.find_opt` is exact.  The row names the specialised `List.find?` because
   `entryAt` itself is inlined away by the mono phase. *)
let sh_scope_entry_at key store = M.find_opt key store

(* Effect4.Machine.ScopeStore.setEntry, ScopeStore.setEntry (src/Effect4/Machine/Stores.lean) -- the
   replace-by-key map, a no-op on an absent key. *)
let sh_scope_set_entry store (entry : scope_entry) = M.set entry.key entry store

(* Effect4.Machine.ScopeStore.make, ScopeStore.make (src/Effect4/Machine/Stores.lean).  Scope keys are
   SUPPLY-drawn (`Stores.nextName`), never dense, so this is `add` at a given key and never
   `cardinal` (E4-CHECK-CE-016).  `scope_make` is `Effect4.Scope.make`, an extra root. *)
let sh_scope_store_make scope_make store key strategy =
  M.add key { key; scope = scope_make strategy } store
;;

(* Effect4.Machine.ScopeStore.forkChild, ScopeStore.forkChild (src/Effect4/Machine/Stores.lean).
   `scope_fork` is `Effect4.Scope.fork`, an extra root (its specialisation was a callee of
   this row). *)
let sh_nat_eq (a : Z.t) (b : Z.t) = Z.equal a b

let sh_scope_fork_child scope_fork store parent_key child_key shared_key strategy =
  match M.find_opt parent_key store with
  | None -> store
  | Some (parent : scope_entry) ->
    (* the generic `Scope.fork` keeps the `[DecidableEq κ]` argument the specialisation this
       row deletes had baked in; κ is the finalizer key, a `Nat` (ScopeEntry (src/Effect4/Machine/Stores.lean)). *)
    let parent_scope, child_scope =
      scope_fork
        sh_nat_eq
        parent.scope
        strategy
        shared_key
        (FinName_closeChildScope child_key)
        (FinName_detachFromParent (parent_key, shared_key))
    in
    M.add
      child_key
      { key = child_key; scope = child_scope }
      (M.set parent.key { key = parent.key; scope = parent_scope } store)
;;

(* -- the memo world ----------------------------------------------------------------------- *)

(* The world itself stays a list (engine-a1 §1.2: `syncOpStep`'s memoFork arm appends to it
   inline and `syncOpStep` must stay generated); only `MemoMap.entries` is tabled.
   `MemoWorld.mapAt` and `MemoWorld.setMap` (src/Effect4/Machine/Stores.lean) are transcribed here rather than
   called, because both are list operations over the world and both would otherwise be
   orphaned by the four rows below. *)
let sh_memo_map_at w id = List.find_opt (fun (m : memo_map) -> Z.equal m.id id) w

let sh_memo_set_map w (m : memo_map) =
  List.map (fun (n : memo_map) -> if Z.equal n.id m.id then m else n) w
;;

(* Effect4.Machine.MemoWorld.entryAt, MemoWorld.entryAt (src/Effect4/Machine/Stores.lean). *)
let sh_memo_entry_at w id layer =
  match sh_memo_map_at w id with
  | None -> None
  | Some m -> L.find_opt layer m.entries
;;

(* Effect4.Machine.MemoWorld.updateEntry, MemoWorld.updateEntry (src/Effect4/Machine/Stores.lean). *)
let sh_memo_update_entry w id layer f =
  match sh_memo_map_at w id with
  | None -> w
  | Some m -> sh_memo_set_map w { m with entries = L.update layer f m.entries }
;;

(* Effect4.Machine.MemoWorld.insertEntry, MemoWorld.insertEntry (src/Effect4/Machine/Stores.lean).  Lean
   appends and `find?` answers the FIRST, so "insert keeps an existing binding" (LAYERS) is
   exact for every observation the machine can make (engine-a1 §4.6 MM2). *)
let sh_memo_insert_entry w id layer entry =
  match sh_memo_map_at w id with
  | None -> w
  | Some m -> sh_memo_set_map w { m with entries = L.insert layer entry m.entries }
;;

(* Effect4.Machine.MemoWorld.deleteEntry, MemoWorld.deleteEntry (src/Effect4/Machine/Stores.lean). *)
let sh_memo_delete_entry w id layer =
  match sh_memo_map_at w id with
  | None -> w
  | Some m -> sh_memo_set_map w { m with entries = L.delete layer m.entries }
;;

(* -- the point's position and environment (lane G2) ---------------------------------------- *)

(* Effect4.Program.Node.at_, Node.at_ (src/Effect4/Program/Refs.lean), applied to a path that
   is now a carrier.  The spine already holds the node it addresses, computed one `Node.child`
   at a time as the path grew (`P.snoc`), so the walk is a field read -- PROVIDED the node the
   caller passes is the one the spine was rooted at.  Every one of the eleven call sites
   passes `Node.eff root` for the same `root`, but the block is freshly allocated each time,
   so the test is on the root program INSIDE it; when it does not hold, the row walks, which
   is Lean's own definition.

   LAW NODE-AT  sh_node_at c n p = Node.at_ n (P.to_list p)   for every n and p.
   Proof: if the test holds, `P.node c p = walk c (P.root p) (P.to_list p)` (PPATH PP3) and
   `P.root p` is `n` up to the reallocated constructor; otherwise it is `P.walk`, which IS
   `Node.at_`. *)
let sh_node_at child (n : NativeOp.t node) (p : NativeOp.t node P.t)
  : NativeOp.t node option
  =
  match n, P.root p with
  | Node_eff a, Node_eff b when a == b -> P.node child p
  | _ -> P.walk child n (P.to_list p)
;;

(* Effect4.Program.rootPoint, src/Effect4/Program/Compile.lean
   (`{ path := [], env := [], fuel, tape }`: the completed view, the root index, the stack of
   passed programs (decisions row 340) and the running call (row 341, step 3) start empty).
   The spine has to be told which program it addresses, and the generated `rootPoint` is not: `Program.compile` -- its only caller -- holds the root
   under that name, so the row hands it in. *)
let sh_root_point (root : NativeOp.t Eff.t) (fuel : Z.t) (tape : bool list) : point =
  ({ path = P.make (Node_eff root)
   ; env = E.empty
   ; fuel
   ; tape
   ; completed = []
   ; root = Z.zero
   ; params = []
   ; call = []
   }
   : point)
;;

(* Effect4.Program.Point.redirect, src/Effect4/Program/Refs.lean *)
let sh_point_redirect child (p : point) target : point =
  { p with
    path = P.append child (P.make (P.root p.path)) target
  ; fuel = Lcnf_nat.sub p.fuel Z.one
  }
;;

(* -- carrier constructors the mono phase inlines ------------------------------------------ *)

(* `MemoMap.mk` with `entries := []`: `syncOpStep`'s memoFork arm builds one inline
   (syncOpStep (src/Effect4/Machine/Stores.lean)) and `syncOpStep` stays generated, so the
   construction — not a function — is what the row replaces.  Any other entry list is a hole
   in the table, and says so rather than answering. *)
let sh_memo_map_mk id parent entries =
  match entries with
  | [] -> ({ id; parent; entries = L.empty } : memo_map)
  | _ ->
    failwith
      "api_engine: MemoMap.mk with a non-empty entry list (extern table incomplete)"
;;

(* The one-field Lean dispatcher lowers to its bucket list. *)
let sh_dispatcher_insert priority task dispatcher = D.enqueue dispatcher ~priority task

(* PRELUDE-END *)
