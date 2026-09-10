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
   --------------------------------------------------------------------------------------- *)

(* -- carriers of a whole store ---------------------------------------------------------- *)

(* Effect4.Machine.Stores.empty, src/Effect4/Machine/Stores.lean:1987 (`⟨[], ⟨[], []⟩, ⟨[]⟩, [], 0⟩`).
   `scope_store` is a trivial structure, so it IS the carrier. *)
let sh_stores_empty : stores =
  { refs = M.empty;
    deferreds = { cells = M.empty; due = [] };
    scopes = M.empty;
    memo = [];
    timers = { now = 0; wake = { waiters = []; batch = None; phase = 0 }; target = None };
    next_name = 0;
    externals = { answers = []; allocated = []; rejected = None } }

(* Effect4.Machine.RunMachine.empty, src/Effect4/Machine/Fibers.lean:612-622. *)
let sh_machine_empty state =
  { fibers = F.empty; races = []; next_id = 0; next_token = 0; next_race = 0;
    middleware_installed = false; armed = []; state; trace = T.empty; stuck = None }

(* A fiber's completion, as the FIBERS carrier's `~exit_of` (lane G3).  The fiber record is
   declared here, inside the functor, and `E4_fibers_view` is a compilation unit beside it, so
   the projection travels as an argument.  It is a field read: the option block it answers is
   the one stored in the record, which is what makes the sharing law FV8 hold for every
   `{ f with … }` that does not touch the exit. *)
let sh_fiber_exit (f : (_, _, _, _, _, _, _, _, _, _) run_fiber) = f.exit_

(* Effect4.Machine.RunMachine.emit, src/Effect4/Machine/Fibers.lean:585-587.  The empty guard is
   Lean's own (direction L4); `T.emit [] t == t` makes it redundant, and it is kept so the two
   read alike. *)
let sh_machine_emit m events =
  match events with [] -> m | _ -> { m with trace = T.emit events m.trace }

(* Effect4.Machine.RunMachine.fiber?, src/Effect4/Machine/Fibers.lean:573-575. *)
let sh_machine_fiber m id = F.find_opt id m.fibers

(* Effect4.Machine.RunMachine.update, src/Effect4/Machine/Fibers.lean:577-579.  Lean's
   replace-by-key map is a NO-OP on an absent id, which is exactly `F.set` (FIBERS FV2). *)
let sh_machine_update m (f : (_, _, _, _, _, _, _, _, _, _) run_fiber) =
  { m with fibers = F.set ~exit_of:sh_fiber_exit f.id f m.fibers }

(* Effect4.Machine.RunMachine.finished, src/Effect4/Machine/Fibers.lean:608-609. *)
let sh_machine_finished m =
  F.for_all (fun _ (f : (_, _, _, _, _, _, _, _, _, _) run_fiber) -> Option.is_some f.exit_)
    m.fibers

(* Effect4.Machine.RunMachine.completedExits, src/Effect4/Machine/Fibers.lean:1543 --
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

(* Effect4.Machine.RunFiber.make, src/Effect4/Machine/Fibers.lean:252-268, with
   `core.start current interruptible` at the `frameCore` instance (:196) spelled out:
   `Effect4.FrameFiber.start` is `⟨current, [], true, none, false⟩` and `make` overrides
   `interruptible`.  Transcribed rather than called, because the two specialisations of
   `RunFiber.make` were callees of `Api.load` and of `spawn`, which this table deletes, and
   the generic `RunFiber.make` takes the `FiberCore` record — a `@[reducible] instance` that
   the mono phase never emits — as its first argument. *)
let sh_run_fiber_make id current interruptible (budget : int * bool) context =
  { id;
    frame = ({ current; stack = []; interruptible; interrupted_cause = None;
               deferred_interrupt = false } : (_, _, _, _, _, _, _) frame_fiber);
    running = false; parked = Parked_notParked; pending = []; finalizing = None;
    exit_ = None; current_op_count = 0;
    max_ops_before_yield = fst budget; prevent_yield = snd budget; yield_override = None;
    observers = []; children = []; dispatcher = D.empty; context }

(* Effect4.Api.load, src/Effect4/Api.lean:137-140:
   `{ (RunMachine.empty Stores.empty) with fibers := [RunFiber.make root (compile …) true
      (stores.budgetOf emptyCtx) emptyCtx], nextId := 1 }`.
   `compile` (`Program.compile`), `ectx` (`emptyCtx`) and `interp` (`Machine.stores`) are
   generated and come AFTER this prelude, so the row hands them in at the call site; `emit`
   adds the emission-order edge that keeps each of them above its user. *)
let sh_api_load compile ectx interp program fuel choices answers =
  let stores = { sh_stores_empty with externals = { answers; allocated = []; rejected = None } } in
  let m = sh_machine_empty stores in
  let root = sh_run_fiber_make 0 (compile program fuel choices) true (interp.budget_of ectx) ectx in
  { m with fibers = F.add ~exit_of:sh_fiber_exit 0 root F.empty; next_id = 1 }

(* Effect4.Machine.spawn, src/Effect4/Machine/Fibers.lean:863-878.  One row deletes both of
   its specialisations (`evaluatePrim.withFiber`'s and `launchEntrant`'s). *)
let sh_spawn interp m (parent : (_, _, _, _, _, _, _, _, _, _) run_fiber) program options =
  let child_id = m.next_id in
  let child_interruptible =
    match options.mask_mode with
    | MaskMode_interruptible -> true
    | MaskMode_uninterruptible -> false
    | MaskMode_inherit ->
      (* `core.interruptible parent.frame` (Fibers.lean:872), which the mono phase reads off
         the frame record; the annotation is needed because `interruptible` is also a field of
         `fiber_core`, where it is a function. *)
      (parent.frame : (_, _, _, _, _, _, _) frame_fiber).interruptible
  in
  let child =
    sh_run_fiber_make child_id program child_interruptible (interp.budget_of parent.context)
      parent.context
  in
  let m =
    { m with fibers = F.add ~exit_of:sh_fiber_exit child_id child m.fibers;
      next_id = m.next_id + 1 }
  in
  (sh_machine_emit m [ RunEvent_forked (parent.id, child_id, options.daemon) ],
   (parent, child_id))

(* The same at a generic `FiberCore` (`Effect4.Machine.spawn` itself, reached from the
   `driveState`/`stepDecisionState` roots): `core.start`/`core.interruptible` are record
   fields there, and the generic `RunFiber.make` — which takes `core` — is generated, so the
   row hands it in. *)
let sh_spawn_generic mk_fiber (core : (_, _, _, _, _, _, _, _) fiber_core) interp m
    (parent : (_, _, _, _, _, _, _, _, _, _) run_fiber) program options =
  let child_id = m.next_id in
  let child_interruptible =
    match options.mask_mode with
    | MaskMode_interruptible -> true
    | MaskMode_uninterruptible -> false
    | MaskMode_inherit -> core.interruptible parent.frame
  in
  let child =
    mk_fiber core child_id program child_interruptible (interp.budget_of parent.context)
      parent.context
  in
  let m =
    { m with fibers = F.add ~exit_of:sh_fiber_exit child_id child m.fibers;
      next_id = m.next_id + 1 }
  in
  (sh_machine_emit m [ RunEvent_forked (parent.id, child_id, options.daemon) ],
   (parent, child_id))

(* Effect4.Machine.dropObservers, src/Effect4/Machine/Fibers.lean:1341-1349: the bulk,
   id-preserving map over the fiber table.  The observer filter (:1345-1348) is transcribed
   here rather than called, because its own specialisation is a callee of the map's and is
   deleted with it.  The third argument is `List.mapTR.loop`'s accumulator, always `[]`. *)
let sh_drop_observer_keep token = function
  | Observer_resumeAwait (_, t, _) -> t <> token
  | Observer_countdown (_, t) -> t <> token
  | _ -> true

let sh_drop_observers token fibers (_acc : 'acc list) =
  F.map ~exit_of:sh_fiber_exit
    (fun (g : (_, _, _, _, _, _, _, _, _, _) run_fiber) ->
       { g with observers = List.filter (sh_drop_observer_keep token) g.observers })
    fibers

(* -- the ref heap ------------------------------------------------------------------------ *)

(* Effect4.Machine.refStep, src/Effect4/Machine/Stores.lean:1149-1186, arm for arm.
   `refPeek` (:1116, `heap[cell.index]?`) is `M.find_opt` and `refPoke` (:1119-1120,
   `heap.set i v`, a NO-OP out of range) is `M.set`; `refMake` (:1150,
   `(Val.cell ⟨heap.length⟩, heap ++ [initial])`) is the one arm that forced this row -- it
   applies `List.length` and `++` to the carrier inline.  `Val.cell k` is `Val.handle 2 k`.
   `total`, `partial_update`, `modify` and `modify_some` are `Effect4.Machine.FnName.*`,
   generated below this prelude, so the row hands them in. *)
let sh_ref_step total partial_update modify modify_some op heap =
  match op with
  | SyncOp_refMake initial ->
    let k = M.cardinal heap in
    Some (Val_handle (2, k), M.add k initial heap)
  | SyncOp_refGet cell ->
    (match M.find_opt cell heap with None -> None | Some a -> Some (a, heap))
  | SyncOp_refSet (cell, value) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some _ -> Some (Val_handle (2, cell), M.set cell value heap))
  | SyncOp_refGetAndSet (cell, value) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> Some (a, M.set cell value heap))
  | SyncOp_refSetAndGet (cell, value) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some _ -> Some (value, M.set cell value heap))
  | SyncOp_refUpdate (cell, f) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> Some (Val_unit, M.set cell (total f a) heap))
  | SyncOp_refGetAndUpdate (cell, f) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> Some (a, M.set cell (total f a) heap))
  | SyncOp_refUpdateAndGet (cell, f) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> let a' = total f a in Some (a', M.set cell a' heap))
  | SyncOp_refUpdateSome (cell, pf) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match partial_update pf a with
        | None -> Some (Val_unit, heap)
        | Some a' -> Some (Val_unit, M.set cell a' heap)))
  | SyncOp_refGetAndUpdateSome (cell, pf) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match partial_update pf a with
        | None -> Some (a, heap)
        | Some a' -> Some (a, M.set cell a' heap)))
  | SyncOp_refUpdateSomeAndGet (cell, pf) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       (match partial_update pf a with
        | None -> Some (a, heap)
        | Some a' ->
          let heap' = M.set cell a' heap in
          (match M.find_opt cell heap' with
           | None -> None
           | Some fresh -> Some (fresh, heap'))))
  | SyncOp_refModify (cell, f) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a -> let (b, a') = modify f a in Some (b, M.set cell a' heap))
  | SyncOp_refModifySome (cell, pf) ->
    (match M.find_opt cell heap with
     | None -> None
     | Some a ->
       let (b, a') = modify_some pf a in
       let stored = match a' with None -> a | Some v -> v in
       Some (b, M.set cell stored heap))
  | _ -> None

(* -- the deferred cells ------------------------------------------------------------------ *)

(* Effect4.Machine.DeferredStore.make, src/Effect4/Machine/Stores.lean:1365-1366. *)
let sh_deferred_make (self : deferred_store) =
  let k = M.cardinal self.cells in
  (k, { self with cells = M.add k { completion = None; wake = { waiters = []; batch = None; phase = 0 } } self.cells })

(* Effect4.Machine.DeferredStore.cellAt, src/Effect4/Machine/Stores.lean:1369-1370. *)
let sh_deferred_cell_at (self : deferred_store) cell = M.find_opt cell self.cells

(* Effect4.Machine.DeferredStore.setCell, src/Effect4/Machine/Stores.lean:1373-1374
   (`cells.set i v`: a no-op out of range, which is `M.set`). *)
let sh_deferred_set_cell (self : deferred_store) cell value =
  { self with cells = M.set cell value self.cells }

(* -- the scope entries -------------------------------------------------------------------- *)

(* Effect4.Machine.ScopeStore.entryAt, src/Effect4/Machine/Stores.lean:1567-1568 -- a `find?`
   BY KEY, so `M.find_opt` is exact.  The row names the specialised `List.find?` because
   `entryAt` itself is inlined away by the mono phase. *)
let sh_scope_entry_at key store = M.find_opt key store

(* Effect4.Machine.ScopeStore.setEntry, src/Effect4/Machine/Stores.lean:1571-1572 -- the
   replace-by-key map, a no-op on an absent key. *)
let sh_scope_set_entry store (entry : scope_entry) = M.set entry.key entry store

(* Effect4.Machine.ScopeStore.make, src/Effect4/Machine/Stores.lean:1575-1576.  Scope keys are
   SUPPLY-drawn (`Stores.nextName`), never dense, so this is `add` at a given key and never
   `cardinal` (E4-CHECK-CE-016).  `scope_make` is `Effect4.Scope.make`, an extra root. *)
let sh_scope_store_make scope_make store key strategy =
  M.add key { key; scope = scope_make strategy } store

(* Effect4.Machine.ScopeStore.forkChild, src/Effect4/Machine/Stores.lean:1597-1607.
   `scope_fork` is `Effect4.Scope.fork`, an extra root (its specialisation was a callee of
   this row). *)
let sh_int_eq (a : int) (b : int) = a = b

let sh_scope_fork_child scope_fork store parent_key child_key shared_key strategy =
  match M.find_opt parent_key store with
  | None -> store
  | Some (parent : scope_entry) ->
    (* the generic `Scope.fork` keeps the `[DecidableEq κ]` argument the specialisation this
       row deletes had baked in; κ is the finalizer key, a `Nat` (Stores.lean:1542). *)
    let (parent_scope, child_scope) =
      scope_fork sh_int_eq parent.scope strategy shared_key
        (FinName_closeChildScope child_key)
        (FinName_detachFromParent (parent_key, shared_key))
    in
    M.add child_key { key = child_key; scope = child_scope }
      (M.set parent.key { key = parent.key; scope = parent_scope } store)

(* -- the memo world ----------------------------------------------------------------------- *)

(* The world itself stays a list (engine-a1 §1.2: `syncOpStep`'s memoFork arm appends to it
   inline and `syncOpStep` must stay generated); only `MemoMap.entries` is tabled.
   `mapAt` (Stores.lean:859-860) and `setMap` (:862-863) are transcribed here rather than
   called, because both are list operations over the world and both would otherwise be
   orphaned by the four rows below. *)
let sh_memo_map_at w id = List.find_opt (fun (m : memo_map) -> m.id = id) w
let sh_memo_set_map w (m : memo_map) =
  List.map (fun (n : memo_map) -> if n.id = m.id then m else n) w

(* Effect4.Machine.MemoWorld.entryAt, src/Effect4/Machine/Stores.lean:866-867. *)
let sh_memo_entry_at w id layer =
  match sh_memo_map_at w id with None -> None | Some m -> L.find_opt layer m.entries

(* Effect4.Machine.MemoWorld.updateEntry, src/Effect4/Machine/Stores.lean:869-873. *)
let sh_memo_update_entry w id layer f =
  match sh_memo_map_at w id with
  | None -> w
  | Some m -> sh_memo_set_map w { m with entries = L.update layer f m.entries }

(* Effect4.Machine.MemoWorld.insertEntry, src/Effect4/Machine/Stores.lean:876-880.  Lean
   appends and `find?` answers the FIRST, so "insert keeps an existing binding" (LAYERS) is
   exact for every observation the machine can make (engine-a1 §4.6 MM2). *)
let sh_memo_insert_entry w id layer entry =
  match sh_memo_map_at w id with
  | None -> w
  | Some m -> sh_memo_set_map w { m with entries = L.insert layer entry m.entries }

(* Effect4.Machine.MemoWorld.deleteEntry, src/Effect4/Machine/Stores.lean:883-886. *)
let sh_memo_delete_entry w id layer =
  match sh_memo_map_at w id with
  | None -> w
  | Some m -> sh_memo_set_map w { m with entries = L.delete layer m.entries }

(* -- the point's position and environment (lane G2) ---------------------------------------- *)

(* Effect4.Program.Node.at_, src/Effect4/Program/Compile.lean:118-122, applied to a path that
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
let sh_node_at child (n : native_op node) (p : native_op node P.t) : native_op node option =
  match n, P.root p with
  | Node_eff a, Node_eff b when a == b -> P.node child p
  | _ -> P.walk child n (P.to_list p)

(* Effect4.Program.rootPoint, src/Effect4/Program/Compile.lean:1490-1491
   (`⟨[], [], fuel, tape, [], 0⟩`).  The spine has to be told which program it addresses, and
   the generated `rootPoint` is not: `Program.compile` -- its only caller -- holds the root
   under that name, so the row hands it in. *)
let sh_root_point (root : native_op eff) (fuel : int) (tape : bool list) : point =
  ({ path = P.make (Node_eff root); env = E.empty; fuel; tape; completed = []; root = 0 }
   : point)

(* Effect4.Program.Point.redirect, src/Effect4/Program/Refs.lean *)
let sh_point_redirect child (p : point) target : point =
  { p with
    path = P.append child (P.make (P.root p.path)) target;
    fuel = max 0 (p.fuel - 1) }

(* -- carrier constructors the mono phase inlines ------------------------------------------ *)

(* `MemoMap.mk` with `entries := []`: `syncOpStep`'s memoFork arm builds one inline
   (src/Effect4/Machine/Stores.lean:2238) and `syncOpStep` stays generated, so the
   construction — not a function — is what the row replaces.  Any other entry list is a hole
   in the table, and says so rather than answering. *)
let sh_memo_map_mk id parent entries =
  match entries with
  | [] -> ({ id; parent; entries = L.empty } : memo_map)
  | _ -> failwith "api_engine: MemoMap.mk with a non-empty entry list (extern table incomplete)"

(* `Dispatcher.mk`: the only construction left in the closure is `⟨[], false⟩`, the second
   component of `Dispatcher.drain` (src/Effect4/Machine/Fibers.lean:153), which the mono phase
   inlines into `fireState` (a function that must stay generated). *)
let sh_dispatcher_mk buckets armed =
  match buckets, armed with
  | [], false -> D.empty
  | _ -> failwith "api_engine: Dispatcher.mk with a non-empty bucket list (extern table incomplete)"

(* PRELUDE-END *)
