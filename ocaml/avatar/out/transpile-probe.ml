let rec insert priority task x0 =
  match x0 with
    | [] -> [{ priority = priority; tasks = [task] }]
    | bucket :: rest -> if bucket.priority = priority then { priority = bucket.priority; tasks = bucket.tasks @ [task] } :: rest else if priority < bucket.priority then { priority = priority; tasks = [task] } :: bucket :: rest else bucket :: insert priority task rest

let rec enqueue d priority task =
  { buckets = insert priority task d.buckets; armed = true }

let rec drain d =
  List.concat (List.map tasks d.buckets), { buckets = []; armed = false }

let rec empty =
  { buckets = []; armed = false }

let rec arm m owner =
  m.armed <- (if List.mem owner m.armed then m.armed else m.armed @ [owner]);
  m

let rec disarm m owner =
  m.armed <- List.filter (fun x -> x <> owner) m.armed;
  m

let rec countdown_walk m x0 x1 =
  match x0, x1 with
    | [], exits -> exits, None
    | (t :: rest), exits -> (match fiber_opt m t with
        | None -> countdown_walk m rest exits
        | Some g -> (match g.exit_ with
            | Some exit_ -> countdown_walk m rest (exits @ [exit_])
            | None -> exits, Some (t, rest)))

let rec runloop_top f =
  if f.frame.deferred_interrupt then (f.frame.deferred_interrupt <- false;
    f.frame.current <- failure f.frame.pending_cause;
    f) else f

let rec count_op f =
  f.current_op_count <- f.current_op_count + 1;
  f

let rec yield_verdict f =
  match f.yield_override with
    | Some x -> x
    | None -> f.current_op_count >= f.max_ops_before_yield

let rec interrupt_each interp who extra targets acc =
  List.fold_left (fun a t -> match fiber_opt (fst a) t with
    | None -> a
    | Some g -> (let g, apply_now = interrupt_record interp (Some who) extra g in
      let m = emit (fst a) [InterruptRecorded (Some who, t)] in
      m, snd a @ (if apply_now then [Cevaluate t] else []))) acc targets

let rec start m parent child immediately =
  if immediately then m, parent, [Cevaluate child] else (let parent = { parent with dispatcher = Dispatcher.enqueue parent.dispatcher 0 (Tstart child) } in
    emit (arm m parent.id) [ScheduledTask (parent.id, 0, Tstart child)], parent, [])

let rec launch_entrant interp race_id m host program =
  let m, _, child = spawn interp m host program { start_immediately = true; daemon = true; mask_mode = Minterruptible } in
  ((match fiber_opt m child with
    | Some c -> ignore { c with observers = c.observers @ [RaceCallback race_id] };
      ()
    | None -> ());
  m), child

let rec spawn interp m parent program options =
  let child_id = m.next_id in
  let child_interruptible = match options.mask_mode with
    | Minterruptible -> true
    | Muninterruptible -> false
    | Minherit -> parent.frame.interruptible in
  let child = run_fiber_make child_id program child_interruptible (budget_of interp parent.context) parent.context in
  let child = if options.daemon then child else { child with observers = [UntrackChild parent.id] } in
  let parent = { parent with children = if options.daemon then parent.children else parent.children @ [child_id] } in
  let m = { m with fibers = m.fibers @ [child]; next_id = m.next_id + 1 } in
  emit m [Forked (parent.id, child_id, options.daemon)], parent, child_id

let rec link_scope interp m mode scope key target interruptor extra =
  match scope_status interp scope m.state with
    | None -> halt m (UnknownScope scope), []
    | Some (Some _) -> (match fiber_opt m target with
        | None -> halt m (UnknownFiber target), []
        | Some t -> (let t, apply_now = interrupt_record interp interruptor extra t in
          let m = emit m [ScopeClosedOnLink (scope, target); InterruptRecorded (interruptor, target)] in
          m, (if apply_now then [Cevaluate target] else [])))
    | Some None -> (match fiber_opt m target with
        | None -> halt m (UnknownFiber target), []
        | Some t -> if t.exit_ <> None then m, [] else (match scope_link_fiber interp mode scope key target m.state with
              | None -> halt m (UnknownScope scope), []
              | Some state -> (let m = { m with state = state } in
                let m = (match fiber_opt m target with
                  | Some t -> ignore { t with observers = t.observers @ [DropScopeFinalizer (scope, key)] };
                    ()
                  | None -> ());
                m in
                emit m [ScopeLinked (mode, scope, key, target)], [])))

let rec step_decision interp fuel m x0 =
  match x0 with
    | Dfire owner -> fire interp fuel m owner
    | Dflush -> flush_all interp fuel fuel m
    | Devaluate id -> drive interp fuel m [Cevaluate id; CdrainDue]
    | DyieldVerdict (id, verdict) -> (match fiber_opt m id with
        | Some f -> ignore { f with yield_override = Some verdict };
          ()
        | None -> ());
      m
    | DanswerAsync (id, token, answer) -> drive interp fuel m [Cresume (id, token, answer); CdrainDue]
    | DinterruptFrom (interruptor, annotations, target) -> (match fiber_opt m target with
        | None -> m
        | Some t -> (let t, apply_now = interrupt_record interp interruptor annotations t in
          let m = emit m [InterruptRecorded (interruptor, target)] in
          let m = if t.frame.deferred_interrupt && t.running then emit m [InterruptDeferred target] else m in
          let m = m in
          if apply_now then drive interp fuel m [Cevaluate target; CdrainDue] else m))
    | DinstallMiddleware -> { m with middleware_installed = true }

and fire interp fuel m owner =
  match fiber_opt m owner with
    | None -> m
    | Some o -> (let tasks, dispatcher = Dispatcher.drain o.dispatcher in
      let m = disarm m owner in
      List.fold_left (fun m task -> let m = emit m [RanTask (owner, task)] in
      match task with
        | Tstart child -> drive interp fuel m [Cevaluate child; CdrainDue]
        | Tresume (target, token, answer) -> drive interp fuel m [Cresume (target, token, answer); CdrainDue]) m tasks)

and flush_all interp fuel x0 x1 =
  match x0, x1 with
    | 0, m -> m
    | rounds, m when rounds > 0 -> (let rounds = rounds - 1 in
      match m.armed with
        | [] -> m
        | owner :: _ -> if m.stuck <> None then m else flush_all interp fuel rounds (fire interp fuel m owner))

and flush_root interp fuel root x0 x1 =
  match x0, x1 with
    | 0, m -> m
    | rounds, m when rounds > 0 -> (let rounds = rounds - 1 in
      match fiber_opt m root with
        | None -> m
        | Some o -> if o.dispatcher.buckets = [] || m.stuck <> None then m else flush_root interp fuel root rounds (fire interp fuel m root))

let rec interrupt_record interp interruptor extra f =
  if f.exit_ <> None then f, false else (let cause = cause_annotate (cause_interrupt interp.encode_fiber interruptor (stack_annotations interp f.id)) extra false in
    let accumulated = match f.frame.interrupted_cause with
      | None -> cause
      | Some previous -> cause_combine previous cause in
    f.frame.interrupted_cause <- Some accumulated;
    if f.frame.interruptible then (if f.running then { f with frame = { f.frame with deferred_interrupt = true } }, false else { f with parked = NotParked; pending = []; frame = { f.frame with current = failure accumulated } }, true) else f, false)

let rec inject_yield m f yielding =
  if (not yielding && not f.prevent_yield) && yield_verdict f then (let token = m.next_token in
    let m = { m with next_token = m.next_token + 1 } in
    let f = { f with yield_override = None; dispatcher = Dispatcher.enqueue f.dispatcher 0 (Tresume (f.id, token, (* HOLE: frame:current *) f.frame.current)) } in
    let f = park f { token = token; waiting_on = None; remaining = []; collected = []; resume_with = Rvoid; fail_fast = false } in
    Some { token = emit (arm m f.id) [YieldInjected (f.id, f.current_op_count); ParkedOn (f.id, token)]; waiting_on = f; remaining = true; collected = parked; resume_with = [] }) else None

let rec countdown_park interp m f targets resume_with fail_fast =
  let token = m.next_token in
  let m = { m with next_token = m.next_token + 1 } in
  match countdown_walk m targets [] with
    | exits, None -> m, { f with frame = { f.frame with current = resume_prim interp resume_with exits } }, false
    | exits, Some (target, remaining) -> (let m = (match fiber_opt m target with
        | Some g -> ignore { g with observers = g.observers @ [Countdown (f.id, token)] };
          ()
        | None -> ());
      m in
      let name = cancel_name interp interp.park_cancel_name f.id token in
      let f = { f with frame = { f.frame with stack = async_finalizer name :: (* HOLE: frame:stack *) f.frame.stack } } in
      let f = park f { token = token; waiting_on = Some target; remaining = remaining; collected = exits; resume_with = resume_with; fail_fast = fail_fast } in
      emit m [ParkedOn (f.id, token)], f, true)

and resume_prim interp resume_with exits =
  match resume_with with
    | RexitsValue -> success (exits_value interp exits)
    | Rvoid -> success interp.void_value
    | RcontinueWith name -> on_success (success (exits_value interp exits)) name

let rec fire_observer interp id exit_ acc observer =
  let m = emit (fst acc) [ObserverFired (id, observer)] in
  match observer with
    | ResumeAwait (waiter, token, mode) -> m, snd acc @ [Cresume (waiter, token, exit_value interp exit_ mode)]
    | UntrackChild parent -> ((match fiber_opt m parent with
        | Some p -> ignore { p with children = List.filter (fun c -> c <> id) p.children };
          ()
        | None -> ());
      m), snd acc
    | DropScopeFinalizer (scope, key) -> (match drop_finalizer interp scope key m.state with
        | None -> halt m (UnknownScope scope), snd acc
        | Some state -> { m with state = state }, snd acc)
    | Countdown (waiter, token) -> (match fiber_opt m waiter with
        | None -> m, snd acc
        | Some w -> (match List.find_opt (fun p -> p.token = token) w.pending with
            | None -> m, snd acc
            | Some p -> (let collected = p.collected @ [exit_] in
              let first_failure = (p.fail_fast && not exit_.is_success) && List.for_all is_success p.collected in
              let m, nested = if first_failure then interrupt_each interp waiter (stack_annotations interp waiter) p.remaining (m, []) else m, [] in
              match countdown_walk m p.remaining collected with
                | exits, None -> (let w = { w with pending = List.map (fun q -> if q.token = token then { q with waiting_on = None; remaining = []; collected = exits } else q) w.pending } in
                  m, (snd acc @ nested) @ [Cresume (waiter, token, resume_prim interp p.resume_with exits)])
                | exits, Some (next, rest) -> (let m = (match fiber_opt m next with
                    | Some g -> ignore { g with observers = g.observers @ [Countdown (waiter, token)] };
                      ()
                    | None -> ());
                  m in
                  let w = { w with pending = List.map (fun q -> if q.token = token then { q with waiting_on = Some next; remaining = rest; collected = exits } else q) w.pending } in
                  m, snd acc @ nested))))
    | RaceCallback race_id -> (match race_opt m race_id with
        | None -> m, snd acc
        | Some race -> (let state = race_complete race.state id exit_ in
          let race = { race with state = state } in
          let m = update_race m race in
          match state.accepted, race.settled with
            | Some accepted, false_ -> (let m = update_race m { race with settled = true } in
              let m = emit m [RaceSettled (race_id, accepted)] in
              m, snd acc @ [Cresume (race.host, race.token, race_settle interp state.live accepted)])
            | _, _ -> m, snd acc))
    | Callback key -> emit m [CallbackEv (key, exit_)], snd acc

let rec exit_fiber interp m f exit_ =
  if (m.middleware_installed && f.finalizing = None) && not (f.children = []) then (let m, nested = interrupt_each interp f.id (stack_annotations interp f.id) f.children (m, []) in
    let m = emit m [ChildrenInterrupted (f.id, f.children)] in
    let f = { f with finalizing = Some exit_; frame = { f.frame with deferred_interrupt = false } } in
    let m, f, parked = countdown_park interp m f f.children (RcontinueWith (restore_name interp exit_)) in
    m, f, parked, nested) else (let f = { f with exit_ = Some exit_; finalizing = None; frame = { f.frame with stack = []; deferred_interrupt = false }; children = []; parked = NotParked; pending = []; context = interp.empty_context } in
    let m = emit m [Exited (f.id, exit_)] in
    let m, nested = List.fold_left (fire_observer interp f.id exit_) (m, []) f.observers in
    let f = { f with observers = [] } in
    m, f, false, nested)

let rec settle id rest it =
  match it.outcome with
    | _outcome_2046continue_0 -> it.machine, (it.nested @ [loop id it.yielding]) @ rest
    | _outcome_2046answered -> it.machine, (it.nested @ [deliver id it.yielding]) @ rest
    | _outcome_2046parked -> it.machine, it.nested @ rest
    | Finished exit_ -> it.machine, (it.nested @ [finish id exit_]) @ rest
    | Stuck why -> halt it.machine why, []

let rec drive interp x0 x1 x2 =
  match x0, x1, x2 with
    | 0, m, _ -> m
    | _2091anonymous_2093, m, [] when _2091anonymous_2093 > 0 -> (let _2091anonymous_2093 = _2091anonymous_2093 - 1 in
      m)
    | fuel, m, (cmd :: rest) when fuel > 0 -> (let fuel = fuel - 1 in
      if m.stuck <> None then m else (match cmd with
          | Cevaluate id -> (match fiber_opt m id with
              | None -> drive interp fuel m rest
              | Some f -> if f.exit_ <> None || f.running then drive interp fuel m rest else (let f = { f with running = true; current_op_count = 0; parked = NotParked } in
                  let m = emit m [Started id] in
                  drive interp fuel m (loop id false :: rest)))
          | Loop (id, yielding) -> (match fiber_opt m id with
              | None -> drive interp fuel m rest
              | Some f -> (let m, cmds = settle id rest (iteration interp m f yielding) in
                drive interp fuel m cmds))
          | Deliver (id, yielding) -> (match fiber_opt m id with
              | None -> drive interp fuel m rest
              | Some f -> (let m, cmds = settle id rest (evaluate_prim interp m f yielding) in
                drive interp fuel m cmds))
          | Cresume (id, token, answer) -> (match fiber_opt m id with
              | None -> drive interp fuel m rest
              | Some t -> (match t.parked with
                  | WithGuard parked_token -> if parked_token = token then (let t = { t with parked = NotParked; pending = List.filter (fun p -> p.token <> token) t.pending; frame = { t.frame with current = answer } } in
                      let m = emit m [ResumedWith (id, token, answer)] in
                      drive interp fuel m (Cevaluate id :: rest)) else drive interp fuel m rest
                  | NotParked -> drive interp fuel m rest))
          | Claunch race_id -> (match race_opt m race_id with
              | None -> drive interp fuel m rest
              | Some race -> (match race.programs with
                  | [] -> drive interp fuel m rest
                  | program :: more -> if race.state.accepted <> None then drive interp fuel m rest else (match fiber_opt m race.host with
                        | None -> drive interp fuel m rest
                        | Some host -> (let m, child = launch_entrant interp race_id m host program in
                          let m = update_race m { race with programs = more; state = { race.state with live = race.state.live @ [child] } } in
                          drive interp fuel (emit m [RaceLaunched (race_id, child)]) (Cevaluate child :: Claunch race_id :: rest)))))
          | Clink (mode, scope, key, target, interruptor, extra) -> (let m, nested = link_scope interp m mode scope key target interruptor extra in
            drive interp fuel m (nested @ rest))
          | Finish (id, exit_) -> (match fiber_opt m id with
              | None -> drive interp fuel m rest
              | Some f -> (let m, f, parked, nested = exit_fiber interp m { f with running = false } exit_ in
                let m = m in
                drive interp fuel m ((nested @ (if parked then [] else [CdrainDue])) @ rest)))
          | CdrainDue -> (let due, state = due_resumes interp m.state in
            let m = { m with state = state } in
            drive interp fuel m (List.map (fun d -> Cresume (fst d, fst (snd d), snd (snd d))) due @ rest))))


