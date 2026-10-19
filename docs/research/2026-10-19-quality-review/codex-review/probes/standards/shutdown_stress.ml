open Effect4_engine
module Sched=E4_sched
let applied = Atomic.make 0
let engine : (unit,int) Sched.engine =
  {init=ignore; thread_init=ignore; thread_finalize=ignore;
   programs=(fun()->["p"]);load=(fun ~program:_ ~fuel:_ ->());
   step=(fun () ~fuel:_ _ -> Atomic.incr applied);release=ignore;
   finished=(fun _->false);answer=(fun _->Sched.Suspended);armed=(fun _->[]);
   fire_of=Fun.id;trace_len=(fun _->0);rows=(fun _ ~cursor:_ ->[]);
   to_wire=string_of_int;snapshot=(fun _->"");
   abandon={E4_abandon.interrupt=(fun m ~reason:_->m,0);open_scopes=(fun _->[]);
            finalizer_step=(fun _ ~scope:_->None)}}
let cfg = {Sched.default_config with domains=1;minor_heap_words=0;spin_budget=0}
let () =
 let found = ref false in
 for iteration=1 to 2000 do
  if not !found then (
   Atomic.set applied 0;
   let t=Sched.start engine cfg in
   let id=match Sched.spawn t ~program:"p" ~fuel:1 with Ok i->i|Error _->failwith "spawn" in
   let go=Atomic.make false in
   let accepted=Atomic.make 0 in
   let client() =
     while not(Atomic.get go) do Domain.cpu_relax() done;
     for _=1 to 10000 do match Sched.send t id 1 with Ok _->Atomic.incr accepted|Error _->() done in
   let d1=Domain.spawn client in
   Atomic.set go true;
   while Atomic.get accepted=0 do Domain.cpu_relax() done;
   ignore(Sched.shutdown t);
   Domain.join d1;
   let a=Atomic.get accepted and b=Atomic.get applied and pending=Sched.pending t in
   if a <> b || pending <> 0 then (
     Printf.printf "UNMODIFIED LIBRARY RACE: iteration=%d accepted=%d applied=%d pending=%d\n%!" iteration a b pending;
     found:=true)
  )
 done;
 if not !found then print_endline "No mismatch found in 2000 races" 
