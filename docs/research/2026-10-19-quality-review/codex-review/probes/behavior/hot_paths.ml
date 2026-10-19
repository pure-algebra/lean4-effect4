open Effect4_engine
let best f =
 let out=ref [] in
 for _=1 to 5 do Gc.full_major(); let t=Unix.gettimeofday() in f();out:= (Unix.gettimeofday() -. t)::!out done;
 let xs=List.sort Float.compare !out in List.hd xs,List.nth xs 2
let env () =
 List.iter(fun n ->
 let xs=List.init n Fun.id in let e=E4_env.of_list xs and v=Lcnf_array.of_list xs in
 let measure name f=let a,b=best(fun()->for _=1 to 20000 do ignore(Sys.opaque_identity(f())) done) in Printf.printf "env n=%d reads=20000 %s best_ms=%.4f median_ms=%.4f\n%!" n name (1000.*.a) (1000.*.b) in
 measure "outer" (fun()-> E4_env.get e 0);measure "recent" (fun()->E4_env.get e (n-1));measure "vector_outer" (fun()->Lcnf_array.get v 0)) [100;1000;10000]
let sched n =
 let applied=Atomic.make 0 in
 let allocated()=let s=Gc.stat() in s.Gc.minor_words +. s.Gc.major_words -. s.Gc.promoted_words in
 let eng : (unit,int) E4_sched.engine =
 {init=ignore;thread_init=ignore;thread_finalize=ignore;programs=(fun()->["p"]);load=(fun ~program:_ ~fuel:_->());step=(fun m ~fuel:_ _->Atomic.incr applied;m);release=ignore;finished=(fun _->false);answer=(fun _->E4_sched.Suspended);armed=(fun _->[]);fire_of=(fun _-> -1);trace_len=(fun _->0);rows=(fun _ ~cursor:_->[]);to_wire=string_of_int;snapshot=(fun _->"");abandon={interrupt=(fun m ~reason:_->m,0);open_scopes=(fun _->[]);finalizer_step=(fun _ ~scope:_->None)}} in
 let cfg={E4_sched.default_config with domains=1;mailbox_bound=n+1;ring_capacity=16;batch=64;spin_budget=0;checkpoint_every=0;minor_heap_words=0} in
 Gc.full_major();let before=allocated() in let t0=Unix.gettimeofday() in let t=E4_sched.start eng cfg in let id=match E4_sched.spawn t ~program:"p" ~fuel:1 with Ok x->x|_->assert false in
 for i=1 to n do match E4_sched.send t id i with Ok _ -> ()|_->assert false done;
 let done_=E4_sched.run_until_quiescent ~timeout:10. t in
 ignore(E4_sched.shutdown t);
 let elapsed=Unix.gettimeofday()-.t0 in Gc.full_major(); let words=allocated()-.before in
 Printf.printf "scheduler n=%d done=%b applied=%d ms=%.4f total_words=%.0f words_per_send=%.2f\n%!" n done_ (Atomic.get applied) (elapsed*.1000.) words (words/.float n)
let () = env(); List.iter sched [1000;10000;100000]
