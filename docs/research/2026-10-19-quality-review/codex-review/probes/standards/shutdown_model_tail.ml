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
module Spec = struct
  type cmd = Send | Shutdown
  type state = {stopped:bool; sent:int}
  type sut = {scheduler:(unit,int) Sched.t;id:int}
  let init_state={stopped=false;sent=0}
  let show_cmd=function Send->"Send"|Shutdown->"Shutdown"
  let arb_cmd _=QCheck.make ~print:show_cmd QCheck.Gen.(oneof_list [Send;Shutdown])
  let init_sut () =
    Atomic.set applied 0;Atomic.set reached false;Atomic.set released false;
    Atomic.set pause false;
    let scheduler=Sched.start engine cfg in
    let id=match Sched.spawn scheduler ~program:"p" ~fuel:1 with Ok i->i|Error _->failwith "spawn" in
    E4_quiescence.wait_zero scheduler.Sched.quiescence;
    Atomic.set pause true;{scheduler;id}
  let cleanup t = Atomic.set released true;Atomic.set pause false;ignore(Sched.shutdown t.scheduler)
  let precond _ _=true
  let next_state c s=match c with
    | Send -> if s.stopped then s else {s with sent=s.sent+1}
    | Shutdown -> {s with stopped=true}
  let run c t =
    let response=match c with
    | Send -> (match Sched.send t.scheduler t.id 1 with Ok _->"ok"|Error `Stopped->"stopped"|Error _->"other")
    | Shutdown ->
      while not(Atomic.get reached) do Domain.cpu_relax() done;
      ignore(Sched.shutdown t.scheduler);
      let n=Atomic.get applied in
      Atomic.set released true;
      "applied="^string_of_int n
    in
    Printf.printf "%s => %s; pending=%d\n%!" (show_cmd c) response (Sched.pending t.scheduler);
    STM.Res(STM.string,response)
  let postcond c s (r:STM.res)=match r with
    | STM.Res ((STM.String,_),actual)->String.equal actual
      (match c with Send->if s.stopped then "stopped" else "ok"|Shutdown->"applied="^string_of_int s.sent)
    | _->false
end
module P=STM_domain.Make(Spec)
let () =
  Atomic.set pause false;
  Atomic.set applied 0;
  let serial=Sched.start engine cfg in
  let sid=match Sched.spawn serial ~program:"p" ~fuel:1 with Ok i->i|Error _->failwith "spawn" in
  ignore(Sched.send serial sid 1);
  ignore(Sched.shutdown serial);
  Printf.printf "serial positive: applied=%d pending=%d post_shutdown_send=%s\n%!"
    (Atomic.get applied) (Sched.pending serial)
    (match Sched.send serial sid 2 with Error `Stopped->"stopped"|_->"unexpected");
  (* These are the only two model orders: Send;Shutdown applies one, while
     Shutdown;Send refuses. The pause picks an OS-permitted execution. *)
  let triple=([],[Spec.Send],[Spec.Shutdown]) in
  let test=QCheck.Test.make ~count:1 ~retries:1 ~name:"shutdown drains every accepted send"
    (QCheck.make (QCheck.Gen.return triple)) P.agree_prop_par in
  exit(QCheck_base_runner.run_tests ~colors:false [test])
