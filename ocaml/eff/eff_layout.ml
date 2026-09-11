(* cut-from: rev=5db3329-dirty toolchain=4.33.1 inputs=793592db9627b7e4a1bebf7e8e15634598076209b0c2cc6b9826329864b4af66 *)
(* GENERATED source-structure view; no runtime or execution-permission claim. *)
let wire_families = [
  ("Ty", ["never"; "unit"; "nat"; "int"; "string"; "bool"; "handle"; "option"; "list"; "prod"; "except"; "exitOf"; "causeOf"; "fiberOf"; "union"; "lit"]);
  ("Lit", ["unit"; "nat"; "bool"; "str"]);
  ("Term", ["var"; "lit"; "app"]);
  ("Terms", ["nil"; "cons"]);
  ("CauseTerm", ["fail"; "die"; "interrupt"; "both"]);
  ("MaskMode", ["interruptible"; "uninterruptible"; "inherit"]);
  ("ForkOptions", ["startImmediately"; "daemon"; "maskMode"]);
  ("ObserverMode", ["awaitValue"; "joinEffect"]);
  ("FinalizerStrategy", ["sequential"; "parallel"]);
  ("FnName", ["incr"; "double"; "zeroWhenPositive"; "noChange"; "takeAndBump"]);
  ("NativeOp", ["refMake"; "refGet"; "refSet"; "refGetAndSet"; "refSetAndGet"; "refUpdate"; "refGetAndUpdate"; "refUpdateAndGet"; "refUpdateSome"; "refGetAndUpdateSome"; "refUpdateSomeAndGet"; "refModify"; "refModifySome"; "deferredMake"; "deferredIsDone"; "deferredPoll"; "deferredSucceed"; "deferredFail"; "deferredAwait"; "scopeMake"; "sleep"; "clockNow"; "external"]);
  ("ServiceName", ["value"]);
  ("ServiceTypeCode", ["value"]);
  ("ServiceKey", ["name"; "service"]);
  ("Eff", ["succeed"; "fail"; "failCause"; "yieldError"; "sync"; "suspend"; "perform"; "bind"; "gen"; "catchCause"; "matchCause"; "onExit"; "exit"; "uninterruptible"; "interruptible"; "branch"; "whileLoop"; "yieldNow"; "callback"; "awaitFiber"; "withFiber"; "scoped"; "acquireRelease"; "provideLayer"; "service"; "provideService"; "catchIf"]);
  ("Stmt", ["bindYield"; "yieldDiscard"; "ret"; "ifElse"; "whileTrue"; "breakLoop"]);
  ("Stmts", ["nil"; "cons"]);
  ("Effs", ["nil"; "cons"]);
  ("ActionTerm", ["fork"; "forkIn"; "forkScoped"; "runIn"; "interrupt"; "interruptScoped"; "interruptAll"; "awaitAll"; "awaitAllFailFast"; "snapshotChildren"; "awaitNewChildren"; "raceAll"; "setContext"; "getContext"; "getId"; "closeScope"]);
  ("LayerTerm", ["succeed"; "effect"; "effectDiscard"; "provide"; "provideMerge"; "merge"; "fresh"; "orDie"; "ref"; "mergeAll"]);
  ("LayerTerms", ["nil"; "cons"]);
  ("RowKind", ["sync"; "async"; "program"]);
  ("RowShape", ["call"; "value"; "tupleCall"; "method"]);
  ("Registration", ["deferred"; "external"]);
  ("Row", ["name"; "spelling"; "shape"; "trailing"; "kind"; "request"; "answer"; "error"; "requires"; "cite"; "typeArgs"; "registration"]);
  ("EffTy", ["answer"; "error"; "requires"])
]
