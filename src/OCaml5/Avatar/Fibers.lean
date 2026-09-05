import OCaml5.Ml.Reflect
import OCaml5.Ml.Passes
import OCaml5.Avatar.Part
import OCaml5.Avatar.Derived.Fibers

/-!
# OCaml5.Avatar.Fibers

**What it is.** The descriptions behind `ocaml/avatar/deep_fibers.ml`, the port of
`src/Effect4/Machine/Fibers.lean`: the substitution table, the two records and five variants of
A0's requests 1, 2 and 5, the two request-3 functions written pure and rendered through
`Ml.mutate`, the compile-check module, and the `RunDecision` tape wire (request 4). `generated`
is what `ocaml/tools/fuzz.sh avatar` renders, compiles on three hosts and diffs against the file.

**Depends on.** `OCaml5.Ml.Reflect`, `OCaml5.Ml.Passes`, `OCaml5.Avatar.Part`,
`OCaml5.Avatar.Derived.Fibers` (the twins).

**Properties.**
* **Field and constructor order is the Lean order**; arity for arity except the named erasures;
  the holes reach the output as `HOLE` comments — *tested* (the `#guard`s below).
* **The mangling is injective** on every name rendered here — *tested*.
* **The pass fired on every update** of the request-3 functions: `residue` is empty — *tested*.
* **Byte-identical to the hand-written file** — *tested* (`ocaml/tools/fuzz.sh avatar`), executed.
-/

namespace OCaml5.Avatar

open OCaml5.Ml

/-! ## The avatar's carriers, described

`ocaml/avatar/deep_fibers.ml` transcribed `src/Effect4/Machine/Fibers.lean` by hand. These
are the descriptions that generate the carriers A0's request 1 and request 2 name, against the
one substitution table below. `ocaml/tools/fuzz.sh avatar` renders them, compiles the result, and diffs
it against A0's file. -/

namespace Fibers

/-- The one substitution table for the avatar module: what each Lean type head becomes. Every
entry is a decision A0 made by hand in `deep_fibers.ml`; collecting them here is the point.

* the family's parameters are fixed by the fixture: `χ` is `unit` (no context service) and `ν`
  is a program name, printed as a string;
* `Exit β ε δ ι α` is `exitv`, `Cause ε δ ι α` is `cause`, `ReasonAnnotations α` is
  `string list`;
* `Prim ν σ β ε δ ι α` is `answer` — every `Prim` in an answer position is `Prim.success` or
  `Prim.failure` (`deep_fibers.ml:121-124`), and `Prim` proper is never rendered (request 5);
* `FrameEvent` is a `string`: the avatar prints frame events, it does not carry them. -/
def subst : Subst :=
  [("FiberId", Ty.int),
   ("Parked", Ty.named "parked"),
   ("FrameFiber", Ty.named "frame_fiber"),
   ("Pending", Ty.named "pending"),
   ("Exit", Ty.named "exitv"),
   ("Observer", Ty.named "observer"),
   ("Dispatcher", Ty.named "dispatcher"),
   ("Task", Ty.named "task"),
   ("Prim", Ty.named "answer"),
   ("Cause", Ty.named "cause"),
   ("FrameEvent", Ty.string),
   ("ReasonAnnotations", Ty.list Ty.string),
   ("Supervision.ObserverMode", Ty.named "observer_mode"),
   ("Supervision.ScopeMode", Ty.int),
   ("Supervision.ForkOptions", Ty.named "fork_options"),
   ("χ", Ty.unit),
   ("ν", Ty.string),
   ("σ", Ty.unit)]

private def fid : LTy := .nm "FiberId"
private def exitL : LTy := .app "Exit" [.nm "β", .nm "ε", .nm "δ", .nm "ι", .nm "α"]
private def primL : LTy :=
  .app "Prim" [.nm "ν", .nm "σ", .nm "β", .nm "ε", .nm "δ", .nm "ι", .nm "α"]
private def taskL : LTy :=
  .app "Task" [.nm "ν", .nm "σ", .nm "β", .nm "ε", .nm "δ", .nm "ι", .nm "α"]

/-! ### Request 5: `FrameFiber`, with the `Prim` pair as a hole

`src/Effect4/Machine/Frames.lean:269`, five fields. `current : Prim …` and `stack : List (Prim …)`
are DIVERGENCE 1 — the OCaml 5 stack itself — and the renderer refuses them. `control` is the
substitute the hand-written module fills. -/
def frameFiber : StructDesc where
  leanName := "FrameFiber"
  site := "Runtime.lean:269"
  subst := subst
  fields :=
    [{ leanName := "current", leanTy := primL,
       kind := .hole ("the OCaml 5 stack: a closure, `Onstack`, a captured continuation,"
         ++ " or a recorded failure. DIVERGENCE 1.") },
     { leanName := "stack", leanTy := .lst primL,
       kind := .hole "rc.112's `_stack`; the OCaml 5 stack carries it. DIVERGENCE 1." },
     { leanName := "control", leanTy := .nm "control", isMutable := true, kind := .substitute,
       ocamlName := Option.some "control",
       comment := Option.some "current + stack, DIVERGENCE 1" },
     { leanName := "interruptible", leanTy := .bool, isMutable := true },
     { leanName := "interruptedCause", leanTy := .opt (.app "Cause" [.nm "ε"]), isMutable := true },
     { leanName := "deferredInterrupt", leanTy := .bool, isMutable := true }]

/-! ### Request 1: `RunFiber`, fifteen fields in the Lean order

`Fibers.lean:157`. Everything but `id` and `frame` is `mutable`: DIVERGENCE 3, the machine is a
value threaded through pure updates in Lean and a record updated in place in OCaml. -/
def runFiber : StructDesc where
  leanName := "RunFiber"
  site := "Fibers.lean:157"
  subst := subst
  fields :=
    [{ leanName := "id", leanTy := fid },
     { leanName := "frame", leanTy := .app "FrameFiber" [.nm "ν"] },
     { leanName := "running", leanTy := .bool, isMutable := true },
     { leanName := "parked", leanTy := .nm "Parked", isMutable := true },
     { leanName := "pending", leanTy := .lst (.app "Pending" [.nm "ν"]), isMutable := true },
     { leanName := "finalizing", leanTy := .opt exitL, isMutable := true },
     { leanName := "exit", leanTy := .opt exitL, isMutable := true },
     { leanName := "currentOpCount", leanTy := .nat, isMutable := true },
     { leanName := "maxOpsBeforeYield", leanTy := .nat, isMutable := true },
     { leanName := "preventYield", leanTy := .bool, isMutable := true },
     { leanName := "yieldOverride", leanTy := .opt .bool, isMutable := true },
     -- No Lean counterpart: the avatar carries `Cmd.loop`'s `yielding` argument on the fiber,
     -- because `Cmd.loop` has no OCaml existence (DIVERGENCE 2). The comment is A0's own.
     { leanName := "yielding", leanTy := .bool, isMutable := true, kind := .substitute,
       ocamlName := Option.some "yielding",
       leading :=
         ["(* Not a Lean field: `iteration`'s per-entry injection latch is Lean's `yielding` argument",
          "   to `Cmd.loop` (`Fibers.lean:683`, rc.112's `runLoop` local at `internal/effect.ts:634`).",
          "   `Cmd.loop` has no OCaml existence (DIVERGENCE 2), so the latch lives on the fiber and is",
          "   cleared wherever Lean's `Cmd.evaluate` would have passed `false`. *)"] },
     -- No Lean counterpart either: a `raceAll` host is resumed by two different tokens and the
     -- OCaml continuation has to survive both, where Lean keeps the program in `frame.current`
     -- (DIVERGENCE 1). Added by A0 after round three; the byte diff went red on exactly this
     -- field, which is what the diff is for.
     { leanName := "raceAnswer", leanTy := .opt (.nm "Kops"), isMutable := true,
       kind := .substitute, ocamlName := Option.some "race_answer",
       leading :=
         ["(* Not a Lean field: a `raceAll` host is resumed either by its own race token or by the",
          "   settle path's countdown token, and the OCaml continuation has to survive both. Lean",
          "   keeps the program in `frame.current` instead (DIVERGENCE 1). *)"] },
     { leanName := "observers", leanTy := .lst (.nm "Observer"), isMutable := true },
     { leanName := "children", leanTy := .lst fid, isMutable := true },
     { leanName := "dispatcher", leanTy := .app "Dispatcher" [.nm "ν"], isMutable := true },
     { leanName := "context", leanTy := .nm "χ", isMutable := true }]

/-! ### Request 2: the five inductives -/

/-- `Observer` (`Fibers.lean:93`), six shapes, no prefix. -/
def observer : InductiveDesc where
  leanName := "Observer"
  site := "Fibers.lean:93"
  subst := subst
  ctors :=
    [{ leanName := "resumeAwait",
       args := [⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩,
                ⟨"mode", .nm "Supervision.ObserverMode", false⟩] },
     { leanName := "untrackChild", args := [⟨"parent", fid, false⟩] },
     { leanName := "dropScopeFinalizer", args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "countdown", args := [⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] },
     { leanName := "raceCallback", args := [⟨"race", .nat, false⟩] },
     { leanName := "callback", args := [⟨"key", .nat, false⟩] }]

/-- `RunEvent` (`Fibers.lean:268`), 21 constructors since `57924eb` (R2-11): `raceStarted`
carries the entrant *count* (`entrants : Nat`) — an entrant has no id before its launch — and
`raceSkipped` is gone, a skipped entrant never existing (the drift re-diff of 2026-09-04;
`deep_fibers.ml` had already moved). Two names are overridden because they would collide inside
one OCaml module: `frame` with the `frame_fiber` field and `callback` with `Observer.callback`.
Two arguments are erased, both of them A0's own omissions, now recorded: `scopeLinked.mode` and
`contextSet.context` (the profile's context is `unit`). -/
def runEvent : InductiveDesc where
  leanName := "RunEvent"
  site := "Fibers.lean:268"
  subst := subst
  ctors :=
    [{ leanName := "forked",
       args := [⟨"parent", fid, false⟩, ⟨"child", fid, false⟩, ⟨"daemon", .bool, false⟩] },
     { leanName := "started", args := [⟨"fiber", fid, false⟩] },
     { leanName := "scheduledTask",
       args := [⟨"owner", fid, false⟩, ⟨"priority", .nat, false⟩, ⟨"task", taskL, false⟩] },
     { leanName := "ranTask", args := [⟨"owner", fid, false⟩, ⟨"task", taskL, false⟩] },
     { leanName := "yieldInjected", args := [⟨"fiber", fid, false⟩, ⟨"atOp", .nat, false⟩] },
     { leanName := "parkedOn", args := [⟨"fiber", fid, false⟩, ⟨"token", .nat, false⟩] },
     { leanName := "resumedWith",
       args := [⟨"fiber", fid, false⟩, ⟨"token", .nat, false⟩, ⟨"answer", primL, false⟩] },
     { leanName := "interruptRecorded",
       args := [⟨"interruptor", .opt fid, false⟩, ⟨"target", fid, false⟩] },
     { leanName := "interruptDeferred", args := [⟨"target", fid, false⟩] },
     { leanName := "childrenInterrupted",
       args := [⟨"parent", fid, false⟩, ⟨"children", .lst fid, false⟩] },
     { leanName := "observerFired",
       args := [⟨"fiber", fid, false⟩, ⟨"observer", .nm "Observer", false⟩] },
     { leanName := "frame", ocamlName := Option.some "FrameEv",
       args := [⟨"fiber", fid, false⟩, ⟨"event", .nm "FrameEvent", false⟩] },
     { leanName := "finalizerProgram",
       args := [⟨"fiber", fid, false⟩, ⟨"finalizer", .nm "ν", false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "scopeLinked",
       args := [⟨"mode", .nm "Supervision.ScopeMode", true⟩, ⟨"scope", .nat, false⟩,
                ⟨"key", .nat, false⟩, ⟨"fiber", fid, false⟩] },
     { leanName := "scopeClosedOnLink", args := [⟨"scope", .nat, false⟩, ⟨"fiber", fid, false⟩] },
     { leanName := "raceStarted",
       args := [⟨"race", .nat, false⟩, ⟨"host", fid, false⟩, ⟨"entrants", .nat, false⟩] },
     { leanName := "raceLaunched", args := [⟨"race", .nat, false⟩, ⟨"entrant", fid, false⟩] },
     { leanName := "raceSettled", args := [⟨"race", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "contextSet",
       args := [⟨"fiber", fid, false⟩, ⟨"context", .nm "χ", true⟩] },
     { leanName := "callback", ocamlName := Option.some "CallbackEv",
       args := [⟨"key", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "exited", args := [⟨"fiber", fid, false⟩, ⟨"exit", exitL, false⟩] }]

/-- `RunDecision` (`Fibers.lean:362`), seven constructors, prefix `D`. -/
def runDecision : InductiveDesc where
  leanName := "RunDecision"
  site := "Fibers.lean:362"
  ctorPrefix := "D"
  subst := subst
  ctors :=
    [{ leanName := "fire", args := [⟨"owner", fid, false⟩] },
     { leanName := "flush" },
     { leanName := "evaluate", args := [⟨"fiber", fid, false⟩] },
     { leanName := "yieldVerdict", args := [⟨"fiber", fid, false⟩, ⟨"verdict", .bool, false⟩] },
     { leanName := "answerAsync",
       args := [⟨"fiber", fid, false⟩, ⟨"token", .nat, false⟩, ⟨"answer", primL, false⟩] },
     { leanName := "interruptFrom",
       args := [⟨"interruptor", .opt fid, false⟩,
                ⟨"annotations", .app "ReasonAnnotations" [.nm "α"], false⟩,
                ⟨"target", fid, false⟩] },
     { leanName := "installMiddleware" }]

/-- `Cmd` (`Fibers.lean:511`), eight constructors, prefix `C`. Three have no OCaml existence,
on purpose — DIVERGENCE 2, decided arm by arm at the top of `deep_fibers.ml`: `loop`, because
`continue k` runs the fiber to its next `perform`; `deliver`, because the second half of
`Sync[evaluate]` is the function `deliver`, whose continuation is the OCaml `k` the store arm
holds; `finish`, because the exit path is the function `finish`, run from `retc`/`exnc` after
the last primitive's nested commands ran inline. They are rendered here anyway — the request is
arity for arity, and the projection guard reads the Lean arms — and the diff against
`deep_fibers.ml`'s five-arm `cmd` is the divergence, stated rather than silently absorbed.
`launch` carries the race alone since `57924eb` (R2-11: an entrant has no id before its launch);
`link` is `forkIn`'s link as a command (R2-8). The drift re-diff of 2026-09-04. -/
def cmd : InductiveDesc where
  leanName := "Cmd"
  site := "Fibers.lean:511"
  ctorPrefix := "C"
  subst := subst
  ctors :=
    [{ leanName := "evaluate", args := [⟨"fiber", fid, false⟩] },
     { leanName := "loop", args := [⟨"fiber", fid, false⟩, ⟨"yielding", .bool, false⟩],
       comment := Option.some "DIVERGENCE 2: absent from deep_fibers.ml (`continue k` is the loop)" },
     { leanName := "deliver", args := [⟨"fiber", fid, false⟩, ⟨"yielding", .bool, false⟩],
       comment := Option.some "DIVERGENCE 2: absent from deep_fibers.ml (the function `deliver`)" },
     { leanName := "finish", args := [⟨"fiber", fid, false⟩, ⟨"exit", exitL, false⟩],
       comment := Option.some "DIVERGENCE 2: absent from deep_fibers.ml (the function `finish`)" },
     { leanName := "resume",
       args := [⟨"fiber", fid, false⟩, ⟨"token", .nat, false⟩, ⟨"answer", primL, false⟩] },
     { leanName := "launch", args := [⟨"race", .nat, false⟩] },
     { leanName := "link",
       args := [⟨"mode", .nm "Supervision.ScopeMode", false⟩, ⟨"scope", .nat, false⟩,
                ⟨"key", .nat, false⟩, ⟨"target", fid, false⟩, ⟨"interruptor", .opt fid, false⟩,
                ⟨"extra", .app "ReasonAnnotations" [.nm "α"], false⟩] },
     { leanName := "drainDue" }]

/-- `WithFiberAction` (`Fibers.lean:211`), 20 constructors, prefix `W`: the seventeen of
`e77282d`, `dropObservers` and `cancelRace` (`2f77f7d`, R2-3/R2-13), and `awaitAllFailFast`
(`Effect.all`/`forEach` with concurrency, `Layer.ts:1597-1598`) — the last three caught up by the
drift re-diff of 2026-09-04. Every `Prim` argument is an *action's program*, not an answer, so
each is a hole: `Prim` is never rendered (request 5), and the avatar reaches these shapes through
its own `Effect.t` constructors (`deep_fibers.ml`, the `Op_*` alphabet under "the service
alphabet") with the program left to the hand-written handler. -/
def withFiberAction : InductiveDesc where
  leanName := "WithFiberAction"
  site := "Fibers.lean:211"
  ctorPrefix := "W"
  subst := subst
  ctors :=
    [{ leanName := "fork",
       args := [⟨"program", primL, true⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
     { leanName := "forkIn",
       args := [⟨"program", primL, true⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "forkScoped",
       args := [⟨"program", primL, true⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"key", .nat, false⟩] },
     { leanName := "runIn",
       args := [⟨"target", fid, false⟩, ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "interrupt", args := [⟨"target", fid, false⟩] },
     { leanName := "interruptScoped", args := [⟨"target", fid, false⟩] },
     { leanName := "interruptAll",
       args := [⟨"targets", .lst fid, false⟩, ⟨"interruptor", .opt fid, false⟩] },
     { leanName := "awaitAll", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "awaitAllFailFast", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "snapshotChildren" },
     { leanName := "awaitNewChildren", args := [⟨"snapshot", .lst fid, false⟩] },
     { leanName := "raceAll", args := [⟨"entrants", .lst primL, true⟩] },
     { leanName := "setInterruptible",
       args := [⟨"body", primL, true⟩, ⟨"flag", .bool, false⟩] },
     { leanName := "setContext", args := [⟨"context", .nm "χ", false⟩] },
     { leanName := "getContext" },
     { leanName := "getId" },
     { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "refuse", args := [⟨"cause", .app "Cause" [.nm "ε"], false⟩] },
     { leanName := "dropObservers", args := [⟨"token", .nat, false⟩] },
     { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] }]

def inductives : List InductiveDesc := [observer, runEvent, runDecision, cmd, withFiberAction]


/-! ## Request 3: the pure-update → mutation pass

`Ml.mutate` and `Ml.residue` are in `OCaml5.Ml.Passes`, with the precondition they need stated
there: the names in the `linear` list are the ones the caller asserts are used linearly, so that
overwriting the old record is unobservable. What is below is the two functions of A0's request 3,
each written twice — `…Pure` is the Lean function transcribed with its pure record updates, and
the rendered declaration is `mutate ["f"] …Pure`. -/

/-! ### The three functions of request 3

`fireObserver` (`:923`), `exitFiber` (`:992`) and `interruptRecord` (`:550`) are the three A0
names. Two are here; §"what did not land" of the report says why the other two are not.

Each is written twice: `…Pure` is the Lean function transcribed as written, with its pure record
updates, and the rendered declaration is `mutate ["f"] …Pure`. The `#guard`s below check that
`residue` is empty, so the pass fired on every update rather than leaving one behind. -/

/-- `RunFiber.park` (`Fibers.lean:249`), the smallest instance of the rewrite:
`{ f with parked := …, pending := … }`. Not one of the three, but it is the shape they are made
of, and `deep_fibers.ml:228` is the text to compare against. -/
def parkPure : Expr :=
  .letIn "f"
    (.recordWith (.var "f")
      [("parked", .ctor "WithGuard" [.field (.var "p") "token"]),
       ("pending", .binop "@" (.field (.var "f") "pending") (.listLit [.var "p"]))])
    (.var "f")

def parkDecl : Decl :=
  .letD false
    [{ name := "run_fiber_park", params := [("f", Option.none), ("p", Option.none)],
       body := mutate ["f"] parkPure }]

/-- `interruptRecord` (`Fibers.lean:550`), arm for arm. Three divergences meet here and each is
visible in the output rather than absorbed:

* DIVERGENCE 3, the pure updates — three of them, one nested through `frame` — become mutations,
  by the pass and not by hand;
* DIVERGENCE 3 again, the Lean function returns `RunFiber × Bool` and the OCaml one returns the
  `Bool`: the record the caller holds *is* the updated one;
* request 5: `frame := { f.frame with current := Prim.failure accumulated }` is a `Prim`
  assignment, so the renderer refuses it and emits a hole. `deep_fibers.ml:405-409` is what fills
  it, and it is the only place in this function a human has to write. -/
def interruptRecordPure : Expr :=
  .ifThen (.binop "<>" (.field (.var "f") "exit_") (.ctor "None" []))
    (.bool false)
    (.letIn "cause"
      (Expr.call "cause_annotate"
        [Expr.call "cause_interrupt" [.var "interruptor"],
         .binop "::"
           (Expr.call "Printf.sprintf" [.str "stack:%d", .field (.var "f") "id"])
           (.var "extra")])
      (.letIn "accumulated"
        (.matchE (.field (.field (.var "f") "frame") "interrupted_cause")
          [.mk (.ctor "None" []) Option.none (.var "cause"),
           .mk (.ctor "Some" [.var "previous"]) Option.none
             (Expr.call "cause_combine" [.var "previous", .var "cause"])])
        (.letIn "f"
          (.recordWith (.var "f")
            [("frame", .recordWith (.field (.var "f") "frame")
               [("interrupted_cause", .ctor "Some" [.var "accumulated"])])])
          (.ifThen (.field (.field (.var "f") "frame") "interruptible")
            (.ifThen (.field (.var "f") "running")
              (.letIn "f"
                (.recordWith (.var "f")
                  [("frame", .recordWith (.field (.var "f") "frame")
                     [("deferred_interrupt", .bool true)])])
                (.bool false))
              (.seq
                (.hole "FrameFiber.current := Prim.failure accumulated (Fibers.lean:571)"
                  (Expr.call "frame_fail" [.var "f", .var "accumulated"]))
                (.letIn "f"
                  (.recordWith (.var "f")
                    [("parked", .ctor "NotParked" []), ("pending", .listLit [])])
                  (.bool true))))
            (.bool false)))))

def interruptRecordDecl : Decl :=
  .letD false
    [{ name := "interrupt_record",
       params := [("_m", Option.none), ("interruptor", Option.none),
                  ("extra", Option.some (Ty.list Ty.string)),
                  ("f", Option.some (Ty.named "run_fiber"))],
       result := Option.some Ty.bool,
       body := mutate ["f"] interruptRecordPure }]


/-! ### The compile check

`Avatar.generated` is a fragment: it names `exitv`, `cause`, `task` and the rest without
declaring them, because the avatar declares them. `checkModule` closes it — the supporting
carriers `deep_fibers.ml` spells above the generated ones, and the four helpers
`interrupt_record` calls, `frame_fail` among them, which is the hand-written filling of the hole
the renderer left. `ocaml/tools/fuzz.sh avatar` compiles it on all three hosts. -/

/-- The carriers `deep_fibers.ml` declares before the generated ones, in its spelling, so that
the generated fragment type-checks in isolation. Not generated, and not claimed to be. -/
def preamble : List Decl :=
  [.comment "Hand-written: the carriers the generated fragment refers to (deep_fibers.ml:64-160).",
   .rawD "type value = Vunit | Vnat of int",
   .rawD "type reason = Rfail of int | Rdie of string | Rinterrupt of int option",
   .rawD "type cause = { reasons : reason list; annotations : string list }",
   .rawD "type exitv = Esuccess of value | Efailure of cause",
   .rawD "type observer_mode = MJoin | MAwait",
   .rawD "type parked = NotParked | WithGuard of int",
   .rawD "type resume_with = RexitsValue | Rvoid | RcontinueWith of exitv",
   .rawD ("type pending = { token : int; waiting_on : int option; mutable remaining : int;"
     ++ " mutable collected : exitv list; resume_with : resume_with }"),
   .rawD "type answer = Aval of value | Acause of cause",
   .rawD "type task = Tstart of int | Tresume of int * int * answer",
   .rawD "type bucket = { priority : int; mutable tasks : task list }",
   .rawD "type dispatcher = { mutable buckets : bucket list; mutable armed : bool }",
   .rawD "type control = Program of (unit -> value) | Onstack | Failing of cause | Ended",
   -- `deep_fibers.ml:180`: the pair of callbacks a store arm answers through, which is what
   -- `run_fiber.race_answer` holds.
   .rawD "type kops = { ret : value -> unit; thr : exn -> unit }",
   .rawD "type fork_options = { daemon : bool }"]

/-- The four functions `interrupt_record` calls. `frame_fail` is the hole of request 5: the
renderer refuses `FrameFiber.current := Prim.failure` and this is what the avatar puts there
(`deep_fibers.ml:405-409`). -/
def helpers : List Decl :=
  [.comment "Hand-written: the helpers the generated functions call. `frame_fail` fills the HOLE.",
   .rawD "let cause_interrupt who = { reasons = [ Rinterrupt who ]; annotations = [] }",
   .rawD "let cause_annotate c extra = { c with annotations = c.annotations @ extra }",
   .rawD ("let cause_combine a b ="
     ++ " { reasons = a.reasons @ b.reasons; annotations = a.annotations @ b.annotations }"),
   .rawD ("let frame_fail (f : run_fiber) (c : cause) =\n"
     ++ "  match f.frame.control with\n"
     ++ "  | Onstack -> ()\n"
     ++ "  | Program _ | Failing _ | Ended -> f.frame.control <- Failing c")]

/-- Declaration order is dependency order, which is `deep_fibers.ml`'s own: `Observer` before
`RunFiber`, `FrameFiber` before it too. The Lean file's order is not a constraint — only the
field and constructor order inside each carrier is. -/
def generatedTypes : List Decl :=
  [.comment "Generated by OCaml5.Ml (spike P5, round three). Do not edit; edit the descriptions.",
   observer.header, observer.decl,
   frameFiber.header, frameFiber.decl,
   runFiber.header, runFiber.decl,
   runEvent.header, runEvent.decl,
   runDecision.header, runDecision.decl,
   cmd.header, cmd.decl,
   withFiberAction.header, withFiberAction.decl]

def generatedFns : List Decl :=
  [.comment "`RunFiber.park` (`Fibers.lean:249`), pure update rewritten to mutation.",
   parkDecl,
   .comment "`interruptRecord` (`Fibers.lean:550`), pure updates rewritten to mutation.",
   interruptRecordDecl]

/-- A compilation unit: the hand-written support, the generated carriers, the hand-written
helpers, the generated functions. -/
def checkModule : List Decl := preamble ++ generatedTypes ++ helpers ++ generatedFns


/-- The generated part of the avatar: the carriers of requests 1, 2 and 5, and the functions of
request 3. `ocaml/tools/fuzz.sh avatar` renders this, compiles it against a small hand-written
preamble, and diffs each carrier against `deep_fibers.ml`. -/
def generated : List Decl := generatedTypes ++ generatedFns


/-! ### Request 4: the `RunDecision` tape, as a wire

A0's request 4 is a differential fuzzer: generate `RunDecision` tapes, run `replayEval` in Lean
and the rendered OCaml, compare the traces. Two halves of that are not P5's to land yet — the
report says why — but the half that is, is the **tape itself**: the wire both sides must agree on.

The spelling is derived from `Avatar.runDecision`, so the OCaml literal and the wire line cannot
drift from the constructor order and arity the same description generates the type from. One
entry per line-separated field:

```
fire 3 | flush | evaluate 1 | yieldVerdict 2 true | answerAsync 1 7 v5
  | interruptFrom - a;b 2 | installMiddleware
```

the head being the *Lean* constructor name, which is the one name both files share. -/

/-- The types a tape module needs, and nothing else. -/
def tapePreamble : List Decl :=
  [.comment "Hand-written: the value alphabet a tape's answers are drawn from.",
   .rawD "type value = Vunit | Vnat of int",
   .rawD "type reason = Rfail of int | Rdie of string | Rinterrupt of int option",
   .rawD "type cause = { reasons : reason list; annotations : string list }",
   .rawD "type answer = Aval of value | Acause of cause",
   .rawD "let cause_fail e = { reasons = [ Rfail e ]; annotations = [] }"]

/-- A tape module: the alphabet, the generated `run_decision`, and the tapes as OCaml literals.
`ocaml/tools/fuzz.sh tapes` compiles it on all three hosts, which is what makes "every generated tape
is a well-typed `run_decision list`" a fact rather than a claim. -/
def tapeModule (tapes : List (List Expr)) : List Decl :=
  tapePreamble ++ [runDecision.header, runDecision.decl] ++
  [.comment s!"{tapes.length} generated tapes.",
   .letD false
     [{ name := "tapes", result := Option.some (Ty.list (Ty.list (Ty.named "run_decision"))),
        body := .listLit (tapes.map (fun t => .listLit t)) }]]


/-- The descriptions under the projection guard, in the order the report prints. -/
def all : List TypeDesc := [.struct frameFiber, .struct runFiber, .induct observer, .induct runEvent, .induct runDecision, .induct cmd, .induct withFiberAction]

/-- `deep_fibers.ml` as a part of the avatar. `generated` is a fragment: `checkModule` closes it. -/
def part : Part :=
  { name := "fibers", file := "deep_fibers.ml", guarded := all, derived := Derived.Fibers.all,
    generated := generated }

end Fibers

/-! ### Checks: names, order, arity, holes

The rendered text is checked against `deep_fibers.ml` itself by `ocaml/tools/fuzz.sh avatar`, which
diffs the real file rather than a copy of it. What is pinned here is everything that must hold
for that diff to be meaningful. -/

-- The mangling is injective: `unmangleField` is a left inverse, on every field name rendered
-- here and on a row of adversarial ones.
#guard (Fibers.runFiber.fields.map (·.leanName)).all
  (fun n => unmangleField (mangleField n) == n)
#guard (Fibers.frameFiber.fields.map (·.leanName)).all
  (fun n => unmangleField (mangleField n) == n)
#guard ["exit", "type", "currentOpCount", "a_b", "aB", "x'", "ABC", "", "let", "a__b"].all
  (fun n => unmangleField (mangleField n) == n)

-- …and the two adversarial pairs really are separated.
#guard mangleField "aB" == "a_b"
#guard mangleField "a_b" == "a_0b"
#guard mangleField "exit" == "exit_"
#guard mangleField "currentOpCount" == "current_op_count"
#guard typeName "RunFiber" == "run_fiber"
#guard typeName "WithFiberAction" == "with_fiber_action"
#guard ctorName "" "resumeAwait" == "ResumeAwait"
#guard ctorName "C" "drainDue" == "CdrainDue"
#guard ctorName "D" "yieldVerdict" == "DyieldVerdict"

-- Request 1: fifteen Lean fields, in the Lean order, mangled, plus two substitutes with no
-- Lean counterpart: `yielding`, which the avatar carries because `Cmd.loop` has none
-- (DIVERGENCE 2), and `race_answer`, which it carries because a race host is resumed by two
-- tokens (DIVERGENCE 1).
#guard Fibers.runFiber.fields.length == 17
#guard (Fibers.runFiber.fields.filter (fun f =>
          match f.kind with | .substitute => false | _ => true)).length == 15
#guard Fibers.runFiber.fields.map (·.ocaml) ==
  ["id", "frame", "running", "parked", "pending", "finalizing", "exit_", "current_op_count",
   "max_ops_before_yield", "prevent_yield", "yield_override", "yielding", "race_answer",
   "observers", "children", "dispatcher", "context"]
#guard (Fibers.runFiber.fields.filter (·.isMutable)).length == 15
#guard Fibers.runFiber.substitutes == ["yielding", "race_answer"]

-- Request 5: `FrameFiber`'s `Prim` pair is a hole, and `prim` never reaches the output.
#guard Fibers.frameFiber.holes.map (·.1) == ["current", "stack"]
#guard ((renderDecl Fibers.frameFiber.decl).splitOn "prim").length == 1
#guard ((moduleText Fibers.generated).splitOn "prim").length == 1
-- three holes reach the output: the two `FrameFiber` fields, and `interruptRecord`'s
-- `current := Prim.failure`.
#guard ((moduleText Fibers.generated).splitOn "HOLE").length == 4

-- Request 2: constructor order and arity, per carrier.
-- (`Fibers.lean` of 2026-09-04: `RunEvent` 21 since `raceSkipped` retired, `Cmd` 8 with
-- `deliver`/`finish`/`link`, `WithFiberAction` 20 with `awaitAllFailFast`/`dropObservers`/
-- `cancelRace`.)
#guard Fibers.observer.ctors.length == 6
#guard Fibers.runEvent.ctors.length == 21
#guard Fibers.runDecision.ctors.length == 7
#guard Fibers.cmd.ctors.length == 8
#guard Fibers.withFiberAction.ctors.length == 20
-- The three `Cmd` arms with no OCaml existence say so; the five others do not.
#guard (Fibers.cmd.ctors.filter (·.comment.isSome)).map (·.leanName) == ["loop", "deliver", "finish"]
#guard Fibers.cmd.ctors.map (CtorDesc.ocaml "C") ==
  ["Cevaluate", "Cloop", "Cdeliver", "Cfinish", "Cresume", "Claunch", "Clink", "CdrainDue"]

-- Arity for arity, except the erasures, which are named.
#guard Fibers.inductives.all
  (fun d => d.arities.all (fun a => a.2.1 == a.2.2 || (d.erasures.map (·.1)).contains a.1))
#guard Fibers.runEvent.erasures == [("scopeLinked", "mode"), ("contextSet", "context")]
#guard Fibers.observer.erasures == []
#guard Fibers.runDecision.erasures == []
#guard (Fibers.withFiberAction.erasures.map (·.1)) ==
  ["fork", "forkIn", "forkScoped", "raceAll", "setInterruptible"]

-- The names `deep_fibers.ml` actually uses.
#guard Fibers.observer.ctors.map (CtorDesc.ocaml "") ==
  ["ResumeAwait", "UntrackChild", "DropScopeFinalizer", "Countdown", "RaceCallback", "Callback"]
#guard Fibers.runDecision.ctors.map (CtorDesc.ocaml "D") ==
  ["Dfire", "Dflush", "Devaluate", "DyieldVerdict", "DanswerAsync", "DinterruptFrom",
   "DinstallMiddleware"]
#guard (Fibers.runEvent.ctors.map (CtorDesc.ocaml "")).contains "FrameEv"
#guard (Fibers.runEvent.ctors.map (CtorDesc.ocaml "")).contains "CallbackEv"

-- Request 3: the pass fired on every update in both functions.
#guard (residue (mutate ["f"] Fibers.parkPure)).isEmpty
#guard (residue (mutate ["f"] Fibers.interruptRecordPure)).isEmpty
-- …and it had something to fire on: the unrewritten forms do have residue.
#guard (residue Fibers.parkPure).length == 2
#guard (residue Fibers.interruptRecordPure).length == 6
-- The rewrite produced mutations, including one through the nested `frame` update.
#guard ((renderDecl Fibers.parkDecl).splitOn " <- ").length == 3
#guard ((renderDecl Fibers.interruptRecordDecl).splitOn "f.frame.interrupted_cause <- ").length
  == 2
#guard ((renderDecl Fibers.interruptRecordDecl).splitOn "f.frame.deferred_interrupt <- ").length
  == 2

end OCaml5.Avatar
