import OCaml5.Ml.Render

/-!
# OCaml5.Avatar.Probe

**What it is.** The shape probe of spike A0: a slice of `src/Effect4/Machine/Fibers.lean` written
out in `OCaml5.Ml.Syntax`, one `Decl` per Lean declaration, so the Lean → OCaml mapping could be
seen before the avatar committed to it. `ocaml/tools/fuzz.sh surface` renders `sample`, compiles it with
`ocamlc`, `ocamlopt` and `js_of_ocaml`, runs it on all three and compares the rows with
`sampleRows`.

**Depends on.** `OCaml5.Ml.Syntax`, `OCaml5.Ml.Render`.

**Properties.**
* **Pinned text.** The rendered strings are pinned by the `#guard`s below: if one changes, the
  module the hosts compiled is no longer the one this file renders — *tested*.
* **Executed acceptance.** Being OCaml is decided by the hosts, not here — *tested*
  (`ocaml/tools/fuzz.sh surface`).
-/

namespace OCaml5.Avatar

open OCaml5.Ml

/-! ## The Deep-shaped probe

A slice of `src/Effect4/Machine/Fibers.lean` written out in this surface, one `Ml` value per Lean
declaration, so that A0 can see what the mapping looks like before committing to it:

| `Fibers.lean` | here |
| --- | --- |
| `abbrev FiberId := Nat` | `TyBody.alias` |
| `inductive Parked` (`:62-65`) | `TyBody.variant` |
| `inductive Resume (ν)` (`:68-75`) | `TyBody.variant`, one type parameter |
| `structure Pending` (`:81-87`) | `TyBody.record`, `mutable` on the fields the avatar updates |
| `inductive Observer` (`:93-100`) | `TyBody.variant` with multi-argument constructors |
| `inductive Task` / `structure Bucket` / `structure Dispatcher` (`:104-120`) | one `Decl.types` group joined by `and` |
| `structure RunFiber` (`:157-173`) | `TyBody.record` |
| `inductive Stuck` (`:332-335`) | `Decl.exn` |
| `Dispatcher.enqueue` (`:137`) | `Decl.letD true`, mutually recursive with a list helper |
| `RunFiber.status` (`:181-191`) | a `match` with a `when` guard |
| the interpreter loop | `Effect.Deep.match_with` with an `effc` table |

The parameter discipline: a Lean carrier's `Type u` parameters become OCaml type variables, and a
parameter a constructor cannot determine is dropped (OCaml rejects an unused type parameter in a
variant, Lean does not), which is why `Task` here is `'b task` and not `('nu, 'b) task`.

Executed check: `ocaml/tools/fuzz.sh surface` renders `deepSample`, compiles it with `ocamlc`,
`ocamlopt` and `js_of_ocaml`, and runs it on all three. -/

namespace Probe

private def tyA : Ty := .var "a"
private def tyNu : Ty := .var "nu"
private def tyB : Ty := .var "b"
private def fiberId : Ty := .named "fiber_id"
private def bucketOf (t : Ty) : Ty := .con "bucket" [t]
private def taskOf (t : Ty) : Ty := .con "task" [t]
private def dispatcherOf (t : Ty) : Ty := .con "dispatcher" [t]

/-- `abbrev FiberId := Nat`. -/
def fiberIdDecl : Decl := .types [{ name := "fiber_id", body := .alias Ty.int }]

/-- `inductive Parked` (`Fibers.lean:62-65`). -/
def parkedDecl : Decl :=
  .types [{ name := "parked",
            body := .variant [{ name := "NotParked" }, { name := "WithGuard", args := [Ty.int] }] }]

/-- `inductive Resume (ν : Type u)` (`:68-75`). -/
def resumeDecl : Decl :=
  .types [{ name := "resume", params := ["nu"],
            body := .variant [{ name := "ExitsValue" }, { name := "Void" },
                              { name := "ContinueWith", args := [tyNu] }] }]

/-- `structure Pending` (`:81-87`); `remaining` and `collected` are the fields the avatar
counts down and accumulates into, so they are `mutable`. -/
def pendingDecl : Decl :=
  .types [{ name := "pending", params := ["nu", "b"],
            body := .record
              [{ name := "token", ty := Ty.int },
               { name := "waiting_on", ty := Ty.option fiberId },
               { name := "remaining", ty := Ty.int, isMutable := true },
               { name := "collected", ty := Ty.list tyB, isMutable := true },
               { name := "resume_with", ty := .con "resume" [tyNu] }] }]

/-- `inductive Observer` (`:93-100`). -/
def observerDecl : Decl :=
  .types [{ name := "observer",
            body := .variant
              [{ name := "ResumeAwait", args := [fiberId, Ty.int] },
               { name := "UntrackChild", args := [fiberId] },
               { name := "Countdown", args := [fiberId, Ty.int] }] }]

/-- `Task`, `Bucket` and `Dispatcher` (`:104-120`) as one `and`-joined group. -/
def schedulerDecls : Decl :=
  .types
    [{ name := "task", params := ["b"],
       body := .variant [{ name := "Start", args := [fiberId] },
                         { name := "Resume", args := [fiberId, Ty.int, tyB] }] },
     { name := "bucket", params := ["b"],
       body := .record [{ name := "priority", ty := Ty.int },
                        { name := "tasks", ty := Ty.list (taskOf tyB) }] },
     { name := "dispatcher", params := ["b"],
       body := .record [{ name := "buckets", ty := Ty.list (bucketOf tyB), isMutable := true },
                        { name := "armed", ty := Ty.bool, isMutable := true }] }]

/-- `structure RunFiber` (`:157-173`), trimmed to the fields this slice needs. -/
def runFiberDecl : Decl :=
  .types [{ name := "run_fiber", params := ["nu", "b"],
            body := .record
              [{ name := "id", ty := fiberId },
               { name := "running", ty := Ty.bool, isMutable := true },
               { name := "parked", ty := .named "parked", isMutable := true },
               { name := "pending", ty := Ty.list (.con "pending" [tyNu, tyB]), isMutable := true },
               { name := "exit", ty := Ty.option tyB, isMutable := true },
               { name := "observers", ty := Ty.list (.named "observer"), isMutable := true },
               { name := "children", ty := Ty.list fiberId, isMutable := true },
               { name := "dispatcher", ty := dispatcherOf tyB }] }]

/-- `inductive Stuck` (`:332-335`): a Lean sum of failure reasons becomes an OCaml exception. -/
def stuckDecl : Decl := .exn "Stuck_unknown_fiber" [fiberId]

/-- The effects the avatar performs. -/
def effectsDecl : Decl :=
  .effects [("Fork", [.arrow Ty.unit Ty.unit], fiberId),
            ("Yield", [], Ty.unit),
            ("Await", [fiberId], Ty.int)]

/-- A `ref` and the function that bumps it. -/
def freshIdDecls : List Decl :=
  [.letD false [{ name := "next_id", body := .mkRef (.int 0) }],
   .letD false [{ name := "fresh_id", params := [("()", Option.none)],
                  body := .seq (.assign (.var "next_id")
                                 (.binop "+" (.deref (.var "next_id")) (.int 1)))
                               (.deref (.var "next_id")) }]]

/-- `Dispatcher.enqueue` (`:137`) as a mutually recursive pair: the list walk, with a `when`
guard, and the in-place update of two `mutable` fields. -/
def enqueueDecl : Decl :=
  .letD true
    [{ name := "push_bucket",
       params := [("bs", Option.some (Ty.list (bucketOf tyA))), ("priority", Option.some Ty.int),
                  ("task", Option.some (taskOf tyA))],
       result := Option.some (Ty.list (bucketOf tyA)),
       body := .matchE (.var "bs")
         [.mk (.ctor "[]" []) Option.none
              (.listLit [.record [("priority", .var "priority"), ("tasks", .listLit [.var "task"])]]),
          .mk (.cons (.var "b") (.var "rest"))
              (Option.some (.binop "=" (.field (.var "b") "priority") (.var "priority")))
              (.binop "::"
                 (.recordWith (.var "b")
                    [("tasks", .binop "@" (.field (.var "b") "tasks") (.listLit [.var "task"]))])
                 (.var "rest")),
          .mk (.cons (.var "b") (.var "rest")) Option.none
              (.binop "::" (.var "b")
                 (Expr.call "push_bucket" [.var "rest", .var "priority", .var "task"]))] },
     { name := "enqueue",
       params := [("d", Option.some (dispatcherOf tyA)), ("priority", Option.some Ty.int),
                  ("task", Option.some (taskOf tyA))],
       result := Option.some Ty.unit,
       body := .seq
         (.setField (.var "d") "buckets"
            (Expr.call "push_bucket" [.field (.var "d") "buckets", .var "priority", .var "task"]))
         (.ifThen (Expr.call "not" [.field (.var "d") "armed"])
            (.setField (.var "d") "armed" (.bool true)) .unit) }]

/-- `RunFiber.status` (`:181-191`): the computed lifecycle phase, as a `match` with a guard. -/
def statusDecl : Decl :=
  .letD false
    [{ name := "status", params := [("f", Option.none)],
       body := .ifThen (Expr.call "Option.is_some" [.field (.var "f") "exit"]) (.str "done")
         (.matchE (.field (.var "f") "parked")
           [.mk (.ctor "NotParked" []) Option.none (.str "runnable"),
            .mk (.ctor "WithGuard" [.var "token"])
                (Option.some (.binop ">" (.var "token") (.int 0))) (.str "waiting"),
            .mk (.ctor "WithGuard" [.wild]) Option.none (.str "runnable")]) }]

/-- The interpreter: one `Effect.Deep.match_with` with a `retc`, an `exnc` that turns the
`Stuck` exception back into a value, and an `effc` table with one clause per effect. -/
def runDecl : Decl :=
  .letD false
    [{ name := "run", params := [("comp", Option.none)],
       body := .matchWith (.var "comp") .unit Ty.int "v" (.var "v")
         [.mk (.ctor "Stuck_unknown_fiber" [.var "i"]) Option.none (.var "i")]
         [.mk "Fork" [.var "f"] "k" (.continueK (.var "k") (Expr.call "fresh_id" [.unit])),
          .mk "Yield" [] "k" (.continueK (.var "k") .unit),
          .mk "Await" [.var "i"] "k"
            (.discontinueK (.var "k") (.ctor "Stuck_unknown_fiber" [.var "i"]))] }]

/-- `let () = …`: a driver that exercises every declaration above and prints two rows, so the
probe is executed and not only compiled. -/
def mainDecl : Decl :=
  .letD false
    [{ name := "()",
       body := .letIn "d" (.record [("buckets", .listLit []), ("armed", .bool false)])
         (.seq (Expr.call "enqueue" [.var "d", .int 3, .ctor "Start" [.int 1]])
           (.letIn "f"
             (.record
               [("id", .int 1), ("running", .bool false),
                ("parked", .ctor "WithGuard" [.int 7]), ("pending", .listLit []),
                ("exit", .ctor "None" []),
                ("observers", .listLit [.ctor "Countdown" [.int 1, .int 7]]),
                ("children", .listLit []), ("dispatcher", .var "d")])
             (.seq (Expr.call "print_endline" [Expr.call "status" [.var "f"]])
               (Expr.call "print_endline"
                 [Expr.call "string_of_int"
                   [Expr.call "run"
                     [.fn ["()"]
                       (.seq (Expr.ignoreE (.perform (.ctor "Yield" [])))
                         (.perform (.ctor "Await" [.int 2])))]]])))) }]

/-- The whole probe, in declaration order. -/
def sample : List Decl :=
  [.comment "Generated by OCaml5.Ml (spike P5 part 2), the A0 shape probe. Do not edit.",
   fiberIdDecl, parkedDecl, resumeDecl, pendingDecl, observerDecl, schedulerDecls,
   runFiberDecl, stuckDecl, effectsDecl] ++ freshIdDecls ++
  [enqueueDecl, statusDecl, runDecl, mainDecl]

/-- The rows the probe prints, checked by `ocaml/tools/fuzz.sh surface`. -/
def sampleRows : List String := ["waiting", "2"]

end Probe

/-! ### Checks

`ocamlc` acceptance is executed (`ocaml/tools/fuzz.sh surface`), so what is pinned here is the text: if
one of these strings changes, the module that was compiled is no longer the module this file
renders. -/

#guard renderTy (Ty.cont (.var "a") Ty.int) == "('a, int) Effect.Deep.continuation"
-- The renderer now emits only the parentheses the form needs: an arrow at the top level
-- of a type has none, and one in the domain of another arrow has them.
#guard renderTy (.arrow Ty.unit (Ty.list (.con "bucket" [.var "b"]))) == "unit -> 'b bucket list"
#guard renderTy (.con "pending" [.var "nu", .var "b"]) == "('nu, 'b) pending"

#guard renderDecl Probe.fiberIdDecl == "type fiber_id = int"

#guard renderDecl Probe.parkedDecl == "type parked = NotParked | WithGuard of int"

#guard renderDecl Probe.stuckDecl == "exception Stuck_unknown_fiber of fiber_id"

#guard renderDecl Probe.effectsDecl ==
  "type _ Effect.t +=\n  | Fork : (unit -> unit) -> fiber_id Effect.t\n"
    ++ "  | Yield : unit Effect.t\n  | Await : fiber_id -> int Effect.t"

-- A record with `mutable` fields, and a mutually recursive `and` group.
#guard renderDecl Probe.runFiberDecl ==
  "type ('nu, 'b) run_fiber = {\n  id : fiber_id;\n  mutable running : bool;\n"
    ++ "  mutable parked : parked;\n  mutable pending : ('nu, 'b) pending list;\n"
    ++ "  mutable exit : 'b option;\n  mutable observers : observer list;\n"
    ++ "  mutable children : fiber_id list;\n  dispatcher : 'b dispatcher;\n}"

#guard ((renderDecl Probe.schedulerDecls).splitOn "\nand ").length == 3

-- `let rec … and …`, a `when` guard, `::`, functional record update and a mutable-field write.
#guard ((renderDecl Probe.enqueueDecl).splitOn "let rec ").length == 2
#guard ((renderDecl Probe.enqueueDecl).splitOn "\n\nand ").length == 2
#guard ((renderDecl Probe.enqueueDecl).splitOn " when ").length == 2
#guard ((renderDecl Probe.enqueueDecl).splitOn " with tasks = ").length == 2
#guard ((renderDecl Probe.enqueueDecl).splitOn "d.buckets <- ").length == 2

-- The `effc` table: a locally abstract type, one clause per constructor, a `None` default.
#guard ((renderDecl Probe.runDecl).splitOn "(fun (type a) (eff : a Effect.t) ->").length == 2
#guard ((renderDecl Probe.runDecl).splitOn "(k : (a, int) Effect.Deep.continuation)").length == 4
#guard ((renderDecl Probe.runDecl).splitOn "| _ -> None)").length == 2
#guard ((renderDecl Probe.runDecl).splitOn "Effect.Deep.discontinue").length == 2

-- The module is one text, and every declaration is in it.
#guard (Ml.moduleText Probe.sample).length > 2000
#guard ((Ml.moduleText Probe.sample).splitOn "type _ Effect.t +=").length == 2

end OCaml5.Avatar
