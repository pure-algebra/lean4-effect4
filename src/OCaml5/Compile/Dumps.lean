import OCaml5.Compile
import OCaml5.Ir.Programs

/-!
# Spike P4: `compile`'s output against js_of_ocaml's own

Status: spike P4, 2026-09-04. Module `OCaml5.Compile.Dumps`. Report:
`docs/research/2026-09-04-spike-p4-compile.md`.

Two comparisons, one executed on the real tools and one machine-checked in Lean.

## Executed

Four witness sources were compiled and dumped afresh for this spike, with the commands spike O2
records (`docs/research/2026-09-03-spike-o2-jsoo.md` §1):

```
$ ocamlc -c wNN.ml
$ js_of_ocaml.exe compile --enable effects --target-env=nodejs --pretty --debug main \
    wNN.cmo -o wNN.main.js 2> wNN.pre.dump
```

The dumps are the sibling files `w01_repeated.pre.dump`, `w03_cancelled.pre.dump`,
`w05_forwarded.pre.dump`, `w13_runstack_return.pre.dump`. They show what a witness's *own*
compilation unit contains: `%perform` and nothing else, because `Effect.Deep.match_with`,
`continue`, `discontinue` and `Fun.protect` are separate compilation units. This is the one
structural fact that separates `compile` from `parse_bytecode`: `compile` inlines
`OCaml5.Stdlib`, so `caml_alloc_stack`, `%resume` and `%reperform` appear in the same program,
while js_of_ocaml calls into `Stdlib__Effect` for them.

## Machine-checked

Spike O2's `ir/p1`, `ir/p2`, `ir/p3` *are* three real `--debug main` dumps, transcribed block by
block with the compiler's own variable numbers, and `ir/pNLinked` is each of them with the
pieces of `Stdlib.Effect.Deep` transcribed in as blocks 200-211 — exactly the inlining `compile`
does. So the sharp comparison is `compile tN` against `pNLinked`, where `tN` is the same OCaml
source written as a `Term`. That is what this module does, on the **effect skeleton**: every
occurrence of one of the seven runtime entry points, the terminator of the block it sits in, and
whether it is in tail position in `Code.Machine.contFor`'s sense — which is what decides which
blocks end in a CPS call after `Cps.f`, and so is what P2's theorem is about.
-/

namespace OCaml5.Compile.Dumps

open OCaml5 OCaml5.Code

/-! ## The effect skeleton -/

/-- The runtime entry points the analysis and the transform care about
(`partial_cps_analysis.ml:82`, `effects.ml:168`, `:532-552`) plus the two `Stdlib.Effect` reaches
through `external`. -/
def effExterns : List String :=
  ["%perform", "%reperform", "%resume", "caml_alloc_stack", "caml_continuation_use_noexc",
   "caml_continuation_use_and_update_handler_noexc", "caml_drop_continuation"]

def lastKind : Last → String
  | .return _ => "return"
  | .raise _ _ => "raise"
  | .stop => "stop"
  | .branch _ => "branch"
  | .cond _ _ _ => "cond"
  | .switch _ _ => "switch"
  | .pushtrap _ _ _ => "pushtrap"
  | .poptrap _ => "poptrap"

/-- `Code.Machine.contFor`'s condition (`effects.ml:833-834` reads the same condition off the
branch): the primitive is the block's last instruction and the block returns exactly the
variable it binds, so the caller's own `k` is handed to the fiber instead of a fresh frame. -/
def tailSite (b : Block K) (i : Instr K) (x : Var) : Bool :=
  (b.body.getLast? == Option.some i) && (match b.branch with | .return y => y == x | _ => false)

/-- One row per effect-primitive occurrence: its name, its block's terminator, and whether it is
in tail position. -/
def sites (p : Program K) : List (String × String × Bool) :=
  p.addrs.flatMap fun a =>
    match p.block? a with
    | Option.none => []
    | Option.some b =>
      b.body.filterMap fun i =>
        match i with
        | .letIn x (.prim (.extern n) _) =>
            if effExterns.contains n
            then Option.some (n, lastKind b.branch, tailSite b i x)
            else Option.none
        | _ => Option.none

/-- The trap terminators, in address order. -/
def trapKinds (p : Program K) : List String :=
  p.addrs.filterMap fun a =>
    match p.block? a with
    | Option.some b =>
      match b.branch with
      | .pushtrap _ _ _ => Option.some "pushtrap"
      | .poptrap _ => Option.some "poptrap"
      | _ => Option.none
    | _ => Option.none

private def sortedNames (l : List (String × String × Bool)) : List String :=
  (l.map (·.1)).foldl (fun acc s => ins acc s) []
where
  ins : List String → String → List String
    | [], s => [s]
    | h :: r, s => if s ≤ h then s :: h :: r else h :: ins r s

/-! ## The three programs of spike O2, as `Term`s

`ir/p1_perform_continue.ml`, `p2_nested_forward.ml` and `p3_trap_discontinue.ml`, transcribed
line by line through `OCaml5.Stdlib`, which is `stdlib/effect.ml` transcribed line by line. In
an `effc` clause the environment is `payload :: last_fiber :: k :: eff`, so the continuation is
`.var 2` and the payload `n` is `.var 0`. -/

/-- `type _ Effect.t += E : int -> int Effect.t`. -/
def eE : EffId := ⟨1⟩

/-- `exception Boom` of `p3_trap_discontinue.ml:1`. -/
def xBoom : ExnId := ⟨3⟩

/-- `p1_perform_continue.ml`: `match_with body () {retc = fun v -> v; exnc = raise;
effc = E n -> Some (fun k -> continue k n)}` over `body () = 1 + perform (E 41)`. Prints 42. -/
def t1 : Term Nat :=
  Stdlib.deepMatchWith
    (.lam (.add (.val 1) (.perform (.eff eE (.val 41)))))
    .unit (.lam (.var 0)) (.lam (.raise (.var 0)))
    [(eE, Stdlib.deepContinue (.var 2) (.var 0))]

/-- `p2_nested_forward.ml`: an inner handler whose `effc` is `fun _ -> None`, so the effect is
forwarded by `%reperform` to the outer one, whose `retc` doubles. Prints 84. -/
def t2 : Term Nat :=
  Stdlib.deepMatchWith
    (.lam (Stdlib.deepMatchWith
      (.lam (.add (.val 1) (.perform (.eff eE (.val 41)))))
      .unit (.lam (.var 0)) (.lam (.raise (.var 0))) []))
    .unit (.lam (.add (.var 0) (.var 0))) (.lam (.raise (.var 0)))
    [(eE, Stdlib.deepContinue (.var 2) (.var 0))]

/-- `p3_trap_discontinue.ml`: the `perform` is inside a `try … with Boom -> 7` and the handler
`discontinue`s, so the captured trap must survive the capture. Prints 7. -/
def t3 : Term Nat :=
  Stdlib.deepMatchWith
    (.lam (.tryWith (.add (.val 1) (.perform (.eff eE (.val 41))))
            (.matchExn (.var 0) [(xBoom, .val 7)] (.raise (.var 0)))))
    .unit (.lam (.var 0)) (.lam (.raise (.var 0)))
    [(eE, Stdlib.deepDiscontinue (.var 2) (.exn xBoom .unit))]

/-! ### Check 0: the same answer

`ir/Programs.lean` runs `pNLinked` — the real IR — and gets `"42\n"`, `"84\n"`, `"7\n"`, which
is what `ocamlrun pN.byte` and `node pN.js` print. The `Term` transcriptions compute the same
three integers under the runtime machine, and so do their compilations under the `effect.js`
machine. -/

private def termVal (fuel : Nat) (t : Term Nat) : OCaml5.Outcome Nat :=
  (Machine.run fuel (Machine.start t)).2

private def codeVal (t : Term Nat) : Code.Outcome := (Code.Machine.exec 200000 (Compile.compile t)).1

#guard termVal 8000 t1 matches .value (.base 42)
#guard termVal 20000 t2 matches .value (.base 84)
#guard termVal 8000 t3 matches .value (.base 7)

#guard codeVal t1 == .value (.int 42)
#guard codeVal t2 == .value (.int 84)
#guard codeVal t3 == .value (.int 7)

/- …and the real IR, run by `ir/Programs.lean`'s own machine, prints those three integers. -/
#guard Code.Machine.exec 20000 Ir.Programs.p1Linked == (Code.Outcome.stopped, "42\n")
#guard Code.Machine.exec 20000 Ir.Programs.p2Linked == (Code.Outcome.stopped, "84\n")
#guard Code.Machine.exec 20000 Ir.Programs.p3Linked == (Code.Outcome.stopped, "7\n")

/-! ### Check 1: the same effect primitives

The multiset of runtime entry points is the same in `compile tN` and in `pNLinked`, with one
systematic difference: `pNLinked` transcribes the *whole* of `Deep` — `continue` at blocks
203/205 and `discontinue` at 204/206 — because a compilation unit is linked whole, while
`compile` inlines only the occurrences the `Term` has. So `p1Linked` and `p2Linked` carry a
dead `discontinue` (one `caml_continuation_use_noexc` and one `%resume` more than `compile`'s
output) and `p3Linked` a dead `continue`. -/

#guard sortedNames (sites (Compile.compile t1)) ==
  ["%perform", "%reperform", "%resume", "%resume", "caml_alloc_stack",
   "caml_continuation_use_noexc"]
#guard sortedNames (sites Ir.Programs.p1Linked) ==
  ["%perform", "%reperform", "%resume", "%resume", "%resume", "caml_alloc_stack",
   "caml_continuation_use_noexc", "caml_continuation_use_noexc"]

/- Two handlers, so two `caml_alloc_stack`s and two `%resume`s from `runstack`, in both. -/
#guard sortedNames (sites (Compile.compile t2)) ==
  ["%perform", "%reperform", "%reperform", "%resume", "%resume", "%resume",
   "caml_alloc_stack", "caml_alloc_stack", "caml_continuation_use_noexc"]

#guard sortedNames (sites (Compile.compile t3)) ==
  ["%perform", "%reperform", "%resume", "%resume", "caml_alloc_stack",
   "caml_continuation_use_noexc"]

/- The difference is exactly the dead half of the linked `Deep`: one extra
`caml_continuation_use_noexc` and one extra `%resume` in each of the three. -/
#guard (sortedNames (sites Ir.Programs.p1Linked)).length == (sortedNames (sites (Compile.compile t1))).length + 2
#guard (sortedNames (sites Ir.Programs.p3Linked)).length == (sortedNames (sites (Compile.compile t3))).length + 2

/-! ### Check 2: where the primitives sit

This is the part P2's theorem depends on. In `pNLinked`, every `%resume` and every `%reperform`
is in tail position and every `caml_alloc_stack` is in a block that returns. `compile` puts them
in exactly the same places — with one deviation, stated in `OCaml5.Compile`'s header: the
null-stack test of `interp.c:1291-1294` and `effect.js:79-80` is emitted as a `Cond` in the IR,
so the `caml_continuation_use_noexc` that feeds a `%resume` ends its block with `cond` instead of
`return`. The `%resume` itself is still in tail position. -/

/-- Every occurrence of `n`, with its terminator and tail flag. -/
def sitesOf (p : Program K) (n : String) : List (String × Bool) :=
  (sites p).filterMap fun s => if s.1 = n then Option.some (s.2.1, s.2.2) else Option.none

/- `%resume` in tail position, in both, everywhere. -/
#guard (sitesOf (Compile.compile t1) "%resume").all (fun s => s == ("return", true))
#guard (sitesOf Ir.Programs.p1Linked "%resume").all (fun s => s == ("return", true))
#guard (sitesOf (Compile.compile t2) "%resume").all (fun s => s == ("return", true))
#guard (sitesOf (Compile.compile t3) "%resume").all (fun s => s == ("return", true))
#guard (sitesOf Ir.Programs.p3Linked "%resume").all (fun s => s == ("return", true))

/- `%reperform` in tail position, in both. This is the `bytegen.ml:800-804` clause holding at
the IR level as well as at the `Term` level. -/
#guard (sitesOf (Compile.compile t1) "%reperform").all (fun s => s == ("return", true))
#guard (sitesOf Ir.Programs.p1Linked "%reperform").all (fun s => s == ("return", true))
#guard (sitesOf (Compile.compile t2) "%reperform").all (fun s => s == ("return", true))

/- `caml_alloc_stack` in a returning block, in both: `let s = alloc_stack … in runstack s …`
is one block (`effect.ml:78-79`). -/
#guard (sitesOf (Compile.compile t1) "caml_alloc_stack").all (fun s => s == ("return", false))
#guard (sitesOf Ir.Programs.p1Linked "caml_alloc_stack").all (fun s => s == ("return", false))

/- The one deviation, isolated: the `caml_continuation_use_noexc` that feeds a guarded
`%resume`. -/
#guard (sitesOf (Compile.compile t1) "caml_continuation_use_noexc") == [("cond", false)]
#guard (sitesOf Ir.Programs.p1Linked "caml_continuation_use_noexc") ==
  [("return", false), ("return", false)]

/-! ### Check 3: `%perform`, and where the trap sits

`p1`'s `%perform` is in a block that returns (`1 + perform (E 41)` is the body's tail);
`p3`'s is inside a `try … with`, so its block ends with `Poptrap` — the body returned, the trap
goes (`interp.c:940-950`). `compile` reproduces both, and reproduces `p3`'s single
`Pushtrap`/`Poptrap` pair. -/

#guard sitesOf (Compile.compile t1) "%perform" == [("return", false)]
#guard sitesOf Ir.Programs.p1Linked "%perform" == [("return", false)]

#guard sitesOf (Compile.compile t3) "%perform" == [("poptrap", false)]
#guard sitesOf Ir.Programs.p3Linked "%perform" == [("poptrap", false)]

#guard trapKinds (Compile.compile t3) == ["pushtrap", "poptrap"]
#guard trapKinds Ir.Programs.p3Linked == ["pushtrap", "poptrap"]
#guard trapKinds (Compile.compile t1) == []
#guard trapKinds Ir.Programs.p1Linked == []

/-! ### Check 4: the freshly dumped witnesses

`w01_repeated.pre.dump` block 2 is the fiber body of witness 1:

```
==== 2 () ====
  v41 = v5!(v40)          (* row "perform\tNumber"          *)
  v42 = "%perform"(v4)
  v45 = v44[3]            (* Printf.sprintf                 *)
  v46 = v45(v43, v42)
  v47 = v5!(v46)          (* row "got\t%d"                  *)
  v49 = v5!(v48)
  v50 = "%perform"(v4)
  ...
  v55 = v42 + v50
  return v55
```

Both `%perform`s are in **one** block, straight-line between the printing calls, and the block
returns the sum. `compile` puts them in one block too, and that block returns. -/

#guard sitesOf (Compile.compile W.w01) "%perform" == [("return", false), ("return", false)]

/-- The addresses of the blocks that hold a given extern, so that "both in one block" is a
check and not a reading. -/
def externBlocks (p : Program K) (n : String) : List Addr :=
  p.addrs.filter fun a =>
    match p.block? a with
    | Option.some b => b.body.any fun i =>
        match i with
        | .letIn _ (.prim (.extern m) _) => m == n
        | _ => false
    | _ => false

#guard (externBlocks (Compile.compile W.w01) "%perform").length == 1

/- `w05_forwarded.pre.dump` block 2 likewise holds both of witness 5's `%perform`s, one per
effect constructor, in one block. -/
#guard (externBlocks (Compile.compile W.w05) "%perform").length == 1

/- `w13_runstack_return.pre.dump` has no `%perform` at all — witness 13 only exercises the
return and raise routes — and neither does the compiled program. -/
#guard sitesOf (Compile.compile W.w13) "%perform" == []

/-! ## The two skeletons, printed

What the report quotes. -/

#eval IO.println s!"compile t1 {sites (Compile.compile t1)}"
#eval IO.println s!"p1Linked   {sites Ir.Programs.p1Linked}"
#eval IO.println s!"compile t2 {sites (Compile.compile t2)}"
#eval IO.println s!"p2Linked   {sites Ir.Programs.p2Linked}"
#eval IO.println s!"compile t3 {sites (Compile.compile t3)}"
#eval IO.println s!"p3Linked   {sites Ir.Programs.p3Linked}"

/-! `compile t1` in the compiler's own printed syntax (`code.ml:461-556`), for the report's
side-by-side against `p1_perform_continue.pre.dump`. -/

#eval IO.println (Print.program (Compile.compile t1))

end OCaml5.Compile.Dumps
