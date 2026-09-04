# Spike P5: Lean emits OCaml — a renderer, a generator, and a fuzzing campaign

Status: 2026-09-03 night, round two. Spike P5 of
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, base commit `7729f58`. Reads O1
(`2026-09-03-spike-o1-runtime-machine.md`, the machine and the witness protocol) and O5
(`2026-09-03-spike-o5-compiler.md`, the admission predicate); imports `OCaml5.Effect`,
`OCaml5.Compiler` and `OCaml5.Witnesses` and edits none of them.

Files owned and written: `workshop/OCaml5/Render.lean`, `workshop/OCaml5/Fuzz.lean`,
`workshop/OCaml5/tools/fuzz.sh`, `workshop/OCaml5/fuzz/`.

Three parts. §§1–6 are the spike as the plan's §6 asked for it: a `Term` renderer, a random term
generator and a fuzzing campaign against the three hosts. §7 is the second part, added after the
estate's target moved to an OCaml avatar of the Effect runtime (spike A0): a general Lean → OCaml
*declaration* surface, so that the avatar's OCaml is generated from the Lean carriers rather than
hand-written. §11 is the third, answering A0's five requests once its report existed: the
description layer that drives that surface from the real `Deep` carriers, and the diff against
A0's hand-written file. §12 is the fourth: a random *program* generator over the alphabet the
avatar answers, each program rendered twice — the avatar's OCaml fixture and the harness's
TypeScript fixture — from one Lean description, with rc.112 through the estate harness as the
oracle.

This closes the top edge of the plan's §6 diagram. Round one had `Term ─▶ M_T` and a hand-written
OCaml file per witness, related by a human transcribing one into the other. P5 replaces the human:
`Term.render` produces the OCaml source, so the arrow is a Lean function and the corpus can be
made as large as the compilers will tolerate.

```
OCaml source text  ──ocamlc/ocamlopt/ocamlrun (trusted)──▶ bytecode, native and jsoo rows
   ▲ render (this spike)                                        ║  compared, four ways
OCaml5.Term ──▶ M_T, the runtime machine (O1) ──▶ Machine.rows ═╝
```

## 1. Headline

| | |
| --- | --- |
| Witnesses rendered from Lean, compiled and run on three hosts | 13 |
| …whose four row lists all agree | 12 (the thirteenth is `w12-drop`, §6) |
| Programs generated, sizes 4–9 | 1300 |
| …accepted by the filters (`Admissible`, terminates, rows printable) | 1300 |
| …compiled by `ocamlc`, by `ocamlopt`, by `js_of_ocaml` | 1300 / 1300 / 1300 |
| …on which all four row lists agree | 1219 |
| **Lean-vs-hosts disagreements** | **0** |
| Host-vs-host disagreements | 81, all one cause (§6) |
| Compile refusals | 0 |

Wall clock: 6 min 20 s for the 1300 on this laptop at eight-way parallelism, ≈0.3 s per program
for three compilers and three runs. A 60-program pilot at size 6 (seeds 1000–1059) ran the same
way earlier: 58 agree, 2 host-vs-host, same cause.

## 2. The typing discipline

`Term` is untyped and OCaml is not, so `render` needs a discipline that makes it total and its
output well-typed. The discipline is **one universal type**, one constructor per `OCaml5.Value`
constructor:

```ocaml
type ('a, 'b) stack
type ('a, 'b) continuation
type last_fiber
type u =
  | I of int | U | F of (u -> u) | Ef of u Effect.t | Xn of exn
  | Nn | Sm of u | Kt of (u, u) continuation | Sk of (u, u) stack | Lf of last_fiber
```

`Value.stack` and `Value.nullStack` share `Sk`, because a null stack *is* a `('a,'b) stack` at the
OCaml level — that is exactly what `caml_continuation_use_noexc` returns on a taken handle
(`fiber.c:595-622`), and `%resume` on it raises `Continuation_already_resumed` in the runtime
rather than at any Lean-visible boundary. Every rendered subterm has OCaml type `u`; the
primitives are reached through coercions `as_int`, `as_fun`, `as_eff`, `as_exn`, `as_k`, `as_stk`,
`as_lf`, each of which prints `!stuck` and exits 2 on a mismatch — precisely the terms on which
`Machine.step` answers `Outcome.stuck`.

Because everything is at `u`, the whole external block is monomorphic and the GADT indices never
have to be reasoned about:

| external | `stdlib/effect.ml` | instantiated here |
| --- | --- | --- |
| `%perform` (`:16`) | `'a t -> 'a` | `u Effect.t -> u` |
| `%resume` (`:41`) | `('a,'b) stack -> ('c -> 'a) -> 'c -> 'b` | `(u,u) stack -> (u -> u) -> u -> u` |
| `%runstack` (`:42`) | idem | idem |
| `%reperform` (`:69-70`) | `'a t -> ('a,'b) continuation -> last_fiber -> 'b` | at `u` |
| `caml_alloc_stack` (`:51-55`) | `('a -> 'b) -> (exn -> 'b) -> ('c t -> ('c,'b) continuation -> last_fiber -> 'b) -> ('a,'b) stack` | at `u` |
| `caml_continuation_use_noexc` (`:49-50`) | `('a,'b) continuation -> ('a,'b) stack` | at `u` |
| `caml_continuation_use_and_update_handler_noexc` (`:130-135`) | `('a,'b) continuation -> ('b -> 'c) -> (exn -> 'c) -> (…) -> ('a,'c) stack` | at `u` |
| `caml_drop_continuation` (`fiber.c:659-664`) | not exported by `Stdlib` | `('a,'b) continuation -> unit` |

The three type constructors are declared abstract in the generated unit, as `effect.ml:39,46-47,
100-101` declares them. Ruling 2 is respected: the externals are the raw ones, never
`Stdlib.Effect`'s wrappers, so a term built by an `OCaml5.Stdlib` builder renders to the
primitives that builder is *defined over*, and the wrapper stays derived. The machine has one
continuation type, so `Deep.continuation` and `Shallow.continuation` are one type here; the C
entry points do not distinguish them. `ExnId 0` is `Effect.Unhandled` and `ExnId 1` is
`Effect.Continuation_already_resumed`, because those are the two the runtime itself raises through
`Callback.register_exception` (`effect.ml:34-36`); every other `ExnId n` becomes
`exception Xn of u` and every `EffId n` becomes `type _ Effect.t += En : u -> u Effect.t`.

### The four restrictions

1. **`emitOf` only on a printable value.** `Value.render` prints `cont7`, `stack3`, `null` — heap
   identities the machine invents and no host can know (O1 report §4.1). The rendered `render_u`
   prints `cont`/`stack` without an index, so a term that `emitOf`s a continuation is outside the
   fragment. `Fuzz.rowSafe` decides this on the machine's rows and discards such a program rather
   than counting it as a disagreement; none of the 1360 draws hit it, and no witness does.
2. **No payload binder in an `Unhandled` or `Continuation_already_resumed` clause.**
   `Effect.Unhandled : 'a t -> exn` is existential, so its payload cannot be put back into `u`;
   the rendered clause binds `U`. Witnesses 04 and 08 match on `Unhandled` and never read the
   binder; the generator never emits such a clause at all.
3. **Evaluation order is forced left to right.** OCaml evaluates the arguments of an application
   right to left; `Machine.step` evaluates them left to right (`Frame.appArg` is pushed and the
   function is evaluated first, `Effect.lean:614`). Every multi-operand form is therefore rendered
   as a chain of `let`s, `t<d>a`…`t<d>d`.
4. **`Compiler.Admissible`.** `render` is claimed faithful only on admissible terms. §5 reports
   that the claim held on 1313 of them.

The `let`-chain of restriction 3 is also what keeps the `reperform`-in-tail-position property
intact. `Admissible` puts every primitive operand at `nonTail` and lets a `letIn` body inherit the
ambient polarity (`bytegen.ml:636-639`, O5 report §3); `let a = … in let b = … in reperform a b c`
therefore has the `reperform` in exactly the position the unrendered term had it in. Executed
check: all 13 witnesses and all 1300 generated programs compile, `Kreperformterm` included.

### The rendering table

De Bruijn indices become depth-indexed names: a binder introduced at depth `d` is `vd`, and
`Term.var i` at depth `d` is `v(d-1-i)`. Shadowing is impossible, so no capture-avoidance is
needed; the `let`-chain temporaries and the `alloc_stack` wrapper parameters (`q<d>e`, `q<d>k`,
`q<d>l`, `q<d>x`) are also depth-indexed, and a nested form at the same depth shadows them only
inside its own operand, which has closed before the outer name is read.

| `Term` | OCaml |
| --- | --- |
| `val n` / `unit` / `none` | `(I n)` / `U` / `Nn` |
| `lam b` | `(F (fun vd -> b))` |
| `app f a` | `(let tda = f in let tdb = a in as_fun tda tdb)` |
| `letIn b body` / `seq f n` | `(let vd = b in body)` / `(f; n)` |
| `add a b` | `(let tda = a in let tdb = b in I (as_int tda + as_int tdb))` |
| `emit r` / `emitOf l e` | `(emit "r")` / `(let tda = e in emit ("l" ^ "\t" ^ render_u tda))` |
| `getCell` / `setCell e` | `(!cell)` / `(cell := e; U)` |
| `eff i p` / `exn i p` | `(Ef (Ei p))` / `(Xn (Xi p))`, `Unhandled`/`Continuation_already_resumed` for `i = 0, 1` |
| `matchEff s cls d` | `(match s with \| Ef (Ei vd) -> … \| vd -> d)` |
| `matchExn s cls d` | `(match s with \| Xn (Xi vd) -> … \| vd -> d)` |
| `raise e` / `tryWith b h` | `(raise (as_exn e))` / `(try b with xd -> let vd = Xn xd in h)` |
| `matchOpt s n sc` | `(match s with Nn -> n \| Sm vd -> sc \| _ -> stuck ())` |
| `perform e` | `(perform (as_eff e))` |
| `resume s f a` / `runstack s f a` | `(let … in resume (as_stk tda) (as_fun tdb) tdc)` |
| `reperform e c l` | `(let … in reperform (as_eff tda) (as_k tdb) (as_lf tdc))` |
| `allocStack hv hx hf` | `Sk (alloc_stack (as_fun tda) (fun qdx -> as_fun tdb (Xn qdx)) (fun qde qdk qdl -> as_fun (as_fun (as_fun tdc (Ef qde)) (Kt qdk)) (Lf qdl)))` |
| `contUseNoexc c` | `(Sk (take_cont_noexc (as_k c)))` |
| `contUseUpdate c hv hx hf` | `Sk (update_handler (as_k tda) (as_fun tdb) … …)` |
| `dropCont c` | `(drop_continuation (as_k c); U)` |

The whole term sits at `let () = ignore (…)`. That is the position `Admissible` reads a term in
(`nonTail`), and `ignore (reperform …)` is one of the ten shapes O5 confirmed `ocamlc` refuses
(report §4, probe `ccall operand`), so the top of the rendered unit and the top of the predicate
agree.

The `alloc_stack` wrapper is the one place where an argument order matters and is not free: the
handler is invoked as `caml_apply3 handler eff cont last_fiber` (`amd64.S:895`,
`interp.c:1355-1357`), and `Stdlib.effcClosure`'s de Bruijn convention binds
`payload :: last_fiber :: k :: eff`, so the wrapper must apply the `u`-valued closure to
`Ef eff`, then `Kt cont`, then `Lf last_fiber`, in that order. The rendered witnesses' rows are
the check that it does.

## 3. `render` is faithful on the corpus

```
$ ./workshop/OCaml5/tools/fuzz.sh witnesses
witnesses 13
programs checked: 13
   12 AGREE
    1 HOSTS
disagreements: 1
  HOSTS w12-drop
```

Per witness the script does: `Machine.rows` of `Term.render`'s input must equal the bytecode rows
`OCaml5.Witnesses` recorded in round one (13/13); then `ocamlc -w -a` + `ocamlrun`,
`ocamlopt -w -a`, and `js_of_ocaml compile --enable effects --target-env=nodejs` + `node` on the
rendered source, and all four row lists compared. `AGREE` means the machine, the bytecode
interpreter, the native code and the JavaScript printed the same list.

So the hand-written witness files of O1 and the machine-rendered ones are behaviourally the same
programs — including `w11-shallow-reinstall`, whose `Shallow.fiber` renders through
`caml_continuation_use_and_update_handler_noexc` and a local `exception E`, and
`w08-reperform-root`, whose `Kreperformterm` is in the tail of a `match` arm inside an
`alloc_stack` closure. One rendered witness is kept for eyeballing at
`workshop/OCaml5/fuzz/rendered/w01-repeated.ml`.

`w12-drop` is the same divergence round one recorded: js_of_ocaml 5.7.1 does not implement
`caml_drop_continuation`. It is host-vs-host, not Lean-vs-hosts. §6.

## 4. The generator

`OCaml5.Fuzz` is a pure PRNG (xorshift64 behind a SplitMix scramble), a `StateM Rng` generator,
and filters. Everything is a function of one `Nat` seed, which is what makes shrinking stateless:
a shrink is a list of one-step-reduction indices, and `stepsOf seed size path` replays generation
and then applies them, so no term is ever serialised and `fuzz.sh` can hand a path back to Lean.

**Sorts.** The generator tracks a `VSort` for every binder — `int` (an integer it may read back),
`cont` (the `k` of an `effc` clause, always at `.var 2` by `Stdlib.effcClosure`'s convention),
`opaque` (everything else) — and only ever emits `.var i` where the sort fits the use. That is
what makes the rendered coercions total: no generated program can reach `as_fun (I 3)`.

The environments are the delicate part, because the `Stdlib` builders are terms with holes at
different depths. For `Stdlib.deepMatchWith comp arg retc exnc effc` placed with outer
environment Γ: `retc`, `exnc` and the `effc` table sit inside the `alloc_stack`, at Γ; `comp` and
`arg` sit under the `let s = alloc_stack …` binder of `effect.ml:78`, so they are at
`stack :: Γ`; and an `effc` clause body is at `payload :: last_fiber :: k :: eff :: Γ`, and runs
on the *parent* stack, so the effects it may `perform` are Γ's handled set, not this handler's.
Witness 10 is the reason that last point is a rule and not a detail.

**The grammar**, all integer-valued, weighted and fuel-bounded (`genInt`):

| alternative | weight | what it exercises |
| --- | --- | --- |
| literal / integer variable | 14 | leaves |
| `add` | 10 | that a resumed value really came back |
| `emit; e` | 10 | rows |
| `let x = e in emitOf x; e'` | 12 | observable intermediate values |
| `perform` of a handled effect | 14 | `PERFORM` with a parent; `Unhandled` at the root when nothing handles it |
| deep handler (`try_with` / `match_with` / logging `try_with`) | 18 + 14 | `runstack`, `alloc_stack`, `reperform` forwarding, `retc`, `exnc` |
| `try … with X p -> …` around a raiser | 8 | traps, `raise` past a fiber boundary |
| `match … with None \| Some x` | 4 | options |
| `Fun.protect ~finally` | 4 | a trap a `discontinue` must run through |
| the parking template | 4 | `setCell`, resume/discontinue/drop after the handler returned |
| `Shallow.fiber` + `continue_with` | 2 | `caml_continuation_use_and_update_handler_noexc` |

Handler clause bodies are drawn separately: `continue` with a generated value, `discontinue` with
a user exception, abandon the continuation, or witness 02's double-`continue` shape whose second
resume must raise `Continuation_already_resumed`.

**Filters** (`Fuzz.classify`), applied before a program is written: `Compiler.Admissible`; the
machine's outcome must be `.value` or `.uncaught`, never `.stuck` or `.fuel`; at least one row and
at most 400; every row `rowSafe`. Of 1360 draws across the pilot and the campaign, 1360 passed —
the generator is well-sorted by construction rather than by rejection, which is the point of
tracking `VSort`.

**Shrinking** is `shrinks : T → List T`, the one-step reductions of a term in a fixed order
(replace a node by `.val 0` or by one of its `Term`-typed children; drop a clause; reduce one
subterm), and a greedy loop in `fuzz.sh`: emit every candidate at the current path, run the three
hosts on each, take the first whose verdict is still the original class, recurse. Reductions are
blind about scope; a candidate whose de Bruijn indices no longer make sense simply gets stuck and
is rejected by `classify`, so the shrinker never has to be clever.

## 5. The campaign

```
$ ./workshop/OCaml5/tools/fuzz.sh run 100000 250 4     # and 200000/250/5 … 600000/150/9
```

| size | seeds | generated | kept | AGREE | HOSTS | LEAN | REFUSED |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 4 | 100000–100249 | 250 | 250 | 242 | 8 | 0 | 0 |
| 5 | 200000–200249 | 250 | 250 | 240 | 10 | 0 | 0 |
| 6 | 300000–300249 | 250 | 250 | 236 | 14 | 0 | 0 |
| 7 | 400000–400249 | 250 | 250 | 232 | 18 | 0 | 0 |
| 8 | 500000–500149 | 150 | 150 | 136 | 14 | 0 | 0 |
| 9 | 600000–600149 | 150 | 150 | 133 | 17 | 0 | 0 |
| **total** | | **1300** | **1300** | **1219** | **81** | **0** | **0** |

Per-seed verdicts are in `workshop/OCaml5/fuzz/results/size-<n>.tsv` and `all.tsv`; the sources
are not kept, because a seed and a size regenerate them exactly (7.5 MB of OCaml for the 1300).

Outcomes as the machine saw them: 1101 `value`, 199 `uncaught` — the `uncaught` ones are the
programs whose `perform` reached the root, or whose user exception escaped every handler, so the
host prints a fatal error on stderr after the rows and exits 2. Their stdout rows still matched.
6627 rows in all, median 3 per program, longest 31.

What the 1300 actually reached, counted on the rendered sources by call site:

| primitive | programs that call it |
| --- | --- |
| `%runstack` / `caml_alloc_stack` / `%reperform` in an `effc` default | 983 |
| `%perform` | 983 |
| `%resume` | 971 |
| `caml_continuation_use_noexc` | 930 |
| `try … with` | 893 |
| the cell (`r := k`) | 304 |
| `caml_continuation_use_and_update_handler_noexc` (`Shallow`) | 175 |
| `caml_drop_continuation` | 118 |

The 317 programs with no handler at all are the ones whose top-level draw was arithmetic,
sequencing and prints; they are cheap and they check the boring half of `stepEval`.

## 6. Every disagreement

All 81 are host-vs-host, and all 81 call `caml_drop_continuation`. In all 81, `ocamlc` + `ocamlrun`,
`ocamlopt` and `Machine.rows` produced the *same* list and js_of_ocaml produced a different one.
No program that does not call `caml_drop_continuation` disagreed with anything. This is the O1
report §6 finding — js_of_ocaml 5.7.1's `runtime/effect.js` has no `caml_drop_continuation` and
`Failure "caml_drop_continuation not implemented"` is raised when one is reached — reproduced 81
times from independent random programs, and it comes in two observables.

### 6.1 `drop-min`: js_of_ocaml dies

Seed 100010 at size 4, shrunk by eleven one-step reductions
(path `1 12 12 24 23 24 31 31 32 36 40`). Source:
`workshop/OCaml5/fuzz/min/drop-min.ml`; pinned in `Fuzz.lean` as `dropMinTerm`, with a `#guard`
that `stepsOf 100010 4 [1, 12, …]` renders to exactly it.

```
let () = ignore
  (let v0 =
     (let v0 = Sk (alloc_stack (as_fun (F (fun v0 -> (I 0)))) … (fun … ->
                     match v0 with
                     | Ef (E2 v3) -> (cell := v1; U)     (* park the continuation *)
                     | v3 -> (I 0)))
      in runstack (as_stk v0) (as_fun (F (fun v1 -> perform (as_eff (Ef (E2 U)))))) U)
   in let v1 = (drop_continuation (as_k (!cell)); U)
      in emit ("r56530" ^ "\t" ^ render_u v1))
```

| row list | |
| --- | --- |
| `Machine.rows` | `r56530 ()` |
| bytecode (`ocamlrun`) | `r56530 ()` |
| native (`ocamlopt`) | `r56530 ()` |
| js_of_ocaml + node | *(empty)*, `Fatal error: exception Failure("caml_drop_continuation not implemented")` |

### 6.2 `drop-caught`: js_of_ocaml diverges silently

The same gap with the `drop` inside a `try`. Ten of the 81 have this shape; shrinking one of them
preserves the class but routes the `Failure` into a coercion trap, which is a shrinker artefact
rather than a cleaner witness, so the companion is hand-built from the witness-07 shape and
checked on all three hosts. Source: `workshop/OCaml5/fuzz/min/drop-caught.ml`; pinned as
`dropCaughtTerm`.

| row list | |
| --- | --- |
| machine, bytecode, native | `perform` `handled` `parked` `status 2` `drop` `after 0` |
| js_of_ocaml + node | `perform` `handled` `parked` `status 2` `drop` **`caught`** `after 9` |

js_of_ocaml does not die: the program's own `try` catches the runtime's `Failure` and takes a
branch the two OCaml hosts never take. That is the dangerous shape of this gap — a program that
uses `caml_drop_continuation` and has any exception handler around it will silently compute a
different answer under js_of_ocaml, with a zero exit status.

### 6.3 Which arm each implicates

* **P1, the run invariant.** None. Zero Lean-vs-host disagreements over 1313 programs (1300
  generated plus the 13 witnesses) means the campaign found no arm of `Machine.step` to correct,
  and in particular no counterexample to the invariant P1 is proving. The arms most heavily
  exercised are `doPerform` with a parent, `doResumeStack`, `doRunstack`, `doReturnToParent`,
  `doRaiseToParent` and `doReperform` with a parent, each in 971–983 programs; the root arms
  (`doPerform` with no parent, `doReperform` with no parent) are covered by the 199 `uncaught`
  outcomes.
* **P3, `MachineJ`.** `Machine.doDropCont` (`Effect.lean`, `fiber.c:659-664`) is the arm with no
  counterpart in `effect.js`. P3's bisimulation between `Machine.step` and `MachineJ.step` cannot
  cover `Term.dropCont`: either the relation carries the hypothesis "the term contains no
  `dropCont`", or `MachineJ` models the gap explicitly, with `dropCont` stepping to
  `.throw (.exn failureExn …)` so that §6.2's `caught` row is *derived* rather than a divergence.
  The second is the honest one, because §6.2 shows the difference is observable inside a program
  and not only at its edge. Either way, §6.1 and §6.2 are the two witnesses that relation has to
  account for, and both are now in `Fuzz.lean` with all four row lists.
* **O5, `Admissible`.** `Admissible` accepted 1313 terms and `ocamlc` refused none of them. That
  is executed evidence for the direction O5 claims — `Admissible t = true` implies `ocamlc`
  compiles `t` — on 1300 machine-generated shapes rather than the eighteen hand-written probes.
  It says nothing about the converse, which O5 already records as deliberately conservative
  (`let x = reperform … in x`).

## 7. Part two: a general Lean → OCaml declaration surface

After the campaign above landed as a checkpoint, the estate's target changed: spike A0 wants an
OCaml **avatar** of the Effect runtime — `workshop/Deep/Fibers.lean` transcribed into OCaml 5
effects — and asks P5 how that OCaml gets *generated* rather than hand-written.

`Term.render` is the wrong shape for that. It emits one expression over the raw effect primitives
into a fixed prelude, which is what a reference machine needs; an avatar needs declarations —
records, variants, `let rec`, handler blocks. `Render.lean` now carries a second, independent
surface, `OCaml5.Ml`.

It is a **reflected description, not metaprogramming**: `Ml.TypeDecl`, `Ml.Expr` and `Ml.Decl` are
ordinary Lean data that A0 populates by hand from `Fibers.lean` — a `structure` becomes an
`Ml.TyBody.record`, an `inductive` an `Ml.TyBody.variant` — and `Ml.moduleText : List Ml.Decl →
String` renders a compilation unit. Nothing inspects a Lean declaration. If and when the mapping
is settled, an elaborator that builds these values from `Lean.Expr` is a later step, and this type
is the interface it would target.

Covered: type parameters; records with `mutable` fields; variants; type aliases; mutually
recursive type groups joined by `and`; `ref`, `!` and `:=`; `let rec … and …` with optional
parameter and result annotations; `match` with `when` guards, `try … with`, `if`, tuples, lists,
record literals and functional update (`{ b with … }`), field read and mutable-field write;
`exception`; `external`; `open`; effect declarations as
`type _ Effect.t += C : t -> answer Effect.t`; and `Effect.Deep.match_with` / `Effect.Deep.try_with`
blocks with a `retc`/`exnc`/`effc` record. Expressions are parenthesised aggressively rather than
by a precedence table — `ocamlc` accepts redundant parentheses, and a wrong precedence table is a
silent miscompile.

### The probe

`Ml.Deep.sample` is a slice of `Fibers.lean` written in the surface, one `Ml` value per Lean
declaration:

| `Fibers.lean` | `Ml` |
| --- | --- |
| `abbrev FiberId := Nat` | `TyBody.alias` |
| `inductive Parked` (`:62-65`) | `TyBody.variant` |
| `inductive Resume (ν)` (`:68-75`) | `TyBody.variant`, one parameter |
| `structure Pending` (`:81-87`) | `TyBody.record`, `mutable` on the counted-down fields |
| `inductive Observer` (`:93-100`) | multi-argument constructors |
| `Task` / `Bucket` / `Dispatcher` (`:104-120`) | one `Decl.types` group joined by `and` |
| `structure RunFiber` (`:157-173`) | `TyBody.record` |
| `inductive Stuck` (`:332-335`) | `Decl.exn` |
| `Dispatcher.enqueue` (`:137`) | `Decl.letD true`, mutually recursive, `when` guard, mutable writes |
| `RunFiber.status` (`:181-191`) | `match` with a guard |
| the interpreter loop | `Effect.Deep.match_with` with an `effc` table |

```
$ ./workshop/OCaml5/tools/fuzz.sh surface
surface 16 declarations
AGREE surface
```

`AGREE` is the four-way one: `ocamlc` + `ocamlrun`, `ocamlopt` and `js_of_ocaml` + `node` all
compile the rendered module, run it, and print the two rows `Ml.Deep.sampleRows` pins in Lean.
The rendered text is at `workshop/OCaml5/fuzz/rendered/surface.ml`; sixteen `#guard`s in
`Render.lean` pin the rendered text of the individual declarations, so a change to the renderer
that would alter the module `ocamlc` accepted fails in Lean rather than silently.

### Two constraints A0 needs before transcribing

1. **The `effc` continuation annotation must name the locally abstract type, `a`, not `'a`.**
   `effect.ml:66-68` types `effc` as `'c. 'c t -> (('c,'b) continuation -> 'b) option`, so a
   clause is `fun (type a) (eff : a Effect.t) -> match eff with | C … -> Some (fun (k : (a, b)
   continuation) -> …)`. Writing `'a` there makes it an ordinary type variable, the GADT match
   does not refine it, and every clause is forced to one answer type — `ocamlc` then rejects the
   *second* effect constructor with a type error pointing at its payload, which reads like a
   mistake in the clause rather than in the annotation. The renderer emits `a`; the first draft
   emitted `'a` and this is how it was found.
2. **OCaml rejects an unused type parameter in a variant; Lean does not.** `Fibers.lean`'s `Task`
   is `Task ν σ β ε δ ι α` and its two constructors mention only some of those. The OCaml
   transcription must drop every parameter no constructor determines — `'b task`, not
   `('nu, 'b) task` — or `ocamlc` refuses the declaration outright. That is a mapping decision A0
   has to make per carrier, and the surface cannot make it: `Ml.TypeDecl.params` is whatever the
   caller writes.

A smoke run after the surface landed (40 fresh programs, seeds 700000–700039, size 6) reproduces
the checkpoint exactly: 37 agree, 3 host-vs-host, all three calling `caml_drop_continuation` and
all three with the Lean machine equal to both OCaml hosts. The `Term` renderer is untouched by
part two; `tools/fuzz.sh witnesses` still gives 12 agree and `w12-drop`.

`docs/research/2026-09-04-spike-a0-avatar.md` does not exist yet, so its "Requests to P5" section
has not been read. When it appears, its requests come next, in its order.

## 8. Findings

1. **The renderer is faithful on everything checked.** 1313 programs, three hosts each; the only
   divergence is a documented js_of_ocaml gap, and the OCaml hosts and the Lean machine never
   parted company. The `Term ─▶ OCaml source` arrow of the §6 diagram is now a Lean function, and
   the corpus is no longer bounded by how many witnesses a person will write.
2. **One universal type is enough.** The `u` encoding renders every `Term` constructor, including
   the four C entry points and both `Deep` and `Shallow` continuations, into source `ocamlc`,
   `ocamlopt` and `js_of_ocaml` all accept, with no type annotation anywhere and no `Obj.magic`.
   The cost is four restrictions (§2), of which only the first (`emitOf` on a heap identity) bites
   at all, and it bites on nothing the machine is meant to model.
3. **The `let`-chain is load-bearing twice.** It fixes OCaml's right-to-left argument order to the
   machine's left-to-right one, and it is exactly the shape that preserves `Admissible`'s
   tail-position discipline. Rendering `reperform` operands inline would have been both wrong and
   uncompilable.
4. **`caml_drop_continuation` is the whole of the js_of_ocaml gap, at least at this size.** 118
   programs called it and 81 of them diverged (the other 37 never reached the call at run time);
   1182 programs never called it and none diverged. On this corpus js_of_ocaml's effects CPS
   transform is behaviourally the OCaml runtime for everything else the fragment can express:
   deep and shallow handlers, forwarding by `reperform`, one-shot enforcement, traps across
   capture, `Unhandled` at the root, and continuations resumed long after their handler returned.
5. **The gap can be silent.** §6.2 is a program that runs to completion under node, exits 0 and
   prints a different answer. Anything that reports js_of_ocaml effects support as "works except
   for a missing primitive" understates it.
6. **A declaration surface is enough to generate an avatar, and it is small.** `OCaml5.Ml` is a
   few hundred lines of ordinary data and one renderer, and it already emits a sixteen-declaration
   slice of `Fibers.lean` that all three hosts compile and agree on. No Lean metaprogramming was
   needed to find that out, and the two constraints of §7 — the locally abstract `a`, and OCaml's
   refusal of an undetermined type parameter — are the kind of thing that is cheap to find with a
   renderer and expensive to find by hand at transcription time.

## 9. Open items

1. **Rows are shallow.** Median 3 rows per program. The grammar prints where it is told to and the
   generator does not force an `emit` at every control-flow junction, so a long control-flow path
   can be observed by a short row list. Biasing the generator towards `emit` at handler entry,
   `retc`, `exnc` and every resume would make each program a stronger test at no extra host cost.
2. **The `handled` set is approximated.** The generator only performs effects some enclosing
   handler in the current fiber chain has a clause for, plus the occasional unhandled one. It
   never constructs a chain where an effect is handled two handlers out *and* shadowed in between
   by a clause that forwards conditionally, which is where `reperform`'s `last_fiber` tail
   splicing (`interp.c:1383-1398`) would be stressed hardest.
3. **`Shallow` is one fixed shape.** `genShallow` is witness 11 with generated constants: a fiber
   that performs exactly twice under a two-handler chain. A generator that unrolls the chain to a
   random depth would exercise `caml_continuation_use_and_update_handler_noexc`'s
   walk-to-the-outermost properly.
4. **The shrinker is greedy and blind.** It found an eleven-step minimisation in 78 s, but it
   preserves only the *class* of the verdict, which is how §6.2's fuzzed instance shrank into a
   coercion trap. Preserving the exact host-vs-host row diff, not just the class, would be a small
   change and a better minimiser.
5. **`Fuzz.lean` declares a root `main`.** `lake env lean --run` needs it there. It is harmless
   while `OCaml5.Fuzz` is a leaf module and nothing else in the tree has one, but at the landing
   the driver should move to its own executable target rather than keep a `_root_.main` in a
   library module.
6. **`emitOf` on a continuation is a modelling hole, not just a filter.** The machine can print
   `cont7`; no host can. If the landing wants rows to be a genuine bisimulation alphabet,
   `Value.render` should refuse the heap-identity constructors rather than invent a spelling for
   them, and `Machine.rows` should be typed to say so.
7. **The `Ml` surface has no module system.** No `module`, no signature, no `include`, no
   `let module M = struct … end in` and no `let exception E in` — which is exactly what
   `Shallow.fiber` (`effect.ml:110-123`) needs for its local effect and its local exception. If
   A0's avatar wants shallow handlers or a per-fiber effect constructor, either the surface gains
   local `module`/`exception` forms or those declarations get hoisted to the top level. Also
   absent: labelled and optional arguments, `while`/`for`, arrays, and `Ml.Ty` has no way to say
   `private` or a constraint. `Expr.raw` and `Decl.rawD` are the escape hatch, and every use of
   one is a place the surface should grow.
8. **The `Ml` surface is untyped.** It will happily describe a module `ocamlc` rejects; the only
   check is executed. A type-checker over `Ml.Decl` is not worth writing, but a discipline for A0
   is: transcribe one carrier, run `tools/fuzz.sh surface`, then the next.
9. **The mapping is by hand.** A0 populates `Ml` values from `Fibers.lean` by reading it. That is
   the right first step — the mapping is not obvious enough to automate before it has been done
   once — but the elaborator that would build `Ml.Decl` from `Lean.Expr` is the thing that makes
   the avatar track the carriers rather than drift from them, and it is not written.
10. **Not run: sizes above 9, and multi-day soak.** The campaign is 1300 programs over six minutes.
   The machinery is a shell loop with a seed range; a nightly job over a few hundred thousand
   seeds costs nothing but time and would be the real evidence.

## 10. Commands

```
$ git rev-parse HEAD                       # 7729f58, the base of round two
$ lake build OCaml5.Effect OCaml5.Compiler OCaml5.Render OCaml5.Fuzz
$ ./workshop/OCaml5/tools/fuzz.sh witnesses
$ ./workshop/OCaml5/tools/fuzz.sh surface
$ ./workshop/OCaml5/tools/fuzz.sh avatar                # round three
$ ./workshop/OCaml5/tools/fuzz.sh tapes 7 60 8          # round three
$ ./workshop/OCaml5/tools/fuzz.sh corpus 400000 220     # round four
$ ./workshop/OCaml5/tools/fuzz.sh corpus-smoke 60       # round four
$ ./workshop/OCaml5/tools/fuzz.sh run 100000 250 4      # … 600000 150 9
$ ./workshop/OCaml5/tools/fuzz.sh shrink 100010 4
$ ./workshop/OCaml5/tools/fuzz.sh _one workshop/OCaml5/fuzz/min/drop-min.ml
```

Toolchain: OCaml 5.1.1 at `/Users/pooks/.opam/default/bin` (`ocamlc`, `ocamlopt`, `ocamlrun`),
js_of_ocaml 5.7.1 at
`.../_build/toolchains/ocaml5-jsoo-5.7.1/.../js_of_ocaml.exe`, node v22.23.2, macOS arm64,
Lean 4.33.1, no Mathlib. Build products under the session scratchpad; nothing written into
`effect4_of_ocaml` or the opam switches. Nothing committed.

## 11. Round three: generating the avatar's carriers (A0's five requests)

`docs/research/2026-09-04-spike-a0-avatar.md` §1 asks P5 for five things, in priority order, so
that `workshop/OCaml5/avatar/deep_fibers.ml` is *generated* from the Lean carriers rather than
retyped. Round two's `OCaml5.Ml` already rendered records, variants and `let rec` groups; what
round three adds is the layer that drives it from a **description of the actual `Deep` carriers**,
and the two mappings that description needs.

| # | Request | Landed |
| --- | --- | --- |
| 1 | Lean `structure` → OCaml record, same field order, total injective mangling | **yes**, byte-identical to `deep_fibers.ml`'s `run_fiber` |
| 2 | Lean `inductive` → OCaml variant, same order, arity for arity | **yes**, three of five byte-identical; the other two have no identical counterpart, §11.3 |
| 3 | a `let rec` group with the pure-update → mutation rewrite as a named pass | **partly**: the pass and two functions, not all three A0 named |
| 4 | a differential fuzzer over `RunDecision` tapes | **partly**: the tape, the wire and the type-check; the comparison is blocked, §11.6 |
| 5 | never render `Prim`/`FrameFiber.step`; emit a hole | **yes**, three holes, and `prim` occurs nowhere in the output |

```
$ ./workshop/OCaml5/tools/fuzz.sh avatar
avatar 19 declarations
holes 2 in FrameFiber
ocamlc     OK
ocamlopt   OK
js_of_ocaml OK
run_fiber: IDENTICAL to deep_fibers.ml
frame_fiber: IDENTICAL to deep_fibers.ml
observer: IDENTICAL to deep_fibers.ml
run_event: IDENTICAL to deep_fibers.ml
run_decision: IDENTICAL to deep_fibers.ml
```

`IDENTICAL` is a byte comparison against A0's file itself, not against a copy of it: the script
cuts the block out of `workshop/OCaml5/avatar/deep_fibers.ml` and out of the generated module and
runs `diff`. So the claim decays the moment either side changes, which is the point — and it did,
once, during this session: A0 added a sixteenth field to `run_fiber` while the diff was running,
the check went red on exactly that field, and the description now records it (§11.2).

The round-one and round-two checks are unaffected and were re-run on the same tree:
`fuzz.sh witnesses` 12 agree + `w12-drop`, `fuzz.sh surface` AGREE, and a 40-program smoke
(seeds 800000–800039, size 6) 38 agree with 2 host-vs-host, both calling
`caml_drop_continuation` and both with the Lean machine equal to the two OCaml hosts.

### 11.1 The two mappings

**Names.** `Ml.mangleField` is total, and injective because `Ml.unmangleField` is an exhibited
left inverse. The code: a lowercase letter or digit is itself; an uppercase `X` is `_` ++
lowercase `X`, which *is* camelCase → snake_case; `_` is `_0`, `'` is `_1`, anything else is `_2`
++ three decimal digits; and an image that is an OCaml keyword — or `exit` — gets one `_`
appended. That last step cannot collide, because every escape `_` is followed by a letter or a
digit, so no image of the character code ends in a bare `_`. `exit` → `exit_` is
`deep_fibers.ml:194`, and `currentOpCount` → `current_op_count` is the camel rule. The pair that
a naive `camelToSnake` would collapse is separated: `aB` → `a_b`, `a_b` → `a_0b`.

`typeName` is the same code minus the leading `_` an initial capital produces (`RunFiber` →
`run_fiber`). `ctorName` takes a per-type prefix: empty means capitalise the initial
(`resumeAwait` → `ResumeAwait`), non-empty means the prefix supplies the capital and the Lean name
is kept (`"C"`, `drainDue` → `CdrainDue`). Those prefixes are **not derivable** — they are how
`deep_fibers.ml` keeps `Cmd`, `RunDecision` and `Observer` from colliding in one module — so they
are a field of the description, and so are the two per-constructor overrides a prefix cannot
solve: `RunEvent.frame` → `FrameEv` (the `frame` field) and `RunEvent.callback` → `CallbackEv`
(`Observer.callback`).

**Types.** `Ml.Avatar.subst` is one visible list: `Exit β ε δ ι α` is `exitv`, `Cause ε δ ι α` is
`cause`, `ReasonAnnotations α` is `string list`, `FrameEvent` is `string`, `χ` is `unit`, `ν` is
`string`, `Prim …` in an answer position is `answer`. Keyed on the head, arguments dropped on a
hit, because the avatar is one profile of the family and its parameters are fixed by the fixture.
Every entry is a substitution A0 made by hand; collecting them in one place is most of the value
of doing this at all.

### 11.2 Request 1: `RunFiber`

`Ml.Avatar.runFiber` is the fifteen fields of `Fibers.lean:157` in the Lean order, with
`isMutable` on the thirteen the avatar updates in place (everything but `id` and `frame`,
DIVERGENCE 3). The rendered record is byte-identical to `deep_fibers.ml`'s `run_fiber`, `exit_`
included. `#guard`s pin the field list, the count, the mutable count, and the round-trip
`unmangleField ∘ mangleField = id` on every one of them.

There is a sixteenth field, and it is the one interesting thing the diff found. Partway through
this session A0 added `mutable yielding : bool` — no Lean counterpart, carrying `Cmd.loop`'s
`yielding` argument on the fiber because `Cmd.loop` has no OCaml existence (DIVERGENCE 2). The
check went red on exactly that field and on nothing else. It is now a `FieldKind.substitute` in
the description, with A0's own four-line comment carried verbatim, and `#guard`s separate the
fifteen Lean fields from the one substitute. A field with no Lean counterpart is the thing a
simulation relation cannot see, so the description had better name it.

### 11.3 Request 2: the five inductives

| carrier | Lean | rendered | against `deep_fibers.ml` |
| --- | --- | --- | --- |
| `Observer` (`:93`) | 6 | 6 | IDENTICAL |
| `RunEvent` (`:305`) | 22 | 22 | IDENTICAL |
| `RunDecision` (`:362`) | 7 | 7 | IDENTICAL |
| `Cmd` (`:526`) | 5 | 5 | differs by exactly `Cloop`, §11.5 |
| `WithFiberAction` (`:258`) | 17 | 17 | no counterpart: the avatar substitutes `Effect.t` constructors |

Two counts in the request are off by one against the file: `RunEvent` has 22 constructors, not 23,
and `WithFiberAction` has 17, not 18. Worth reconciling before the simulation relation is stated
arm by arm.

Two arguments A0 dropped by hand are now **recorded** rather than silently absent, as
`CtorArg.erased`: `RunEvent.scopeLinked.mode` (a `Supervision.ScopeMode` the avatar does not
carry) and `RunEvent.contextSet.context` (`χ` is `unit` in this profile). `InductiveDesc.erasures`
lists them and a `#guard` says that every other constructor is arity for arity. The five
`WithFiberAction` erasures are all `Prim` arguments, which is request 5 (§11.5) rather than a
substitution.

### 11.4 Request 3: the mutation pass

`Ml.mutate` is the named pass. It fires on one shape and only one:

```
let f = { f with x = v; y = w } in body            ⟶   f.x <- v; f.y <- w; body
let f = { f with g = { f.g with x = v } } in body  ⟶   f.g.x <- v; body
```

for `f` in a declared **linear** set, and only when the `let` rebinds the name it updates. When
the body is just `f` — a Lean function returning the updated record — the result is `()`, because
the OCaml caller already holds it.

`Ml.residue` is the checker: the `{ … with … }` occurrences the pass did *not* eliminate. Both
functions below are `#guard`ed to have empty residue after the pass and non-empty before, so
"the pass applied everywhere" is a fact rather than a hope.

Encoded: `RunFiber.park` (`Fibers.lean:249`, two updates) and `interruptRecord` (`:550`, three
updates, one of them nested through `frame`). `interruptRecord` is where three divergences meet
and each is visible in the output — the mutations, the dropped record half of the returned pair,
and the `Prim` hole. Not encoded: `fireObserver` (`:923`) and `exitFiber` (`:992`); the pass does
not need them and they are a transcription job, but the request named three and two are here.

The generated text is arm for arm with `deep_fibers.ml:386-410`; the visible difference is
parenthesisation — `((f).frame).interrupted_cause <- …` where A0 writes
`f.frame.interrupted_cause <- …` — because `Ml` parenthesises aggressively rather than carrying a
precedence table (§7).

### 11.5 Request 5: the holes

`Ml.FieldKind.hole` on a field and `Ml.Expr.hole` in an expression. Three holes reach the output
and `prim` reaches it nowhere (both `#guard`ed):

* `FrameFiber.current : Prim …` and `FrameFiber.stack : List (Prim …)` — not rendered at all. The
  record that comes out is A0's four-field `frame_fiber`, byte-identical, with `control` as the
  declared substitute;
* `interruptRecord`'s `frame := { f.frame with current := Prim.failure accumulated }` — rendered
  as `(* HOLE: FrameFiber.current := Prim.failure accumulated (Fibers.lean:571) *) frame_fail f
  accumulated`. `frame_fail` is the hand-written filling, `deep_fibers.ml:405-409`, and it is the
  only line of that function a human has to write.

`Cmd.loop` is a different kind of gap and is treated differently: it is rendered, arity for arity
as the request asks, and carries a generated comment saying it is absent from `deep_fibers.ml`
(DIVERGENCE 2). A divergence the generator states is better than one it absorbs.

### 11.6 Request 4: what a tape is, and what blocks the comparison

Landed: `Fuzz.genDecision`/`genTape` draw `RunDecision` tapes uniformly over the seven
constructors, and print each entry twice from the same draw — as the OCaml literal and as a wire
line — with both spellings derived from `Ml.Avatar.runDecision`, so they cannot drift from the
type the same description generates. `tools/fuzz.sh tapes SEED COUNT LEN` writes both and
compiles the OCaml on all three hosts, which is what makes "every generated tape is a well-typed
`run_decision list`" a fact.

Blocked, and this is the report: the comparison needs two things P5 does not own.

1. **The avatar has no `RunDecision` entry point.** `EFFECT4_TAPE` is the *fork-branch* tape of
   `harness/trace/fiber-tail.ts` — `site:branch` pairs, read by `Tape.decide`
   (`deep_fibers.ml:48-58`) — and `avatar_main.ml` never consumes a `run_decision`. The type is
   declared (`:329`) and unused. A reader against the wire above, and a driver that feeds it to
   the machine the way `replayEval` does, is A0's half.
2. **`replayEval` is in another spike's file.** `Effect4.Deep.replayEval` is
   `workshop/Deep/Fibers.lean:1164` and needs a `Stores` fixture (`Deep.Witnesses.replay`,
   `:45`). Importing `Deep.Fibers` from `OCaml5.Fuzz` couples this spike to a file P1 and A0 are
   both editing; the round-two rule — own your file, import the frozen ones — says not to, until
   the names are frozen.

So request 4 landed as its wire and its generator, and the differential half is one reader away on
each side.

### 11.7 Findings for A0

1. **Five of six carriers come out byte-identical.** The hand-written transcription was accurate;
   what the generator adds is that it stays accurate. The three checks that matter are cheap and
   now exist: the diff against the real file, the compile on three hosts, and the `#guard`s on
   order, arity and mangling.
2. **The non-mechanical decisions are exactly three, and they are now enumerated.** The
   substitution table (17 entries), the constructor prefixes (four), and the two name overrides.
   Everything else — order, arity, mutability, layout, names — is derived. That is the shape of
   the elaborator this should eventually become: it would compute all of the second list and none
   of the first.
3. **Two erasures, one extra constructor and one extra field are the whole diff.**
   `RunEvent.scopeLinked.mode` and `RunEvent.contextSet.context` are dropped by hand in
   `deep_fibers.ml`; `Cmd.loop` is present in Lean and absent in OCaml; `run_fiber.yielding` is
   present in OCaml and absent in Lean. Nothing else in the carriers differs. For a simulation
   relation stated field by field and arm by arm, that is the complete list of places that need a
   clause of their own — and the last one, a field with no Lean counterpart, is the only one the
   relation cannot state as an equality.
4. **Declaration order is not Lean order.** `deep_fibers.ml` declares `Observer` before
   `RunFiber` because OCaml needs it to; `Fibers.lean` declares `RunFiber` at `:157` and
   `Observer` at `:93` for its own reasons. The generator sorts by dependency and says so; a
   future elaborator must too, and it is a topological sort over the substitution table, not over
   the Lean file.
5. **The mangling had to be designed, not guessed.** `camelToSnake` alone is not injective —
   `aB` and `a_b` collide — and the simulation relation is stated field by field, so a collision
   would be a hole in the relation rather than a cosmetic bug. The escape code above is injective
   and has a left inverse that is run on every name in the corpus.

### 11.8 What did not land

1. `fireObserver` (`Fibers.lean:923`) and `exitFiber` (`:992`) are not encoded. They are the two
   longest of the three, both build `Cmd` lists and match over `Observer`, and both are within the
   surface — `Ml.Expr` already has `matchE`, `listLit`, `binop` and the mutation pass. It is
   transcription time, not a missing capability.
2. `Ml.mutate` handles one level of nesting (`{ f with g = { f.g with x = v } }`). A third level
   would need `setPath` to walk further; nothing in `Fibers.lean` has one today.
3. The differential comparison of request 4, for the two reasons in §11.6.
4. `Ml` still has no module system (§9 item 7), which `Shallow.fiber`-shaped code needs. The
   avatar does not need it yet.
5. **A cross-spike build coupling, worth naming.** `workshop/OCaml5/Compiler.lean` imports
   `OCaml5.Witnesses`, and P3 has added `import OCaml5.EffectJsoo` to `Witnesses.lean`. Every
   consumer of `Compiler` — this spike included — therefore cannot build while `EffectJsoo.lean`
   is mid-proof, and during this session that was several times: the tree went green, red, green
   and red again over an hour as P3 worked, and §11 had to be verified in the green windows.
   It is green as this is written, and every claim in §11 was re-run on it. Additive-only on a
   shared file is not enough: an *import* added to a shared file is not additive for that file's
   consumers, and the plan's parallel-spike rule should say so.

## 12. Round four: a program corpus, rendered twice

The user's round-four instruction: the corpus must be far larger and nastier, and **request 4 is
unblocked by changing the reference** — rc.112 itself, through the estate harness, is the oracle,
not `replayEval`. That is the right move. §11.6 recorded two blockers, and both were about
`replayEval`: the avatar has no `RunDecision` entry point, and importing `Deep.Fibers` would
couple this spike to a file two other spikes are editing. With rc.112 as the reference neither
matters: the comparison is `avatar` vs `rc.112` on programs generated here, and the tape is the
one both faces already read — `site:branch`, `deep_fibers.ml:48-58` and `fiber-tail.ts`'s
`decide`.

### 12.1 The alphabet

One Lean description per program, over what the avatar answers (`deep_fibers.ml`'s `Effect.t`)
intersected with what the estate's *generated* fixtures declare, so both renderings land in a
shape the existing runners consume:

| family | operations | OCaml wrappers | TypeScript service |
| --- | --- | --- | --- |
| fiber | `fork`, `forkDetach`, `join`, `awaitValue`, `awaitError`, `interrupt`, `started`, `cleanups` | `Fibers_fixture` | `Fibers` (`fiber-fixture.ts`) |
| fiber, extra | `yieldNow`, `interruptAll`, `awaitAll` | `Extra_fixture` | declared on `Fibers` here |
| ref | `make`, `get`, `set`, `update`, `modify`, `getAndSet` | `Store_fixtures` | `Refs` (`ref-fixture.ts`) |
| deferred | `make`, `succeed`, `fail`, `isDone`, `poll`, `awaitValue`, `awaitError` | `Store_fixtures` | `Deferreds` |
| scope | `make`, `addFinalizer`, `remove`, `close` | `Store_fixtures` | `Scopes` |
| layer | `build`, `provideCount`, `scopeOf`, `close` | `Store_fixtures` | `Layers` |

Three rows are in the avatar and in rc.112 (`Effect.yieldNowWith`, `Fiber.interruptAll`,
`Fiber.awaitAll`) but not in the generated fiber fixture's service; a program using one is flagged
`usesExtra` in its `meta.json`, and the generated `fixture.ts` declares them on `Fibers` so the
file typechecks as it stands. `Op_ref_try_take` is in the avatar and not in `ref-fixture.ts`, so
it is out.

Two of the brief's asks enter through the **shared child-body table** rather than as operations,
because that is where the estate puts them and a fork names a declared root, never a closure:

* **masks** — body 5 masks itself across a yield and takes the interrupt only when it restores
  interruptibility (M2, `fibers_fixture.ml:28-35`). 26 forks in the corpus draw it;
* **a deferred completed by a sibling or a daemon** — body 6 completes the `Deferred` at handle
  0 (`:36-40`), the one shape M1 is about. 14 forks draw it, and the generator only draws it once
  the program has made a deferred, so the handle exists.

`raceAll` is **not** generated: the avatar refuses it (`Op_refuse "raceAll"`,
`extra_fixture.ml:75`), so every such program would be a refusal on one side and a race on the
other. That is a gap in the avatar, not in the generator, and it is recorded here rather than
papered over.

### 12.2 One description, two renderings

`Corpus.Op` is 31 constructors and every operand is a **variable number**, so a program is
self-contained and well-scoped by construction: the generator only draws an operand from the
handles of the right kind the program has already bound. `Prog.wellScoped` decides it anyway, and
a `#guard` runs it over thirty consecutive seeds of the committed schedule — a badly scoped
program would be a type error on *both* sides, and the corpus is meant to compile unattended.

`Op.ocaml` renders the avatar's fixture spelling, qualified (`Fibers_fixture.fork 0`,
`Store_fixtures.ref_modify v3 4`, `Extra_fixture.await_all [ v0; v2 ]`), so a generated module is
one more entry in `build-avatar.sh`'s module list and needs no edit to any other file. A binding
nothing later reads is named `_vN`, which is how `fibers_fixture.ml` spells its own
(`let _a = fork 0`) and what keeps `ocamlc` warning-free.

`Op.ts` renders the generated fixtures' spelling, with nullary rows as *properties*
(`fibers.started`, `deferreds.make`, `layers.close`) exactly as `fiber-fixture.ts` and its
siblings declare them, and the `Context.Service` declarations and `Rows` tables are copied from
those files verbatim.

Both bodies come from the one `ops` list in one pass, so they cannot drift: `#guard`s check that
the OCaml body has one line per operation and the TypeScript body one `yield*` per operation plus
one per service acquired.

### 12.3 The corpus

```
$ ./workshop/OCaml5/tools/fuzz.sh corpus 400000 220
corpus 220 programs, 5158 operations, 721 forks, 155 using the extra rows
```

`workshop/OCaml5/fuzz/corpus/<name>/{fixture.ml,fixture.ts,tape,meta.json}`, 220 directories, plus
three files a runner links rather than 220: `corpus_fixture.ml` (every program and the `programs`
table `avatar_main.ml` looks a name up in), `corpus-fixture.ts` (the five services once, then
every program, then `corpusPrograms`), and `index.tsv`. 4.6 MB in all.

The seed schedule is `400000 … 400219` and the size of a program is a fixed function of its seed
(`5 + (seed * 7 + 3) % 36`), so the whole corpus is two numbers: nothing is stored that a
regeneration would not reproduce byte for byte.

| | |
| --- | --- |
| programs | 220 |
| operations | 5158, min 6, median 23, max 41 |
| forks | 721, at most 11 in one program; 127 of them daemons (`forkDetach`) |
| tape entries | 721, one per fork, `site:branch` |
| programs using all five families | 47 |
| programs using the extra rows | 155 |
| child bodies drawn | 0 (207), 1 (167), 2 (101), 3 (90), 4 (116), 5 (26), 6 (14) |

Every operation of every family is exercised dozens of times: `ref` 547 operations, `deferred`
500, `scope` 296, `layer` 287, `fiber` 3528, and no single store row fewer than 22.

### 12.4 The smoke check

```
$ ./workshop/OCaml5/tools/fuzz.sh corpus-smoke 60
corpus: 220 programs
ocamlc avatar modules   OK
ocamlc corpus_fixture   OK (220 programs in one module)
ocamlc per-program      60 of 60 sampled
tsc corpus-fixture      OK (220 programs) + 60 sampled fixtures
```

The aggregates are the strong half: one `ocamlc -c corpus_fixture.ml` against the avatar's own
modules typechecks **every** generated OCaml program at once, and one `tsc` run over
`corpus-fixture.ts` typechecks every generated TypeScript program at once. The sample then checks
that each per-program file also stands alone. `ocamlc` is OCaml 5.1.1 with default warnings, not
`-w -a`, and the corpus is warning-free. `tsc` is the estate's own
(`node_modules/.bin/tsc`, `@effect/tsgo`) under the harness's compiler options — `strict`,
`exactOptionalPropertyTypes`, `noUncheckedIndexedAccess`, `verbatimModuleSyntax`, bundler
resolution; the `@effect/language-service` plugin block is dropped because it is a
language-service plugin and `tsc` does not run it. The check was confirmed to have teeth by
introducing a deliberate type error and watching it fail.

### 12.5 What A0 needs to run it

Two additions, both small and both on the runner's side of the ownership line:

1. **OCaml.** Add `corpus_fixture.ml` to `build-avatar.sh`'s module list after
   `extra_fixture.ml` and a `| "corpus" -> Corpus_fixture.programs` arm to `avatar_main.ml`'s
   family table. Each program's tape is in its directory and in `index.tsv`; the rules string in
   `meta.json` is the fiber family's.
2. **TypeScript.** A tail over `corpus-fixture.ts` that provides the services a program needs —
   `Fibers` as `fiber-tail.ts` builds it, plus `Refs`/`Deferreds`/`Scopes`/`Layers` from their own
   tails — and picks the program out of `corpusPrograms`. The three `usesExtra` rows are
   `Effect.yieldNowWith`, `Fiber.interruptAll` and `Fiber.awaitAll`; `fibers-tail.ts` already
   spells the last two.

The wire header each program expects is in its `meta.json`: `program corpus.<name>`, its `tape`,
and the rules string.

### 12.6 Limits, stated

1. **Nested forks are not expressible.** A fork names a declared root from a fixed table, so a
   child cannot fork; the corpus's nesting is the parent's fork tree over that table, not
   arbitrary depth. Changing that means generating child bodies too, and a child body has to
   exist identically on both faces — a bigger change to the fixture format than this round is.
2. **`raceAll` is absent**, because the avatar refuses it (§12.1).
3. **Masks are body 5 only.** `Op_set_interruptible` exists in the avatar but rc.112's
   counterpart is a *region* (`Effect.uninterruptible`), not a flag, so a flag-shaped operation
   has no faithful TypeScript rendering. Body 5 is the shape both faces already agree on.
4. **The corpus is fiber-heavy** by design (3528 of 5158 operations), because the fiber family is
   where the machine lives. The store families are the interleaving, and the weights are one
   line each in `Corpus.genOp` if a different mix is wanted.
5. **Programs may park.** A `join` on a never-settling child, or an `awaitAll` over one, parks —
   which the harness turns into a frontier, as `emptyRacePendingUntilInterrupted` already is.
   That is deliberate and is the interesting half of the corpus, but it means a run needs the
   budget and stall settings the goldens use rather than a naive timeout.
6. **The corpus is not run here.** P5 generates and compiles both sides; A0 runs them and
   compares. Nothing in this section claims agreement — only that 220 programs exist, that they
   are well-scoped, and that both renderings compile.
