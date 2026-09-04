# Spike P5: Lean emits OCaml — a renderer, a generator, and a fuzzing campaign

Status: 2026-09-03 night, round two. Spike P5 of
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, base commit `7729f58`. Reads O1
(`2026-09-03-spike-o1-runtime-machine.md`, the machine and the witness protocol) and O5
(`2026-09-03-spike-o5-compiler.md`, the admission predicate); imports `OCaml5.Effect`,
`OCaml5.Compiler` and `OCaml5.Witnesses` and edits none of them.

Files owned and written: `workshop/OCaml5/Render.lean`, `workshop/OCaml5/Fuzz.lean`,
`workshop/OCaml5/tools/fuzz.sh`, `workshop/OCaml5/fuzz/`.

Two parts. §§1–6 are the spike as the plan's §6 asked for it: a `Term` renderer, a random term
generator and a fuzzing campaign against the three hosts. §7 is the second part, added after the
estate's target moved to an OCaml avatar of the Effect runtime (spike A0): a general Lean → OCaml
*declaration* surface, so that the avatar's OCaml is generated from the Lean carriers rather than
hand-written.

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
$ ./workshop/OCaml5/tools/fuzz.sh run 100000 250 4      # … 600000 150 9
$ ./workshop/OCaml5/tools/fuzz.sh shrink 100010 4
$ ./workshop/OCaml5/tools/fuzz.sh _one workshop/OCaml5/fuzz/min/drop-min.ml
```

Toolchain: OCaml 5.1.1 at `/Users/pooks/.opam/default/bin` (`ocamlc`, `ocamlopt`, `ocamlrun`),
js_of_ocaml 5.7.1 at
`.../_build/toolchains/ocaml5-jsoo-5.7.1/.../js_of_ocaml.exe`, node v22.23.2, macOS arm64,
Lean 4.33.1, no Mathlib. Build products under the session scratchpad; nothing written into
`effect4_of_ocaml` or the opam switches. Nothing committed.
