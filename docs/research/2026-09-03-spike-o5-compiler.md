# Spike O5: the compiler layer between `Stdlib.Effect` and the runtime

Date: 2026-09-03. Base commit `3e2b919` ("Spike O1: the OCaml 5 runtime machine"). Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` (§0 layer L3, §3 row O5, §4 theorems).
Predecessor: `docs/research/2026-09-03-spike-o1-runtime-machine.md`, whose §7 hands this spike
three items. Files owned and touched: `workshop/OCaml5/Compiler.lean` (new), the `OCaml5.Stdlib`
namespace inside `workshop/OCaml5/Effect.lean`, this report. Nothing else, no commit.
`Code.lean`, `Cps.lean`, `Value.lean` (spikes O2 and O3), `Witnesses.lean`, `lakefile.toml`,
`Effect4/` and `workshop/Deep/` are untouched; `Witnesses.lean` needed no import change, for the
reason in §7.

All compiler sources under `~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/`.

## 1. What was built

`OCaml5.Compiler` is the L3 layer of the plan: what `ocamlc` and `ocamlopt` do with the four
Lambda primitives, and the one thing `ocamlc` refuses.

* `Lowering`, a record per primitive — Lambda constructor, `%`-spelling, arity, the `check_stack`
  slack, the bytecode instruction in tail and in non-tail position (`none` = the compiler
  refuses), the native symbol, and the line of each — and `table`, the four rows.
* `TailPosition` (`tail` / `nonTail`), the reflection of `is_tailcall cont`
  (`bytegen.ml:102-106`), and `admissibleAt : TailPosition → Term ν → Bool` with
  `Admissible := admissibleAt .nonTail`, the decidable admission clause. Bool-valued and
  structural, so the O1 report §7 note about `DecidableEq` not being derivable through the nested
  `List` does not bite.
* `opcodesAt : TailPosition → Term ν → List Opcode`, the static read-off of a term's effect
  instructions in emission order, with `opcodes` (as a compilation unit) and `opcodesAsBody` (as
  a function right-hand side).
* Eight preservation theorems, one per builder family.
* 57 `#guard`s: the table's internal consistency, 36 admitted terms, 11 rejected ones, and the
  `ocamlc -dinstr` comparison of §5.

`OCaml5.Stdlib`, in `Effect.lean`, is now a definition-for-definition transcription of
`stdlib/effect.ml:57-156` in source order (§6).

```
$ lake env lean workshop/OCaml5/Compiler.lean     # silent
$ lake build OCaml5.Effect OCaml5.Compiler OCaml5.Witnesses
✔ Built OCaml5.Effect ✔ Built OCaml5.Witnesses ✔ Built OCaml5.Compiler
```

No `sorry`, `axiom`, `partial`, `unsafe`, `native_decide` or `implemented_by`. `#print axioms` on
the nine `Compiler` theorems reports `propext` only; the two new `Stdlib` equations depend on no
axiom. O1's thirteen witnesses are still green, unchanged, with the rewritten `Shallow.fiber`.

## 2. The lowering table

| | `%perform` | `%resume` | `%runstack` | `%reperform` |
| --- | --- | --- | --- | --- |
| Lambda constructor | `Pperform` | `Presume` | `Prunstack` | `Preperform` |
| `lambda.ml` | `:60` | `:61` | `:59` | `:62` |
| arity, `translprim.ml` | 1, `:373` | 3, `:374` | 3, `:371` | 3, `:372` |
| `bytegen` clause | `:417-419` (`comp_primitive`) | `:786-795` (`comp_expr`) | `:786-795`, the same clause | `:796-804` (`comp_expr`) |
| `check_stack` | `sz + 4` (`:418`) | `sz + 4` (`:790`) | `sz + 4` (`:790`) | `sz + 3` (`:799`) |
| tail (`is_tailcall cont`) | `Kperform` | `Kresumeterm (sz+2)` (`:793`) | `Kresumeterm (sz+2)` (`:793`) | `Kreperformterm (sz+2)` (`:802`) |
| non-tail | `Kperform` | `Kresume` (`:795`) | `Kresume` (`:795`) | **`fatal_error "Reperform used in non-tail position"`** (`:804`) |
| opcode(s) | `PERFORM` = 149 | `RESUME` = 150 / `RESUMETERM` = 151 | `RESUME` / `RESUMETERM` | `REPERFORMTERM` = 152 |
| native symbol | `caml_perform` | `caml_resume` | `caml_runstack` | `caml_reperform` |
| `cmmgen.ml` | `:861-865` | `:1121-1126` | `:1128-1132` | `:1134-1138` |

Five things this table records that the plan's §0 does not.

1. **`%perform` has no tail split.** It is the only one of the four that reaches
   `comp_primitive` (`bytegen.ml:417-419`), which is called with the arguments already compiled
   and has no `cont` to test. The other three are intercepted earlier, in `comp_expr`, and
   `comp_primitive`'s catch-all at `:538` says so: `| Prunstack | Presume | Preperform` is listed
   under "the cases below are handled in `comp_expr` before the `comp_primitive` call". All four
   are in `preserve_tailcall_for_prim` (`:111-115`), but that governs only whether the
   *enclosing* application keeps its `Kappterm` (`:1036`), not the primitive's own instruction.
2. **`%resume` and `%runstack` are the same bytecode clause and the same instruction.** There is
   no `RUNSTACK` opcode in `instruct.h:64`; `bytegen.ml:786` matches
   `Lprim((Presume|Prunstack), args, _)` and emits `Kresume`/`Kresumeterm` for both. The runtime
   tells them apart by the stack the first argument names — a fresh one from `caml_alloc_stack`
   for `runstack`, a captured one for `resume`. Native code does have two symbols and two
   calling sequences, because `caml_runstack` must install `frame_runstack` as the return
   address. This is the citation `Effect.lean` already carried as "`RESUME` (`bytegen.ml:786`)";
   it is now a row with both halves.
3. **`%perform` is a one-argument Lambda primitive and a two-argument Cmm call.** `cmmgen.ml:862`
   allocates the `Cont_tag` block itself — `make_alloc dbg Obj.cont_tag [int_const dbg 0]` — and
   passes it as `caml_perform`'s second argument. In bytecode the block is allocated by the
   interpreter (`interp.c:1332`). The Lean machine's `doPerform` allocates it in the transition,
   which matches the bytecode presentation; the native presentation allocates it one step
   earlier, in the caller. Nothing observable depends on which.
4. **The `reperform` restriction is `ocamlc`'s, not `ocamlopt`'s.** `cmmgen.ml:1134-1138` is an
   ordinary `Cop (Capply typ_val, [Cconst_symbol "caml_reperform"; …])` with no position test.
   But `bytegen` runs on every program `ocamlc` compiles, so the restriction is a restriction on
   OCaml source, not on bytecode programs: an `ocamlopt`-only build would accept a non-tail
   `reperform`, and `Stdlib.Effect` is written so that no user program can produce one anyway,
   because `Deep.reperform` and `Shallow.reperform` are not exported.
5. **Line corrections to the plan and to `Effect.lean`'s header.** The plan §0 cites
   `translprim.ml:371-374` (correct), `bytegen.ml:417-419,786-800` and `cmmgen.ml:861-865,
   1122-1140`. The `Preperform` clause runs `:796-804`, and the `fatal_error` is at `:804`, not
   `:799` or `:800`; the three-argument `cmmgen` cases are `:1121-1138`, and `Presume` starts at
   `:1122` only if the `(* Effects *)` comment at `:1121` is excluded. `lambda.ml`'s "Context
   switches" comment is at `:58` and the four constructors at `:59-62`.

Opcode numbers were read back rather than counted by hand:

```
$ cat > op.ml <<'EOF'
let () = Printf.printf "PERFORM=%d RESUME=%d RESUMETERM=%d REPERFORMTERM=%d\n"
  Opcodes.opPERFORM Opcodes.opRESUME Opcodes.opRESUMETERM Opcodes.opREPERFORMTERM
EOF
$ ocamlfind ocamlc -package compiler-libs.common -linkpkg op.ml -o op && ./op
PERFORM=149 RESUME=150 RESUMETERM=151 REPERFORMTERM=152
```

## 3. Tail position, constructor by constructor

`is_tailcall` (`bytegen.ml:102-106`) is a predicate on the continuation `comp_expr` was called
with:

```ocaml
let rec is_tailcall = function
    Kreturn _ :: _ -> true
  | Klabel _ :: c -> is_tailcall c
  | Kpop _ :: c -> is_tailcall c
  | _ -> false
```

On `Term` it is a polarity that each constructor hands down. `Klabel` and `Kpop` being skipped is
exactly what makes `let` bodies and `match` arms tail-transparent.

| `Term` constructor | Which subterms inherit the polarity | Which are `nonTail` | `bytegen` |
| --- | --- | --- | --- |
| `lam body` | — | — (`body` is **always** `tail`) | `:626-635` pushes the body on `functions_to_compile`; it is compiled with `Kreturn` |
| `letIn bound body` | `body` | `bound` | `:636-639`: `bound`'s cont is `Kpush :: …`, `body`'s is `add_pop 1 cont`, and `Kpop` is skipped (`:105`) |
| `seq first next` | `next` | `first` | `:910-911`: `first`'s cont is the compiled `next` |
| `matchEff` / `matchExn` | every clause body, and the default | the scrutinee | `Lswitch` `:933-…` through `make_branch` (`:77-83`), which returns the `Kreturn` itself when the cont is one |
| `matchOpt s n sc` | `n`, `sc` | `s` | as above, or `Lifthenelse` `:908-909` |
| `tryWith body handler` | `handler` | **`body`** | `:895-907`: the body's cont is `Kpoptrap :: branch1 :: …`; the handler's is `add_pop 1 cont1` |
| `app fn arg` | — | both | `comp_args` pushes; the cont is `Kapply`/`Kappterm` |
| `raise e` | — | `e` | `:757`: `Kraise k :: discard_dead_code cont` |
| `perform`, `resume`, `runstack`, `reperform` | — | every operand | `comp_args` pushes; the cont is the instruction |
| `allocStack`, `contUseNoexc`, `contUseUpdate`, `dropCont` | — | every operand | `comp_args`; the cont is the `Kccall` |
| `eff`, `exn`, `some` | — | the payload | `Kmakeblock` follows |
| `add`, `emitOf`, `setCell` | — | every operand | see the ruling below |
| `val`, `unit`, `var`, `none`, `emit`, `getCell` | — | — | leaves |

`Admissible t = admissibleAt .nonTail t`: the whole term is read at `nonTail`, so a `reperform`
that is not under a `lam` is rejected. That is what `ocamlc` does — a structure item is compiled
with the rest of the compilation unit as its continuation (§4, probe `compilation-unit top`).

**Ruling on O1's non-OCaml helpers** (O1 report §7 item 3). `Term.add`, `Term.emit`,
`Term.emitOf`, `Term.getCell` and `Term.setCell` are **opaque, and their operands are not in tail
position**. They stand for `+`, `print_string`, `Printf.printf`, `!r` and `r := e`; each is an
`Lprim` or an `Lapply` whose arguments `comp_args` compiles with a pushing continuation, and none
of them is `Preperform`. So treating them as opaque cannot admit a term `ocamlc` would reject,
and giving their operands `nonTail` cannot reject a term `ocamlc` would admit: `reperform e k l
+ 1`, `f (reperform e k l)` and `ext3 1 (reperform e k l) 3` are all rejected (§4, probes
`arithmetic operand`, `app argument`, `ccall operand`).

## 4. What is admitted and what is rejected

The predicate was fixed against `ocamlc` itself. Eighteen one-line programs, each on top of the
`external` block of `effect.ml:16,41-42,49-55,69-70,130-135` transcribed as `prims.ml`, compiled
with `ocamlc -c`. Every row has a matching `#guard` in `Compiler.lean`.

```
$ ocamlc -c prims.ml && for p in …; do ocamlc -c $p.ml; done
```

| Shape | `ocamlc` | `Admissible` |
| --- | --- | --- |
| `fun … -> reperform e k l` | ADMITTED | `true` |
| `let y = 1 in …; reperform e k l` | ADMITTED | `true` |
| `print_string "x"; reperform e k l` | ADMITTED | `true` |
| `match b with true -> reperform e k l \| false -> 0` | ADMITTED | `true` |
| `match o with None -> 0 \| Some _ -> reperform e k l` | ADMITTED | `true` |
| `try g () with _ -> reperform e k l` | ADMITTED | `true` |
| `let x = reperform e k l in x + 1` | Fatal error | `false` |
| `ignore (reperform e k l); 0` | Fatal error | `false` |
| `g (reperform e k l)` | Fatal error | `false` |
| `try reperform e k l with _ -> 0` | Fatal error | `false` |
| `resume s g (reperform e k l)` | Fatal error | `false` |
| `ext3 1 (reperform e k l) 3` (a `Kccall` operand) | Fatal error | `false` |
| `((reperform e k l), 1)` (a `Kmakeblock` operand) | Fatal error | `false` |
| `raise (X (reperform e k l))` | Fatal error | `false` |
| `match (reperform e k l) with 0 -> 1 \| _ -> 2` | Fatal error | `false` |
| `reperform e k l + 1` | Fatal error | `false` |
| `let v = reperform (mk ()) (mkk ()) (mkl ())` at unit top | Fatal error | `false` |
| `let x = reperform e k l in x` | **ADMITTED** | `false` |

The last row is the one divergence, and it is deliberate. `Simplif`'s let-elimination rewrites
`let x = e in x` to `e` before `bytegen` sees it, so the `reperform` inherits the tail position
the `let` occupied. `Admissible` reads the term as written and rejects. Making the predicate
match would mean transcribing `Simplif`, which is a different layer; the conservative direction
is the safe one (`Admissible t = true` implies `ocamlc` compiles `t`), no `Stdlib` builder and no
witness has that shape, and it is recorded as a `#guard` in the file rather than hidden.

Counts in `Compiler.lean`: **36 admitted** — the fourteen `Stdlib` builders, the thirteen
witnesses of `OCaml5.Witnesses`, and nine hand-built positive shapes — and **11 rejected**
hand-built shapes, the ten `ocamlc` rejects plus the `Simplif` divergence. Plus four table
consistency guards, six `-dinstr` comparisons, and seven read-off guards on the corpus: 57 in
all.

The theorem the plan asks for as "preserved by the substitution or unrolling your builders use"
is proved as compositionality, since the builders substitute nothing: each is a fixed shape with
holes, and `admissible_effcClosure`, `admissible_effcClosureWith`, `admissible_deepMatchWith`,
`admissible_deepTryWith`, `admissible_shallowContinueGen`, `admissible_shallowFiber`,
`admissible_deepContinue` and `admissible_deepDiscontinue` each say that the builder is
admissible at *any* ambient polarity as soon as its term arguments are admissible at the polarity
the builder puts them in. `admissible_shallowContinueGen`'s hypothesis on `effc` is its own
conclusion one layer down, which is what makes every finite unrolling of witness 11's
`let rec h2` (O1 report §6) admissible, by induction on the depth.

## 5. `ocamlc -dinstr`, compared

Done, at the level where the comparison is exact: one `.ml` file per `stdlib/effect.ml`
definition, transcribed verbatim on the `prims.ml` externals, so each dump is unambiguous.

```
$ for f in d_continue d_discontinue d_match_with d_try_with d_fiber d_continue_gen; do
    ocamlc -dinstr -c $f.ml 2>&1 | grep -oE '^\s*(perform|resume|resumeterm|reperformterm)\b'
  done
```

| `effect.ml` definition | `ocamlc -dinstr`, in order | `opcodesAsBody` of the builder |
| --- | --- | --- |
| `continue` (`:57`) | `resumeterm` | `[RESUMETERM]` |
| `discontinue` (`:59`) | `resumeterm` | `[RESUMETERM]` |
| `match_with` (`:72-79`) | `reperformterm` `resumeterm` | `[REPERFORMTERM, RESUMETERM]` |
| `try_with` (`:84-91`) | `reperformterm` `resumeterm` | `[REPERFORMTERM, RESUMETERM]` |
| `fiber` (`:110-123`) | `perform` `resume` | `[PERFORM, RESUME]` |
| `continue_gen` (`:140-147`) | `reperformterm` `resumeterm` | `[REPERFORMTERM, RESUMETERM]` |

Six for six, sequence and order. The read-off's order rule — a primitive's operands first, then
its own instruction — reproduces `bytegen`'s emission order on all six, because the closures a
definition allocates (`effc`, `f'`) are emitted before the body that allocates them.

Two things the dump settles that no amount of reading `bytegen` would have settled as cleanly.

**`Shallow.fiber`'s `runstack` is the one non-tail effect primitive in `stdlib/effect.ml`.** It
sits under the trap of `match runstack s f' () with exception E k -> k | _ -> error ()`
(`:121-123`), and `Ltrywith` gives its body a `Kpoptrap :: …` continuation, so it compiles to
`RESUME`, not `RESUMETERM`. Here is the block, from `ocamlc -dinstr -c` on a copy of
`stdlib/effect.ml`:

```
        ccall caml_alloc_stack, 3
        push
        pushtrap L24
        const 0
        push
        acc 8
        push
        acc 6
        resume
        poptrap
        branch L23
L24:    push ... eqint / branchifnot L25 / acc 0 / getfield 1 / return 8
L25:    acc 0
        reraise
L23:    push / const 0 / push / acc 4 / appterm 1, 9        (* error () *)
```

`L23` is the `| _ -> error ()` arm of `:123`, which the O1 transcription did not have: it is dead
(a normal return of `f'` runs `error` as the fiber's own `retc` and raises first) but it is
compiled, and §6 now transcribes it. `L25`'s `reraise` is the non-`E` exception path, which O1
already had.

**`perform` is emitted the same in either position.** The `f'` closure of `:113` is
`f (perform M.Initial_setup__)` — the `perform` is an argument of `f`, as non-tail as it gets —
and the dump is `perform; push; envacc 3; appterm 1, 2`.

The witness `.ml` files were dumped too, and they contain only the `perform`s they write
themselves, because `Deep.continue`, `Deep.try_with` and the rest are *calls* into `stdlib.cmo`:

```
$ for f in workshop/OCaml5/witnesses/w*.ml; do ocamlc -dinstr -c $f | grep -E '^(perform|resume…)'; done
w01 perform perform   w05 perform perform   w11 perform perform   w13 (none)   …
```

`#guard`s in `Compiler.lean` pin the `PERFORM` counts: two for witness 01 and two for witness 05,
matching their dumps, and **three** for witness 11 — the extra one is `Shallow.fiber`'s
`perform M.Initial_setup__` (`effect.ml:113`), which lives in `effect.ml`, not in the witness.

That gap is the one caveat on the witness-level read-off, and it is recorded rather than papered
over. The Lean terms *inline* the `Stdlib` builders; OCaml *calls* them. Inlining moves a
primitive out of the callee's tail position (`runstack s comp arg` is the last expression of
`match_with`) into wherever the caller put the call, which in twelve of the thirteen witnesses is
a `letIn` bound position — so the witness read-offs carry `RESUME` where `effect.ml` carries
`RESUMETERM`. The demotion is harmless, both instructions exist, and it never reaches a
`reperform`, because the three `lam`s of `effcClosure` restore the tail polarity wherever the
closure is placed. `#guard`s pin exactly that: every witness is `Admissible` read as a
compilation unit *and* read as a function body, and its `REPERFORMTERM` count is the same either
way.

Full read-offs, pinned as `#guard`s:

| Witness | `opcodes w.term` |
| --- | --- |
| `w01-repeated` | `RESUMETERM, REPERFORMTERM, PERFORM, PERFORM, RESUME` |
| `w05-forwarded` | `RESUMETERM, REPERFORMTERM, RESUMETERM, REPERFORMTERM, PERFORM, PERFORM, RESUMETERM, RESUME` |
| `w11-shallow-reinstall` | `PERFORM, PERFORM, PERFORM, RESUME, REPERFORMTERM, RESUMETERM, REPERFORMTERM, RESUMETERM, REPERFORMTERM, RESUME` |

## 6. `Stdlib`, in its final form

`stdlib/effect.ml:57-156`, one Lean `def` per OCaml `let`, in source order, each docstring citing
its lines. Fourteen definitions where O1 had eleven.

| `effect.ml` | Lean | Note |
| --- | --- | --- |
| `Deep.continue` `:57` | `deepContinue` | unchanged |
| `Deep.discontinue` `:59` | `deepDiscontinue` | unchanged |
| `Deep.discontinue_with_backtrace` `:61-62` | `deepDiscontinueWithBacktrace` | **new**; no backtraces in the machine, so `raise_with_backtrace e bt` is `raise e` and `bt` is dropped |
| the `effc` of `:73-77` / `:85-89` / `:141-145` | `effcClosure` | one Lean def for three identical OCaml closures |
| — | `effcClosureWith` | O1's logging variant, marked as not an `effect.ml` definition |
| `Deep.match_with` `:72-79` | `deepMatchWith` | unchanged |
| — | `deepMatchWithLogging` | O1's |
| `Deep.try_with` `:84-91` | `deepTryWith` | unchanged |
| — | `deepTryWithLogging` | O1's |
| `Shallow.fiber` `:110-123` | `shallowFiber` | **rewritten**, see below |
| `Shallow.continue_gen` `:140-147` | `shallowContinueGen` | unchanged |
| `Shallow.continue_with` `:149-150` | `shallowContinueWith` | unchanged |
| `Shallow.discontinue_with` `:152-153` | `shallowDiscontinueWith` | unchanged |
| `Shallow.discontinue_with_backtrace` `:155-156` | `shallowDiscontinueWithBacktrace` | **new** |

The externals get no builder and are named in the namespace docstring against the `Term`
constructor each is: `perform` `:16`, `resume` `:41`, `runstack` `:42`, `Deep.take_cont_noexc`
`:49-50`, `Deep.alloc_stack` `:51-55` and `Shallow.alloc_stack` `:103-107`, `Deep.reperform`
`:69-70` and `Shallow.reperform` `:137-138`, `Shallow.update_handler` `:130-135`.
`get_callstack` (`:93-95`, `:158-160`) and the `Printexc` printer registration (`:21-37`) are out
of scope per the plan §0 and are recorded as such.

`shallowFiber` was rewritten to close three fidelity gaps O1's version had, all of them invisible
to witness 11 and all of them now transcribed:

1. `error _ = failwith "impossible"` (`:114`) raises `Failure`, not the local `E`. O1's `err`
   raised `E ()`, whose payload would have been read as a continuation by the outer
   `exception E k -> k` arm. `Stdlib.failureExn = ⟨5⟩` is the global constructor, alongside
   `ExnId.unhandled = ⟨0⟩` and `ExnId.continuationAlreadyResumed = ⟨1⟩`; it is an optional
   argument (`failId`), so every existing three-argument call site still elaborates.
2. `let s = alloc_stack error error effc` (`:120`) is now a real `letIn`, not an inlining of the
   `alloc_stack` into the `runstack`'s stack operand.
3. `| _ -> error ()` (`:123`), the value arm of the `match runstack …`, is transcribed. It is
   dead — a normal return of `f'` runs `error` as the fiber's `retc` and raises first — but
   `ocamlc` compiles it (label `L23` in §5) and the transcription follows the source.

`raise_notrace` is `Term.raise` (the machine has one raise), and `error` is a closed closure
duplicated at its three occurrences rather than `let`-bound; both are recorded in the docstring.
After the rewrite, `lake build OCaml5.Witnesses` is still green: all thirteen `#guard`s pass, and
witness 11's ten rows are unchanged.

## 7. Where `Stdlib` lives, and why not in its own module

`OCaml5.Stdlib` stays in the `Stdlib` namespace of `Effect.lean`, rewritten in place. A separate
`workshop/OCaml5/Stdlib.lean` would have to import `OCaml5.Effect` for `Term`, and `Effect.lean`
would then have to import it back to re-export — a cycle. Splitting `Term`, `Value` and `Frame`
into a third module would break the cycle, but those are O1's carriers and the whole `Machine`
hangs off them; restructuring them is not this spike's file. Moving `Stdlib` into `Compiler.lean`
has the same problem in reverse: `Witnesses.lean` imports only `OCaml5.Effect` and every witness
is built from `Stdlib` builders, so `Witnesses` would have to import `Compiler`, which imports
`Witnesses`. Leaving it where it is costs nothing — the namespace is self-contained, its
docstring points at `OCaml5.Compiler` for the compilation facts, and `Witnesses.lean` needed no
edit at all. If the landing splits the carriers out, `Stdlib.lean` becomes free and should be
taken.

`Compiler.lean` imports `OCaml5.Witnesses` (which imports `OCaml5.Effect`) so that the read-off
and admission guards can be run on the executed corpus rather than on terms invented here.

## 8. Findings

1. **`%resume` and `%runstack` are one bytecode instruction.** No `RUNSTACK` opcode exists. The
   machine's `doRunstack` and `doResume` are distinguished only by the stack argument, which is
   exactly the runtime's own criterion; the plan's §0 row "`runstack` | `RESUME`
   (`bytegen.ml:786`)" is right and now has both halves of the pair.
2. **`Shallow.fiber` is the only non-tail effect primitive in `stdlib/effect.ml`**, and the
   reason is the trap at `:121`. Executed: `ocamlc -dinstr` on `effect.ml` prints exactly one
   `resume` and it is in the `fiber` block.
3. **The `reperform` admission clause is enforced by `ocamlc` on all programs**, including those
   only ever built with `ocamlopt`, because `cmmgen` has no such test. It is therefore a
   restriction on OCaml source, and `Stdlib.Effect` keeps it invisible by not exporting
   `reperform`.
4. **`Simplif` can rescue one shape the term-level predicate rejects** (`let x = reperform … in
   x`). The predicate is conservative in the safe direction and the divergence is a `#guard`.
5. **Inlining a `Stdlib` builder demotes `RESUMETERM` to `RESUME`, and never demotes a
   `REPERFORMTERM`.** The three `lam`s of `effcClosure` are what make the second half true, which
   is the structural reason O1's report §7 item 2 guessed at.
6. **Line corrections**, §2 item 5: `bytegen.ml:796-804` (the `fatal_error` is at `:804`),
   `cmmgen.ml:1121-1138`, `lambda.ml:58-62`.

## 9. Open items

**For whoever lands this.**

1. `admissibleAt .nonTail t = true → admissibleAt .tail t = true` — the polarity is monotone,
   because it is consulted only at `reperform` and only to reject. It needs an induction over the
   nested `Term`/`List (EffId × Term)` recursor, which is the same missing infrastructure O1's
   report §5 names for the `run`-level invariants. Stated and used pointwise for now; the
   corpus-level `#guard` (`admissibleAt .tail w.term && admissibleAt .nonTail w.term` for all
   thirteen) is its executed instance.
2. `Kresumeterm n` and `Kreperformterm n` carry `sz + nargs`, a stack depth. `opcodesAt` reads
   opcodes only, because modelling `sz` means modelling `bytegen`'s `env`/`sz` discipline. If a
   later spike wants a real disassembly comparison rather than a subsequence one, that is the
   piece to build; `Instruct.instruction` is small enough to transcribe whole.
3. `Simplif` (item 4 of §8) is the only pass between `Translcore` and `bytegen` that this layer
   ignores. One pass, one shape, recorded.
4. `Term.letrec` was **not** added. O1's report §6 offers it as the way to remove witness 11's
   one-step unrolling of `let rec h2`. It would have to change `Machine.step`, which this spike
   is forbidden to touch, and `admissible_shallowContinueGen` covers every finite unrolling
   anyway, so the unrolling stays and is recorded here as well as in O1's report.

**For O2 (js_of_ocaml).** `Effects.f` and `Partial_cps_analysis.f` see the same four primitives
under jsoo's own names (`%perform` becomes `caml_perform_effect`, `%resume`/`%runstack` become
`caml_resume_stack` plus a direct call, `%reperform` becomes a re-entry into
`caml_perform_effect`). jsoo has no tail-position restriction at all, because it is a CPS
transform; the correspondence to state is that the bytecode restriction is vacuous under CPS,
not that jsoo is more permissive in any observable way.

**For O4 (the bridge note).** The `Lowering` table is the row-per-carrier form O4 wants for the
compiler layer; `Deep.RunFiber` has no analogue of the tail restriction, which is one of the
places the two machines differ for a compiler reason rather than a semantic one.
