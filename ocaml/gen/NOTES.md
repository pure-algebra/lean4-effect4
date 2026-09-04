# The LCNF route: Lean's compiler IR → OCaml (spike, 2026-09-04)

Status: **works end to end.** Every top-level function of `src/Effect4/Machine/Fibers.lean`
(43 roots, 154 declarations with their transitive helpers, 38 types) translates through the
mono-phase LCNF into OCaml that `ocamlopt` type-checks, with zero holes; the nine target
functions are exercised by `gen_check.ml`, and the dispatcher agrees with the hand-written
avatar on 1419 compared steps. Lean 4.33.1, OCaml 5.1.1, dune 3.24.2.

## Commands (every claim below is behind one of these)

```
# Lean side (repo root, PowerShell; one lean at a time, -M4096). Library modules compile
# into the scratch olean dir in import order: Dump, Naming, Types, Translate.
$out='…\scratchpad\ocaml5-olean'; $env:LEAN_PATH="$out;$(lake env pwsh -NoProfile -Command '$env:LEAN_PATH')"
lean -M4096 -o "$out\OCaml5\Lcnf\Dump.olean" -i "$out\OCaml5\Lcnf\Dump.ilean" src\OCaml5\Lcnf\Dump.lean   # then Naming, Types, Translate

# dump the mono LCNF of constants
lean -M4096 --run src/OCaml5/Tools/LcnfDump.lean Effect4.Machine.Dispatcher.insert Effect4.Machine.Dispatcher.insert._redArg

# the nine targets (what gen_check exercises)
lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean --out ocaml/gen/machine_gen.ml --cap 60 --types Effect4.Machine.Task Effect4.Machine.Dispatcher.insert Effect4.Machine.Dispatcher.enqueue Effect4.Machine.Dispatcher.drain Effect4.Machine.RunMachine.update Effect4.Machine.RunMachine.fiber? Effect4.Machine.RunMachine.emit Effect4.Machine.RunMachine.finished Effect4.Machine.countdownWalk Effect4.Machine.interruptRecord

# every top-level function of Fibers.lean (the command is in fibers_gen.ml's header)
lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean --out ocaml/gen/fibers_gen.ml --cap 400 --types Effect4.Machine.Task Effect4.Machine.Dispatcher.empty … Effect4.Machine.promiseOutcome

# OCaml side (WSL). Standalone (its own build dir, gen/_build):
wsl -e bash -lc 'eval $(opam env --switch=effect4 --set-switch) && cd /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/gen && dune build --root . && dune test --root .'
# or as part of the estate's workspace (ocaml/dune lists gen; builds into ocaml/_build):
wsl -e bash -lc 'eval $(opam env --switch=effect4 --set-switch) && cd /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml && dune build gen && dune build @gen/runtest'
```

## 1. The API that worked, and what mono LCNF looks like

| step | what worked | notes |
| --- | --- | --- |
| environment | `importModules #[{ module := `Effect4.Machine.Fibers }] {} 0` after `initSearchPath (← findSysroot)`, `LEAN_PATH` from `lake env` | 4 s per run; the driver does not `import Effect4.*` itself |
| the decl | `Lean.Compiler.LCNF.getMonoDecl? : Name → CoreM (Option (Decl .pure))` (`PhaseExt.lean:162`), reading `monoExt` | present for every constant of a non-`module` file (`isDeclTransparent` is `true` there, `PhaseExt.lean:42`); no compilation pass had to be run — the `.olean` of `Fibers` (built 2026-09-04 12:13 by 4.33.1) carries the mono phase as `saveMono` wrote it after `normalizeFVarIds` (`Passes.lean:66-74`) |
| printing | `ppDecl' decl .mono` (`PrettyPrinter.lean:218`), plus `OCaml5.Lcnf.Dump.sketch` (node kinds with binder types) | `ppDecl'` prints both `priority`s of `insert` as `priority` — the names collide, the `FVarId`s do not |
| pure lookups | `getDeclCore? env monoExt n` is pure given the environment; `hasTrivialStructure?` reads the persisted verdict; `Code.collectUsed` gives the free variables of an arm | the translator is a pure `ReaderT Environment (StateM St)`; only the closure loop and the type generator run in `CoreM`/`MetaM` |

What the mono phase has already done for us (each seen in the dumps): type arguments are `◾`;
`Decidable` is `Bool` (`Nat.decEq` returns `Bool`, `cases` on it has `Bool.true/false` arms);
`FiberId`, `Cause`, `ReasonAnnotations` are erased to their one relevant field (`Nat`,
`List Reason`, `List (String × ◾)`); every structure projection is a single-alternative `cases`
binding all fields (`structProjCases`); every local `fun` has been lifted to a `_lam_N` decl;
`reduceArity` has split every polymorphic function into a wrapper `f ν σ … x := f._redArg x`
and the twin; `@[specialize]` helpers appear as `List.mapTR.loop._at_.<host>.spec_N`; `++` is
`List.appendTR._redArg`; `List.flatten` goes through `flatMapTR.go` with an `Array` accumulator.

Verbatim (`LcnfDump`): the wrapper and the twin of `Dispatcher.insert`.

```
def Effect4.Machine.Dispatcher.insert ν σ β ε δ ι α priority task x.1 : List
  (Effect4.Machine.Bucket lcAny lcAny lcAny lcAny lcAny lcAny lcAny) :=
  let _x.2 := Effect4.Machine.Dispatcher.insert._redArg priority task x.1;
  return _x.2

def Effect4.Machine.Dispatcher.insert._redArg priority task x.1 : lcAny :=
  cases x.1 : lcAny
  | List.nil =>
    let _x.2 := List.nil ◾;
    let _x.3 := List.cons ◾ task _x.2;
    let _x.4 := Effect4.Machine.Bucket.mk ◾ ◾ ◾ ◾ ◾ ◾ ◾ priority _x.3;
    let _x.5 := List.cons ◾ _x.4 _x.2;
    return _x.5
  | List.cons head.6 tail.7 =>
    cases head.6 : lcAny
    | Effect4.Machine.Bucket.mk priority tasks =>
      let _x.8 := Nat.decEq priority priority;
      cases _x.8 : lcAny
      | Bool.false =>
        let _x.9 := Nat.decLt priority priority;
        cases _x.9 : lcAny
        | Bool.false =>
          let _x.10 := Effect4.Machine.Dispatcher.insert._redArg priority task tail.7;
          let _x.11 := List.cons ◾ head.6 _x.10;
          return _x.11
        | Bool.true =>
          let _x.12 := List.nil ◾;
          let _x.13 := List.cons ◾ task _x.12;
          let _x.14 := Effect4.Machine.Bucket.mk ◾ ◾ ◾ ◾ ◾ ◾ ◾ priority _x.13;
          let _x.15 := List.cons ◾ head.6 tail.7;
          let _x.16 := List.cons ◾ _x.14 _x.15;
          return _x.16
      | Bool.true =>
        let _x.17 := List.nil ◾;
        let _x.18 := List.cons ◾ task _x.17;
        let _x.19 := List.appendTR._redArg tasks _x.18;
        let _x.20 := Effect4.Machine.Bucket.mk ◾ ◾ ◾ ◾ ◾ ◾ ◾ priority _x.19;
        let _x.21 := List.cons ◾ _x.20 tail.7;
        return _x.21
```

## 2. The translation rules (`Lcnf/Translate.lean`, header)

| LCNF construct | OCaml |
| --- | --- |
| `Decl` params `(x : T)…`, type `T₁ → … → R` | `let [rec] f (x : T)… : R =`, `◾`/`lcAny` as `_`, an all-`_` annotation omitted |
| `let x := v; k` | `let x = v in k` |
| `fun f ps := b; k` / `jp j ps := b; k` | `let f = fun ps -> b in k`; `let rec` when `b` mentions `f`; no params → `fun () ->` |
| `jmp j args` | `j args`; no args → `j ()` |
| `cases x` on `Bool` | `if x then … else …` |
| `cases x : T`, other | `match (x : (_,…) t) with` — annotated, so OCaml's record disambiguation never guesses |
| `\| C.mk f₁ … fₙ =>` on a `structure` | `\| { f₁ = f₁; …; _ } ->`, binding only the fields the arm uses (`Code.collectUsed`) |
| `\| C.c a₁ … aₙ =>` on an `inductive` | `\| C_c (a₁, …, aₙ) ->`, `_` for an unused field |
| `List.nil/cons`, `Option.none/some`, `Prod.mk`, `Except.ok/error`, `Bool` | `[]`, `h :: t`, `None`, `Some x`, `(a, b)`, `Ok x`, `Error e`, `true/false` — in patterns and constructions |
| `\| _ =>` | `\| _ ->` |
| `return x` | `x` |
| `⊥` (`unreach`) | `assert false` |
| `LetValue.lit (nat n)` / `(str s)` | `n` (63-bit caveat) / `"s"` |
| `LetValue.erased` | `()` |
| `LetValue.proj T i s` | `s.fᵢ` on a structure; `fst`/`snd` on `Prod`; otherwise a hole (never seen in mono: `structProjCases` removed them all) |
| `LetValue.fvar f args` | `f args`, `◾` as `()` |
| structure constructor `C.mk ◾… fields` | `({ f₁ = …; … } : (_,…) t)`, erased fields dropped |
| inductive constructor `C.c ◾… args` | `C_c (args)` (constructor names are `<Type>_<ctor>`: `Task_start`, `Prim_failure`, so `Prim.failure` and `Exit.failure` cannot collide) |
| `g args`, `g` in the builtin table | `Nat.decEq/beq` → `=`, `decLt` → `<`, `decLe` → `<=`, `Nat.sub` → `max 0 (a - b)`, `List.appendTR/append` → `@`, `List.reverse` → `List.rev`, `List.reverseAux` → `List.rev_append`, `List.instDecidableEqNil` → `= []`, `List.all l p` → `List.for_all p l`, `List.elem inst a l` → `List.exists (inst a) l`, `Array.mkEmpty` → `[]`, `Array.toList` → identity, `Array.push` → `@ [x]`, `List.foldl._at_.Array.appendList.spec_0` → `@`, `Option.isSome` → `Option.is_some`, `Option.getD` → `Option.value ~default`, `panic` → `failwith`, … (`builtin?`, 50 rows) |
| `g args`, other | `g' args`, `g' = globalName g`; `g` is enqueued for translation (closure with a cap) |
| `g._redArg` | translated under `g`'s name; the wrapper is skipped; a direct (partial) reference to the wrapper passes the twin exactly the parameters it kept, read off the wrapper's own body (`wrapperKeep?`) |
| `Decl.value = extern` | a hole |
| binder names | unique per declaration by `FVarId` (`priority`, `priority_1`), so LCNF shadowing never becomes OCaml capture |
| emission | strongly connected components (Tarjan) of the call graph, dependencies first; `let rec` for a self- or mutually-recursive component; an `(* LCNF mono: … *)` origin comment above each |

Types (`Lcnf/Types.lean`): `structure` → record, `inductive` → variant, a *trivial structure*
(the compiler's own verdict, `hasTrivialStructure?`) → abbreviation (`fiber_id = int`,
`cause = reason list`, `reason_annotations = (string * 'a) list`); a relevant field is one that
is neither a `Prop` nor a type (the compiler's `getRelevantCtorFields?` test); a type nothing
destructs or constructs and nobody asked for becomes a *placeholder* variant
`Placeholder_<type>`; everything goes into one `type … and …` group; `Nat` → `int`,
`Except ε α` → `(α, ε) result`, `Array` → `list`.

## 3. The generated dispatcher, verbatim (`machine_gen.ml`)

```ocaml
type ('nu, 's, 'b, 'e, 'd, 'i, 'a) bucket = { priority : int; tasks : ('nu, 's, 'b, 'e, 'd, 'i, 'a) task list }
and ('nu, 's, 'b, 'e, 'd, 'i, 'a) dispatcher = { buckets : ('nu, 's, 'b, 'e, 'd, 'i, 'a) bucket list; armed : bool }
…
and ('nu, 's, 'b, 'e, 'd, 'i, 'a) task = Task_start of fiber_id | Task_resume of fiber_id * int * ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
…
and fiber_id = int

let rec dispatcher_insert (priority : int) (task : (_, _, _, _, _, _, _) task) (x_1 : (_, _, _, _, _, _, _) bucket list) =
  match x_1 with
    | [] -> (let _x_2 = [] in
      let _x_3 = task :: _x_2 in
      let _x_4 = ({ priority = priority; tasks = _x_3 } : (_, _, _, _, _, _, _) bucket) in
      let _x_5 = _x_4 :: _x_2 in
      _x_5)
    | head_6 :: tail_7 -> (match (head_6 : (_, _, _, _, _, _, _) bucket) with
        | { priority = priority_1; tasks = tasks } -> (let _x_8 = priority_1 = priority in
          if _x_8 then (let _x_17 = [] in
            let _x_18 = task :: _x_17 in
            let _x_19 = tasks @ _x_18 in
            let _x_20 = ({ priority = priority_1; tasks = _x_19 } : (_, _, _, _, _, _, _) bucket) in
            let _x_21 = _x_20 :: tail_7 in
            _x_21) else (let _x_9 = priority < priority_1 in
            if _x_9 then (let _x_12 = [] in
              let _x_13 = task :: _x_12 in
              let _x_14 = ({ priority = priority; tasks = _x_13 } : (_, _, _, _, _, _, _) bucket) in
              let _x_15 = head_6 :: tail_7 in
              let _x_16 = _x_14 :: _x_15 in
              _x_16) else (let _x_10 = dispatcher_insert priority task tail_7 in
              let _x_11 = head_6 :: _x_10 in
              _x_11))))

let dispatcher_enqueue (d : (_, _, _, _, _, _, _) dispatcher) (priority : int) (task : (_, _, _, _, _, _, _) task) : (_, _, _, _, _, _, _) dispatcher =
  match (d : (_, _, _, _, _, _, _) dispatcher) with
    | { buckets = buckets; _ } -> (let _x_1 = dispatcher_insert priority task buckets in
      let _x_2 = true in
      let _x_3 = ({ buckets = _x_1; armed = _x_2 } : (_, _, _, _, _, _, _) dispatcher) in
      _x_3)

let rec list_map_tr_loop_at_dispatcher_drain_spec_0 (a_1 : (_, _, _, _, _, _, _) bucket list) (a_2 : (_, _, _, _, _, _, _) task list list) : (_, _, _, _, _, _, _) task list list =
  match a_1 with
    | [] -> (let _x_3 = List.rev a_2 in
      _x_3)
    | head_4 :: tail_5 -> (match (head_4 : (_, _, _, _, _, _, _) bucket) with
        | { tasks = tasks; _ } -> (let _x_6 = tasks :: a_2 in
          let _x_7 = list_map_tr_loop_at_dispatcher_drain_spec_0 tail_5 _x_6 in
          _x_7))

let rec list_flat_map_tr_go_at_dispatcher_drain_spec_1 (a_1 : (_, _, _, _, _, _, _) task list list) (a_2 : (_, _, _, _, _, _, _) task list) : (_, _, _, _, _, _, _) task list =
  match a_1 with
    | [] -> (let _x_3 = a_2 in
      _x_3)
    | head_4 :: tail_5 -> (let _x_6 = a_2 @ head_4 in
      let _x_7 = list_flat_map_tr_go_at_dispatcher_drain_spec_1 tail_5 _x_6 in
      _x_7)

let dispatcher_drain (d : (_, _, _, _, _, _, _) dispatcher) : (_, _, _, _, _, _, _) task list * (_, _, _, _, _, _, _) dispatcher =
  match (d : (_, _, _, _, _, _, _) dispatcher) with
    | { buckets = buckets; _ } -> (let _x_1 = [] in
      let _x_2 = list_map_tr_loop_at_dispatcher_drain_spec_0 buckets _x_1 in
      let _x_3 = 0 in
      let _x_4 = [] in
      let _x_5 = list_flat_map_tr_go_at_dispatcher_drain_spec_1 _x_2 _x_4 in
      let _x_6 = false in
      let _x_7 = ({ buckets = _x_1; armed = _x_6 } : (_, _, _, _, _, _, _) dispatcher) in
      let _x_8 = _x_5, _x_7 in
      _x_8)
```

The `RunMachine` four and `interruptRecord` are in the same file: `run_machine_update`
(`List.mapTR.loop` specialisation with a join point `_jp_6` and two record patterns binding
`id` and `id_1`), `run_machine_fiber_opt`, `run_machine_emit`, `run_machine_finished`,
`countdown_walk`, and `interrupt_record` with the whole `Cause`/`Reason`/`ReasonAnnotations`
cluster it calls (29 helpers, including the derived `DecidableEq` instances as functions).

## 4. Build and comparison

| what | result |
| --- | --- |
| `dune build --root .` (library `effect4_gen` = `machine_gen` 506 lines + `fibers_gen` 3263 lines + `avatar_reference`; executable `gen_check`) | exit 0; the only diagnostics are warning 30 (a label defined in two record types of one group: `armed`, `fiber`, `id`, `remaining`, `state`, `token`), harmless because every record literal and scrutinee is annotated |
| `dune test --root .` (`gen_check`) | **ALL PASS, 24/24** (`== ALL PASS: 0 failure(s) ==`; 24 `PASS` lines, re-counted 2026-09-04 after the estate moved to `ocaml/`, on both `dune test --root . --force` and `dune build @gen/runtest --force` from `ocaml/`. An earlier "25/25" here was one too many) |
| §1 `insert` on `[1:[1]; 3:[2,3]]` at priorities 0..4 | generated = avatar, e.g. priority 2 → `1:[1]; 2:[9]; 3:[2,3]` both sides |
| §2 `enqueue`/`drain` differential, 200 random sequences (fixed LCG) | 1419 compared steps (bucket projection and `armed` after every enqueue; drained order and reset after every drain), **0 mismatches**; example: enqueues (2,1)(0,2)(2,3)(1,4)(0,5)(3,6)(1,7) → buckets `0:[2,5]; 1:[4,7]; 2:[1,3]; 3:[6]`, drain → `[2;5;4;7;1;3;6]`, reset `armed=false` |
| §3 `fiber?`, `update`, `emit`, `finished`, `countdownWalk` on a 3-fiber machine | 9/9 against the definitions read by hand |
| §4 `interruptRecord`: live/exited/running/masked fibers, a previous cause (`Cause.combine`), a duplicate cause (`Cause.dedup`), caller annotations | 7/7; e.g. live fiber → `applyNow=true`, `interrupted_cause = [interrupt(Some 7)]`, `current = Prim_failure [...]`, unparked; previous `[interrupt(Some 3)]` → `[interrupt(Some 3); interrupt(Some 7)]`; duplicate → one |

The one representational difference from the avatar is deliberate: the avatar's `bucket`
and `dispatcher` are mutable and `enqueue` returns `unit`; the generated ones are the
Lean values (immutable, `enqueue` returns the new dispatcher). `gen_check` compares
projections.

## 5. What the backend does not handle (and why)

Seen in the nine targets: **nothing** — `todos` is empty for both generated files, and the
only construct classes that exist in mono LCNF (`let`, `jp`/`jmp`, `cases`, `return`,
`unreach`; `lit`, `erased`, `proj`, `const`, `fvar`) all have rules. What is *not* covered,
or covered with a caveat:

| gap | reason / consequence |
| --- | --- |
| `Nat` → `int` | OCaml `int` is 63-bit; `Nat.sub` is emitted as `max 0 (a - b)`, but `Nat.div/mod` by zero (`0` in Lean, `Division_by_zero` in OCaml) and literals ≥ 2^62 are not guarded. Not hit by `Fibers.lean` (counters, tokens, priorities) |
| `Array` as `list` | `Array.mkEmpty/push/toList/appendList/size` are a list shim; `push` is O(n). Only the stdlib's `flatMapTR` accumulator uses it here |
| `LetValue.proj` on a non-structure | a hole; never produced by 4.33.1's mono phase (`structProjCases`) |
| `extern` / `implemented_by` / `noncomputable` callees | listed as `missing`; a `partial def` compiles to `f._unsafe_rec` and is reached through the wrapper. None in `Fibers.lean` (the only "missing" root, `Step`, is a `Prop`) |
| an erased *value* passed to a relevant parameter | becomes `()`, which is a type error at the OCaml level if the parameter is used; not observed in 154 declarations |
| stdlib functions outside the 50-row builtin table | translated from their own mono decls (`List.hasDecEq`, `instDecidableEqProd`, `List.filterTR.loop` all came out this way); a table row is only needed when the stdlib body is an `extern` (strings, floats, `IO`) |
| Lean-side recursion that the compiler turned into `Nat` `cases` | `casesNatToMono` (`Nat.decEq _ 0`, `Nat.sub _ 1`) is covered by the `Nat` rows; `Int`/`UInt` cases likewise map to `int` — untested |
| type names | last component, snake case; a collision between two Lean types with one short name is detected and the second gets its full path (never fired here). Record labels shared by two types raise warning 30 only |
| readability | ANF is kept: `let _x_N = … in` chains and no `{ m with … }` (LCNF rebuilds the whole record). A post-pass inlining single-use lets and recovering `with` is the obvious next 100 lines |
| a `Prop`-valued or type-valued definition | no code, reported as `missing` (`Effect4.Machine.Step`) |

## 6. What it takes to cover all of `Fibers.lean`

Coverage is **already complete at the type-checking level**: `fibers_gen.ml` holds all 43
top-level functions plus 111 transitive helpers (154 `let`s: 31 self-recursive `let rec`s,
no mutually recursive group, 0 holes) and 38 full types (`Prim`, `RunInterp`, `RunFiber`, `RunMachine`,
`Cmd`, `RunDecision`, `Iter`, `Exit`, `Reason`, …; 3 abbreviations; 1 placeholder,
`Supervision.ObserverMode`, because nothing in the closure destructs it — pass it with
`--types` to get its two constructors). The backend needed two rule fixes to get there
(`List.elem`'s `BEq` instance is a relevant argument; `List.all` takes the list first), each
found by `ocamlopt`, each a one-line table row.

What is left is trust, not translation:

1. **Run it.** `gen_check` exercises 9 of 154 functions. Driving `stepDecision`/`runSyncExit`
   over the avatar corpus needs an OCaml `RunInterp` and store: either hand-write one against
   the generated types (a day, the avatar's `deep_stores.ml` is the template) or add
   `Effect4.Machine.Stores`/`Layer`/`Context` to the driver's import list and generate them
   too (the driver takes one module today; making the imports an argument is ten lines, the
   stores have not been dumped, so their frontier is unknown — the `Std.HashMap`/`Array`
   uses there are the likely first `missing` rows). Then the corpus differential the avatar
   already runs (`avatar/compare.py`) can run against the generated machine: one to two days.
2. **Readability pass** (optional): single-use `let` inlining, `with`-recovery, dropping the
   `_x_N` temporaries — the output would then read like the avatar. Half a day.
3. **Build rule.** Regeneration is a documented Lean command (STANDARDS §3 allows it); a dune
   `rule` cannot run `lean` from WSL. The generated headers carry the exact command.
4. **Not in scope:** a Lean proof that the translation preserves meaning. Trust rests on Lean's
   own compiler having produced the IR (the same IR its C backend consumes) and on the
   differential; the rule table is small enough to audit.

## 7. Files

```
src/OCaml5/Lcnf/Dump.lean        monoDecl?/baseDecl?/ppMono, the shape printer (sketch)
src/OCaml5/Lcnf/Naming.lean      Lean name → OCaml name (types, fields, ctors, globals, locals)
src/OCaml5/Lcnf/Types.lean       inductive/structure → Ml.Syntax TypeDecl; trivial structures; closure with placeholders
src/OCaml5/Lcnf/Translate.lean   LCNF → Ml.Syntax (rules table), builtin table, call-graph closure, SCC emission
src/OCaml5/Tools/LcnfDump.lean   driver: print mono (or --base) LCNF of constants
src/OCaml5/Tools/LcnfGen.lean    driver: --out --cap --types roots… → one .ml + report
ocaml/gen/dune-project      (lang dune 3.0)
ocaml/gen/dune              library effect4_gen (machine_gen, fibers_gen, avatar_reference); executable gen_check; runtest
ocaml/gen/machine_gen.ml    GENERATED: the nine targets + 29 helpers, 10 full types
ocaml/gen/fibers_gen.ml     GENERATED: all 43 top-level functions of Fibers.lean, 154 lets, 38 full types
ocaml/gen/avatar_reference.ml  marked verbatim copy of avatar/deep_fibers.ml:184-214 (answer stubbed)
ocaml/gen/gen_check.ml      the checks of §4
ocaml/gen/NOTES.md          this file
```

Oleans of the four library modules live in the session scratch dir
(`…/scratchpad/ocaml5-olean/OCaml5/Lcnf/`), like the rest of `OCaml5.*` this session.
