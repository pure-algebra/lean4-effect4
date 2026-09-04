import OCaml5.Witnesses

/-!
# OCaml 5 spike: the compiler layer

Status: spike O5, 2026-09-03. Module `OCaml5.Compiler` of the non-default `OCaml5` library
(`lakefile.toml`, `srcDir = "workshop"`). Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` (§0 layer L3, §3 row O5).
Report: `docs/research/2026-09-03-spike-o5-compiler.md`. Predecessor: spike O1
(`docs/research/2026-09-03-spike-o1-runtime-machine.md`), whose §7 hands this file three items.

`OCaml5.Effect` is the runtime (L1/L2) and `OCaml5.Stdlib` — in `Effect.lean`, transcribed by
this spike — is the wrapper (L4). This module is the layer between them: how `%perform`,
`%resume`, `%runstack` and `%reperform` reach the runtime in bytecode and in native code, and
the one thing the compiler *refuses* to translate.

All compiler sources under `~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/`.

| What | Where |
| --- | --- |
| the four `Lambda.primitive` constructors | `lambda/lambda.ml:58-62` (`(* Context switches *)`) |
| their spellings and arities | `lambda/translprim.ml:371-374` |
| bytecode, `Pperform` | `bytecomp/bytegen.ml:417-419` (in `comp_primitive`) |
| bytecode, `Presume`/`Prunstack` | `bytecomp/bytegen.ml:786-795` (in `comp_expr`) |
| bytecode, `Preperform` | `bytecomp/bytegen.ml:796-804` |
| the tail test | `bytecomp/bytegen.ml:102-106` (`is_tailcall`), `:111-115` (`preserve_tailcall_for_prim`) |
| the instructions | `bytecomp/instruct.mli:127-130`, `bytecomp/emitcode.ml:312-315` |
| the opcodes | `runtime/caml/instruct.h:64` |
| native | `asmcomp/cmmgen.ml:861-865` (`Pperform`), `:1121-1138` (the three-argument ones) |

`comp_primitive`'s catch-all (`bytegen.ml:538`) lists `Prunstack | Presume | Preperform` among
"the cases below are handled in `comp_expr` before the `comp_primitive` call", which is why the
three-argument primitives have a tail/non-tail split and `Pperform` does not.
`cmmgen.ml:544` is the arity check (`fatal_error "Cmmgen.transl:prim, wrong arity"`), `:873` the
one-argument case that excludes the three-argument primitives, and `:1064` the two-argument case
that excludes all four.

Nothing here is an arm of `Machine.step`: the admission clause is a property of a `Term`, not a
transition, and the machine runs inadmissible terms perfectly well. It is `ocamlc` that refuses
them, and `Admissible` is the transcription of that refusal.
-/

namespace OCaml5

namespace Compiler

universe u

/-! ## The four primitives, the four instructions -/

/-- A `Lambda.primitive` of the "context switches" group (`lambda.ml:58-62`). -/
inductive Prim where
  | perform
  | resume
  | runstack
  | reperform
deriving DecidableEq, Repr, BEq, Inhabited

/-- A bytecode opcode (`runtime/caml/instruct.h:64`). The four effect instructions are the last
four before `FIRST_UNIMPLEMENTED_OP`. -/
inductive Opcode where
  | PERFORM
  | RESUME
  | RESUMETERM
  | REPERFORMTERM
deriving DecidableEq, Repr, BEq, Inhabited

namespace Opcode

/-- The `Instruct.instruction` constructor that `emitcode.ml:312-315` turns into this opcode
(`instruct.mli:127-130`). The two `term` forms carry `sz + nargs`, a stack depth this module
does not model. -/
def instruction : Opcode → String
  | .PERFORM => "Kperform"
  | .RESUME => "Kresume"
  | .RESUMETERM => "Kresumeterm n"
  | .REPERFORMTERM => "Kreperformterm n"

/-- What `ocamlc -dinstr` prints (`bytecomp/printinstr.ml`). -/
def dinstr : Opcode → String
  | .PERFORM => "perform"
  | .RESUME => "resume"
  | .RESUMETERM => "resumeterm"
  | .REPERFORMTERM => "reperformterm"

/-- The numeric opcode. `ACC0 = 0` at `instruct.h:23`, so the four at `:64` are 149-152; read
back from `Opcodes.opPERFORM …` of the installed `compiler-libs` (report §2). -/
def value : Opcode → Nat
  | .PERFORM => 149
  | .RESUME => 150
  | .RESUMETERM => 151
  | .REPERFORMTERM => 152

end Opcode

/-! ## Tail position

`bytegen.ml:102-106`:

```ocaml
let rec is_tailcall = function
    Kreturn _ :: _ -> true
  | Klabel _ :: c -> is_tailcall c
  | Kpop _ :: c -> is_tailcall c
  | _ -> false
```

It is a predicate on the *continuation* `cont` with which `comp_expr` was called, so on `Term`
it is a polarity handed down by the enclosing constructor. The two skipped instructions are what
make `let` bodies and `match` arms tail-transparent: `Llet` compiles its body with
`add_pop 1 cont` (`bytegen.ml:636-639`) and `make_branch` returns the `Kreturn` itself rather
than a branch when the continuation is one (`:67-83`). -/

/-- `is_tailcall cont` (`bytegen.ml:102-106`) as a polarity on the term being compiled. -/
inductive TailPosition where
  /-- `cont` begins with `Kreturn`, possibly behind `Klabel`s and `Kpop`s. -/
  | tail
  /-- Anything else: `Kpush`, `Kapply`, `Kpoptrap`, `Kraise`, `Kbranch`, `Kccall`, `Kstop`. -/
  | nonTail
deriving DecidableEq, Repr, BEq, Inhabited

/-! ## The lowering table -/

/-- Everything the compiler does with one primitive: its Lambda spelling and arity
(`translprim.ml`), the stack slack `check_stack` asks for, the bytecode instruction in each of
the two positions (`none` = the compiler refuses), and the native symbol. -/
structure Lowering where
  prim : Prim
  /-- The `external … = "%…"` spelling (`translprim.ml:371-374`). -/
  spelling : String
  /-- The `Lambda.primitive` constructor (`lambda.ml:59-62`). -/
  lambdaCtor : String
  /-- The arity `translprim.ml` records in `Primitive (P…, n)`. -/
  arity : Nat
  translprimLine : Nat
  /-- `check_stack stack_info (sz + slack)` in the `bytegen` clause. -/
  checkStackSlack : Nat
  bytegenLines : String
  /-- The opcode emitted when `is_tailcall cont`. -/
  tailOpcode : Option Opcode
  /-- The opcode emitted when not. `none` means `fatal_error`: the admission clause. -/
  nonTailOpcode : Option Opcode
  bytegenNote : String
  /-- The symbol `cmmgen` wraps in `Cop (Capply typ_val, [Cconst_symbol s; …])`. -/
  nativeSymbol : String
  cmmgenLines : String
  cmmgenNote : String
deriving Repr

/-- `%perform`. One argument in Lambda, two in Cmm: `cmmgen` allocates the `Cont_tag` block the
runtime fills in (`cmmgen.ml:862`, `make_alloc dbg Obj.cont_tag [int_const dbg 0]`) and passes it
alongside the effect value. No tail split — `Pperform` is the only one of the four that reaches
`comp_primitive`, which has no `cont` to test — even though `preserve_tailcall_for_prim`
(`bytegen.ml:111-115`) lists it, which only governs whether the *enclosing* application keeps
its `Kappterm`. -/
def loweringPerform : Lowering where
  prim := .perform
  spelling := "%perform"
  lambdaCtor := "Pperform"
  arity := 1
  translprimLine := 373
  checkStackSlack := 4
  bytegenLines := "bytegen.ml:417-419"
  tailOpcode := Option.some Opcode.PERFORM
  nonTailOpcode := Option.some Opcode.PERFORM
  bytegenNote :=
    "comp_primitive: check_stack stack_info (sz + 4) then Kperform. No is_tailcall test."
  nativeSymbol := "caml_perform"
  cmmgenLines := "cmmgen.ml:861-865"
  cmmgenNote :=
    "Capply of caml_perform on (transl env arg, a fresh Cont_tag block from"
      ++ " make_alloc dbg Obj.cont_tag [int_const dbg 0] at :862)."

/-- `%resume`. Three arguments; `bytegen` handles it in `comp_expr` (`:786-795`) together with
`Prunstack`, so the two are one clause and emit the *same* instruction. `nargs = 2` and the
instruction's operand is `sz + nargs`. The comment at `:788-789` explains the slack: "Resume
itself only pushes 3 words, but perform adds another". -/
def loweringResume : Lowering where
  prim := .resume
  spelling := "%resume"
  lambdaCtor := "Presume"
  arity := 3
  translprimLine := 374
  checkStackSlack := 4
  bytegenLines := "bytegen.ml:786-795"
  tailOpcode := Option.some Opcode.RESUMETERM
  nonTailOpcode := Option.some Opcode.RESUME
  bytegenNote :=
    "Lprim((Presume|Prunstack), args, _): check_stack (sz + 4); Kresumeterm(sz + nargs) with"
      ++ " discard_dead_code cont when is_tailcall cont, else Kresume :: cont."
  nativeSymbol := "caml_resume"
  cmmgenLines := "cmmgen.ml:1121-1126"
  cmmgenNote := "Capply of caml_resume on the three translated arguments."

/-- `%runstack`. Shares `bytegen.ml:786-795` with `%resume`: in bytecode there is no `RUNSTACK`
opcode at all (`instruct.h:64`). The runtime tells them apart by the stack the first argument
names — a fresh one from `caml_alloc_stack` for `runstack`, a captured one for `resume`. Native
code does have a separate symbol, and a separate calling sequence
(`amd64.S:958-995`, `arm64.S:826-872`), because it must install `frame_runstack` as the
return address. -/
def loweringRunstack : Lowering where
  prim := .runstack
  spelling := "%runstack"
  lambdaCtor := "Prunstack"
  arity := 3
  translprimLine := 371
  checkStackSlack := 4
  bytegenLines := "bytegen.ml:786-795"
  tailOpcode := Option.some Opcode.RESUMETERM
  nonTailOpcode := Option.some Opcode.RESUME
  bytegenNote :=
    "The same clause as Presume; no RUNSTACK opcode exists (instruct.h:64), so runstack is"
      ++ " RESUME/RESUMETERM on a stack caml_alloc_stack just made."
  nativeSymbol := "caml_runstack"
  cmmgenLines := "cmmgen.ml:1128-1132"
  cmmgenNote := "Capply of caml_runstack on the three translated arguments."

/-- `%reperform`. Three arguments, `check_stack (sz + 3)`, and **tail position only**: the
non-tail branch is `fatal_error "Reperform used in non-tail position"` (`bytegen.ml:803-804`).
This is the admission clause `Admissible` below decides. Native code has no such restriction —
`caml_reperform` is an ordinary `Capply` of a symbol (`cmmgen.ml:1134-1138`) — so the clause is a
*bytecode* restriction that `ocamlc` enforces on any program it compiles, whether or not that
program is ever run as bytecode. -/
def loweringReperform : Lowering where
  prim := .reperform
  spelling := "%reperform"
  lambdaCtor := "Preperform"
  arity := 3
  translprimLine := 372
  checkStackSlack := 3
  bytegenLines := "bytegen.ml:796-804"
  tailOpcode := Option.some Opcode.REPERFORMTERM
  nonTailOpcode := Option.none
  bytegenNote :=
    "Lprim(Preperform, args, _): check_stack (sz + 3); Kreperformterm(sz + nargs) when"
      ++ " is_tailcall cont, else fatal_error \"Reperform used in non-tail position\" (:804)."
  nativeSymbol := "caml_reperform"
  cmmgenLines := "cmmgen.ml:1134-1138"
  cmmgenNote :=
    "Capply of caml_reperform on the three translated arguments; no tail restriction in Cmm."

/-- The layer, one row per primitive. -/
def table : List Lowering :=
  [loweringPerform, loweringResume, loweringRunstack, loweringReperform]

def lowering : Prim → Lowering
  | .perform => loweringPerform
  | .resume => loweringResume
  | .runstack => loweringRunstack
  | .reperform => loweringReperform

/-- The bytecode instruction a primitive occurrence lowers to; `none` when the compiler refuses.
`bytegen.ml:417-419` (`Pperform`), `:791-795` (`Presume`/`Prunstack`), `:800-804`
(`Preperform`). -/
def Prim.opcode : Prim → TailPosition → Option Opcode
  | .perform, _ => Option.some Opcode.PERFORM
  | .resume, .tail => Option.some Opcode.RESUMETERM
  | .resume, .nonTail => Option.some Opcode.RESUME
  | .runstack, .tail => Option.some Opcode.RESUMETERM
  | .runstack, .nonTail => Option.some Opcode.RESUME
  | .reperform, .tail => Option.some Opcode.REPERFORMTERM
  | .reperform, .nonTail => Option.none

/- `Prim.opcode` is the table, read off in both positions. -/
#guard table.all fun l =>
  l.prim.opcode .tail == l.tailOpcode && l.prim.opcode .nonTail == l.nonTailOpcode

/- `%reperform` is the only primitive the compiler can refuse. -/
#guard (table.filter fun l => l.nonTailOpcode == Option.none).map (·.spelling) == ["%reperform"]

/- `%resume` and `%runstack` are one bytecode clause. -/
#guard loweringResume.tailOpcode == loweringRunstack.tailOpcode
  && loweringResume.nonTailOpcode == loweringRunstack.nonTailOpcode
  && loweringResume.bytegenLines == loweringRunstack.bytegenLines

/- …and four distinct native symbols. -/
#guard (table.map (·.nativeSymbol)) ==
  ["caml_perform", "caml_resume", "caml_runstack", "caml_reperform"]

/-! ## The admission clause

`Admissible t` is "`ocamlc` compiles `t`", i.e. every `reperform` occurrence in `t` is in tail
position in the sense of `is_tailcall`. Per `Term` constructor, with what the corresponding
`bytegen` clause does to the continuation:

| Constructor | Which subterms inherit the polarity | Why |
| --- | --- | --- |
| `lam body` | `body` is `tail`, always | a function body is compiled with `Kreturn` (`bytegen.ml:626-635` pushes it on `functions_to_compile`; `comp_remainder` gives it `Kreturn`) |
| `letIn bound body` | `body`; `bound` is `nonTail` | `Llet` (`:636-639`): the bound expression's continuation is `Kpush :: …`, the body's is `add_pop 1 cont`, and `is_tailcall` skips `Kpop` (`:105`) |
| `seq first next` | `next`; `first` is `nonTail` | `Lsequence` (`:910-911`): `first`'s continuation is the compiled `next` |
| `matchEff` / `matchExn` / `matchOpt` | every clause body and the default; the scrutinee is `nonTail` | `Lswitch` (`:933-…`) and `Lifthenelse` (`:908-909`) go through `make_branch`, which returns the `Kreturn` itself when the continuation is one (`:78-83`) |
| `tryWith body handler` | `handler` only; `body` is **`nonTail`** | `Ltrywith` (`:895-907`): the body's continuation is `Kpoptrap :: branch1 :: …`; the handler's is `add_pop 1 cont1` |
| `app fn arg` | neither | `comp_args` pushes; the continuation is `Kapply`/`Kappterm` |
| `raise e` | neither | `:757`: the operand's continuation is `Kraise k :: …` |
| `perform`, `resume`, `runstack`, `reperform`, `allocStack`, `contUseNoexc`, `contUseUpdate`, `dropCont` | no operand | `comp_args` pushes each operand; the continuation is the instruction or the `Kccall` |
| `eff`, `exn`, `some`, `add`, `emitOf`, `setCell` | no operand | `Kmakeblock` / `Kaddint` / `Kccall` follow |
| `val`, `unit`, `var`, `none`, `emit`, `getCell` | — | leaves |

**The non-OCaml helpers.** `Term.add`, `Term.emit`, `Term.emitOf`, `Term.getCell` and
`Term.setCell` are spike O1's additions (its report §4), not OCaml primitives; the O1 report §7
asks for a ruling. The ruling: **opaque, and their operands are not in tail position**. They
stand for `+`, `print_string`, `Printf.printf`, `!r` and `r := e`, all of which are an `Lprim` or
an `Lapply` whose arguments `comp_args` compiles with a pushing continuation, and none of which
is `Preperform`; so treating them as opaque cannot admit a term `ocamlc` rejects, and treating
their operands as non-tail cannot reject a term `ocamlc` admits, because `x + reperform …`,
`print_string (reperform …)` and `r := reperform …` are all rejected by `ocamlc` (report §4,
probes `makeblock operand` and `ccall operand`).

**Where the top of a term sits.** `Admissible` reads the whole term at `nonTail`, so a
`reperform` that is not under a `lam` is rejected. That is what `ocamlc` does: a structure item
`let v = reperform e k l` is compiled with the rest of the compilation unit as its continuation,
and `ocamlc` reports the fatal error (report §4, probe `toplevel`). -/

mutual

/-- Every `reperform` in the term is in tail position, given that the term itself sits in
position `tp`. Bool-valued and structural: `Term` nests through `List`, so `DecidableEq` is not
derivable (O1 report §7) and none is needed. -/
def admissibleAt {ν : Type u} (tp : TailPosition) : Term ν → Bool
  | .val _ => true
  | .unit => true
  | .var _ => true
  | .lam body => admissibleAt TailPosition.tail body
  | .app fn arg => admissibleAt TailPosition.nonTail fn && admissibleAt TailPosition.nonTail arg
  | .letIn bound body => admissibleAt TailPosition.nonTail bound && admissibleAt tp body
  | .seq first next => admissibleAt TailPosition.nonTail first && admissibleAt tp next
  | .add a b => admissibleAt TailPosition.nonTail a && admissibleAt TailPosition.nonTail b
  | .emit _ => true
  | .emitOf _ e => admissibleAt TailPosition.nonTail e
  | .getCell => true
  | .setCell e => admissibleAt TailPosition.nonTail e
  | .eff _ payload => admissibleAt TailPosition.nonTail payload
  | .matchEff scrutinee clauses default =>
      admissibleAt TailPosition.nonTail scrutinee
        && admissibleEffClauses tp clauses && admissibleAt tp default
  | .exn _ payload => admissibleAt TailPosition.nonTail payload
  | .matchExn scrutinee clauses default =>
      admissibleAt TailPosition.nonTail scrutinee
        && admissibleExnClauses tp clauses && admissibleAt tp default
  | .raise e => admissibleAt TailPosition.nonTail e
  | .tryWith body handler =>
      admissibleAt TailPosition.nonTail body && admissibleAt tp handler
  | .none => true
  | .some e => admissibleAt TailPosition.nonTail e
  | .matchOpt scrutinee noneCase someCase =>
      admissibleAt TailPosition.nonTail scrutinee
        && admissibleAt tp noneCase && admissibleAt tp someCase
  | .perform e => admissibleAt TailPosition.nonTail e
  | .resume s f a =>
      admissibleAt TailPosition.nonTail s && admissibleAt TailPosition.nonTail f
        && admissibleAt TailPosition.nonTail a
  | .runstack s f a =>
      admissibleAt TailPosition.nonTail s && admissibleAt TailPosition.nonTail f
        && admissibleAt TailPosition.nonTail a
  -- `bytegen.ml:800-804`: `Kreperformterm` when `is_tailcall cont`, `fatal_error` otherwise.
  | .reperform e c l =>
      (match tp with | .tail => true | .nonTail => false)
        && admissibleAt TailPosition.nonTail e && admissibleAt TailPosition.nonTail c
        && admissibleAt TailPosition.nonTail l
  | .allocStack hv hx hf =>
      admissibleAt TailPosition.nonTail hv && admissibleAt TailPosition.nonTail hx
        && admissibleAt TailPosition.nonTail hf
  | .contUseNoexc c => admissibleAt TailPosition.nonTail c
  | .contUseUpdate c hv hx hf =>
      admissibleAt TailPosition.nonTail c && admissibleAt TailPosition.nonTail hv
        && admissibleAt TailPosition.nonTail hx && admissibleAt TailPosition.nonTail hf
  | .dropCont c => admissibleAt TailPosition.nonTail c

/-- Every arm of a `matchEff` inherits the polarity of the `match` (`make_branch`,
`bytegen.ml:78-83`). -/
def admissibleEffClauses {ν : Type u} (tp : TailPosition) : List (EffId × Term ν) → Bool
  | [] => true
  | (_, t) :: rest => admissibleAt tp t && admissibleEffClauses tp rest

/-- Likewise for `matchExn`. -/
def admissibleExnClauses {ν : Type u} (tp : TailPosition) : List (ExnId × Term ν) → Bool
  | [] => true
  | (_, t) :: rest => admissibleAt tp t && admissibleExnClauses tp rest

end

/-- `ocamlc` compiles this term: every `reperform` in it is in tail position
(`bytegen.ml:796-804`). A compilation unit's top level is not a tail position, so the whole term
is read at `nonTail`. -/
def Admissible {ν : Type u} (t : Term ν) : Bool :=
  admissibleAt TailPosition.nonTail t

/-! ## Reading the lowering off a term

`opcodesAt tp t` is the sequence of bytecode instructions the four primitives of `t` lower to,
each at the polarity its position gives it, in the order `bytegen` emits them: a primitive's
operands first (`comp_args`), then the instruction. This is a static read of the `Term`, not a
disassembly; §5 of the report compares it against `ocamlc -dinstr`.

An occurrence the compiler refuses contributes nothing, so the sequence is only meaningful on an
`Admissible` term. `opcodesRefused` counts the refusals. -/

mutual

/-- The effect instructions of a term, in emission order. -/
def opcodesAt {ν : Type u} (tp : TailPosition) : Term ν → List Opcode
  | .val _ => []
  | .unit => []
  | .var _ => []
  | .lam body => opcodesAt TailPosition.tail body
  | .app fn arg => opcodesAt TailPosition.nonTail fn ++ opcodesAt TailPosition.nonTail arg
  | .letIn bound body => opcodesAt TailPosition.nonTail bound ++ opcodesAt tp body
  | .seq first next => opcodesAt TailPosition.nonTail first ++ opcodesAt tp next
  | .add a b => opcodesAt TailPosition.nonTail a ++ opcodesAt TailPosition.nonTail b
  | .emit _ => []
  | .emitOf _ e => opcodesAt TailPosition.nonTail e
  | .getCell => []
  | .setCell e => opcodesAt TailPosition.nonTail e
  | .eff _ payload => opcodesAt TailPosition.nonTail payload
  | .matchEff scrutinee clauses default =>
      opcodesAt TailPosition.nonTail scrutinee ++ opcodesEffClauses tp clauses
        ++ opcodesAt tp default
  | .exn _ payload => opcodesAt TailPosition.nonTail payload
  | .matchExn scrutinee clauses default =>
      opcodesAt TailPosition.nonTail scrutinee ++ opcodesExnClauses tp clauses
        ++ opcodesAt tp default
  | .raise e => opcodesAt TailPosition.nonTail e
  | .tryWith body handler => opcodesAt TailPosition.nonTail body ++ opcodesAt tp handler
  | .none => []
  | .some e => opcodesAt TailPosition.nonTail e
  | .matchOpt scrutinee noneCase someCase =>
      opcodesAt TailPosition.nonTail scrutinee ++ opcodesAt tp noneCase
        ++ opcodesAt tp someCase
  | .perform e =>
      opcodesAt TailPosition.nonTail e ++ (Prim.opcode Prim.perform tp).toList
  | .resume s f a =>
      opcodesAt TailPosition.nonTail s ++ opcodesAt TailPosition.nonTail f
        ++ opcodesAt TailPosition.nonTail a ++ (Prim.opcode Prim.resume tp).toList
  | .runstack s f a =>
      opcodesAt TailPosition.nonTail s ++ opcodesAt TailPosition.nonTail f
        ++ opcodesAt TailPosition.nonTail a ++ (Prim.opcode Prim.runstack tp).toList
  | .reperform e c l =>
      opcodesAt TailPosition.nonTail e ++ opcodesAt TailPosition.nonTail c
        ++ opcodesAt TailPosition.nonTail l ++ (Prim.opcode Prim.reperform tp).toList
  | .allocStack hv hx hf =>
      opcodesAt TailPosition.nonTail hv ++ opcodesAt TailPosition.nonTail hx
        ++ opcodesAt TailPosition.nonTail hf
  | .contUseNoexc c => opcodesAt TailPosition.nonTail c
  | .contUseUpdate c hv hx hf =>
      opcodesAt TailPosition.nonTail c ++ opcodesAt TailPosition.nonTail hv
        ++ opcodesAt TailPosition.nonTail hx ++ opcodesAt TailPosition.nonTail hf
  | .dropCont c => opcodesAt TailPosition.nonTail c

def opcodesEffClauses {ν : Type u} (tp : TailPosition) : List (EffId × Term ν) → List Opcode
  | [] => []
  | (_, t) :: rest => opcodesAt tp t ++ opcodesEffClauses tp rest

def opcodesExnClauses {ν : Type u} (tp : TailPosition) : List (ExnId × Term ν) → List Opcode
  | [] => []
  | (_, t) :: rest => opcodesAt tp t ++ opcodesExnClauses tp rest

end

/-- The instructions of a whole compilation unit's term. -/
def opcodes {ν : Type u} (t : Term ν) : List Opcode :=
  opcodesAt TailPosition.nonTail t

/-- The instructions of a term used as a function body, which is how every `Stdlib` builder is
used: `let continue k v = …` compiles its right-hand side at `tail`. -/
def opcodesAsBody {ν : Type u} (t : Term ν) : List Opcode :=
  opcodesAt TailPosition.tail t

/-! ## The `Stdlib` builders are admitted

Spike O1's report §7 item 2: every `OCaml5.Stdlib` builder places its `reperform` as the last
expression of the default arm of the `effc` closure's `matchEff`, which is a tail position, so
all of them compile. Here that is decided rather than argued. The builders' `Term` arguments are
instantiated with `reperform`-free closed terms, which is what every caller passes; the general
statement, with the hypotheses on the arguments, is the theorem block below. -/

/-- `Term Nat`, as in `OCaml5.Witnesses`. -/
abbrev CT := Term Nat

private def k0 : CT := .var 0
private def v0 : CT := .unit
private def body0 : CT := .lam (.var 0)
private def clauses0 : List (EffId × CT) := [(⟨1⟩, .var 2), (⟨2⟩, .emit "x")]

#guard Admissible (Stdlib.deepContinue k0 v0)
#guard Admissible (Stdlib.deepDiscontinue k0 v0)
#guard Admissible (Stdlib.deepDiscontinueWithBacktrace k0 v0 .unit)
#guard Admissible (Stdlib.effcClosure clauses0)
#guard Admissible (Stdlib.effcClosureWith clauses0 (.emit "none"))
#guard Admissible (Stdlib.deepMatchWith body0 v0 body0 body0 clauses0)
#guard Admissible (Stdlib.deepMatchWithLogging body0 v0 body0 body0 (.emit "none") clauses0)
#guard Admissible (Stdlib.deepTryWith body0 v0 clauses0)
#guard Admissible (Stdlib.deepTryWithLogging body0 v0 (.emit "none") clauses0)
#guard Admissible (Stdlib.shallowFiber ⟨4⟩ ⟨4⟩ body0)
#guard Admissible (Stdlib.shallowContinueGen k0 body0 v0 body0 body0 clauses0)
#guard Admissible (Stdlib.shallowContinueWith k0 v0 body0 body0 clauses0)
#guard Admissible (Stdlib.shallowDiscontinueWith k0 v0 body0 body0 clauses0)
#guard Admissible (Stdlib.shallowDiscontinueWithBacktrace k0 v0 .unit body0 body0 clauses0)

/- The whole executed corpus of `OCaml5.Witnesses`, thirteen terms built from those builders. -/
#guard corpus.all fun w => Admissible w.term

/- …including witness 11, the one that uses `Shallow.fiber` and the one-step unrolling of
`let rec h2` (O1 report §6). -/
#guard Admissible witness11.term

/-! ## What is rejected, and what is not

Each `#guard` below pairs with an `ocamlc -c` probe of the same shape, run in report §4. The
`reperform` is put under a `lam` in every case, so it is the *position inside the function* that
decides, not the top of the unit. -/

private def rp : CT := .reperform (.var 3) (.var 2) (.var 1)

/- `let x = reperform e k l in x + 1` — rejected. (`let x = reperform … in x` is *accepted* by
`ocamlc`, because `Simplif` eliminates the binding before `bytegen` sees it; that is a
simplification, not a tail position, and this predicate is on the term as written.) -/
#guard !Admissible (.lam (.letIn rp (.add (.var 0) (.val 1))) : CT)

/- The one place `Admissible` is deliberately stricter than `ocamlc`: `let x = reperform e k l
in x` is *accepted* by the compiler, because `Simplif`'s let-elimination removes the binding
before `bytegen` sees it, so the `reperform` ends up in the tail position the `let` occupied.
This predicate reads the term as written and rejects it. Recorded in report §4; no `Stdlib`
builder and no witness has that shape, and no shape that `Simplif` would rescue is admitted by
`ocamlc` for any other reason. -/
#guard !Admissible (.lam (.letIn rp (.var 0)) : CT)

/- `g (reperform e k l)` — rejected. -/
#guard !Admissible (.lam (.app body0 rp) : CT)

/- `ignore (reperform e k l); 0` — rejected: `seq` evaluates its first operand with the compiled
`next` as continuation. -/
#guard !Admissible (.lam (.seq rp .unit) : CT)

/- `try reperform e k l with _ -> 0` — rejected: the try body's continuation is
`Kpoptrap :: …`. -/
#guard !Admissible (.lam (.tryWith rp (.var 0)) : CT)

/- `resume s g (reperform e k l)` — rejected: an operand of a three-argument primitive. -/
#guard !Admissible (.lam (.resume (.var 0) body0 rp) : CT)

/- `alloc_stack … (reperform e k l)` — rejected: an operand of a `Kccall`. -/
#guard !Admissible (.lam (.allocStack body0 body0 rp) : CT)

/- `raise (X (reperform e k l))` — rejected: `:757` gives the operand a `Kraise` continuation. -/
#guard !Admissible (.lam (.raise (.exn ⟨9⟩ rp)) : CT)

/- `((reperform e k l), 1)` — rejected: an operand of a `Kmakeblock`. -/
#guard !Admissible (.lam (.eff ⟨9⟩ rp) : CT)

/- `match reperform e k l with …` — rejected: the scrutinee. -/
#guard !Admissible (.lam (.matchEff rp [] .unit) : CT)

/- `let v = reperform e k l` at the top of a compilation unit — rejected. -/
#guard !Admissible (rp : CT)

/- `fun … -> reperform e k l` — admitted. -/
#guard Admissible (.lam rp : CT)

/- `let y = 1 in …; reperform e k l` — admitted: `Kpop` is skipped (`:105`). -/
#guard Admissible (.lam (.letIn (.val 1) rp) : CT)

/- `print_string "x"; reperform e k l` — admitted. -/
#guard Admissible (.lam (.seq (.emit "x") rp) : CT)

/- `match eff with … | _ -> reperform e k l` — admitted: this is the `effc` of
`effect.ml:73-77`. -/
#guard Admissible (.lam (.matchEff .unit [] rp) : CT)

/- …and in a named arm too. -/
#guard Admissible (.lam (.matchEff .unit [(⟨1⟩, rp)] .unit) : CT)

/- `match e with X -> reperform … | e -> reperform …` — admitted. -/
#guard Admissible (.lam (.matchExn .unit [(⟨1⟩, rp)] rp) : CT)

/- `match o with None -> reperform … | Some _ -> reperform …` — admitted. -/
#guard Admissible (.lam (.matchOpt .unit rp rp) : CT)

/- `try g () with _ -> reperform e k l` — admitted: the handler's continuation is
`add_pop 1 cont1`. -/
#guard Admissible (.lam (.tryWith .unit rp) : CT)

/- The rejection is *only* about `reperform`: the same shapes with `resume` or `perform` in them
are all admitted, in either position. -/
#guard Admissible (.lam (.seq (.resume (.var 0) body0 .unit) (.perform .unit)) : CT)

/-! ## The lowering, read off against `ocamlc -dinstr`

Report §5. Each row below is one `.ml` file holding exactly one `stdlib/effect.ml` definition,
transcribed verbatim on top of the `external` block of `:16,41-42,49-55,69-70,130-135`, compiled
with `ocamlc -dinstr -c`; `opcodes` is the subsequence of the dump that matches one of the four
effect instructions, in the order printed. The `#guard` next to each is that
`opcodesAsBody` of the corresponding `OCaml5.Stdlib` builder is that same sequence. -/

/-- One `ocamlc -dinstr` observation. -/
structure Dump where
  /-- The `stdlib/effect.ml` definition transcribed. -/
  name : String
  /-- Its lines in `stdlib/effect.ml`. -/
  effectMlLines : String
  /-- The effect instructions `ocamlc -dinstr -c` printed, in order. -/
  opcodes : List Opcode
deriving Repr

/-- `Deep.continue` (`effect.ml:57`). -/
def dumpContinue : Dump :=
  ⟨"continue", "57", [Opcode.RESUMETERM]⟩

/-- `Deep.discontinue` (`effect.ml:59`). -/
def dumpDiscontinue : Dump :=
  ⟨"discontinue", "59", [Opcode.RESUMETERM]⟩

/-- `Deep.match_with` (`effect.ml:64-79`): the `effc` closure is emitted first, then the body. -/
def dumpMatchWith : Dump :=
  ⟨"match_with", "72-79", [Opcode.REPERFORMTERM, Opcode.RESUMETERM]⟩

/-- `Deep.try_with` (`effect.ml:81-91`). -/
def dumpTryWith : Dump :=
  ⟨"try_with", "84-91", [Opcode.REPERFORMTERM, Opcode.RESUMETERM]⟩

/-- `Shallow.fiber` (`effect.ml:110-123`). The `perform` is in the `f'` closure; the `runstack`
is under the trap of `:121`, so it is `RESUME`, not `RESUMETERM` — the only non-tail effect
primitive in `stdlib/effect.ml`. -/
def dumpFiber : Dump :=
  ⟨"fiber", "110-123", [Opcode.PERFORM, Opcode.RESUME]⟩

/-- `Shallow.continue_gen` (`effect.ml:125-147`). -/
def dumpContinueGen : Dump :=
  ⟨"continue_gen", "140-147", [Opcode.REPERFORMTERM, Opcode.RESUMETERM]⟩

def dumps : List Dump :=
  [dumpContinue, dumpDiscontinue, dumpMatchWith, dumpTryWith, dumpFiber, dumpContinueGen]

#guard opcodesAsBody (Stdlib.deepContinue k0 v0) == dumpContinue.opcodes
#guard opcodesAsBody (Stdlib.deepDiscontinue k0 v0) == dumpDiscontinue.opcodes
#guard opcodesAsBody (Stdlib.deepMatchWith body0 v0 body0 body0 clauses0) == dumpMatchWith.opcodes
#guard opcodesAsBody (Stdlib.deepTryWith body0 v0 clauses0) == dumpTryWith.opcodes
#guard opcodesAsBody (Stdlib.shallowFiber ⟨4⟩ ⟨4⟩ body0) == dumpFiber.opcodes
#guard opcodesAsBody (Stdlib.shallowContinueGen k0 body0 v0 body0 body0 clauses0)
  == dumpContinueGen.opcodes

/- The one `RESUME` of `stdlib/effect.ml` is `Shallow.fiber`'s `runstack`, and it is the only
`Stdlib` builder with a non-tail primitive. -/
#guard (dumps.filter fun d => d.opcodes.contains Opcode.RESUME).map (·.name) == ["fiber"]

/-! ### The witnesses

The witness `.ml` files call `Stdlib.Effect`, so their own `ocamlc -dinstr` dumps contain only
the `perform`s they write themselves; the `resumeterm`s and `reperformterm`s are in
`stdlib.cmo`'s `effect.ml`. The Lean terms inline the builders, so their read-off is the union.
The `PERFORM` count is the one part that must agree with the witness's own dump. -/

/-- The number of `perform` instructions in the witness's own `ocamlc -dinstr -c` output
(report §5). -/
def witnessOwnPerforms : List (String × Nat) :=
  [("w01-repeated", 2), ("w05-forwarded", 2), ("w11-shallow-reinstall", 2)]

#guard opcodes witness01.term ==
  [Opcode.RESUMETERM, Opcode.REPERFORMTERM, Opcode.PERFORM, Opcode.PERFORM, Opcode.RESUME]

#guard (opcodes witness01.term).countP (· == Opcode.PERFORM) == 2

#guard (opcodes witness05.term).countP (· == Opcode.PERFORM) == 2

/- Witness 11 has three `PERFORM`s in Lean and two in its own dump: the third is
`Shallow.fiber`'s `perform M.Initial_setup__` (`effect.ml:113`), which lives in `effect.ml`, not
in the witness. -/
#guard (opcodes witness11.term).countP (· == Opcode.PERFORM) == 3

/- Witness 11 is also the only witness whose read-off contains a `RESUME`: it is the one that
goes through `Shallow.fiber`. -/
#guard opcodes witness05.term ==
  [Opcode.RESUMETERM, Opcode.REPERFORMTERM, Opcode.RESUMETERM, Opcode.REPERFORMTERM,
   Opcode.PERFORM, Opcode.PERFORM, Opcode.RESUMETERM, Opcode.RESUME]

#guard opcodes witness11.term ==
  [Opcode.PERFORM, Opcode.PERFORM, Opcode.PERFORM, Opcode.RESUME, Opcode.REPERFORMTERM,
   Opcode.RESUMETERM, Opcode.REPERFORMTERM, Opcode.RESUMETERM, Opcode.REPERFORMTERM,
   Opcode.RESUME]

/- Inlining is the reason the witness read-offs carry `RESUME` where `stdlib/effect.ml` carries
`RESUMETERM`: OCaml *calls* `Deep.try_with`, whose `runstack` is the last expression of the
callee, whereas the Lean term substitutes the builder into the caller, most often into a `letIn`
bound position, which is not a tail position. Twelve of the thirteen witnesses have at least one
such demoted `runstack`/`resume`; only witness 04, which has no `continue`, does not. The
demotion is harmless — both instructions exist — and it never reaches a `reperform`, because the
three `lam`s of `effcClosure` restore the tail polarity wherever the closure is put. -/
#guard (corpus.filter fun w => !(opcodes w.term).contains Opcode.RESUME).map (·.name)
  == ["w04-unhandled-perform"]

/- The `reperform` count is what inlining must not change, and does not: every witness is
admissible read as a compilation unit and read as a function body alike. -/
#guard corpus.all fun w =>
  admissibleAt TailPosition.tail w.term && admissibleAt TailPosition.nonTail w.term

#guard corpus.all fun w =>
  (opcodes w.term).countP (· == Opcode.REPERFORMTERM)
    == (opcodesAsBody w.term).countP (· == Opcode.REPERFORMTERM)

/- No witness is refused: every `reperform` occurrence in the corpus lowers to
`Kreperformterm`. -/
#guard corpus.all fun w => Admissible w.term

/-! ## Preservation

The builders substitute nothing and unroll nothing: each is a fixed term shape with holes, and
the one unrolling in the corpus is witness 11's `let rec h2` (O1 report §6), which is a builder
applied to a clause list that contains the next layer. So "preserved by substitution" is, here,
compositionality: each builder is admissible exactly when its arguments are admissible at the
polarity the builder puts them in. That is what the theorems below say, and the `#guard`s above
are their instances. `admissible_shallowContinueGen` is the one that makes any finite unrolling
of `h2` admissible, by induction on the depth. -/

variable {ν : Type u}

/-- The `effc` closure of `effect.ml:73-77`: admissible at *any* ambient polarity, whatever the
clause bodies do with `reperform`, provided each clause body is admissible in tail position.
The `reperform` of the default arm never depends on the ambient polarity, because three `lam`s
separate it from the outside. -/
theorem admissible_effcClosure (tp : TailPosition) (effc : List (EffId × Term ν))
    (h : admissibleEffClauses TailPosition.tail effc = true) :
    admissibleAt tp (Stdlib.effcClosure effc) = true := by
  simp [Stdlib.effcClosure, admissibleAt, h]

/-- The same for the logging variant, whose default arm is `seq onNone (reperform …)`: `seq`
hands its `next` the ambient polarity, so the `reperform` is still in tail position. -/
theorem admissible_effcClosureWith (tp : TailPosition) (effc : List (EffId × Term ν))
    (onNone : Term ν) (h : admissibleEffClauses TailPosition.tail effc = true)
    (hn : admissibleAt TailPosition.nonTail onNone = true) :
    admissibleAt tp (Stdlib.effcClosureWith effc onNone) = true := by
  simp [Stdlib.effcClosureWith, admissibleAt, h, hn]

/-- `Deep.match_with` (`effect.ml:72-79`) is admissible whenever its four term arguments are
admissible where it puts them: `retc` and `exnc` as operands of `caml_alloc_stack`, `comp` and
`arg` as operands of `runstack`, and every `effc` clause body in tail position. -/
theorem admissible_deepMatchWith (tp : TailPosition) (comp arg retc exnc : Term ν)
    (effc : List (EffId × Term ν))
    (hcomp : admissibleAt TailPosition.nonTail comp = true)
    (harg : admissibleAt TailPosition.nonTail arg = true)
    (hretc : admissibleAt TailPosition.nonTail retc = true)
    (hexnc : admissibleAt TailPosition.nonTail exnc = true)
    (heffc : admissibleEffClauses TailPosition.tail effc = true) :
    admissibleAt tp (Stdlib.deepMatchWith comp arg retc exnc effc) = true := by
  simp [Stdlib.deepMatchWith, admissibleAt, Stdlib.effcClosure, hcomp, harg, hretc, hexnc, heffc]

/-- `Deep.try_with` (`effect.ml:84-91`), the same statement with the two fixed handlers. -/
theorem admissible_deepTryWith (tp : TailPosition) (comp arg : Term ν)
    (effc : List (EffId × Term ν))
    (hcomp : admissibleAt TailPosition.nonTail comp = true)
    (harg : admissibleAt TailPosition.nonTail arg = true)
    (heffc : admissibleEffClauses TailPosition.tail effc = true) :
    admissibleAt tp (Stdlib.deepTryWith comp arg effc) = true := by
  simp [Stdlib.deepTryWith, Stdlib.deepMatchWith, admissibleAt, Stdlib.effcClosure,
    hcomp, harg, heffc]

/-- `Shallow.continue_gen` (`effect.ml:140-147`). Its hypothesis on `effc` is exactly its
conclusion's shape one layer down, which is what makes any finite unrolling of witness 11's
`let rec h2` admissible: if the innermost copy's clause list is admissible, so is every layer
above it. -/
theorem admissible_shallowContinueGen (tp : TailPosition) (k resumeFun v retc exnc : Term ν)
    (effc : List (EffId × Term ν))
    (hk : admissibleAt TailPosition.nonTail k = true)
    (hr : admissibleAt TailPosition.nonTail resumeFun = true)
    (hv : admissibleAt TailPosition.nonTail v = true)
    (hretc : admissibleAt TailPosition.nonTail retc = true)
    (hexnc : admissibleAt TailPosition.nonTail exnc = true)
    (heffc : admissibleEffClauses TailPosition.tail effc = true) :
    admissibleAt tp (Stdlib.shallowContinueGen k resumeFun v retc exnc effc) = true := by
  simp [Stdlib.shallowContinueGen, admissibleAt, Stdlib.effcClosure,
    hk, hr, hv, hretc, hexnc, heffc]

/-- `Shallow.fiber` (`effect.ml:110-123`) contains no `reperform` at all, so it is admissible for
every closed `f` that is: the only hypothesis is on `f`. -/
theorem admissible_shallowFiber (tp : TailPosition) (initId : EffId) (eId failId : ExnId)
    (f : Term ν) (hf : admissibleAt TailPosition.nonTail f = true) :
    admissibleAt tp (Stdlib.shallowFiber initId eId f failId) = true := by
  simp [Stdlib.shallowFiber, admissibleAt, admissibleEffClauses, admissibleExnClauses, hf]

/-- `Deep.continue` and `Deep.discontinue` (`effect.ml:57,59`) contain no `reperform`. -/
theorem admissible_deepContinue (tp : TailPosition) (k v : Term ν)
    (hk : admissibleAt TailPosition.nonTail k = true)
    (hv : admissibleAt TailPosition.nonTail v = true) :
    admissibleAt tp (Stdlib.deepContinue k v) = true := by
  simp [Stdlib.deepContinue, admissibleAt, hk, hv]

theorem admissible_deepDiscontinue (tp : TailPosition) (k e : Term ν)
    (hk : admissibleAt TailPosition.nonTail k = true)
    (he : admissibleAt TailPosition.nonTail e = true) :
    admissibleAt tp (Stdlib.deepDiscontinue k e) = true := by
  simp [Stdlib.deepDiscontinue, admissibleAt, hk, he]

/-- A closed term with no `reperform` at all is admissible in either position; formally, the
polarity only matters at a `reperform` node. Stated for the two builders whose admissibility is
polarity-free above; the general lemma (`admissibleAt .nonTail t → admissibleAt .tail t`) needs
an induction over the nested `Term`/`List` recursor and is recorded as open in the report. -/
theorem admissible_of_admissible_nonTail_effcClosure (effc : List (EffId × Term ν))
    (h : admissibleEffClauses TailPosition.tail effc = true) :
    admissibleAt TailPosition.nonTail (Stdlib.effcClosure effc) = true
      ∧ admissibleAt TailPosition.tail (Stdlib.effcClosure effc) = true :=
  ⟨admissible_effcClosure _ _ h, admissible_effcClosure _ _ h⟩

end Compiler

end OCaml5
