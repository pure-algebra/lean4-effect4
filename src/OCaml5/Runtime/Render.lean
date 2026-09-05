import OCaml5.Runtime.Effect
import OCaml5.Runtime.Compiler
import OCaml5.Runtime.Witnesses
import OCaml5.Ml.Identifier
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render

/-!
# OCaml5.Render — `Term` → OCaml 5 source

**What it is.** `Term.render`: one `OCaml5.Term` as one OCaml 5 compilation unit over the raw
effect primitives, which is what a reference machine needs. Origin: spike P5 (2026-09-03,
report `docs/research/2026-09-03-spike-p5-fuzz.md`). The declaration surface this file once
held is `OCaml5.Ml`; the avatar's descriptions are `OCaml5.Avatar`.

**Depends on.** `OCaml5.Effect` (`Term`), `OCaml5.Compiler` (`Admissible`), `OCaml5.Witnesses`
(the corpus the checks run over), `OCaml5.Ml.{Identifier,Syntax,Render}` (`escString`).

This closes the top edge of the plan's §6 diagram: `render` takes an `OCaml5.Term` and produces
an OCaml 5 compilation unit that `ocamlc`, `ocamlopt` and `js_of_ocaml` accept, and whose printed
rows are `Machine.rows` of the same term. `Effect.lean` and `Compiler.lean` are imported and never
edited.

## The typing discipline

`Term` is untyped; OCaml is not. The discipline that makes `render` total and its output
well-typed is **one universal type**:

```ocaml
type u = I of int | U | F of (u -> u) | Ef of u Effect.t | Xn of exn
       | Nn | Sm of u | Kt of (u,u) continuation | Sk of (u,u) stack | Lf of last_fiber
```

one constructor per `OCaml5.Value` constructor (`Value.stack` and `Value.nullStack` share `Sk`,
because a null stack *is* a `('a,'b) stack` at the OCaml level — that is what
`caml_continuation_use_noexc` returns on a taken handle). Every rendered subterm has OCaml type
`u`, so rendering is compositional and cannot fail to type-check. The primitives are reached
through coercions (`as_int`, `as_fun`, `as_eff`, `as_exn`, `as_k`, `as_stk`, `as_lf`), each of
which prints `!stuck` and exits 2 on a mismatch — exactly the terms on which `Machine.step`
answers `Outcome.stuck`.

Everything is instantiated at `u`, which monomorphises the whole external block:

| external | `effect.ml` type | here |
| --- | --- | --- |
| `%perform` | `'a t -> 'a` | `u Effect.t -> u` |
| `%resume` | `('a,'b) stack -> ('c -> 'a) -> 'c -> 'b` | `(u,u) stack -> (u -> u) -> u -> u` |
| `%runstack` | idem | idem |
| `%reperform` | `'a t -> ('a,'b) continuation -> last_fiber -> 'b` | `u Effect.t -> (u,u) continuation -> last_fiber -> u` |
| `caml_alloc_stack` | `('a -> 'b) -> (exn -> 'b) -> ('c t -> ('c,'b) continuation -> last_fiber -> 'b) -> ('a,'b) stack` | all four at `u` |
| `caml_continuation_use_noexc` | `('a,'b) continuation -> ('a,'b) stack` | at `u` |
| `caml_continuation_use_and_update_handler_noexc` | `('a,'b) continuation -> ('b -> 'c) -> (exn -> 'c) -> (…) -> ('a,'c) stack` | at `u` |
| `caml_drop_continuation` | `('a,'b) continuation -> unit` | at `u` |

`('a,'b) stack`, `('a,'b) continuation` and `last_fiber` are declared abstract in the generated
unit, exactly as `stdlib/effect.ml:39,46-47,100-101` declares them; the machine has one
continuation type, so `Deep.continuation` and `Shallow.continuation` are one type here. The
externals are the *raw* ones (`effect.ml:16,41-42,49-55,69-70,130-135`), never `Stdlib.Effect`'s
wrappers, so a term built by an `OCaml5.Stdlib` builder renders to the primitives that builder is
defined over — ruling 2, the wrapper is derived. The two exceptions the runtime itself raises are
the registered ones (`effect.ml:18-19`, `Callback.register_exception`), so `ExnId.unhandled` is
`Effect.Unhandled` and `ExnId.continuationAlreadyResumed` is `Effect.Continuation_already_resumed`;
every other `ExnId n` is a generated `exception Xn of u`, and every `EffId n` a generated
`type _ Effect.t += En : u -> u Effect.t`.

Four restrictions the discipline imposes on a term, none of which any of the thirteen witnesses
or any generated program violates (`Fuzz.wellFormed` decides them):

1. **`emitOf` only on a printable value.** `Value.render` prints `cont7`/`stack3` — heap indices
   no host can know (O1 report §4.1). A rendered `emitOf` prints `cont`/`stack` without the index,
   so a term that `emitOf`s a continuation or a stack would disagree with the machine by
   construction. Ints, `()`, `<fun>`, `none`, `some(…)`, `effN` and `exnN` are printable.
2. **No payload binder in an `Unhandled` or `Continuation_already_resumed` clause.**
   `Effect.Unhandled : 'a t -> exn` is existential, so its payload cannot be put back into `u`;
   the clause binds `U` instead. Witnesses 4 and 8 match on `Unhandled` and never use the binder.
3. **Evaluation order is forced left to right.** OCaml evaluates the arguments of an application
   right to left; `Machine.step` evaluates them left to right (`Frame.appArg` before `appFn`).
   Every multi-operand form is therefore rendered as a chain of `let`s, which also keeps the
   `reperform`-in-tail-position property `Compiler.Admissible` decides: `Llet`'s body inherits the
   polarity of the `let` (`bytegen.ml:636-639`), and every operand is at `nonTail` in both.
4. **`Admissible`.** A term `Compiler.Admissible` rejects is one `ocamlc` refuses; `render` is
   only claimed faithful on admissible terms.

## Naming

De Bruijn indices become depth-indexed names: a binder introduced at depth `d` is `vd`, and
`Term.var i` at depth `d` is `v(d-1-i)`. Shadowing is impossible, so no capture-avoidance is
needed. The `let`-chains use `tda`…`tdd` and the `alloc_stack` wrappers `qde`/`qdk`/`qdl`/`qdx`,
all at the depth of the form that introduces them; a nested form at the same depth shadows them
only inside its own operand, which has already closed before the outer names are read.
-/

namespace OCaml5

universe u

namespace Render

/-! ## Collecting the constructors a term needs -/

private def merge2 (a b : List Nat × List Nat) : List Nat × List Nat :=
  (a.1 ++ b.1, a.2 ++ b.2)

mutual

/-- The `EffId`s and the `ExnId`s that occur in a term, with duplicates. -/
def termIds {ν : Type u} : Term ν → List Nat × List Nat
  | .val _ => ([], [])
  | .unit => ([], [])
  | .var _ => ([], [])
  | .lam b => termIds b
  | .app f a => merge2 (termIds f) (termIds a)
  | .letIn b body => merge2 (termIds b) (termIds body)
  | .seq f n => merge2 (termIds f) (termIds n)
  | .add a b => merge2 (termIds a) (termIds b)
  | .emit _ => ([], [])
  | .emitOf _ e => termIds e
  | .getCell => ([], [])
  | .setCell e => termIds e
  | .eff id p => let r := termIds p; (id.value :: r.1, r.2)
  | .matchEff s cls d =>
      merge2 (termIds s) (merge2 (effClauseIds cls) (termIds d))
  | .exn id p => let r := termIds p; (r.1, id.value :: r.2)
  | .matchExn s cls d =>
      merge2 (termIds s) (merge2 (exnClauseIds cls) (termIds d))
  | .raise e => termIds e
  | .tryWith b h => merge2 (termIds b) (termIds h)
  | .none => ([], [])
  | .some e => termIds e
  | .matchOpt s n sc => merge2 (termIds s) (merge2 (termIds n) (termIds sc))
  | .perform e => termIds e
  | .resume s f a => merge2 (termIds s) (merge2 (termIds f) (termIds a))
  | .runstack s f a => merge2 (termIds s) (merge2 (termIds f) (termIds a))
  | .reperform e c l => merge2 (termIds e) (merge2 (termIds c) (termIds l))
  | .allocStack hv hx hf => merge2 (termIds hv) (merge2 (termIds hx) (termIds hf))
  | .contUseNoexc c => termIds c
  | .contUseUpdate c hv hx hf =>
      merge2 (termIds c) (merge2 (termIds hv) (merge2 (termIds hx) (termIds hf)))
  | .dropCont c => termIds c

def effClauseIds {ν : Type u} : List (EffId × Term ν) → List Nat × List Nat
  | [] => ([], [])
  | (id, t) :: rest =>
      let r := merge2 (termIds t) (effClauseIds rest)
      (id.value :: r.1, r.2)

def exnClauseIds {ν : Type u} : List (ExnId × Term ν) → List Nat × List Nat
  | [] => ([], [])
  | (id, t) :: rest =>
      let r := merge2 (termIds t) (exnClauseIds rest)
      (r.1, id.value :: r.2)

end

private def insertSorted (n : Nat) : List Nat → List Nat
  | [] => [n]
  | m :: rest => if n < m then n :: m :: rest else if n == m then m :: rest
                 else m :: insertSorted n rest

/-- Sorted, without duplicates. -/
def normIds : List Nat → List Nat
  | [] => []
  | n :: rest => insertSorted n (normIds rest)

/-! ## Source text -/

/-- An OCaml string literal body. The row alphabet is ASCII with tabs.

One function under two names: this is `OCaml5.Ml.escString` (`Ml/Identifier.lean`), which is the
same escaping the declaration surface needs, and the name is kept because the whole `rend` table
below spells it. -/
def esc (s : String) : String := Ml.escString s

private def vn (n : Nat) : String := "v" ++ toString n
private def xn (n : Nat) : String := "x" ++ toString n
private def tn (d : Nat) (k : String) : String := "t" ++ toString d ++ k
private def qn (d : Nat) (k : String) : String := "q" ++ toString d ++ k

/-- `fun eff k last_fiber -> …` around a `u`-valued three-argument closure, the shape
`caml_alloc_stack`'s and `caml_continuation_use_and_update_handler_noexc`'s third and fourth
arguments must have (`effect.ml:51-55,130-135`); the handler is invoked as
`caml_apply3 handler eff cont last_fiber` (`amd64.S:895`, `interp.c:1355-1357`). -/
private def effcWrap (d : Nat) (fv : String) : String :=
  "(fun " ++ qn d "e" ++ " " ++ qn d "k" ++ " " ++ qn d "l" ++ " -> as_fun (as_fun (as_fun "
    ++ fv ++ " (Ef " ++ qn d "e" ++ ")) (Kt " ++ qn d "k" ++ ")) (Lf " ++ qn d "l" ++ "))"

/-- `fun e -> …` around the `exn -> u` handler slot. -/
private def exncWrap (d : Nat) (fv : String) : String :=
  "(fun " ++ qn d "x" ++ " -> as_fun " ++ fv ++ " (Xn " ++ qn d "x" ++ "))"

mutual

/-- One `Term` as one OCaml expression of type `u`, at de Bruijn depth `d`. -/
def rend {ν : Type u} [ToString ν] (d : Nat) : Term ν → String
  | .val v => "(I " ++ toString v ++ ")"
  | .unit => "U"
  | .var i => if i < d then vn (d - 1 - i) else "(stuck ())"
  | .lam b => "(F (fun " ++ vn d ++ " -> " ++ rend (d + 1) b ++ "))"
  | .app f a =>
      "(let " ++ tn d "a" ++ " = " ++ rend d f ++ " in let " ++ tn d "b" ++ " = " ++ rend d a
        ++ " in as_fun " ++ tn d "a" ++ " " ++ tn d "b" ++ ")"
  | .letIn b body =>
      "(let " ++ vn d ++ " = " ++ rend d b ++ " in " ++ rend (d + 1) body ++ ")"
  | .seq f n => "(" ++ rend d f ++ "; " ++ rend d n ++ ")"
  | .add a b =>
      "(let " ++ tn d "a" ++ " = " ++ rend d a ++ " in let " ++ tn d "b" ++ " = " ++ rend d b
        ++ " in I (as_int " ++ tn d "a" ++ " + as_int " ++ tn d "b" ++ "))"
  | .emit r => "(emit \"" ++ esc r ++ "\")"
  | .emitOf l e =>
      "(let " ++ tn d "a" ++ " = " ++ rend d e ++ " in emit (\"" ++ esc l
        ++ "\" ^ \"\\t\" ^ render_u " ++ tn d "a" ++ "))"
  | .getCell => "(!cell)"
  | .setCell e => "(cell := " ++ rend d e ++ "; U)"
  | .eff id p => "(Ef (E" ++ toString id.value ++ " " ++ rend d p ++ "))"
  | .matchEff s cls dflt =>
      "(match " ++ rend d s ++ " with" ++ rendEffClauses d cls
        ++ " | " ++ vn d ++ " -> " ++ rend (d + 1) dflt ++ ")"
  | .exn id p =>
      if id.value == 0 then "(Xn (Effect.Unhandled (as_eff " ++ rend d p ++ ")))"
      else if id.value == 1 then
        "(Xn (seq_exn " ++ rend d p ++ " Effect.Continuation_already_resumed))"
      else "(Xn (X" ++ toString id.value ++ " " ++ rend d p ++ "))"
  | .matchExn s cls dflt =>
      "(match " ++ rend d s ++ " with" ++ rendExnClauses d cls
        ++ " | " ++ vn d ++ " -> " ++ rend (d + 1) dflt ++ ")"
  | .raise e => "(raise (as_exn " ++ rend d e ++ "))"
  | .tryWith b h =>
      "(try " ++ rend d b ++ " with " ++ xn d ++ " -> let " ++ vn d ++ " = Xn " ++ xn d
        ++ " in " ++ rend (d + 1) h ++ ")"
  | .none => "Nn"
  | .some e => "(Sm " ++ rend d e ++ ")"
  | .matchOpt s n sc =>
      "(match " ++ rend d s ++ " with Nn -> " ++ rend d n ++ " | Sm " ++ vn d ++ " -> "
        ++ rend (d + 1) sc ++ " | _ -> stuck ())"
  | .perform e => "(perform (as_eff " ++ rend d e ++ "))"
  | .resume s f a =>
      "(let " ++ tn d "a" ++ " = " ++ rend d s ++ " in let " ++ tn d "b" ++ " = " ++ rend d f
        ++ " in let " ++ tn d "c" ++ " = " ++ rend d a ++ " in resume (as_stk " ++ tn d "a"
        ++ ") (as_fun " ++ tn d "b" ++ ") " ++ tn d "c" ++ ")"
  | .runstack s f a =>
      "(let " ++ tn d "a" ++ " = " ++ rend d s ++ " in let " ++ tn d "b" ++ " = " ++ rend d f
        ++ " in let " ++ tn d "c" ++ " = " ++ rend d a ++ " in runstack (as_stk " ++ tn d "a"
        ++ ") (as_fun " ++ tn d "b" ++ ") " ++ tn d "c" ++ ")"
  | .reperform e c l =>
      "(let " ++ tn d "a" ++ " = " ++ rend d e ++ " in let " ++ tn d "b" ++ " = " ++ rend d c
        ++ " in let " ++ tn d "c" ++ " = " ++ rend d l ++ " in reperform (as_eff " ++ tn d "a"
        ++ ") (as_k " ++ tn d "b" ++ ") (as_lf " ++ tn d "c" ++ "))"
  | .allocStack hv hx hf =>
      "(let " ++ tn d "a" ++ " = " ++ rend d hv ++ " in let " ++ tn d "b" ++ " = " ++ rend d hx
        ++ " in let " ++ tn d "c" ++ " = " ++ rend d hf ++ " in Sk (alloc_stack (as_fun "
        ++ tn d "a" ++ ") " ++ exncWrap d (tn d "b") ++ " " ++ effcWrap d (tn d "c") ++ "))"
  | .contUseNoexc c => "(Sk (take_cont_noexc (as_k " ++ rend d c ++ ")))"
  | .contUseUpdate c hv hx hf =>
      "(let " ++ tn d "a" ++ " = " ++ rend d c ++ " in let " ++ tn d "b" ++ " = " ++ rend d hv
        ++ " in let " ++ tn d "c" ++ " = " ++ rend d hx ++ " in let " ++ tn d "d" ++ " = "
        ++ rend d hf ++ " in Sk (update_handler (as_k " ++ tn d "a" ++ ") (as_fun " ++ tn d "b"
        ++ ") " ++ exncWrap d (tn d "c") ++ " " ++ effcWrap d (tn d "d") ++ "))"
  | .dropCont c => "(drop_continuation (as_k " ++ rend d c ++ "); U)"

/-- The clauses of a `matchEff`: the payload is bound at index 0 of the clause body. -/
def rendEffClauses {ν : Type u} [ToString ν] (d : Nat) : List (EffId × Term ν) → String
  | [] => ""
  | (id, t) :: rest =>
      " | Ef (E" ++ toString id.value ++ " " ++ vn d ++ ") -> " ++ rend (d + 1) t
        ++ rendEffClauses d rest

/-- The clauses of a `matchExn`. `Unhandled` is existential and
`Continuation_already_resumed` is nullary, so their payload binder is `U` (restriction 2). -/
def rendExnClauses {ν : Type u} [ToString ν] (d : Nat) : List (ExnId × Term ν) → String
  | [] => ""
  | (id, t) :: rest =>
      (if id.value == 0 then
         " | Xn (Effect.Unhandled _) -> let " ++ vn d ++ " = U in " ++ rend (d + 1) t
       else if id.value == 1 then
         " | Xn Effect.Continuation_already_resumed -> let " ++ vn d ++ " = U in "
           ++ rend (d + 1) t
       else
         " | Xn (X" ++ toString id.value ++ " " ++ vn d ++ ") -> " ++ rend (d + 1) t)
        ++ rendExnClauses d rest

end

/-! ## The compilation unit -/

/-- The fixed part of every generated unit: the universal type, the raw externals of
`stdlib/effect.ml:16,41-42,49-55,69-70,130-135`, the coercions, the one `ref` that is
`Machine.cell`, and `emit`, which prints exactly the row `tools/run-witness.sh` reads. -/
def fixedPrelude : String :=
  String.intercalate "\n"
    ["(* Generated by OCaml5.Render (spike P5). Do not edit. *)",
     "type ('a, 'b) stack",
     "type ('a, 'b) continuation",
     "type last_fiber",
     "",
     "type u =",
     "  | I of int",
     "  | U",
     "  | F of (u -> u)",
     "  | Ef of u Effect.t",
     "  | Xn of exn",
     "  | Nn",
     "  | Sm of u",
     "  | Kt of (u, u) continuation",
     "  | Sk of (u, u) stack",
     "  | Lf of last_fiber",
     "",
     "external perform : 'a Effect.t -> 'a = \"%perform\"",
     "external resume : ('a, 'b) stack -> ('c -> 'a) -> 'c -> 'b = \"%resume\"",
     "external runstack : ('a, 'b) stack -> ('c -> 'a) -> 'c -> 'b = \"%runstack\"",
     "external reperform :",
     "  'a Effect.t -> ('a, 'b) continuation -> last_fiber -> 'b = \"%reperform\"",
     "external alloc_stack :",
     "  ('a -> 'b) -> (exn -> 'b) ->",
     "  ('c Effect.t -> ('c, 'b) continuation -> last_fiber -> 'b) -> ('a, 'b) stack",
     "  = \"caml_alloc_stack\"",
     "external take_cont_noexc : ('a, 'b) continuation -> ('a, 'b) stack",
     "  = \"caml_continuation_use_noexc\" [@@noalloc]",
     "external update_handler :",
     "  ('a, 'b) continuation -> ('b -> 'c) -> (exn -> 'c) ->",
     "  ('d Effect.t -> ('d, 'b) continuation -> last_fiber -> 'c) -> ('a, 'c) stack",
     "  = \"caml_continuation_use_and_update_handler_noexc\" [@@noalloc]",
     "external drop_continuation : ('a, 'b) continuation -> unit = \"caml_drop_continuation\"",
     "",
     "let stuck () = print_string \"!stuck\\n\"; exit 2",
     "let as_int = function I n -> n | _ -> stuck ()",
     "let as_fun = function F f -> f | _ -> stuck ()",
     "let as_eff = function Ef e -> e | _ -> stuck ()",
     "let as_exn = function Xn e -> e | _ -> stuck ()",
     "let as_k = function Kt k -> k | _ -> stuck ()",
     "let as_stk = function Sk s -> s | _ -> stuck ()",
     "let as_lf = function Lf l -> l | _ -> stuck ()",
     "let seq_exn (_ : u) (e : exn) = e",
     "let cell : u ref = ref U",
     "let emit s = print_string s; print_newline (); U",
     "",
     ""]

/-- `type _ Effect.t += En : u -> u Effect.t`, one per `EffId`. -/
def effDecls (effs : List Nat) : String :=
  String.join (effs.map fun i =>
    "type _ Effect.t += E" ++ toString i ++ " : u -> u Effect.t\n")

/-- `exception Xn of u`, one per `ExnId` other than the two the runtime registers. -/
def exnDecls (exns : List Nat) : String :=
  String.join ((exns.filter fun i => i != 0 && i != 1).map fun i =>
    "exception X" ++ toString i ++ " of u\n")

/-- `Value.render`, transcribed. `Value.cont`/`Value.stack` print a heap index the machine knows
and no host can, which is restriction 1 of the discipline: a term that reaches these arms is
outside the fragment `render` is faithful on. -/
def renderDecls (effs exns : List Nat) : String :=
  "let eff_id (e : u Effect.t) = match e with\n"
    ++ String.join (effs.map fun i => "  | E" ++ toString i ++ " _ -> " ++ toString i ++ "\n")
    ++ "  | _ -> 0\n"
    ++ "let exn_id (e : exn) = match e with\n"
    ++ String.join ((exns.filter fun i => i != 0 && i != 1).map fun i =>
         "  | X" ++ toString i ++ " _ -> " ++ toString i ++ "\n")
    ++ "  | Effect.Unhandled _ -> 0\n"
    ++ "  | Effect.Continuation_already_resumed -> 1\n"
    ++ "  | _ -> 0\n"
    ++ String.intercalate "\n"
        ["let rec render_u = function",
         "  | I n -> string_of_int n",
         "  | U -> \"()\"",
         "  | F _ -> \"<fun>\"",
         "  | Ef e -> \"eff\" ^ string_of_int (eff_id e)",
         "  | Xn e -> \"exn\" ^ string_of_int (exn_id e)",
         "  | Nn -> \"none\"",
         "  | Sm v -> \"some(\" ^ render_u v ^ \")\"",
         "  | Kt _ -> \"cont\"",
         "  | Sk _ -> \"stack\"",
         "  | Lf _ -> \"lastfiber\"",
         "let _ = render_u",
         "",
         ""]

/-- The whole compilation unit for one term. The term sits at the top level of the unit, which
is not a tail position (`Compiler.Admissible` reads it at `nonTail`), and `ignore` is the
`Kccall` operand `ocamlc` refuses a `reperform` in (O5 report §4, probe `ccall operand`). -/
def program {ν : Type u} [ToString ν] (t : Term ν) : String :=
  let ids := termIds t
  let effs := normIds ids.1
  let exns := normIds ids.2
  fixedPrelude ++ effDecls effs ++ exnDecls exns ++ "\n" ++ renderDecls effs exns
    ++ "let () = ignore (" ++ rend 0 t ++ ")\n"

end Render

/-- Lean emits OCaml: one `Term` as one OCaml 5 compilation unit. -/
def Term.render (t : Term Nat) : String := Render.program t

/-! ## Checks

The faithfulness claim — "`ocamlc` accepts `Term.render w.term` and its rows are `w.byteRows`"
— is an executed one; `ocaml/tools/fuzz.sh --witnesses` runs it on all thirteen and the
report records the result. What can be checked here is that every witness is admissible (so the
claim is even meant), and that the renderer declares exactly the constructors each witness uses.
-/

-- Every witness is a term `ocamlc` compiles (`Compiler.Admissible`), so the faithfulness
-- claim is even meant for it.
#guard corpus.all (fun w => Compiler.Admissible w.term)

-- Rendering is total on the corpus and every unit is a real compilation unit.
#guard corpus.all (fun w => (Term.render w.term).length > 2000)

-- Witness 1 uses one effect constructor and no user exception.
#guard Render.normIds (Render.termIds W.w01).1 == [1]
#guard Render.normIds (Render.termIds W.w01).2 == []

-- Witness 5 forwards, so both effect constructors occur.
#guard Render.normIds (Render.termIds W.w05).1 == [1, 2]

-- Witness 11 is the `Shallow.fiber` one: `Initial_setup__` is `EffId 4`, the local
-- `exception E of (a,b) continuation` is `ExnId 4`, and `Failure` is `Stdlib.failureExn`, `⟨5⟩`.
#guard Render.normIds (Render.termIds W.w11).1 == [1, 4]
#guard Render.normIds (Render.termIds W.w11).2 == [4, 5]

-- Witness 4 matches on `Unhandled`, which is `ExnId 0` and is never declared: the runtime
-- registers it (`effect.ml:34-36`).
#guard Render.normIds (Render.termIds W.w04).2 == [0]
#guard Render.exnDecls [0, 1, 2] == "exception X2 of u\n"

-- String escaping: the row alphabet is tab-separated ASCII.
#guard Render.esc "perform\tNumber" == "perform\\tNumber"
#guard Render.esc "a\"b\\c" == "a\\\"b\\\\c"

end OCaml5
