import OCaml5.Effect
import OCaml5.Compiler
import OCaml5.Witnesses
import OCaml5.Ml.Identifier
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Reflect
import OCaml5.Ml.Check
import OCaml5.Ml.Passes

/-!
# OCaml 5 spike: `Term` → OCaml 5 source

Status: spike P5, 2026-09-03. Module `OCaml5.Render`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, row P5. Report:
`docs/research/2026-09-03-spike-p5-fuzz.md`.

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
— is an executed one; `workshop/OCaml5/tools/fuzz.sh --witnesses` runs it on all thirteen and the
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

/-!
# The general Lean → OCaml declaration surface: where it now lives

Status: spike P5 part 2 (2026-09-04), refactored into a package-shaped API by seat W3
(`docs/research/2026-09-04-seat-w3-ml-api.md`).

`Term.render` above emits one expression over the raw effect primitives, which is what a
reference machine needs and not what a program needs. The rest of the surface — declarations,
and the descriptions that generate them — is **no longer in this file**. It is six modules under
`workshop/OCaml5/Ml/`, shaped like the estate's TypeScript target package
(`.lake/packages/typescript/TypeScript/{Syntax,Render,Identifier,HostPin,Structure}.lean`) so
that it can be lifted out as a sibling package `lean4-ocaml` without being rewritten:

| module | what it owns |
| --- | --- |
| `OCaml5.Ml.Identifier` | reserved words, the identifier profile, `escString`, the total injective `mangleField` and its exhibited left inverse |
| `OCaml5.Ml.Syntax` | the OCaml surface as first-order data: `Ty`, `Pat`, `Expr`, `Decl`, `ModTy`, `Module` |
| `OCaml5.Ml.Render` | deterministic rendering with a precedence table: `renderTy`, `renderExpr`, `renderDecl`, `moduleText`, `render : Module → String` |
| `OCaml5.Ml.Reflect` | the description layer: `LTy`, `Subst`, `FieldKind`, `StructDesc`, `InductiveDesc`, `TypeDesc`, `toTypeDecl` |
| `OCaml5.Ml.Check` | well-formedness as decidable predicates with diagnostics |
| `OCaml5.Ml.Passes` | the pure-update → mutation pass and its residue checker |

Every name this file used before the split still resolves to the same thing: the modules are
imported above and every definition kept its name and its namespace (`OCaml5.Ml`). Consumers —
`OCaml5.Fuzz` and `tools/fuzz.sh` — are unchanged.

What remains below is what was always this file's own: the **descriptions and probes**, which are
data about `workshop/Deep/Fibers.lean` and about `workshop/OCaml5/avatar/deep_fibers.ml` rather
than API. `tools/fuzz.sh surface` renders `Ml.Deep.sample` and compiles it; `tools/fuzz.sh
avatar` renders `Ml.Avatar.generated` and diffs it against the hand-written avatar.
-/

namespace OCaml5
namespace Ml

/-! ## The surface itself

`Ty`, `Pat`, `Expr`, `Arm`, `Effc`, `Field`, `Ctor`, `TyBody`, `TypeDecl`, `Bind` and `Decl` are
declared in `OCaml5.Ml.Syntax`, and `renderTy`, `renderPat`, `renderExpr`, `renderDecl` and
`moduleText` in `OCaml5.Ml.Render`. Both are imported above, so every use below is unchanged.

One rendering change came with the split and is visible in the `#guard`s: the renderer carries a
**precedence table** and emits only the parentheses a form needs, where round two parenthesised
every compound form. The table is conservative in one direction — a level that is too low adds a
parenthesis and can never change a parse — and the executed checks (`fuzz.sh surface`,
`fuzz.sh avatar`, `tools/ml-check.sh`) are what say the output is still OCaml. -/

/-! ## The Deep-shaped probe

A slice of `workshop/Deep/Fibers.lean` written out in this surface, one `Ml` value per Lean
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

Executed check: `tools/fuzz.sh surface` renders `deepSample`, compiles it with `ocamlc`,
`ocamlopt` and `js_of_ocaml`, and runs it on all three. -/

namespace Deep

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

/-- The rows the probe prints, checked by `tools/fuzz.sh surface`. -/
def sampleRows : List String := ["waiting", "2"]

end Deep

/-! ### Checks

`ocamlc` acceptance is executed (`tools/fuzz.sh surface`), so what is pinned here is the text: if
one of these strings changes, the module that was compiled is no longer the module this file
renders. -/

#guard renderTy (Ty.cont (.var "a") Ty.int) == "('a, int) Effect.Deep.continuation"
-- The renderer now emits only the parentheses the form needs: an arrow at the top level
-- of a type has none, and one in the domain of another arrow has them.
#guard renderTy (.arrow Ty.unit (Ty.list (.con "bucket" [.var "b"]))) == "unit -> 'b bucket list"
#guard renderTy (.con "pending" [.var "nu", .var "b"]) == "('nu, 'b) pending"

#guard renderDecl Deep.fiberIdDecl == "type fiber_id = int"

#guard renderDecl Deep.parkedDecl == "type parked = NotParked | WithGuard of int"

#guard renderDecl Deep.stuckDecl == "exception Stuck_unknown_fiber of fiber_id"

#guard renderDecl Deep.effectsDecl ==
  "type _ Effect.t +=\n  | Fork : (unit -> unit) -> fiber_id Effect.t\n"
    ++ "  | Yield : unit Effect.t\n  | Await : fiber_id -> int Effect.t"

-- A record with `mutable` fields, and a mutually recursive `and` group.
#guard renderDecl Deep.runFiberDecl ==
  "type ('nu, 'b) run_fiber = {\n  id : fiber_id;\n  mutable running : bool;\n"
    ++ "  mutable parked : parked;\n  mutable pending : ('nu, 'b) pending list;\n"
    ++ "  mutable exit : 'b option;\n  mutable observers : observer list;\n"
    ++ "  mutable children : fiber_id list;\n  dispatcher : 'b dispatcher;\n}"

#guard ((renderDecl Deep.schedulerDecls).splitOn "\nand ").length == 3

-- `let rec … and …`, a `when` guard, `::`, functional record update and a mutable-field write.
#guard ((renderDecl Deep.enqueueDecl).splitOn "let rec ").length == 2
#guard ((renderDecl Deep.enqueueDecl).splitOn "\n\nand ").length == 2
#guard ((renderDecl Deep.enqueueDecl).splitOn " when ").length == 2
#guard ((renderDecl Deep.enqueueDecl).splitOn " with tasks = ").length == 2
#guard ((renderDecl Deep.enqueueDecl).splitOn "d.buckets <- ").length == 2

-- The `effc` table: a locally abstract type, one clause per constructor, a `None` default.
#guard ((renderDecl Deep.runDecl).splitOn "(fun (type a) (eff : a Effect.t) ->").length == 2
#guard ((renderDecl Deep.runDecl).splitOn "(k : (a, int) Effect.Deep.continuation)").length == 4
#guard ((renderDecl Deep.runDecl).splitOn "| _ -> None)").length == 2
#guard ((renderDecl Deep.runDecl).splitOn "Effect.Deep.discontinue").length == 2

-- The module is one text, and every declaration is in it.
#guard (Ml.moduleText Deep.sample).length > 2000
#guard ((Ml.moduleText Deep.sample).splitOn "type _ Effect.t +=").length == 2

/-!
# Descriptions of Lean declarations, and the avatar's carriers

Round three, 2026-09-04: `docs/research/2026-09-04-spike-a0-avatar.md` §1 asks P5 to *generate*
the avatar's carriers rather than let a human retype them.

The description layer itself — `LTy`, `Subst`, `lowerTy`, `FieldKind`, `FieldDesc`, `StructDesc`,
`CtorArg`, `CtorDesc`, `InductiveDesc`, `TypeDesc`, `toTypeDecl` — and the name mangling —
`mangleField`, `unmangleField`, `typeName`, `ctorName`, `reservedNames` — are in
`OCaml5.Ml.Reflect` and `OCaml5.Ml.Identifier`. What is below is the **descriptions**: the actual
carriers of `workshop/Deep/Fibers.lean`, and the one substitution table the avatar is read
against.

The division of labour is the point. The renderer owns everything mechanical: order, arity,
mutability, layout, and the names. The substitution table owns the one thing a renderer cannot
decide — which OCaml type stands for a Lean type the avatar does not transcribe (`Exit β ε δ ι α`
is `exitv`, `χ` is `unit`, `Prim` in an answer position is `answer`). That table is one visible
list per module, not a decision scattered through 900 lines of hand-written OCaml.
-/

/-! ## The avatar's carriers, described

`workshop/OCaml5/avatar/deep_fibers.ml` transcribed `workshop/Deep/Fibers.lean` by hand. These
are the descriptions that generate the carriers A0's request 1 and request 2 name, against the
one substitution table below. `tools/fuzz.sh avatar` renders them, compiles the result, and diffs
it against A0's file. -/

namespace Avatar

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

`Effect4/Runtime/Runtime.lean:269`, five fields. `current : Prim …` and `stack : List (Prim …)`
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

/-- `RunEvent` (`Fibers.lean:305`), 22 constructors. Two names are overridden because they
would collide inside one OCaml module: `frame` with the `frame_fiber` field and `callback` with
`Observer.callback`. Two arguments are erased, both of them A0's own omissions, now recorded:
`scopeLinked.mode` and `contextSet.context` (the profile's context is `unit`). -/
def runEvent : InductiveDesc where
  leanName := "RunEvent"
  site := "Fibers.lean:305"
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
       args := [⟨"race", .nat, false⟩, ⟨"host", fid, false⟩, ⟨"entrants", .lst fid, false⟩] },
     { leanName := "raceLaunched", args := [⟨"race", .nat, false⟩, ⟨"entrant", fid, false⟩] },
     { leanName := "raceSkipped", args := [⟨"race", .nat, false⟩, ⟨"entrant", fid, false⟩] },
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

/-- `Cmd` (`Fibers.lean:526`), five constructors, prefix `C`. `loop` is DIVERGENCE 2: the
avatar has no `Cloop` because `continue k` runs the fiber to its next `perform`. It is rendered
here anyway — the request is arity for arity — and the diff against `deep_fibers.ml:326` is the
divergence, stated rather than silently absorbed. -/
def cmd : InductiveDesc where
  leanName := "Cmd"
  site := "Fibers.lean:526"
  ctorPrefix := "C"
  subst := subst
  ctors :=
    [{ leanName := "evaluate", args := [⟨"fiber", fid, false⟩] },
     { leanName := "loop", args := [⟨"fiber", fid, false⟩, ⟨"yielding", .bool, false⟩],
       comment := Option.some "DIVERGENCE 2: absent from deep_fibers.ml" },
     { leanName := "resume",
       args := [⟨"fiber", fid, false⟩, ⟨"token", .nat, false⟩, ⟨"answer", primL, false⟩] },
     { leanName := "launch", args := [⟨"race", .nat, false⟩, ⟨"entrant", fid, false⟩] },
     { leanName := "drainDue" }]

/-- `WithFiberAction` (`Fibers.lean:258`), 17 constructors, prefix `W`. Every `Prim` argument is
an *action's program*, not an answer, so each is a hole: `Prim` is never rendered (request 5),
and the avatar reaches these shapes through its own `Effect.t` constructors
(`deep_fibers.ml:345-354`) with the program left to the hand-written handler. -/
def withFiberAction : InductiveDesc where
  leanName := "WithFiberAction"
  site := "Fibers.lean:258"
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
     { leanName := "snapshotChildren" },
     { leanName := "awaitNewChildren", args := [⟨"snapshot", .lst fid, false⟩] },
     { leanName := "raceAll", args := [⟨"entrants", .lst primL, true⟩] },
     { leanName := "setInterruptible",
       args := [⟨"body", primL, true⟩, ⟨"flag", .bool, false⟩] },
     { leanName := "setContext", args := [⟨"context", .nm "χ", false⟩] },
     { leanName := "getContext" },
     { leanName := "getId" },
     { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "refuse", args := [⟨"cause", .app "Cause" [.nm "ε"], false⟩] }]

def inductives : List InductiveDesc := [observer, runEvent, runDecision, cmd, withFiberAction]

end Avatar

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

namespace Avatar

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

end Avatar

/-! ### The compile check

`Avatar.generated` is a fragment: it names `exitv`, `cause`, `task` and the rest without
declaring them, because the avatar declares them. `checkModule` closes it — the supporting
carriers `deep_fibers.ml` spells above the generated ones, and the four helpers
`interrupt_record` calls, `frame_fail` among them, which is the hand-written filling of the hole
the renderer left. `tools/fuzz.sh avatar` compiles it on all three hosts. -/

namespace Avatar

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

end Avatar
namespace Avatar

/-- The generated part of the avatar: the carriers of requests 1, 2 and 5, and the functions of
request 3. `tools/fuzz.sh avatar` renders this, compiles it against a small hand-written
preamble, and diffs each carrier against `deep_fibers.ml`. -/
def generated : List Decl := generatedTypes ++ generatedFns

end Avatar

/-! ### Checks: names, order, arity, holes

The rendered text is checked against `deep_fibers.ml` itself by `tools/fuzz.sh avatar`, which
diffs the real file rather than a copy of it. What is pinned here is everything that must hold
for that diff to be meaningful. -/

-- The mangling is injective: `unmangleField` is a left inverse, on every field name rendered
-- here and on a row of adversarial ones.
#guard (Avatar.runFiber.fields.map (·.leanName)).all
  (fun n => unmangleField (mangleField n) == n)
#guard (Avatar.frameFiber.fields.map (·.leanName)).all
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
#guard Avatar.runFiber.fields.length == 17
#guard (Avatar.runFiber.fields.filter (fun f =>
          match f.kind with | .substitute => false | _ => true)).length == 15
#guard Avatar.runFiber.fields.map (·.ocaml) ==
  ["id", "frame", "running", "parked", "pending", "finalizing", "exit_", "current_op_count",
   "max_ops_before_yield", "prevent_yield", "yield_override", "yielding", "race_answer",
   "observers", "children", "dispatcher", "context"]
#guard (Avatar.runFiber.fields.filter (·.isMutable)).length == 15
#guard Avatar.runFiber.substitutes == ["yielding", "race_answer"]

-- Request 5: `FrameFiber`'s `Prim` pair is a hole, and `prim` never reaches the output.
#guard Avatar.frameFiber.holes.map (·.1) == ["current", "stack"]
#guard ((renderDecl Avatar.frameFiber.decl).splitOn "prim").length == 1
#guard ((moduleText Avatar.generated).splitOn "prim").length == 1
-- three holes reach the output: the two `FrameFiber` fields, and `interruptRecord`'s
-- `current := Prim.failure`.
#guard ((moduleText Avatar.generated).splitOn "HOLE").length == 4

-- Request 2: constructor order and arity, per carrier.
#guard Avatar.observer.ctors.length == 6
#guard Avatar.runEvent.ctors.length == 22
#guard Avatar.runDecision.ctors.length == 7
#guard Avatar.cmd.ctors.length == 5
#guard Avatar.withFiberAction.ctors.length == 17

-- Arity for arity, except the erasures, which are named.
#guard Avatar.inductives.all
  (fun d => d.arities.all (fun a => a.2.1 == a.2.2 || (d.erasures.map (·.1)).contains a.1))
#guard Avatar.runEvent.erasures == [("scopeLinked", "mode"), ("contextSet", "context")]
#guard Avatar.observer.erasures == []
#guard Avatar.runDecision.erasures == []
#guard (Avatar.withFiberAction.erasures.map (·.1)) ==
  ["fork", "forkIn", "forkScoped", "raceAll", "setInterruptible"]

-- The names `deep_fibers.ml` actually uses.
#guard Avatar.observer.ctors.map (CtorDesc.ocaml "") ==
  ["ResumeAwait", "UntrackChild", "DropScopeFinalizer", "Countdown", "RaceCallback", "Callback"]
#guard Avatar.runDecision.ctors.map (CtorDesc.ocaml "D") ==
  ["Dfire", "Dflush", "Devaluate", "DyieldVerdict", "DanswerAsync", "DinterruptFrom",
   "DinstallMiddleware"]
#guard (Avatar.runEvent.ctors.map (CtorDesc.ocaml "")).contains "FrameEv"
#guard (Avatar.runEvent.ctors.map (CtorDesc.ocaml "")).contains "CallbackEv"

-- Request 3: the pass fired on every update in both functions.
#guard (residue (mutate ["f"] Avatar.parkPure)).isEmpty
#guard (residue (mutate ["f"] Avatar.interruptRecordPure)).isEmpty
-- …and it had something to fire on: the unrewritten forms do have residue.
#guard (residue Avatar.parkPure).length == 2
#guard (residue Avatar.interruptRecordPure).length == 6
-- The rewrite produced mutations, including one through the nested `frame` update.
#guard ((renderDecl Avatar.parkDecl).splitOn " <- ").length == 3
#guard ((renderDecl Avatar.interruptRecordDecl).splitOn "f.frame.interrupted_cause <- ").length
  == 2
#guard ((renderDecl Avatar.interruptRecordDecl).splitOn "f.frame.deferred_interrupt <- ").length
  == 2

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

namespace Avatar

/-- The types a tape module needs, and nothing else. -/
def tapePreamble : List Decl :=
  [.comment "Hand-written: the value alphabet a tape's answers are drawn from.",
   .rawD "type value = Vunit | Vnat of int",
   .rawD "type reason = Rfail of int | Rdie of string | Rinterrupt of int option",
   .rawD "type cause = { reasons : reason list; annotations : string list }",
   .rawD "type answer = Aval of value | Acause of cause",
   .rawD "let cause_fail e = { reasons = [ Rfail e ]; annotations = [] }"]

/-- A tape module: the alphabet, the generated `run_decision`, and the tapes as OCaml literals.
`tools/fuzz.sh tapes` compiles it on all three hosts, which is what makes "every generated tape
is a well-typed `run_decision list`" a fact rather than a claim. -/
def tapeModule (tapes : List (List Expr)) : List Decl :=
  tapePreamble ++ [runDecision.header, runDecision.decl] ++
  [.comment s!"{tapes.length} generated tapes.",
   .letD false
     [{ name := "tapes", result := Option.some (Ty.list (Ty.list (Ty.named "run_decision"))),
        body := .listLit (tapes.map (fun t => .listLit t)) }]]

end Avatar

end Ml
end OCaml5

/-! ================================================================================
# SEAT W1 — the remaining `Effect4/Deep` carriers (additive only)

Everything below this banner was added by seat W1 (`docs/research/2026-09-04-seat-w1-deep-port.md`)
and nothing above it was touched, so that seat W3's refactor of `OCaml5.Ml` can re-export the
names this section uses without merging into it.

The avatar is one OCaml module per `Effect4/Deep` module, same declaration order, same names and
field order for every carrier. `Ml.Avatar` describes `Fibers.lean`'s carriers; the namespaces
below describe the carriers of the other five modules, so that `deep_stores.ml`,
`deep_context.ml`, `deep_layer.ml`, `deep_forkflow.ml` and `deep_witnesses.ml` are *generated*
where they are data and hand-written only where they are code.

Rendered by `workshop/OCaml5/avatar/render-deep.lean` (a `lake env lean --run` driver that lives
in the scratchpad, not in the repository), diffed against the avatar files the way
`tools/fuzz.sh avatar` diffs `deep_fibers.ml`.
================================================================================ -/

namespace OCaml5
namespace Ml

/-- `typeName` with `mangleField`'s keyword escape. `Ml.typeName` does not apply it because no
`Fibers.lean` carrier needed it; `Stores.lean`'s `Val` and `Layer.lean`'s `St` do — `val` is an
OCaml keyword. The rule is the file's own: `exit` → `exit_`, so `Val` → `val_`. -/
def typeName' (s : String) : String :=
  let e := typeName s
  if reservedNames.contains e then e ++ "_" else e

/-- Rename the single type a `StructDesc.decl`/`InductiveDesc.decl` produces. Additive: the two
description structures are not changed, so seat W3's refactor sees them as they were. -/
def renameDecl (n : String) : Decl → Decl
  | .types [td] => .types [{ td with name := n }]
  | d => d

namespace Deep

/-! ## `Effect4/Deep/Stores.lean` → `workshop/OCaml5/avatar/deep_stores.ml` -/

namespace Stores

/-- The substitution table for `deep_stores.ml`. Ten entries are decisions, not derivations, and
each is a row of the report's divergence table:

* `Val` is **substituted** by the avatar's wire alphabet `value` (`deep_fibers.ml:64`). The two
  alphabets are different — `Val.fiber`/`.cell`/`.promise`/`.scopeHandle` are one `Vhandle`
  under the wire's first-seen handle counter, and `Val.exitNil`/`.exitCons` are one `Vlist` —
  so the map is in the report and not here;
* `Prim ν σ β ε δ ι α` is `program`, i.e. `unit -> value`: DIVERGENCE 1, a program is OCaml
  control and not a tree;
* `Exit β ε δ ι α` and `Exit Unit ε δ ι α` are both `exitv` (`deep_fibers.ml:96`), whose value
  half is the wire alphabet by the `Val` row above;
* `Cause`/`Reason`/`ReasonAnnotations` are the avatar's (`:76-77`);
* `χ` is `unit`: the avatar carries no context service (A0 §18);
* `FiberId` is `int`. -/
def subst : Subst :=
  [("FiberId", Ty.int),
   ("RefKey", Ty.named "ref_key"),
   ("DeferredKey", Ty.named "deferred_key"),
   ("Err", Ty.named "err"),
   ("Defect", Ty.named "defect"),
   ("Ann", Ty.unit),
   ("FnName", Ty.named "fn_name"),
   ("FinName", Ty.named "fin_name"),
   ("Ctx", Ty.named "ctx"),
   ("Val", Ty.named "value"),
   ("Completion", Ty.named "completion"),
   ("SyncOp", Ty.named "sync_op"),
   ("RaceName", Ty.named "race_name"),
   ("ProgName", Ty.named "prog_name"),
   ("Name", Ty.named "name"),
   ("ActionName", Ty.named "action_name"),
   ("Thunk", Ty.named "thunk"),
   ("Program", Ty.named "program"),
   ("Prim", Ty.named "program"),
   ("RefHeap", Ty.list (Ty.named "value")),
   ("DeferredCell", Ty.named "deferred_cell"),
   ("DeferredStore", Ty.named "deferred_store"),
   ("ScopeEntry", Ty.named "scope_entry"),
   ("ScopeStore", Ty.named "scope_store"),
   ("ScopeV", Ty.named "scope"),
   ("Scope", Ty.named "scope"),
   ("ScopeState", Ty.named "scope_state"),
   ("FinalizerStrategy", Ty.named "finalizer_strategy"),
   ("Exit", Ty.named "exitv"),
   ("ExitV", Ty.named "exitv"),
   ("VoidExitV", Ty.named "exitv"),
   ("Cause", Ty.named "cause"),
   ("CauseV", Ty.named "cause"),
   ("Reason", Ty.named "reason"),
   ("ReasonAnnotations", Ty.list Ty.string),
   ("ParkKind", Ty.named "park_kind"),
   ("Supervision.ObserverMode", Ty.named "observer_mode"),
   ("Supervision.ForkOptions", Ty.named "fork_options"),
   ("Supervision.ScopeMode", Ty.int),
   ("χ", Ty.unit)]

private def fid : LTy := .nm "FiberId"
private def exitL : LTy := .nm "ExitV"
private def voidExitL : LTy := .nm "VoidExitV"
private def causeL : LTy := .nm "CauseV"
private def valL : LTy := .nm "Val"

/-- `RefKey` (`Stores.lean:56`). -/
def refKey : StructDesc where
  leanName := "RefKey"; site := "Stores.lean:56"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]

/-- `DeferredKey` (`Stores.lean:62`). -/
def deferredKey : StructDesc where
  leanName := "DeferredKey"; site := "Stores.lean:62"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]

/-- `Err` (`Stores.lean:73`), prefix `E`. -/
def err : InductiveDesc where
  leanName := "Err"; site := "Stores.lean:73"; ctorPrefix := "E"; subst := subst
  ctors := [{ leanName := "boom" }, { leanName := "tag", args := [⟨"code", .nat, false⟩] }]

/-- `Defect` (`Stores.lean:81`), prefix `X`. Five constructors since finding S1-1 (2026-09-04):
`missingService` is `Context.get` on a missing service (`forkScoped` with no ambient `Scope`,
`internal/effect.ts:5400-5406`) and `user n` is `Effect.die(d)` with a numeric payload. Seat F2. -/
def defect : InductiveDesc where
  leanName := "Defect"; site := "Stores.lean:81"; ctorPrefix := "X"; subst := subst
  ctors := [{ leanName := "notImplemented" }, { leanName := "asyncFiber" },
            { leanName := "badName" }, { leanName := "missingService" },
            { leanName := "user", args := [⟨"payload", .nat, false⟩] }]

/-- `FnName` (`Stores.lean:94`), prefix `Fn`. -/
def fnName : InductiveDesc where
  leanName := "FnName"; site := "Stores.lean:94"; ctorPrefix := "Fn"; subst := subst
  ctors := [{ leanName := "incr" }, { leanName := "double" }, { leanName := "zeroWhenPositive" },
            { leanName := "noChange" }, { leanName := "takeAndBump" }]

/-- `FinName` (`Stores.lean:110`), prefix `Fin`. -/
def finName : InductiveDesc where
  leanName := "FinName"; site := "Stores.lean:110"; ctorPrefix := "Fin"; subst := subst
  ctors :=
    [{ leanName := "interruptFiber", args := [⟨"fiber", fid, false⟩, ⟨"skipSelf", .bool, false⟩] },
     { leanName := "closeChildScope", args := [⟨"scope", .nat, false⟩] },
     { leanName := "detachFromParent", args := [⟨"parent", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "release", args := [⟨"label", .nat, false⟩, ⟨"fails", .bool, false⟩] },
     -- `57924eb` (seat F2): `awaitAllChildren`'s finalizer (`:5319-5333`, R2-7)
     { leanName := "awaitNewChildren", args := [⟨"snapshot", .lst fid, false⟩] },
     { leanName := "parkThen", args := [⟨"slot", .nat, false⟩] }]

/-- `Ctx` (`Stores.lean:130`). -/
def ctx : StructDesc where
  leanName := "Ctx"; site := "Stores.lean:130"; subst := subst
  fields :=
    [{ leanName := "ambientScope", leanTy := .opt .nat },
     { leanName := "maxOpsBeforeYield", leanTy := .nat },
     { leanName := "preventYield", leanTy := .bool }]

/-- `Completion` (`Stores.lean:184`), prefix `Co`. -/
def completion : InductiveDesc where
  leanName := "Completion"; site := "Stores.lean:184"; ctorPrefix := "Co"; subst := subst
  ctors := [{ leanName := "ofExit", args := [⟨"exit", exitL, false⟩] },
            { leanName := "ofRefGet", args := [⟨"cell", .nm "RefKey", false⟩] }]

/-- `SyncOp` (`Stores.lean:193`), 23 constructors, prefix `S`. -/
def syncOp : InductiveDesc where
  leanName := "SyncOp"; site := "Stores.lean:193"; ctorPrefix := "S"; subst := subst
  ctors :=
    [{ leanName := "refMake", args := [⟨"initial", valL, false⟩] },
     { leanName := "refGet", args := [⟨"cell", .nm "RefKey", false⟩] },
     { leanName := "refSet", args := [⟨"cell", .nm "RefKey", false⟩, ⟨"value", valL, false⟩] },
     { leanName := "refGetAndSet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"value", valL, false⟩] },
     { leanName := "refSetAndGet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"value", valL, false⟩] },
     { leanName := "refUpdate",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refGetAndUpdate",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refUpdateAndGet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refUpdateSome",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "refGetAndUpdateSome",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "refUpdateSomeAndGet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "refModify",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refModifySome",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "deferredMake" },
     { leanName := "deferredIsDone", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "deferredPoll", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "deferredCompleteWith",
       args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"completion", .nm "Completion", false⟩] },
     { leanName := "deferredInterruptWith",
       args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"interruptor", fid, false⟩] },
     { leanName := "deferredAwaitCleanup",
       args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"waiter", fid, false⟩,
                ⟨"token", .nat, false⟩] },
     { leanName := "scopeMake", args := [⟨"strategy", .nm "FinalizerStrategy", false⟩] },
     { leanName := "scopeAdd",
       args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩,
                ⟨"finalizer", .nm "FinName", false⟩] },
     { leanName := "scopeRemove", args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "scopeIsClosed", args := [⟨"scope", .nat, false⟩] }]

/-- `RaceName` (`Stores.lean:248`), prefix `Rn`; six since `2f77f7d` (`parkOnly`,
`parkThenSuccess`: R2-12/R2-13's witnesses). Seat F2. -/
def raceName : InductiveDesc where
  leanName := "RaceName"; site := "Stores.lean:248"; ctorPrefix := "Rn"; subst := subst
  ctors := [{ leanName := "empty" }, { leanName := "successThenSecond" },
            { leanName := "failThenSuccess" }, { leanName := "failThenFail" },
            { leanName := "parkOnly" }, { leanName := "parkThenSuccess" }]

/-- `ProgName` (`Stores.lean:265`), 22 constructors, prefix `P`. -/
def progName : InductiveDesc where
  leanName := "ProgName"; site := "Stores.lean:265"; ctorPrefix := "P"; subst := subst
  ctors :=
    [{ leanName := "value", args := [⟨"v", valL, false⟩] },
     { leanName := "failCause", args := [⟨"cause", causeL, false⟩] },
     { leanName := "syncOp", args := [⟨"op", .nm "SyncOp", false⟩] },
     { leanName := "yieldNow", args := [⟨"priority", .nat, false⟩] },
     { leanName := "park", args := [⟨"slot", .nat, false⟩] },
     { leanName := "awaitDeferred", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "intoDeferred",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "intoBody",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "maskedPark", args := [⟨"slot", .nat, false⟩] },
     { leanName := "awaitFibers", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "finalizerOf",
       args := [⟨"fin", .nm "FinName", false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "interruptDeferred", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "onExitOf",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"fin", .nm "FinName", false⟩,
                ⟨"finalizerInterruptible", .bool, false⟩] },
     { leanName := "seqOf",
       args := [⟨"first", .nm "ProgName", false⟩, ⟨"second", .nm "ProgName", false⟩] },
     { leanName := "forkThen",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"mode", .nm "Supervision.ObserverMode", false⟩] },
     { leanName := "forkOnly",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
     { leanName := "forkInScope",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "runInScope",
       args := [⟨"target", fid, false⟩, ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "forkScopedOf",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "raceOf", args := [⟨"race", .nm "RaceName", false⟩] },
     { leanName := "closeScopeOf", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "awaitAllNew", args := [⟨"body", .nm "ProgName", false⟩] },
     -- `2f77f7d` (seat F2): the settle's cleanup half and a join on an existing handle
     { leanName := "interruptFibers", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "joinFiber",
       args := [⟨"target", fid, false⟩, ⟨"mode", .nm "Supervision.ObserverMode", false⟩] }]

/-- `Name` (`Stores.lean:321`), 20 constructors, prefix `N`. -/
def name : InductiveDesc where
  leanName := "Name"; site := "Stores.lean:321"; ctorPrefix := "N"; subst := subst
  ctors :=
    [{ leanName := "restore", args := [⟨"exit", exitL, false⟩] },
     { leanName := "merge", args := [⟨"exit", exitL, false⟩] },
     { leanName := "seq", args := [⟨"next", .nm "ProgName", false⟩] },
     { leanName := "joinOn", args := [⟨"mode", .nm "Supervision.ObserverMode", false⟩] },
     { leanName := "interruptWith", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "doneInto", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "constant", args := [⟨"value", valL, false⟩] },
     { leanName := "exitOfValue" },
     -- `Name.awaitNew` retired in `57924eb` (R2-7): the await is `FinName.awaitNewChildren`
     { leanName := "snapshotThen", args := [⟨"body", .nm "ProgName", false⟩] },
     { leanName := "registerAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "cancelAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "externalRegister", args := [⟨"slot", .nat, false⟩] },
     { leanName := "abortController" },
     -- `2f77f7d` (seat F2): `RunInterp.parkCancelName` and `raceCancelName` (R2-3, R2-13)
     { leanName := "cancelPark" },
     { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] },
     { leanName := "withWaiter",
       args := [⟨"base", .nm "Name", false⟩, ⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] },
     { leanName := "reFail", args := [⟨"cause", causeL, false⟩] },
     { leanName := "finalizerName", args := [⟨"fin", .nm "FinName", false⟩] },
     { leanName := "closeSeq",
       args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩,
                ⟨"captured", .lst (.nm "Reason"), false⟩] },
     { leanName := "closePar",
       args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩,
                ⟨"forked", .lst fid, false⟩, ⟨"closerInterruptible", .bool, false⟩] },
     { leanName := "mergeAwaitedExits" }]

/-- `ActionName` (`Stores.lean:377`), 17 constructors, prefix `A`. Arm for arm with
`Fibers.lean`'s `WithFiberAction` (`Ml.Avatar.withFiberAction`), except that every `Prim`
argument is a `ProgName` here — which is the whole point of the name alphabet. -/
def actionName : InductiveDesc where
  leanName := "ActionName"; site := "Stores.lean:377"; ctorPrefix := "A"; subst := subst
  ctors :=
    [{ leanName := "fork",
       args := [⟨"program", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
     { leanName := "forkIn",
       args := [⟨"program", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "forkScoped",
       args := [⟨"program", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "runIn",
       args := [⟨"target", fid, false⟩, ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "interrupt", args := [⟨"target", fid, false⟩] },
     { leanName := "interruptScoped", args := [⟨"target", fid, false⟩] },
     { leanName := "interruptAll",
       args := [⟨"targets", .lst fid, false⟩, ⟨"interruptor", .opt fid, false⟩] },
     { leanName := "awaitAll", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "snapshotChildren" },
     { leanName := "awaitNewChildren", args := [⟨"snapshot", .lst fid, false⟩] },
     { leanName := "raceAll", args := [⟨"race", .nm "RaceName", false⟩] },
     { leanName := "setContext", args := [⟨"context", .nm "Ctx", false⟩] },
     { leanName := "getContext" },
     { leanName := "getId" },
     { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "setInterruptible",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"flag", .bool, false⟩] },
     { leanName := "refuse", args := [⟨"cause", causeL, false⟩] },
     -- `2f77f7d` (seat F2): the two park cleanups (R2-3, R2-13)
     { leanName := "dropObservers", args := [⟨"token", .nat, false⟩] },
     { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] }]

/-- `Thunk` (`Stores.lean:403`), prefix `T`. -/
def thunk : InductiveDesc where
  leanName := "Thunk"; site := "Stores.lean:403"; ctorPrefix := "T"; subst := subst
  ctors :=
    [{ leanName := "park", args := [⟨"kind", .nm "ParkKind", false⟩] },
     { leanName := "act", args := [⟨"action", .nm "ActionName", false⟩] },
     { leanName := "op", args := [⟨"operation", .nm "SyncOp", false⟩] },
     { leanName := "body", args := [⟨"program", .nm "ProgName", false⟩] }]

/-! ### `Effect4/Runtime/Scope.lean`

`ScopeStore` is keyed `Effect4.Scope`s, "reused unchanged" (`Stores.lean:850`). There is no
OCaml module for `Effect4/Runtime` in this pass — the seat's frame is one module per
`Effect4/Deep` module — so the two carriers the store needs are described here and rendered into
`deep_stores.ml` under their own banner, with their Lean site named. -/

/-- `FinalizerStrategy` (`Scope.lean:39`), prefix `Fs`. -/
def finalizerStrategy : InductiveDesc where
  leanName := "FinalizerStrategy"; site := "Scope.lean:39"; ctorPrefix := "Fs"; subst := subst
  ctors := [{ leanName := "sequential" }, { leanName := "parallel" }]

/-- `ScopeState` (`Scope.lean:71`), five states, prefix `Ss`. `κ` is `Nat` and `φ` is `FinName`
at this instantiation (`ScopeV`, `Stores.lean:850`). -/
def scopeState : InductiveDesc where
  leanName := "ScopeState"; site := "Scope.lean:71"; ctorPrefix := "Ss"; subst := subst
  ctors :=
    [{ leanName := "empty" },
     { leanName := "openEmpty" },
     { leanName := "openInline",
       args := [⟨"key", .nat, false⟩, ⟨"finalizer", .nm "FinName", false⟩] },
     { leanName := "openMap",
       args := [⟨"entries", .lst (.nm "ScopeEntryPair"), false⟩] },
     { leanName := "closed", args := [⟨"exit", exitL, false⟩] }]

/-- `Scope` (`Scope.lean:86`). -/
def scope : StructDesc where
  leanName := "Scope"; site := "Scope.lean:86"; subst := subst
  fields :=
    [{ leanName := "strategy", leanTy := .nm "FinalizerStrategy" },
     { leanName := "state", leanTy := .nm "ScopeState", isMutable := true }]

/-! ### The three stores -/

/-- `DeferredCell` (`Stores.lean:653`). Both fields are `mutable`: DIVERGENCE 3, the pure
updates of `DeferredStore.register`/`cancel`/`complete` are in-place writes here. -/
def deferredCell : StructDesc where
  leanName := "DeferredCell"; site := "Stores.lean:653"; subst := subst
  fields :=
    [{ leanName := "completion", leanTy := .opt (.nm "Completion"), isMutable := true,
       comment := Option.some "Lean: `Option Program`; see the report" },
     { leanName := "waiters", leanTy := .lst (.nm "WaiterPair"), isMutable := true }]

/-- `DeferredStore` (`Stores.lean:663`). -/
def deferredStore : StructDesc where
  leanName := "DeferredStore"; site := "Stores.lean:663"; subst := subst
  fields :=
    [{ leanName := "cells", leanTy := .lst (.nm "DeferredCell"), isMutable := true },
     { leanName := "due", leanTy := .lst (.nm "DuePair"), isMutable := true }]

/-- `ScopeEntry` (`Stores.lean:859`). -/
def scopeEntry : StructDesc where
  leanName := "ScopeEntry"; site := "Stores.lean:859"; subst := subst
  fields :=
    [{ leanName := "key", leanTy := .nat },
     { leanName := "scope", leanTy := .nm "ScopeV", isMutable := true }]

/-- `ScopeStore` (`Stores.lean:867`). -/
def scopeStore : StructDesc where
  leanName := "ScopeStore"; site := "Stores.lean:867"; subst := subst
  fields := [{ leanName := "entries", leanTy := .lst (.nm "ScopeEntry"), isMutable := true }]

/-- `Stores` (`Stores.lean:1002`), the `St` of this profile. -/
def stores : StructDesc where
  leanName := "Stores"; site := "Stores.lean:1002"; subst := subst
  fields :=
    [{ leanName := "refs", leanTy := .nm "RefHeap", isMutable := true },
     { leanName := "deferreds", leanTy := .nm "DeferredStore" },
     { leanName := "scopes", leanTy := .nm "ScopeStore" },
     { leanName := "nextName", leanTy := .nat, isMutable := true }]

/-- The tuple aliases the descriptions above name, because `LTy` has no product head: a
`ScopeState.openMap` entry is `Nat × FinName`, a waiter is `FiberId × Nat`, and a due resume is
`FiberId × Nat × Prim`. -/
def tupleAliases : List Decl :=
  [.rawD "type scope_entry_pair = int * fin_name",
   .rawD "type waiter_pair = int * int",
   .rawD "(* `FiberId × Nat × Prim`; the `Prim` is the avatar's `answer` (DIVERGENCE 1). *)",
   .rawD "type due_pair = int * int * answer"]

def structs : List StructDesc :=
  [refKey, deferredKey, ctx, scope, deferredCell, deferredStore, scopeEntry, scopeStore, stores]

def inductives : List InductiveDesc :=
  [err, defect, fnName, finName, completion, syncOp, raceName, progName, name, actionName,
   thunk, finalizerStrategy, scopeState]

/-- The generated carriers of `deep_stores.ml`, in dependency order (which is not the Lean order:
`FinalizerStrategy` and `ScopeState` come from `Scope.lean`, and OCaml needs a type before its
use — P5 §11.7 finding 4). -/
def generatedHead : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions.\n   One declaration per `Effect4/Deep/Stores.lean` carrier, same field"
      ++ " and constructor order."),
   refKey.header, renameDecl "ref_key" refKey.decl,
   deferredKey.header, renameDecl "deferred_key" deferredKey.decl,
   err.header, renameDecl "err" err.decl,
   defect.header, renameDecl "defect" defect.decl,
   fnName.header, renameDecl "fn_name" fnName.decl,
   finName.header, renameDecl "fin_name" finName.decl,
   .comment ("The tuple aliases the descriptions name, because `LTy` has no product head."
      ++ " `answer` is `deep_fibers.ml:131`.")]

/-- The carriers after the tuple aliases. -/
def generatedTail : List Decl :=
  [.comment "`Effect4/Runtime/Scope.lean`: the two carriers `ScopeStore` is made of.",
   finalizerStrategy.header, renameDecl "finalizer_strategy" finalizerStrategy.decl,
   scopeState.header, renameDecl "scope_state" scopeState.decl,
   scope.header, renameDecl "scope" scope.decl,
   ctx.header, renameDecl "ctx" ctx.decl,
   completion.header, renameDecl "completion" completion.decl,
   syncOp.header, renameDecl "sync_op" syncOp.decl,
   raceName.header, renameDecl "race_name" raceName.decl,
   .comment ("`ProgName`, `Name`, `ActionName` and `Thunk` are one mutually recursive group in"
      ++ " OCaml, which Lean does not need because its four are separate inductives over"
      ++ " already-declared types. Order inside the group is the Lean order."),
   progName.header, renameDecl "prog_name" progName.decl,
   name.header, renameDecl "name" name.decl,
   actionName.header, renameDecl "action_name" actionName.decl,
   thunk.header, renameDecl "thunk" thunk.decl,
   .comment "The three stores and the `St` over them.",
   deferredCell.header, renameDecl "deferred_cell" deferredCell.decl,
   deferredStore.header, renameDecl "deferred_store" deferredStore.decl,
   scopeEntry.header, renameDecl "scope_entry" scopeEntry.decl,
   scopeStore.header, renameDecl "scope_store" scopeStore.decl,
   stores.header, renameDecl "stores" stores.decl]

/-- The generated carriers of `deep_stores.ml`: the head, the tuple aliases, the tail. -/
def generated : List Decl := generatedHead ++ tupleAliases ++ generatedTail

end Stores

/-! ## `Effect4/Deep/Layer.lean` → `workshop/OCaml5/avatar/deep_layer.ml` (seat F2)

The collision ruling (F1.4 step 2, taken): Layer's carriers keep the Lean type names inside
their own module (`Deep_layer.sync_op` beside `Deep_stores.sync_op`, as `Effect4.Deep.Layers`
beside `Effect4.Deep`), `deep_layer.ml` does not `open Deep_stores`, and every constructor takes
a Layer prefix (`Lc`/`Lk`/`Ld`/`Lfin`/`Ls`/`Lp`/`Ln`/`La`/`Lt`/`Lu`/`Lx`, `Lss` for the
`ScopeState` copy) so a file opening both modules is unambiguous. The SHIM
`DeferredKey`/`DeferredCell`/`DeferredStore` (`Layer.lean:367-429`) are *substituted* by
`Deep_stores`' (one store, as the landing intends); `ScopeEntry`/`ScopeStore` and the `Scope`/
`ScopeState` they are made of are rendered as Layer's own monomorphic copies over Layer's
`FinName` (`Layer.lean:431-482`; the generator has no type parameters here — a row). `Val`
(`Context.lean:797`) is the wire alphabet `value` (W1-1 again: `memoMap`/`promise`/`scopeHandle`
are one `Vhandle`, `ctxNil`/`ctxCons` the context list, `exitOk`/`exitErr` lost); `Ctx` is
`(service_key * value) list`; `Err` is `Deep_stores.err` (the same two constructors,
`Context.lean:772`); `Ann` is `unit`. -/

/-! ## `Effect4/Deep/Context.lean` → `workshop/OCaml5/avatar/deep_context.ml` (seat F2)

The first-order environment (M4a/M4b) and the machine's value alphabet. `Context`'s `keysNodup`
proof field is ERASED (F2-L2: a proof has no OCaml counterpart; `add`/`mergeEntries` keep the
invariant by construction). `Val` is generated as its own carrier `val_` (prefix `Cv`) so that
`encode`/`decode` and the hooks keep the Lean shape; `Deep_context.wire_of_val` is the projection
onto the avatar's wire alphabet, the W1-1 row. `Requirement` (`Row ServiceKey`) is the strictly
ascending key list; `ServiceProgram`/`UsesOnly`/`interpret` (an `Effects` free program) refuse. -/

namespace Context

def subst : Subst :=
  [("FiberId", Ty.int),
   ("ServiceKey", Ty.named "service_key"),
   ("ServiceName", Ty.int),
   ("ServiceTypeCode", Ty.int),
   ("Err", Ty.named "err"),
   ("Defect", Ty.named "defect"),
   ("Ann", Ty.unit),
   ("Val", Ty.named "val_"),
   ("Ctx", Ty.named "context"),
   ("Context", Ty.named "context"),
   ("Service", Ty.named "service"),
   ("Reference", Ty.named "reference"),
   ("Requirement", Ty.list (Ty.named "service_key")),
   ("CauseV", Ty.named "cause_v"), ("Cause", Ty.named "cause_v"),
   ("ExitV", Ty.named "exit_v"), ("Exit", Ty.named "exit_v"),
   ("ServiceKey.Carrier", Ty.named "val_")]

private def keyL : LTy := .nm "ServiceKey"
private def valL : LTy := .nm "Val"

def serviceKey : StructDesc where
  leanName := "ServiceKey"; site := "Context/Key.lean:79"; subst := subst
  fields := [{ leanName := "name", leanTy := .nm "ServiceName" },
             { leanName := "service", leanTy := .nm "ServiceTypeCode" }]
/-- `Service U` (`Context.lean:89`): the key and its carrier value, `Val` at `ValU`. -/
def service : StructDesc where
  leanName := "Service"; site := "Context.lean:89"; subst := subst
  fields := [{ leanName := "key", leanTy := keyL }, { leanName := "value", leanTy := valL }]
/-- `Context U` (`Context.lean:180`): the insertion-ordered entries; the proof field erased. -/
def context : StructDesc where
  leanName := "Context"; site := "Context.lean:180"; subst := subst
  fields := [{ leanName := "entries", leanTy := .lst (.nm "Service") },
             { leanName := "keysNodup", leanTy := .unit,
               kind := .erased "a proof (`(entries.map Service.key).Nodup`); kept by construction (F2-L2)" }]
/-- `Reference U` (`Context.lean:406`). -/
def reference : StructDesc where
  leanName := "Reference"; site := "Context.lean:406"; subst := subst
  fields := [{ leanName := "key", leanTy := keyL }, { leanName := "default", leanTy := valL }]
def err : InductiveDesc where
  leanName := "Err"; site := "Context.lean:772"; ctorPrefix := "Ce"; subst := subst
  ctors := [{ leanName := "boom" }, { leanName := "tag", args := [⟨"code", .nat, false⟩] }]
def defect : InductiveDesc where
  leanName := "Defect"; site := "Context.lean:781"; ctorPrefix := "Cx"; subst := subst
  ctors := [{ leanName := "notImplemented" }, { leanName := "asyncFiber" }, { leanName := "badName" },
            { leanName := "serviceNotFound", args := [⟨"key", keyL, false⟩] },
            { leanName := "unknownLayer", args := [⟨"index", .nat, false⟩] }]
/-- `Val` (`Context.lean:797`), fifteen constructors, prefix `Cv`. -/
def val : InductiveDesc where
  leanName := "Val"; site := "Context.lean:797"; ctorPrefix := "Cv"; subst := subst
  ctors := [{ leanName := "unit" }, { leanName := "nat", args := [⟨"n", .nat, false⟩] },
            { leanName := "bool", args := [⟨"b", .bool, false⟩] },
            { leanName := "fiber", args := [⟨"id", .nm "FiberId", false⟩] },
            { leanName := "fibers", args := [⟨"ids", .lst (.nm "FiberId"), false⟩] },
            { leanName := "scopeHandle", args := [⟨"scope", .nat, false⟩] },
            { leanName := "memoMap", args := [⟨"id", .nat, false⟩] },
            { leanName := "promise", args := [⟨"cell", .nat, false⟩] },
            { leanName := "pair", args := [⟨"first", valL, false⟩, ⟨"second", valL, false⟩] },
            { leanName := "exitOk", args := [⟨"value", valL, false⟩] },
            { leanName := "exitErr", args := [⟨"cause", .nm "CauseV", false⟩] },
            { leanName := "exitNil" },
            { leanName := "exitCons", args := [⟨"head", valL, false⟩, ⟨"tail", valL, false⟩] },
            { leanName := "ctxNil" },
            { leanName := "ctxCons", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩, ⟨"rest", valL, false⟩] }]
def contextUpdate : InductiveDesc where
  leanName := "ContextUpdate"; site := "Context.lean:1005"; ctorPrefix := "Cu"; subst := subst
  ctors := [{ leanName := "setTo", args := [⟨"context", .nm "Ctx", false⟩] },
            { leanName := "provide", args := [⟨"that", .nm "Ctx", false⟩] },
            { leanName := "provideService", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩] }]

def structs : List StructDesc := [serviceKey, service, context, reference]
def inductives : List InductiveDesc := [err, defect, val, contextUpdate]

def generated : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions (`Ml.Deep.Context`, seat F2).\n   One declaration per `Effect4/Deep/Context.lean`"
      ++ " carrier (and `ServiceKey` of `Context/Key.lean`), same field and constructor order."),
   serviceKey.header, renameDecl "service_key" serviceKey.decl,
   err.header, renameDecl "err" err.decl,
   defect.header, renameDecl "defect" defect.decl,
   .comment "`CauseV`/`ExitV` (`Context.lean:829-832`) over this `Err`/`Defect`: the avatar's `cause`/`exitv` carry the wire's `int` error and `string` defect (W1-1); the aliases name the site.",
   .rawD "type cause_v = cause",
   .rawD "type exit_v = exitv",
   .comment "`Val`, `Service ValU` and `Context ValU` are one mutually recursive group in OCaml (`ctxCons` names a key and a value; `Context` holds services).",
   val.header, renameDecl "val_" val.decl,
   service.header, renameDecl "service" service.decl,
   context.header, renameDecl "context" context.decl,
   reference.header, renameDecl "reference" reference.decl,
   contextUpdate.header, renameDecl "context_update" contextUpdate.decl]

end Context

namespace Layer

def subst : Subst :=
  [("FiberId", Ty.int),
   ("LayerId", Ty.named "layer_id"),
   ("MemoMapId", Ty.named "memo_map_id"),
   ("DeferredKey", Ty.named "Deep_stores.deferred_key"),
   ("DeferredCell", Ty.named "Deep_stores.deferred_cell"),
   ("DeferredStore", Ty.named "Deep_stores.deferred_store"),
   ("ServiceKey", Ty.named "Deep_context.service_key"),
   ("ServiceName", Ty.int),
   ("ServiceTypeCode", Ty.int),
   ("Err", Ty.named "Deep_stores.err"),
   ("Defect", Ty.named "Deep_context.defect"),
   ("Ann", Ty.unit),
   ("Val", Ty.named "value"),
   ("Ctx", Ty.list (Ty.named "service_pair")),
   ("ContextUpdate", Ty.named "Deep_context.context_update"),
   ("CombineMode", Ty.named "combine_mode"),
   ("Construction", Ty.named "construction"),
   ("LayerDesc", Ty.named "layer_desc"),
   ("LayerTable", Ty.list (Ty.named "layer_desc")),
   ("FinName", Ty.named "fin_name"),
   ("SyncOp", Ty.named "sync_op"),
   ("ProgName", Ty.named "prog_name"),
   ("Name", Ty.named "name"),
   ("ActionName", Ty.named "action_name"),
   ("Thunk", Ty.named "thunk"),
   ("Program", Ty.named "program"),
   ("Prim", Ty.named "program"),
   ("MemoEntry", Ty.named "memo_entry"),
   ("MemoMap", Ty.named "memo_map"),
   ("MemoWorld", Ty.list (Ty.named "memo_map")),
   ("ScopeEntry", Ty.named "scope_entry"),
   ("ScopeStore", Ty.named "scope_store"),
   ("ScopeV", Ty.named "scope"),
   ("Scope", Ty.named "scope"),
   ("ScopeState", Ty.named "scope_state"),
   ("FinalizerStrategy", Ty.named "Deep_stores.finalizer_strategy"),
   ("Exit", Ty.named "exitv"), ("ExitV", Ty.named "exitv"),
   ("Cause", Ty.named "cause"), ("CauseV", Ty.named "cause"),
   ("Reason", Ty.named "reason"), ("ReasonV", Ty.named "reason"),
   ("ReasonAnnotations", Ty.list Ty.string),
   ("Supervision.ObserverMode", Ty.named "observer_mode"),
   ("Supervision.ForkOptions", Ty.named "fork_options"),
   ("χ", Ty.list (Ty.named "service_pair"))]

private def fid : LTy := .nm "FiberId"
private def exitL : LTy := .nm "ExitV"
private def causeL : LTy := .nm "CauseV"
private def valL : LTy := .nm "Val"
private def ctxL : LTy := .nm "Ctx"
private def lid : LTy := .nm "LayerId"
private def mid : LTy := .nm "MemoMapId"
private def keyL : LTy := .nm "ServiceKey"
private def progL : LTy := .nm "ProgName"

def layerId : StructDesc where
  leanName := "LayerId"; site := "Layer.lean:53"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]
def memoMapId : StructDesc where
  leanName := "MemoMapId"; site := "Layer.lean:58"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]
/-- `ServiceKey` (`Effect4/Context/Key.lean:79`): `ServiceName`/`ServiceTypeCode` are `Nat`
boxes, rendered as `int`. -/
def serviceKey : StructDesc where
  leanName := "ServiceKey"; site := "Context/Key.lean:79"; subst := subst
  fields := [{ leanName := "name", leanTy := .nm "ServiceName" },
             { leanName := "service", leanTy := .nm "ServiceTypeCode" }]
/-- `Defect` (`Context.lean:781`), prefix `Lx`. -/
def defect : InductiveDesc where
  leanName := "Defect"; site := "Context.lean:781"; ctorPrefix := "Lx"; subst := subst
  ctors := [{ leanName := "notImplemented" }, { leanName := "asyncFiber" }, { leanName := "badName" },
            { leanName := "serviceNotFound", args := [⟨"key", keyL, false⟩] },
            { leanName := "unknownLayer", args := [⟨"index", .nat, false⟩] }]
/-- `ContextUpdate` (`Context.lean:1005`), prefix `Lu`. -/
def contextUpdate : InductiveDesc where
  leanName := "ContextUpdate"; site := "Context.lean:1005"; ctorPrefix := "Lu"; subst := subst
  ctors := [{ leanName := "setTo", args := [⟨"context", ctxL, false⟩] },
            { leanName := "provide", args := [⟨"that", ctxL, false⟩] },
            { leanName := "provideService", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩] }]
def combineMode : InductiveDesc where
  leanName := "CombineMode"; site := "Layer.lean:69"; ctorPrefix := "Lc"; subst := subst
  ctors := [{ leanName := "provide" }, { leanName := "provideMerge" }]
def construction : InductiveDesc where
  leanName := "Construction"; site := "Layer.lean:76"; ctorPrefix := "Lk"; subst := subst
  ctors := [{ leanName := "succeedContext", args := [⟨"services", .lst (.nm "ServicePair"), false⟩] },
            { leanName := "failWith", args := [⟨"error", .nm "Err", false⟩] },
            { leanName := "acquire", args := [⟨"services", .lst (.nm "ServicePair"), false⟩, ⟨"release", .nat, false⟩] },
            { leanName := "fromService", args := [⟨"input", keyL, false⟩, ⟨"output", keyL, false⟩] }]
def layerDesc : InductiveDesc where
  leanName := "LayerDesc"; site := "Layer.lean:92"; ctorPrefix := "Ld"; subst := subst
  ctors := [{ leanName := "atom", args := [⟨"construction", .nm "Construction", false⟩] },
            { leanName := "memoized", args := [⟨"construction", .nm "Construction", false⟩] },
            { leanName := "childScope", args := [⟨"inner", lid, false⟩] },
            { leanName := "fresh", args := [⟨"inner", lid, false⟩] },
            { leanName := "provideWith", args := [⟨"self", lid, false⟩, ⟨"that", lid, false⟩, ⟨"mode", .nm "CombineMode", false⟩] },
            { leanName := "mergeAll", args := [⟨"layers", .lst lid, false⟩] }]
def finName : InductiveDesc where
  leanName := "FinName"; site := "Layer.lean:115"; ctorPrefix := "Lfin"; subst := subst
  ctors := [{ leanName := "closeChildScope", args := [⟨"scope", .nat, false⟩] },
            { leanName := "detachFromParent", args := [⟨"parent", .nat, false⟩, ⟨"key", .nat, false⟩] },
            { leanName := "closeChildOnFailure", args := [⟨"scope", .nat, false⟩] },
            { leanName := "memoEntry", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "memoDone", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "restoreContext", args := [⟨"prev", ctxL, false⟩] },
            { leanName := "scopedExit", args := [⟨"prev", ctxL, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "closeScopeWith", args := [⟨"scope", .nat, false⟩] },
            { leanName := "release", args := [⟨"label", .nat, false⟩, ⟨"fails", .bool, false⟩] },
            { leanName := "releaseWith", args := [⟨"label", .nat, false⟩, ⟨"captured", ctxL, false⟩] },
            { leanName := "interruptFiber", args := [⟨"fiber", fid, false⟩, ⟨"skipSelf", .bool, false⟩] }]
def syncOp : InductiveDesc where
  leanName := "SyncOp"; site := "Layer.lean:144"; ctorPrefix := "Ls"; subst := subst
  ctors := [{ leanName := "scopeMake", args := [⟨"strategy", .nm "FinalizerStrategy", false⟩] },
            { leanName := "scopeFork", args := [⟨"parent", .nat, false⟩, ⟨"strategy", .nm "FinalizerStrategy", false⟩] },
            { leanName := "scopeAdd", args := [⟨"scope", .nat, false⟩, ⟨"finalizer", .nm "FinName", false⟩] },
            { leanName := "scopeRemove", args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
            { leanName := "memoFork", args := [⟨"parent", .opt mid, false⟩] },
            { leanName := "memoGet", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "memoBuild", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "memoComplete", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "memoRelease", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "deferredAwaitCleanup", args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] }]
def progName : InductiveDesc where
  leanName := "ProgName"; site := "Layer.lean:174"; ctorPrefix := "Lp"; subst := subst
  ctors := [{ leanName := "value", args := [⟨"v", valL, false⟩] },
            { leanName := "failCause", args := [⟨"cause", causeL, false⟩] },
            { leanName := "getContext" },
            { leanName := "service", args := [⟨"key", keyL, false⟩] },
            { leanName := "setContextTo", args := [⟨"context", ctxL, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "provideContext", args := [⟨"context", ctxL, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "provideService", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "scoped", args := [⟨"body", progL, false⟩] },
            { leanName := "acquireRelease", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "acquireMasked", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"captured", ctxL, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "addFinalizer", args := [⟨"label", .nat, false⟩] },
            { leanName := "seq", args := [⟨"first", progL, false⟩, ⟨"second", progL, false⟩] },
            { leanName := "never" },
            { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "build", args := [⟨"layer", lid, false⟩] },
            { leanName := "buildWithScope", args := [⟨"layer", lid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "buildWithMemoMap", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "layerBuild", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "buildAdding", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "buildThenNever", args := [⟨"layer", lid, false⟩] },
            { leanName := "launch", args := [⟨"layer", lid, false⟩] },
            { leanName := "provideLayer", args := [⟨"layer", lid, false⟩, ⟨"isLocal", .bool, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "scopedWithAlloc", args := [⟨"layer", lid, false⟩, ⟨"isLocal", .bool, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "memoLookup", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"construction", .nm "Construction", false⟩] },
            { leanName := "finalizerOf", args := [⟨"fin", .nm "FinName", false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "memoReleaseOf", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "releaseOf", args := [⟨"label", .nat, false⟩] }]
def name : InductiveDesc where
  leanName := "Name"; site := "Layer.lean:233"; ctorPrefix := "Ln"; subst := subst
  ctors := [{ leanName := "restore", args := [⟨"exit", exitL, false⟩] },
            { leanName := "merge", args := [⟨"exit", exitL, false⟩] },
            { leanName := "seq", args := [⟨"next", progL, false⟩] },
            { leanName := "constant", args := [⟨"value", valL, false⟩] },
            { leanName := "registerAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
            { leanName := "cancelAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
            { leanName := "neverRegister" },
            { leanName := "abortController" },
            { leanName := "cancelPark" },
            { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] },
            { leanName := "withWaiter", args := [⟨"base", .nm "Name", false⟩, ⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] },
            { leanName := "reFail", args := [⟨"cause", causeL, false⟩] },
            { leanName := "finalizerName", args := [⟨"fin", .nm "FinName", false⟩] },
            { leanName := "closeSeq", args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩, ⟨"captured", .lst (.nm "ReasonV"), false⟩] },
            { leanName := "closePar", args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩, ⟨"forked", .lst fid, false⟩, ⟨"closerInterruptible", .bool, false⟩] },
            { leanName := "mergeAwaitedExits" },
            { leanName := "afterScopeAdd", args := [⟨"fin", .nm "FinName", false⟩] },
            { leanName := "updateThen", args := [⟨"update", .nm "ContextUpdate", false⟩, ⟨"body", progL, false⟩] },
            { leanName := "bodyThen", args := [⟨"body", progL, false⟩, ⟨"prev", ctxL, false⟩] },
            { leanName := "scopedThen", args := [⟨"body", progL, false⟩] },
            { leanName := "scopedInstall", args := [⟨"body", progL, false⟩, ⟨"prev", ctxL, false⟩] },
            { leanName := "scopedBody", args := [⟨"body", progL, false⟩, ⟨"prev", ctxL, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "thenClose", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "serviceLookup", args := [⟨"key", keyL, false⟩] },
            { leanName := "bindService", args := [⟨"output", keyL, false⟩] },
            { leanName := "acquireWith", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "acquireInScope", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"captured", ctxL, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "registerRelease", args := [⟨"scope", .nat, false⟩, ⟨"release", .nat, false⟩, ⟨"captured", ctxL, false⟩] },
            { leanName := "addFinalizerOn", args := [⟨"label", .nat, false⟩] },
            { leanName := "addFinalizerCaptured", args := [⟨"scope", .nat, false⟩, ⟨"label", .nat, false⟩] },
            { leanName := "buildFromContext", args := [⟨"layer", lid, false⟩] },
            { leanName := "buildWithScopeFromContext", args := [⟨"layer", lid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "withMemoMapThen", args := [⟨"layer", lid, false⟩, ⟨"scope", .opt .nat, false⟩] },
            { leanName := "addCurrentMemoMap", args := [⟨"memoMap", mid, false⟩] },
            { leanName := "memoize", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"construction", .nm "Construction", false⟩] },
            { leanName := "awaitPromise", args := [⟨"cell", .nm "DeferredKey", false⟩] },
            { leanName := "buildIntoLayerScope", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"construction", .nm "Construction", false⟩] },
            { leanName := "thenBuildInto", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"construction", .nm "Construction", false⟩, ⟨"layerScope", .nat, false⟩] },
            { leanName := "closeIfLast", args := [⟨"exit", exitL, false⟩] },
            { leanName := "fromBuildThen", args := [⟨"desc", .nm "LayerDesc", false⟩, ⟨"self", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "freshThen", args := [⟨"inner", lid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "provideThen", args := [⟨"self", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"mode", .nm "CombineMode", false⟩] },
            { leanName := "combineWith", args := [⟨"mode", .nm "CombineMode", false⟩, ⟨"thatContext", ctxL, false⟩] },
            { leanName := "mergeChildren", args := [⟨"layers", .lst lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "mergeForkOne", args := [⟨"layer", lid, false⟩, ⟨"rest", .lst lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"parent", .nat, false⟩, ⟨"forked", .lst fid, false⟩] },
            { leanName := "mergeForkNext", args := [⟨"rest", .lst lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"parent", .nat, false⟩, ⟨"forked", .lst fid, false⟩] },
            { leanName := "mergeContexts" },
            { leanName := "provideLayerWith", args := [⟨"layer", lid, false⟩, ⟨"isLocal", .bool, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "provideLayerBody", args := [⟨"body", progL, false⟩] }]
def actionName : InductiveDesc where
  leanName := "ActionName"; site := "Layer.lean:341"; ctorPrefix := "La"; subst := subst
  ctors := [{ leanName := "fork", args := [⟨"program", progL, false⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
            { leanName := "forkScoped", args := [⟨"program", progL, false⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩, ⟨"key", .nat, false⟩] },
            { leanName := "interrupt", args := [⟨"target", fid, false⟩] },
            { leanName := "interruptScoped", args := [⟨"target", fid, false⟩] },
            { leanName := "awaitAll", args := [⟨"targets", .lst fid, false⟩] },
            { leanName := "awaitAllFailFast", args := [⟨"targets", .lst fid, false⟩] },
            { leanName := "setContext", args := [⟨"context", ctxL, false⟩] },
            { leanName := "getContext" },
            { leanName := "getId" },
            { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "setInterruptible", args := [⟨"body", progL, false⟩, ⟨"flag", .bool, false⟩] },
            { leanName := "refuse", args := [⟨"cause", causeL, false⟩] },
            { leanName := "dropObservers", args := [⟨"token", .nat, false⟩] }]
def thunk : InductiveDesc where
  leanName := "Thunk"; site := "Layer.lean:361"; ctorPrefix := "Lt"; subst := subst
  ctors := [{ leanName := "act", args := [⟨"action", .nm "ActionName", false⟩] },
            { leanName := "op", args := [⟨"operation", .nm "SyncOp", false⟩] },
            { leanName := "body", args := [⟨"program", progL, false⟩] }]
/-- `ScopeState` (`Scope.lean:71`) at Layer's `FinName`, prefix `Lss`. -/
def scopeState : InductiveDesc where
  leanName := "ScopeState"; site := "Scope.lean:71 at Layer.lean:437"; ctorPrefix := "Lss"; subst := subst
  ctors := [{ leanName := "empty" }, { leanName := "openEmpty" },
            { leanName := "openInline", args := [⟨"key", .nat, false⟩, ⟨"finalizer", .nm "FinName", false⟩] },
            { leanName := "openMap", args := [⟨"entries", .lst (.nm "ScopeEntryPair"), false⟩] },
            { leanName := "closed", args := [⟨"exit", exitL, false⟩] }]
def scope : StructDesc where
  leanName := "Scope"; site := "Scope.lean:86 at Layer.lean:437"; subst := subst
  fields := [{ leanName := "strategy", leanTy := .nm "FinalizerStrategy" },
             { leanName := "state", leanTy := .nm "ScopeState", isMutable := true }]
def scopeEntry : StructDesc where
  leanName := "ScopeEntry"; site := "Layer.lean:439"; subst := subst
  fields := [{ leanName := "key", leanTy := .nat }, { leanName := "scope", leanTy := .nm "ScopeV", isMutable := true }]
def scopeStore : StructDesc where
  leanName := "ScopeStore"; site := "Layer.lean:444"; subst := subst
  fields := [{ leanName := "entries", leanTy := .lst (.nm "ScopeEntry"), isMutable := true }]
def memoEntry : StructDesc where
  leanName := "MemoEntry"; site := "Layer.lean:487"; subst := subst
  fields := [{ leanName := "observers", leanTy := .nat, isMutable := true },
             { leanName := "effect", leanTy := .nm "Program", isMutable := true,
               comment := Option.some "Lean: `Program`; a thunk here (DIVERGENCE 1)" },
             { leanName := "layerScope", leanTy := .nat },
             { leanName := "deferred", leanTy := .nm "DeferredKey" },
             { leanName := "finalizer", leanTy := .nm "FinName" }]
def memoMap : StructDesc where
  leanName := "MemoMap"; site := "Layer.lean:501"; subst := subst
  fields := [{ leanName := "id", leanTy := mid },
             { leanName := "parent", leanTy := .opt mid },
             { leanName := "entries", leanTy := .lst (.nm "MemoPair"), isMutable := true }]
def st : StructDesc where
  leanName := "St"; site := "Layer.lean:624"; subst := subst
  fields := [{ leanName := "memo", leanTy := .nm "MemoWorld", isMutable := true },
             { leanName := "scopes", leanTy := .nm "ScopeStore" },
             { leanName := "deferreds", leanTy := .nm "DeferredStore" },
             { leanName := "nextName", leanTy := .nat, isMutable := true }]

def tupleAliases : List Decl :=
  [.rawD "type service_pair = service_key * value",
   .rawD "type scope_entry_pair = int * fin_name",
   .rawD "type memo_pair = layer_id * memo_entry"]

def structs : List StructDesc := [layerId, memoMapId, scope, scopeEntry, scopeStore, memoEntry, memoMap, st]
def inductives : List InductiveDesc :=
  [combineMode, construction, layerDesc, finName, syncOp, progName, name, actionName, thunk, scopeState]

def generated : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions (`Ml.Deep.Layer`, seat F2).\n   One declaration per `Effect4/Deep/Layer.lean`"
      ++ " carrier (and the four `Context.lean`/`Key.lean` carriers it names), same field and"
      ++ " constructor order."),
   layerId.header, renameDecl "layer_id" layerId.decl,
   memoMapId.header, renameDecl "memo_map_id" memoMapId.decl,
   .comment "`ServiceKey`, `Defect` and `ContextUpdate` are `deep_context.ml`'s (`Context.lean`, which `Layer.lean` imports).",
   .rawD "type service_pair = Deep_context.service_key * value",
   combineMode.header, renameDecl "combine_mode" combineMode.decl,
   construction.header, renameDecl "construction" construction.decl,
   layerDesc.header, renameDecl "layer_desc" layerDesc.decl,
   finName.header, renameDecl "fin_name" finName.decl,
   .rawD "type scope_entry_pair = int * fin_name",
   scopeState.header, renameDecl "scope_state" scopeState.decl,
   scope.header, renameDecl "scope" scope.decl,
   scopeEntry.header, renameDecl "scope_entry" scopeEntry.decl,
   scopeStore.header, renameDecl "scope_store" scopeStore.decl,
   syncOp.header, renameDecl "sync_op" syncOp.decl,
   .comment ("`ProgName`, `Name`, `ActionName` and `Thunk` are one mutually recursive group in"
      ++ " OCaml; order inside the group is the Lean order."),
   progName.header, renameDecl "prog_name" progName.decl,
   name.header, renameDecl "name" name.decl,
   actionName.header, renameDecl "action_name" actionName.decl,
   thunk.header, renameDecl "thunk" thunk.decl,
   memoEntry.header, renameDecl "memo_entry" memoEntry.decl,
   .rawD "type memo_pair = layer_id * memo_entry",
   memoMap.header, renameDecl "memo_map" memoMap.decl,
   st.header, renameDecl "st" st.decl]

end Layer

/-! ## `Effect4/Deep/ForkFlow.lean` → `workshop/OCaml5/avatar/deep_forkflow.ml` (seat F2)

The fiber profile's alphabet: `FiberOp` (twelve rows), the request carriers and the refusal
alphabet. Everything else in `ForkFlow.lean` is the compile of that profile over the Flow IR
(`RegionFlow`, `Code`, `Config`, `OpSpec`), which the avatar has no carriers for: it refuses by
name. `Val` here is `Effects.Trace.Val` (`str`/`nat`/`bool`/`pair`/`unit`/`none`/`some`), which
the wire `value` spells one for one; `BlockId` and `FiberId` are `int`. -/

namespace ForkFlow

def subst : Subst :=
  [("FiberId", Ty.int), ("BlockId", Ty.int), ("Val", Ty.named "value"),
   ("Res", Ty.named "exitv"), ("FiberOp", Ty.named "fiber_op"),
   ("RootRequest", Ty.named "root_request"), ("ForkRequest", Ty.named "fork_request"),
   ("ForkRefusal", Ty.named "fork_refusal")]

/-- `FiberOp` (`ForkFlow.lean:122`), twelve rows in profile order, prefix `Fo`. -/
def fiberOp : InductiveDesc where
  leanName := "FiberOp"; site := "ForkFlow.lean:122"; ctorPrefix := "Fo"; subst := subst
  ctors := [{ leanName := "fork" }, { leanName := "forkScoped" }, { leanName := "join" },
            { leanName := "await" }, { leanName := "interrupt" }, { leanName := "interruptAll" },
            { leanName := "childrenSnapshot" }, { leanName := "awaitChildren" }, { leanName := "raceAll" },
            { leanName := "uninterruptibleIn" }, { leanName := "interruptibleIn" }, { leanName := "yieldNow" }]
def rootRequest : StructDesc where
  leanName := "RootRequest"; site := "ForkFlow.lean:382"; subst := subst
  fields := [{ leanName := "root", leanTy := .nm "BlockId" }, { leanName := "args", leanTy := .lst (.nm "Val") }]
def forkRequest : StructDesc where
  leanName := "ForkRequest"; site := "ForkFlow.lean:401"; subst := subst
  fields := [{ leanName := "root", leanTy := .nm "BlockId" }, { leanName := "args", leanTy := .lst (.nm "Val") },
             { leanName := "daemon", leanTy := .bool }, { leanName := "region", leanTy := .opt .nat }]
/-- `ForkRefusal` (`ForkFlow.lean:449`), prefix `Fr`. -/
def forkRefusal : InductiveDesc where
  leanName := "ForkRefusal"; site := "ForkFlow.lean:449"; ctorPrefix := "Fr"; subst := subst
  ctors := [{ leanName := "requestMalformed", args := [⟨"request", .nm "Val", false⟩] },
            { leanName := "rootUndeclared", args := [⟨"root", .nm "BlockId", false⟩] },
            { leanName := "rootUnknown", args := [⟨"root", .nm "BlockId", false⟩] },
            { leanName := "rootArity", args := [⟨"root", .nm "BlockId", false⟩, ⟨"declared", .nat, false⟩, ⟨"supplied", .nat, false⟩] },
            { leanName := "handleMalformed", args := [⟨"request", .nm "Val", false⟩] },
            { leanName := "scopedNamesRegion", args := [⟨"root", .nm "BlockId", false⟩] }]

def generated : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions (`Ml.Deep.ForkFlow`, seat F2).\n   One declaration per `Effect4/Deep/ForkFlow.lean`"
      ++ " carrier of the profile's alphabet, same order."),
   fiberOp.header, renameDecl "fiber_op" fiberOp.decl,
   rootRequest.header, renameDecl "root_request" rootRequest.decl,
   forkRequest.header, renameDecl "fork_request" forkRequest.decl,
   forkRefusal.header, renameDecl "fork_refusal" forkRefusal.decl]

end ForkFlow

end Deep

/-! ### Checks on the seat-W1 descriptions

Counts and names pinned the way `Ml.Avatar`'s are: constructor counts against the Lean file,
field order against the Lean field order, and the mangling round-trip on every field name. -/

-- The keyword escape for type names, and the reason it exists.
#guard typeName "Val" == "val"
#guard typeName' "Val" == "val_"
#guard typeName' "RunFiber" == "run_fiber"
#guard typeName' "SyncOp" == "sync_op"

-- `Stores.lean`'s constructor counts.
#guard Deep.Stores.err.ctors.length == 2
#guard Deep.Stores.defect.ctors.length == 5
#guard Deep.Stores.fnName.ctors.length == 5
#guard Deep.Stores.finName.ctors.length == 6
#guard Deep.Stores.completion.ctors.length == 2
#guard Deep.Stores.syncOp.ctors.length == 23
#guard Deep.Stores.raceName.ctors.length == 6
#guard Deep.Stores.progName.ctors.length == 24
#guard Deep.Stores.name.ctors.length == 21
#guard Deep.Stores.actionName.ctors.length == 19
#guard Deep.Stores.thunk.ctors.length == 4
#guard Deep.Stores.finalizerStrategy.ctors.length == 2
#guard Deep.Stores.scopeState.ctors.length == 5

-- `ActionName` is arm for arm with `WithFiberAction` — the same 17 names — but *not* in the
-- same order: `setInterruptible` is `WithFiberAction`'s twelfth and `ActionName`'s sixteenth.
-- A0 §3 lists no such row, so it is seat W1's, and `deep_stores.ml` follows the `Stores.lean`
-- order because that is the file it is the port of.
-- Seat F2: `WithFiberAction` gained `dropObservers` and `cancelRace` in `2f77f7d`;
-- `Ml.Avatar.withFiberAction` (above the banner, not this seat's to edit) still describes the
-- seventeen of `e77282d`, so the two are named here until that description catches up.
#guard (Deep.Stores.actionName.ctors.map (·.leanName)).all
  (fun n => (Avatar.withFiberAction.ctors.map (·.leanName)).contains n
    || n == "dropObservers" || n == "cancelRace")
#guard (Avatar.withFiberAction.ctors.map (·.leanName)).all
  (fun n => (Deep.Stores.actionName.ctors.map (·.leanName)).contains n)
#guard Deep.Stores.actionName.ctors.map (·.leanName) !=
  Avatar.withFiberAction.ctors.map (·.leanName)

-- Field order, in the Lean order, mangled.
#guard Deep.Stores.stores.fields.map (·.ocaml) == ["refs", "deferreds", "scopes", "next_name"]
#guard Deep.Stores.deferredCell.fields.map (·.ocaml) == ["completion", "waiters"]
#guard Deep.Stores.deferredStore.fields.map (·.ocaml) == ["cells", "due"]
#guard Deep.Stores.scopeEntry.fields.map (·.ocaml) == ["key", "scope"]
#guard Deep.Stores.ctx.fields.map (·.ocaml) ==
  ["ambient_scope", "max_ops_before_yield", "prevent_yield"]

-- The mangling is injective on every name this section renders.
#guard (Deep.Stores.structs.flatMap (fun d => d.fields.map (·.leanName))).all
  (fun n => unmangleField (mangleField n) == n)

-- No description erases an argument: every `Stores.lean` constructor is arity for arity.
#guard Deep.Stores.inductives.all (fun d => d.erasures.isEmpty)
#guard Deep.Stores.inductives.all (fun d => d.arities.all (fun a => a.2.1 == a.2.2))

-- The names `deep_stores.ml` uses.
#guard Deep.Stores.syncOp.ctors.map (CtorDesc.ocaml "S") ==
  ["SrefMake", "SrefGet", "SrefSet", "SrefGetAndSet", "SrefSetAndGet", "SrefUpdate",
   "SrefGetAndUpdate", "SrefUpdateAndGet", "SrefUpdateSome", "SrefGetAndUpdateSome",
   "SrefUpdateSomeAndGet", "SrefModify", "SrefModifySome", "SdeferredMake", "SdeferredIsDone",
   "SdeferredPoll", "SdeferredCompleteWith", "SdeferredInterruptWith", "SdeferredAwaitCleanup",
   "SscopeMake", "SscopeAdd", "SscopeRemove", "SscopeIsClosed"]
#guard Deep.Stores.scopeState.ctors.map (CtorDesc.ocaml "Ss") ==
  ["Ssempty", "SsopenEmpty", "SsopenInline", "SsopenMap", "Ssclosed"]

-- `Layer.lean`'s constructor counts (seat F2, at `2f77f7d`).
#guard Deep.Layer.combineMode.ctors.length == 2
#guard Deep.Layer.construction.ctors.length == 4
#guard Deep.Layer.layerDesc.ctors.length == 6
#guard Deep.Layer.finName.ctors.length == 11
#guard Deep.Layer.syncOp.ctors.length == 10
#guard Deep.Layer.progName.ctors.length == 27
#guard Deep.Layer.name.ctors.length == 49
#guard Deep.Layer.actionName.ctors.length == 13
#guard Deep.Layer.thunk.ctors.length == 3
#guard Deep.ForkFlow.fiberOp.ctors.length == 12
#guard Deep.ForkFlow.forkRefusal.ctors.length == 6
#guard Deep.ForkFlow.forkRequest.fields.map (·.ocaml) == ["root", "args", "daemon", "region"]
#guard Deep.Context.contextUpdate.ctors.length == 3
#guard Deep.Context.defect.ctors.length == 5
#guard Deep.Context.val.ctors.length == 15
#guard Deep.Context.err.ctors.length == 2
#guard Deep.Context.context.erasures.map (·.1) == ["keysNodup"]
#guard Deep.Context.structs.all (fun d => d.holes.isEmpty)
#guard Deep.Layer.scopeState.ctors.length == 5
#guard Deep.Layer.st.fields.map (·.ocaml) == ["memo", "scopes", "deferreds", "next_name"]
#guard Deep.Layer.memoEntry.fields.map (·.ocaml) == ["observers", "effect", "layer_scope", "deferred", "finalizer"]
#guard Deep.Layer.inductives.all (fun d => d.erasures.isEmpty)
#guard (Deep.Layer.structs.flatMap (fun d => d.fields.map (·.leanName))).all
  (fun n => unmangleField (mangleField n) == n)
-- Layer's `ActionName` is `WithFiberAction` minus the fork-in/run-in/race family plus nothing:
-- every name is a `WithFiberAction` name (`dropObservers` since `2f77f7d`).
#guard (Deep.Layer.actionName.ctors.map (·.leanName)).all
  (fun n => (Avatar.withFiberAction.ctors.map (·.leanName)).contains n
    || n == "dropObservers" || n == "awaitAllFailFast")

end Ml
end OCaml5
