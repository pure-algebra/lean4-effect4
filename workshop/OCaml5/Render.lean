import OCaml5.Effect
import OCaml5.Compiler
import OCaml5.Witnesses

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

private def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else if s.length == 2 then "0" ++ s else "00" ++ s

/-- An OCaml string literal body. The row alphabet is ASCII with tabs. -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
      (if c == '"' then "\\\""
       else if c == '\\' then "\\\\"
       else if c == '\t' then "\\t"
       else if c == '\n' then "\\n"
       else if c.toNat < 32 || c.toNat > 126 then "\\" ++ pad3 c.toNat
       else String.singleton c)

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
# A general Lean → OCaml declaration surface

Status: spike P5 part 2, 2026-09-04, for spike A0 (`docs/research/2026-09-04-spike-a0-avatar.md`):
the OCaml avatar of `workshop/Deep/Fibers.lean` is to be *generated* from the Lean carriers, not
hand-written. `Term.render` above emits one expression over the raw effect primitives, which is
what a reference machine needs and not what a program needs. This section is the rest of the
surface: declarations.

It is a **reflected description**, not Lean metaprogramming. `Ml.TypeDecl`, `Ml.Expr` and
`Ml.Decl` are ordinary data; A0 populates them by hand from `Fibers.lean` (a `structure` becomes
an `Ml.TyBody.record`, an `inductive` becomes an `Ml.TyBody.variant`), and `Ml.moduleText` turns
a `List Ml.Decl` into a compilation unit. Nothing here inspects a Lean declaration; when the
mapping is settled, an elaborator that builds these values from `Lean.Expr` is a separate,
later step, and this type is the interface it would target.

What the surface covers, in the order A0 asked for it:

* records, with `mutable` fields, and variants, both with type parameters, and mutually recursive
  groups joined by `and`;
* `ref`s, dereference and assignment;
* `let rec` and mutually recursive functions (`let rec f … and g …`), with optional parameter and
  result annotations;
* `match` with `when` guards, `try … with`, `if`, tuples, lists, record literals and functional
  record update;
* effect declarations as `type _ Effect.t += C : t -> answer Effect.t`, exceptions, `external`s
  and `open`;
* `Effect.Deep.match_with` and `Effect.Deep.try_with` handler blocks with a `retc`/`exnc`/`effc`
  record, the `effc` table written the way `effect.ml:66-68` types it — a locally abstract `type
  a`, one clause per effect constructor, `Some (fun (k : (a, answer) continuation) -> …)`, and a
  `| _ -> None` default.

Two deliberate simplifications. Expressions are **parenthesised aggressively** rather than by a
precedence table: `ocamlc` accepts redundant parentheses everywhere and a wrong precedence table
is a silent miscompile. And the surface is untyped — it will happily describe a module `ocamlc`
rejects. The check is executed, not structural: `tools/fuzz.sh surface` renders the sample below
and compiles it.
-/

namespace OCaml5
namespace Ml

/-! ## Types -/

/-- An OCaml type expression. Type application is postfix, as OCaml writes it. -/
inductive Ty where
  | var (name : String)
  | con (name : String) (args : List Ty)
  | arrow (dom cod : Ty)
  | tuple (parts : List Ty)
deriving Repr, Inhabited

namespace Ty
def int : Ty := .con "int" []
def bool : Ty := .con "bool" []
def unit : Ty := .con "unit" []
def string : Ty := .con "string" []
def exn : Ty := .con "exn" []
def named (n : String) : Ty := .con n []
def list (t : Ty) : Ty := .con "list" [t]
def option (t : Ty) : Ty := .con "option" [t]
def ref (t : Ty) : Ty := .con "ref" [t]
/-- `'a Effect.t`. -/
def effect (t : Ty) : Ty := .con "Effect.t" [t]
/-- `('a, 'b) Effect.Deep.continuation`. -/
def cont (a b : Ty) : Ty := .con "Effect.Deep.continuation" [a, b]
end Ty

mutual

def renderTy : Ty → String
  | .var n => "'" ++ n
  | .con n [] => n
  | .con n [a] => renderTy a ++ " " ++ n
  | .con n args => "(" ++ String.intercalate ", " (renderTys args) ++ ") " ++ n
  | .arrow a b => "(" ++ renderTy a ++ " -> " ++ renderTy b ++ ")"
  | .tuple ps => "(" ++ String.intercalate " * " (renderTys ps) ++ ")"

def renderTys : List Ty → List String
  | [] => []
  | t :: rest => renderTy t :: renderTys rest

end

/-! ## Patterns -/

inductive Pat where
  | wild
  | var (name : String)
  | int (n : Nat)
  | str (s : String)
  /-- A constructor pattern; `≥ 2` arguments are rendered as one tuple, as OCaml requires. -/
  | ctor (name : String) (args : List Pat)
  | record (fields : List (String × Pat))
  | tuple (parts : List Pat)
  /-- `hd :: tl`, which `Pat.ctor` cannot spell. -/
  | cons (hd tl : Pat)
  | alias (p : Pat) (name : String)
  | orPat (a b : Pat)
deriving Repr, Inhabited

mutual

def renderPat : Pat → String
  | .wild => "_"
  | .var n => n
  | .int n => toString n
  | .str s => "\"" ++ Render.esc s ++ "\""
  | .ctor n [] => n
  | .ctor n [a] => "(" ++ n ++ " " ++ renderPat a ++ ")"
  | .ctor n args => "(" ++ n ++ " (" ++ String.intercalate ", " (renderPats args) ++ "))"
  | .record fs => "{ " ++ String.intercalate "; " (renderPatFields fs) ++ " }"
  | .tuple ps => "(" ++ String.intercalate ", " (renderPats ps) ++ ")"
  | .cons hd tl => "(" ++ renderPat hd ++ " :: " ++ renderPat tl ++ ")"
  | .alias p n => "(" ++ renderPat p ++ " as " ++ n ++ ")"
  | .orPat a b => "(" ++ renderPat a ++ " | " ++ renderPat b ++ ")"

def renderPats : List Pat → List String
  | [] => []
  | p :: rest => renderPat p :: renderPats rest

def renderPatFields : List (String × Pat) → List String
  | [] => []
  | (n, p) :: rest => (n ++ " = " ++ renderPat p) :: renderPatFields rest

end

/-! ## Expressions -/

mutual

/-- An OCaml expression. -/
inductive Expr where
  | var (name : String)
  | int (n : Nat)
  | str (s : String)
  | bool (b : Bool)
  | unit
  | ctor (name : String) (args : List Expr)
  | app (fn : Expr) (args : List Expr)
  /-- An infix application: `(l op r)`. -/
  | binop (op : String) (l r : Expr)
  /-- `fun p1 p2 -> body`; a parameter named `()` renders as the unit pattern. -/
  | fn (params : List String) (body : Expr)
  | letIn (name : String) (value body : Expr)
  /-- A local `let rec … and …`. -/
  | letRecIn (binds : List (String × List String × Expr)) (body : Expr)
  | seq (a b : Expr)
  | ifThen (cond thenE elseE : Expr)
  | matchE (scrut : Expr) (arms : List Arm)
  | tryWith (body : Expr) (arms : List Arm)
  | record (fields : List (String × Expr))
  /-- `{ base with f = e; … }`. -/
  | recordWith (base : Expr) (fields : List (String × Expr))
  | field (e : Expr) (name : String)
  /-- `e.f <- v`, the mutable-field write. -/
  | setField (e : Expr) (name : String) (v : Expr)
  | tuple (parts : List Expr)
  | listLit (items : List Expr)
  | mkRef (e : Expr)
  | deref (e : Expr)
  | assign (r v : Expr)
  | raiseE (e : Expr)
  | perform (e : Expr)
  | continueK (k v : Expr)
  | discontinueK (k e : Expr)
  /-- `Effect.Deep.match_with comp arg { retc; exnc; effc }`. `answer` is the handler's `'b`,
  which the `effc` clauses need to annotate their continuation with. -/
  | matchWith (comp arg : Expr) (answer : Ty) (retcVar : String) (retc : Expr)
      (exnc : List Arm) (effc : List Effc)
  /-- `Effect.Deep.try_with comp arg { effc }` (`effect.ml:84-91`): the identity `retc` and the
  re-raising `exnc` are the wrapper's, not ours. -/
  | tryWithEff (comp arg : Expr) (answer : Ty) (effc : List Effc)
  | annot (e : Expr) (ty : Ty)
  /-- Request 5: a place the renderer refuses to fill. `note` says what the Lean side had;
  `fill` is what the hand-written module supplies in its place. -/
  | hole (note : String) (fill : Expr)
  /-- Verbatim text, for anything this surface does not spell. -/
  | raw (text : String)

/-- One `match`/`try` arm, with an optional `when` guard. -/
inductive Arm where
  | mk (pat : Pat) (guard : Option Expr) (body : Expr)

/-- One `effc` clause: an effect constructor, its argument patterns, the name the continuation is
bound to, and the body. -/
inductive Effc where
  | mk (ctorName : String) (args : List Pat) (kBinder : String) (body : Expr)

end

namespace Expr
instance : Inhabited Expr := ⟨Expr.unit⟩
def call (f : String) (args : List Expr) : Expr := .app (.var f) args
def ignoreE (e : Expr) : Expr := .app (.var "ignore") [e]
end Expr

private def indentOf (n : Nat) : String := "".pushn ' ' (2 * n)

mutual

/-- One expression. Compound forms are always parenthesised, so no precedence table is needed
and no reparse can change the meaning. `ind` only affects where newlines are indented to. -/
def renderExpr (ind : Nat) : Expr → String
  | .var n => n
  | .int n => toString n
  | .str s => "\"" ++ Render.esc s ++ "\""
  | .bool b => if b then "true" else "false"
  | .unit => "()"
  | .ctor n [] => n
  | .ctor n [a] => "(" ++ n ++ " " ++ renderExpr ind a ++ ")"
  | .ctor n args => "(" ++ n ++ " (" ++ String.intercalate ", " (renderExprs ind args) ++ "))"
  | .app f args =>
      "(" ++ renderExpr ind f ++ " " ++ String.intercalate " " (renderExprs ind args) ++ ")"
  | .binop op l r => "(" ++ renderExpr ind l ++ " " ++ op ++ " " ++ renderExpr ind r ++ ")"
  | .fn ps b => "(fun " ++ String.intercalate " " ps ++ " -> " ++ renderExpr ind b ++ ")"
  | .letIn n v b =>
      "(let " ++ n ++ " = " ++ renderExpr ind v ++ " in\n" ++ indentOf ind ++ renderExpr ind b
        ++ ")"
  | .letRecIn binds b =>
      "(let rec " ++ String.intercalate ("\n" ++ indentOf ind ++ "and ") (renderLocalBinds ind binds)
        ++ " in\n" ++ indentOf ind ++ renderExpr ind b ++ ")"
  | .seq a b => "(" ++ renderExpr ind a ++ ";\n" ++ indentOf ind ++ renderExpr ind b ++ ")"
  | .ifThen c t e =>
      "(if " ++ renderExpr ind c ++ " then " ++ renderExpr (ind + 1) t ++ " else "
        ++ renderExpr (ind + 1) e ++ ")"
  | .matchE s arms =>
      "(match " ++ renderExpr ind s ++ " with" ++ renderArms (ind + 1) arms ++ ")"
  | .tryWith b arms =>
      "(try " ++ renderExpr (ind + 1) b ++ " with" ++ renderArms (ind + 1) arms ++ ")"
  | .record fs => "{ " ++ String.intercalate "; " (renderFields ind fs) ++ " }"
  | .recordWith base fs =>
      "{ " ++ renderExpr ind base ++ " with " ++ String.intercalate "; " (renderFields ind fs)
        ++ " }"
  | .field e n => "(" ++ renderExpr ind e ++ ")." ++ n
  | .setField e n v =>
      "((" ++ renderExpr ind e ++ ")." ++ n ++ " <- " ++ renderExpr ind v ++ ")"
  | .tuple ps => "(" ++ String.intercalate ", " (renderExprs ind ps) ++ ")"
  | .listLit items => "[" ++ String.intercalate "; " (renderExprs ind items) ++ "]"
  | .mkRef e => "(ref " ++ renderExpr ind e ++ ")"
  | .deref e => "(!" ++ renderExpr ind e ++ ")"
  | .assign r v => "(" ++ renderExpr ind r ++ " := " ++ renderExpr ind v ++ ")"
  | .raiseE e => "(raise " ++ renderExpr ind e ++ ")"
  | .perform e => "(Effect.perform " ++ renderExpr ind e ++ ")"
  | .continueK k v =>
      "(Effect.Deep.continue " ++ renderExpr ind k ++ " " ++ renderExpr ind v ++ ")"
  | .discontinueK k e =>
      "(Effect.Deep.discontinue " ++ renderExpr ind k ++ " " ++ renderExpr ind e ++ ")"
  | .matchWith comp arg answer retcVar retc exnc effc =>
      "(Effect.Deep.match_with " ++ renderExpr ind comp ++ " " ++ renderExpr ind arg ++ "\n"
        ++ indentOf (ind + 1) ++ "{ retc = (fun " ++ retcVar ++ " -> "
        ++ renderExpr (ind + 2) retc ++ ");\n"
        ++ indentOf (ind + 1) ++ "  exnc = (function" ++ renderArms (ind + 2) exnc
        ++ "\n" ++ indentOf (ind + 2) ++ "| e -> raise e);\n"
        ++ indentOf (ind + 1) ++ "  effc = (fun (type a) (eff : a Effect.t) ->\n"
        ++ indentOf (ind + 2) ++ "match eff with" ++ renderEffcClauses (ind + 2) answer effc
        ++ "\n" ++ indentOf (ind + 2) ++ "| _ -> None) })"
  | .tryWithEff comp arg answer effc =>
      "(Effect.Deep.try_with " ++ renderExpr ind comp ++ " " ++ renderExpr ind arg ++ "\n"
        ++ indentOf (ind + 1) ++ "{ effc = (fun (type a) (eff : a Effect.t) ->\n"
        ++ indentOf (ind + 2) ++ "match eff with" ++ renderEffcClauses (ind + 2) answer effc
        ++ "\n" ++ indentOf (ind + 2) ++ "| _ -> None) })"
  | .annot e ty => "(" ++ renderExpr ind e ++ " : " ++ renderTy ty ++ ")"
  | .hole note fill => "(* HOLE: " ++ note ++ " *) " ++ renderExpr ind fill
  | .raw t => t

def renderExprs (ind : Nat) : List Expr → List String
  | [] => []
  | e :: rest => renderExpr ind e :: renderExprs ind rest

def renderFields (ind : Nat) : List (String × Expr) → List String
  | [] => []
  | (n, e) :: rest => (n ++ " = " ++ renderExpr ind e) :: renderFields ind rest

def renderLocalBinds (ind : Nat) : List (String × List String × Expr) → List String
  | [] => []
  | (n, ps, b) :: rest =>
      (n ++ (if ps.isEmpty then "" else " " ++ String.intercalate " " ps) ++ " = "
        ++ renderExpr (ind + 1) b) :: renderLocalBinds ind rest

def renderArms (ind : Nat) : List Arm → String
  | [] => ""
  | .mk p g b :: rest =>
      "\n" ++ indentOf ind ++ "| " ++ renderPat p
        ++ (match g with
            | Option.none => ""
            | Option.some ge => " when " ++ renderExpr ind ge)
        ++ " -> " ++ renderExpr (ind + 1) b
        ++ renderArms ind rest

/-- The clauses of the `effc` field of `Effect.Deep.handler` (`effect.ml:66-68`). The
continuation is annotated `(a, answer) Effect.Deep.continuation`, which is what makes the `'c.`
polymorphism of the field check. -/
def renderEffcClauses (ind : Nat) (answer : Ty) : List Effc → String
  | [] => ""
  | .mk name args k body :: rest =>
      -- `a` and not `'a`: the annotation must name the *locally abstract* type the
      -- `(type a)` binder introduced, or the GADT match does not refine it and the clause
      -- bodies are all forced to one answer type.
      "\n" ++ indentOf ind ++ "| " ++ renderPat (.ctor name args) ++ " -> Some (fun ("
        ++ k ++ " : " ++ renderTy (Ty.cont (.named "a") answer) ++ ") -> "
        ++ renderExpr (ind + 1) body ++ ")"
        ++ renderEffcClauses ind answer rest

end

/-! ## Declarations -/

/-- One record field. `isMutable` is the `mutable` keyword, which is how a Lean `structure` field
that the avatar updates in place is spelled. -/
structure Field where
  name : String
  ty : Ty
  isMutable : Bool := false
  /-- A trailing `(* … *)` on the field's own line, when the record is rendered wide. -/
  comment : Option String := Option.none
  /-- Verbatim lines emitted above the field, when the record is rendered wide. A substitute
  field needs one: it has no Lean counterpart, so the only place to say why it exists is here. -/
  leading : List String := []
deriving Repr, Inhabited

/-- One variant constructor: `| C of t1 * t2`. -/
structure Ctor where
  name : String
  args : List Ty := []
  /-- A trailing `(* … *)` on the constructor's own line. -/
  comment : Option String := Option.none
deriving Repr, Inhabited

inductive TyBody where
  | record (fields : List Field)
  | variant (ctors : List Ctor)
  | alias (ty : Ty)
  | abstract
deriving Repr, Inhabited

/-- One `type` declaration. A Lean `structure` becomes a `record`, a Lean `inductive` a
`variant`, and a group of them joined by `and` is a `Decl.types`. -/
structure TypeDecl where
  name : String
  params : List String := []
  body : TyBody
deriving Repr, Inhabited

/-- One `let` binding, possibly a function. -/
structure Bind where
  name : String
  params : List (String × Option Ty) := []
  result : Option Ty := Option.none
  body : Expr

inductive Decl where
  /-- `type a = … and b = …`. -/
  | types (group : List TypeDecl)
  | exn (name : String) (args : List Ty)
  /-- `type _ Effect.t += C : t1 -> t2 -> answer Effect.t`, one entry per constructor. -/
  | effects (ctors : List (String × List Ty × Ty))
  /-- `let [rec] f … and g …`. -/
  | letD (isRec : Bool) (binds : List Bind)
  | ext (name : String) (ty : Ty) (prim : String) (attrs : List String := [])
  | openM (name : String)
  | comment (text : String)
  | rawD (text : String)

private def renderParams : List String → String
  | [] => ""
  | [p] => "'" ++ p ++ " "
  | ps => "(" ++ String.intercalate ", " (ps.map fun p => "'" ++ p) ++ ") "

private def renderField (f : Field) : String :=
  (if f.isMutable then "mutable " else "") ++ f.name ++ " : " ++ renderTy f.ty

private def renderCtor (c : Ctor) : String :=
  "| " ++ c.name
    ++ (if c.args.isEmpty then ""
        else " of " ++ String.intercalate " * " (renderTys c.args))

private def trailing : Option String → String
  | Option.none => ""
  | Option.some t => "  (* " ++ t ++ " *)"

/-- A record or variant with four or more members is laid out one member per line, which is
the shape `workshop/OCaml5/avatar/deep_fibers.ml` is written in; three or fewer stay on one
line. Below the threshold a comment has nowhere to go and is dropped. -/
def wideAt : Nat := 4

private def renderTyBody (b : TyBody) : String :=
  match b with
  | .record fs =>
      if fs.length < wideAt then "{ " ++ String.intercalate "; " (fs.map renderField) ++ " }"
      else
        "{\n" ++ String.join (fs.map fun f =>
          String.join (f.leading.map fun l => "  " ++ l ++ "\n")
            ++ "  " ++ renderField f ++ ";" ++ trailing f.comment ++ "\n") ++ "}"
  | .variant cs =>
      if cs.length < wideAt then
        " " ++ String.intercalate " | " (cs.map fun c =>
          c.name ++ (if c.args.isEmpty then ""
                     else " of " ++ String.intercalate " * " (renderTys c.args)))
      else
        "\n" ++ String.join (cs.map fun c => "  " ++ renderCtor c ++ trailing c.comment ++ "\n")
          |>.dropEnd 1 |>.toString
  | .alias t => renderTy t
  | .abstract => ""

private def renderTypeDecl (d : TypeDecl) : String :=
  renderParams d.params ++ d.name
    ++ (match d.body with
        | .abstract => ""
        -- a variant body starts on its own line, so no space before it
        | .variant cs => " =" ++ renderTyBody (.variant cs)
        | b => " = " ++ renderTyBody b)

private def renderBind (b : Bind) : String :=
  b.name
    ++ String.join (b.params.map fun p =>
         match p.2 with
         | Option.none => " " ++ p.1
         | Option.some t => " (" ++ p.1 ++ " : " ++ renderTy t ++ ")")
    ++ (match b.result with
        | Option.none => ""
        | Option.some t => " : " ++ renderTy t)
    ++ " =\n  " ++ renderExpr 1 b.body

/-- One declaration, as a top-level structure item. -/
def renderDecl : Decl → String
  | .types group =>
      "type " ++ String.intercalate "\nand " (group.map renderTypeDecl)
  | .exn n args =>
      "exception " ++ n
        ++ (if args.isEmpty then ""
            else " of " ++ String.intercalate " * " (renderTys args))
  | .effects ctors =>
      "type _ Effect.t +=\n  "
        ++ String.intercalate "\n  " (ctors.map fun c =>
             "| " ++ c.1 ++ " : "
               ++ String.join ((renderTys c.2.1).map (· ++ " -> "))
               ++ renderTy (Ty.effect c.2.2))
  | .letD isRec binds =>
      "let " ++ (if isRec then "rec " else "")
        ++ String.intercalate "\n\nand " (binds.map renderBind)
  | .ext n ty prim attrs =>
      "external " ++ n ++ " : " ++ renderTy ty ++ " = \"" ++ prim ++ "\""
        ++ String.join (attrs.map fun a => " [@@" ++ a ++ "]")
  | .openM n => "open " ++ n
  | .comment t => "(* " ++ t ++ " *)"
  | .rawD t => t

/-- A whole compilation unit. -/
def moduleText (decls : List Decl) : String :=
  String.join (decls.map fun d => renderDecl d ++ "\n\n")

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
#guard renderTy (.arrow Ty.unit (Ty.list (.con "bucket" [.var "b"]))) == "(unit -> 'b bucket list)"
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
#guard ((renderDecl Deep.enqueueDecl).splitOn ").buckets <- ").length == 2

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
the avatar's carriers rather than let a human retype them. This layer is the description of a
Lean declaration — its name, its field or constructor order, its Lean types — plus the two
mappings that turn one into OCaml: a **name mangling** and a **type substitution**.

The division of labour is deliberate. The renderer owns everything mechanical: order, arity,
mutability, layout, and the names. The substitution table owns the one thing a renderer cannot
decide — which OCaml type stands for a Lean type the avatar does not transcribe (`Exit β ε δ ι α`
is `exitv`, `χ` is `unit`, `Prim` in an answer position is `answer`). That table is one visible
list per module, not a decision scattered through 900 lines of hand-written OCaml.
-/

/-! ## Names

`mangleField` is **total** and **injective**; `unmangleField` is an exhibited left inverse and the
`#guard`s below run it on every field name of the carriers rendered here plus a row of adversarial
ones. The code, character by character:

| source | image |
| --- | --- |
| a lowercase letter or a digit | itself |
| an uppercase `X` | `_` ++ lowercase `X` (this is camelCase → snake_case) |
| `_` | `_0` |
| `'` | `_1` |
| anything else, code `c` | `_2` ++ three decimal digits of `c` |

and a result that is an OCaml keyword, or `exit`, gets one `_` appended. That last step cannot
collide: no image of the character code ends in a bare `_`, because every escape `_` is followed
by a letter or a digit. `exit` → `exit_` is `deep_fibers.ml:194`. -/

/-- The OCaml keywords, plus `exit`: a record field named `exit` is legal, but `f.exit` reads as
`Stdlib.exit` at a glance, and the avatar spells it `exit_`. -/
def reservedNames : List String :=
  ["and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done", "downto",
   "else", "end", "exception", "external", "false", "for", "fun", "function", "functor",
   "if", "in", "include", "inherit", "initializer", "land", "lazy", "let", "lor", "lsl",
   "lsr", "lxor", "match", "method", "mod", "module", "mutable", "new", "nonrec", "object",
   "of", "open", "or", "private", "rec", "sig", "struct", "then", "to", "true", "try",
   "type", "val", "virtual", "when", "while", "with", "exit"]

private def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else if s.length == 2 then "0" ++ s else "00" ++ s

private def encChar (c : Char) : String :=
  if c.isLower || c.isDigit then String.singleton c
  else if c.isUpper then "_" ++ String.singleton (Char.ofNat (c.toNat + 32))
  else if c == '_' then "_0"
  else if c == '\'' then "_1"
  else "_2" ++ pad3 c.toNat

/-- The character code, before the keyword escape. -/
def mangleCore (s : String) : String := s.foldl (init := "") fun acc c => acc ++ encChar c

/-- A Lean field name as an OCaml record label. Total; `unmangleField` is a left inverse. -/
def mangleField (s : String) : String :=
  let e := mangleCore s
  if reservedNames.contains e then e ++ "_" else e

private def decodeAux : List Char → List Char
  | [] => []
  | '_' :: [] => []                                        -- the keyword escape
  | '_' :: '0' :: rest => '_' :: decodeAux rest
  | '_' :: '1' :: rest => '\'' :: decodeAux rest
  | '_' :: '2' :: a :: b :: c :: rest =>
      Char.ofNat (100 * (a.toNat - 48) + 10 * (b.toNat - 48) + (c.toNat - 48))
        :: decodeAux rest
  | '_' :: x :: rest => Char.ofNat (x.toNat - 32) :: decodeAux rest
  | c :: rest => c :: decodeAux rest

/-- The left inverse of `mangleField`. -/
def unmangleField (s : String) : String := String.ofList (decodeAux s.toList)

/-- A Lean type name as an OCaml type name: the same code, minus the leading `_` an initial
capital produces. Injective on names whose first character is an uppercase ASCII letter. -/
def typeName (s : String) : String :=
  let e := mangleCore s
  if e.startsWith "_" then (e.drop 1).toString else e

/-- A Lean constructor name as an OCaml constructor name. With an empty prefix the initial is
capitalised (`resumeAwait` → `ResumeAwait`); with a prefix the prefix supplies the required
capital and the Lean name is kept verbatim (`"C"`, `evaluate` → `Cevaluate`), which is the
scheme `deep_fibers.ml` uses to keep `Cmd` and `RunDecision` from colliding with each other and
with `WithFiberAction`. Injective for a fixed prefix. -/
def ctorName (pfx : String) (s : String) : String :=
  if pfx.isEmpty then
    match s.toList with
    | [] => s
    | c :: rest => String.ofList (Char.ofNat (if c.isLower then c.toNat - 32 else c.toNat) :: rest)
  else pfx ++ s

/-! ## Lean types, and the substitution -/

/-- A Lean type expression, as much of one as the description needs: a head and its arguments. -/
inductive LTy where
  | app (head : String) (args : List LTy)
deriving Repr, Inhabited

namespace LTy
def nm (h : String) : LTy := .app h []
def opt (t : LTy) : LTy := .app "Option" [t]
def lst (t : LTy) : LTy := .app "List" [t]
def nat : LTy := .app "Nat" []
def bool : LTy := .app "Bool" []
def str : LTy := .app "String" []
end LTy

/-- What each Lean type head becomes in OCaml. Keyed on the head only: `Exit β ε δ ι α` and
`Exit β' ε' δ' ι' α'` are both `exitv`, because the avatar is one profile of the family and its
arguments are fixed by the fixture. A head with no entry falls through to `typeName` applied to
its own name, with its arguments lowered — so a carrier that *is* transcribed needs no entry. -/
abbrev Subst := List (String × Ty)

private def substLookup : Subst → String → Option Ty
  | [], _ => Option.none
  | (k, v) :: rest, n => if k == n then Option.some v else substLookup rest n

mutual

def lowerTy (tbl : Subst) : LTy → Ty
  | .app "Nat" [] => Ty.int
  | .app "Bool" [] => Ty.bool
  | .app "String" [] => Ty.string
  | .app "Unit" [] => Ty.unit
  | .app "Option" [t] => Ty.option (lowerTy tbl t)
  | .app "List" [t] => Ty.list (lowerTy tbl t)
  | .app h args =>
      match substLookup tbl h with
      | Option.some t => t
      | Option.none => .con (typeName h) (lowerTys tbl args)

def lowerTys (tbl : Subst) : List LTy → List Ty
  | [] => []
  | t :: rest => lowerTy tbl t :: lowerTys tbl rest

end

/-! ## Structures -/

/-- What becomes of one Lean field. `hole` is A0's request 5: the field is *not* rendered, the
hand-written module supplies it, and `structHoles` names it so a check can insist. -/
inductive FieldKind where
  | keep
  /-- Not rendered. The note says what the avatar must fill in. -/
  | hole (note : String)
  /-- An OCaml field with no Lean counterpart, standing for the holes. -/
  | substitute
deriving Repr, Inhabited

structure FieldDesc where
  leanName : String
  leanTy : LTy
  isMutable : Bool := false
  kind : FieldKind := .keep
  /-- Only for a `substitute`, whose name is not a mangled Lean name. -/
  ocamlName : Option String := Option.none
  comment : Option String := Option.none
  leading : List String := []
deriving Repr, Inhabited

/-- A Lean `structure`, in Lean field order. -/
structure StructDesc where
  leanName : String
  /-- Where it lives, for the generated comment: `"Fibers.lean:157"`. -/
  site : String
  subst : Subst
  fields : List FieldDesc
deriving Repr, Inhabited

def FieldDesc.ocaml (d : FieldDesc) : String :=
  match d.ocamlName with
  | Option.some n => n
  | Option.none => mangleField d.leanName

private def toField (tbl : Subst) (d : FieldDesc) : Field :=
  { name := d.ocaml, ty := lowerTy tbl d.leanTy, isMutable := d.isMutable, comment := d.comment,
    leading := d.leading }

/-- The Lean fields this description refuses to render (request 5). -/
def StructDesc.holes (d : StructDesc) : List (String × String) :=
  d.fields.filterMap fun f =>
    match f.kind with
    | .hole note => Option.some (f.leanName, note)
    | _ => Option.none

/-- The OCaml record: same order, same arity minus the holes, `mutable` where the description
says so, field names mangled. -/
def StructDesc.decl (d : StructDesc) : Decl :=
  .types [{ name := typeName d.leanName,
            body := .record ((d.fields.filter fun f =>
              match f.kind with | .hole _ => false | _ => true).map (toField d.subst)) }]

/-- The comment the generator puts above the record: the Lean site, the field count, and every
hole, so that request 5 is visible in the output and not only in the description. -/
def StructDesc.header (d : StructDesc) : Decl :=
  .comment (s!"`{d.leanName}` (`{d.site}`), {d.fields.length} Lean fields, "
    ++ s!"{(d.fields.filter fun f => match f.kind with | .hole _ => false | _ => true).length}"
    ++ " rendered. Generated by OCaml5.Ml."
    ++ String.join (d.holes.map fun h => s!"\n     HOLE {h.1}: {h.2}"))

/-! ## Inductives -/

structure CtorArg where
  leanName : String
  leanTy : LTy
  /-- Dropped from the OCaml arity. Every use is a divergence and is counted. -/
  erased : Bool := false
deriving Repr, Inhabited

structure CtorDesc where
  leanName : String
  args : List CtorArg := []
  /-- Overrides `ctorName`, for the two names that would collide inside one module. -/
  ocamlName : Option String := Option.none
  comment : Option String := Option.none
deriving Repr, Inhabited

/-- A Lean `inductive`, in Lean constructor order. -/
structure InductiveDesc where
  leanName : String
  site : String
  ctorPrefix : String := ""
  subst : Subst
  ctors : List CtorDesc
deriving Repr, Inhabited

def CtorDesc.ocaml (pfx : String) (c : CtorDesc) : String :=
  match c.ocamlName with
  | Option.some n => n
  | Option.none => ctorName pfx c.leanName

private def toCtor (tbl : Subst) (pfx : String) (c : CtorDesc) : Ctor :=
  { name := CtorDesc.ocaml pfx c,
    args := lowerTys tbl ((c.args.filter fun a => !a.erased).map (·.leanTy)),
    comment := c.comment }

/-- The OCaml variant: same order, arity for arity except where an argument is explicitly
`erased`. -/
def InductiveDesc.decl (d : InductiveDesc) : Decl :=
  .types [{ name := typeName d.leanName,
            body := .variant (d.ctors.map (toCtor d.subst d.ctorPrefix)) }]

/-- The Lean arity of each constructor, and the OCaml one; equal unless an argument is erased. -/
def InductiveDesc.arities (d : InductiveDesc) : List (String × Nat × Nat) :=
  d.ctors.map fun c =>
    (c.leanName, c.args.length, (c.args.filter fun a => !a.erased).length)

/-- Every erasure, as `(constructor, argument, Lean type head)`. -/
def InductiveDesc.erasures (d : InductiveDesc) : List (String × String) :=
  d.ctors.flatMap fun c =>
    (c.args.filter (·.erased)).map fun a => (c.leanName, a.leanName)

def InductiveDesc.header (d : InductiveDesc) : Decl :=
  .comment (s!"`{d.leanName}` (`{d.site}`), {d.ctors.length} constructors"
    ++ (if d.ctorPrefix.isEmpty then "" else s!", prefix `{d.ctorPrefix}`")
    ++ ". Generated by OCaml5.Ml."
    ++ String.join (d.erasures.map fun e => s!"\n     ERASED {e.1}.{e.2}"))

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

Lean threads the machine through pure updates; the avatar mutates a record in place
(`deep_fibers.ml`, DIVERGENCE 3). The rewrite is mechanical on one shape and only on that shape,
which is what makes it checkable:

```
let f = { f with x = v; y = w } in body   ⟶   f.x <- v; f.y <- w; body
let f = { f with g = { f.g with x = v } } in body   ⟶   f.g.x <- v; body
```

with `f` in the declared **linear** set — the names the caller asserts are used linearly, so that
overwriting the old value is unobservable. `mutate` fires only when the `let` rebinds the same
name it updates; anything else is traversed and left alone. When the body is just `f`, the result
is `()`: a Lean function returning the updated record becomes an OCaml procedure whose caller
already holds it.

`residue` is the checker: the `{ … with … }` occurrences the pass did *not* eliminate. A caller
`#guard`s that it is empty, so "the pass applied everywhere" is a fact and not a hope. -/

/-- The nested case: `{ f.g with x = v }` under `{ f with g = … }` targets `f.g`. -/
private def flatten (f : String) : List (String × Expr) → List (String × Expr) × List (String × Expr)
  | [] => ([], [])
  | (g, .recordWith (.field (.var f') g') inner) :: rest =>
      let (flat, nested) := flatten f rest
      if f' == f && g' == g then (flat, inner.map (fun kv => (g ++ "." ++ kv.1, kv.2)) ++ nested)
      else ((g, .recordWith (.field (.var f') g') inner) :: flat, nested)
  | kv :: rest => let (flat, nested) := flatten f rest; (kv :: flat, nested)

private def setPath (f : String) (path : String) (v : Expr) : Expr :=
  match path.splitOn "." with
  | [k] => .setField (.var f) k v
  | [g, k] => .setField (.field (.var f) g) k v
  | _ => .raw ("(* unsupported update path " ++ path ++ " *)")

private def setChainPaths (f : String) (fs : List (String × Expr)) (body : Expr) : Expr :=
  match fs, body with
  | [], _ => body
  -- a trailing `()` is the statement itself; do not sequence it
  | [(k, v)], .unit => setPath f k v
  | [(k, v)], _ => .seq (setPath f k v) body
  | (k, v) :: rest, _ => .seq (setPath f k v) (setChainPaths f rest body)

mutual

/-- The pass. Structural; the only rewrite is the one in the docstring. -/
def mutate (linear : List String) : Expr → Expr
  | .letIn n (.recordWith (.var f) fs) body =>
      let fs' := mutateFields linear fs
      let body' := mutate linear body
      if n == f && linear.contains f then
        let (flat, nested) := flatten f fs'
        let tail := match body with
          | .var b => if b == f then Expr.unit else body'
          | _ => body'
        setChainPaths f (flat ++ nested) tail
      else .letIn n (.recordWith (.var f) fs') body'
  | .letIn n v b => .letIn n (mutate linear v) (mutate linear b)
  | .ctor n args => .ctor n (mutates linear args)
  | .app f args => .app (mutate linear f) (mutates linear args)
  | .binop op l r => .binop op (mutate linear l) (mutate linear r)
  | .fn ps b => .fn ps (mutate linear b)
  | .letRecIn bs b => .letRecIn (mutateBinds linear bs) (mutate linear b)
  | .seq a b => .seq (mutate linear a) (mutate linear b)
  | .ifThen c t e => .ifThen (mutate linear c) (mutate linear t) (mutate linear e)
  | .matchE s arms => .matchE (mutate linear s) (mutateArms linear arms)
  | .tryWith b arms => .tryWith (mutate linear b) (mutateArms linear arms)
  | .record fs => .record (mutateFields linear fs)
  | .recordWith b fs => .recordWith (mutate linear b) (mutateFields linear fs)
  | .field e n => .field (mutate linear e) n
  | .setField e n v => .setField (mutate linear e) n (mutate linear v)
  | .tuple ps => .tuple (mutates linear ps)
  | .listLit xs => .listLit (mutates linear xs)
  | .mkRef e => .mkRef (mutate linear e)
  | .deref e => .deref (mutate linear e)
  | .assign r v => .assign (mutate linear r) (mutate linear v)
  | .raiseE e => .raiseE (mutate linear e)
  | .perform e => .perform (mutate linear e)
  | .continueK k v => .continueK (mutate linear k) (mutate linear v)
  | .discontinueK k e => .discontinueK (mutate linear k) (mutate linear e)
  | .matchWith c a ty rv r ex ef =>
      .matchWith (mutate linear c) (mutate linear a) ty rv (mutate linear r)
        (mutateArms linear ex) (mutateEffc linear ef)
  | .tryWithEff c a ty ef => .tryWithEff (mutate linear c) (mutate linear a) ty (mutateEffc linear ef)
  | .annot e ty => .annot (mutate linear e) ty
  | .hole note fill => .hole note (mutate linear fill)
  | e => e

def mutates (linear : List String) : List Expr → List Expr
  | [] => []
  | e :: rest => mutate linear e :: mutates linear rest

def mutateFields (linear : List String) : List (String × Expr) → List (String × Expr)
  | [] => []
  | (n, e) :: rest => (n, mutate linear e) :: mutateFields linear rest

def mutateBinds (linear : List String) :
    List (String × List String × Expr) → List (String × List String × Expr)
  | [] => []
  | (n, ps, e) :: rest => (n, ps, mutate linear e) :: mutateBinds linear rest

def mutateArms (linear : List String) : List Arm → List Arm
  | [] => []
  | .mk p g b :: rest =>
      .mk p (match g with
             | Option.none => Option.none
             | Option.some ge => Option.some (mutate linear ge))
        (mutate linear b) :: mutateArms linear rest

def mutateEffc (linear : List String) : List Effc → List Effc
  | [] => []
  | .mk n args k b :: rest => .mk n args k (mutate linear b) :: mutateEffc linear rest

end

mutual

/-- Every `{ … with … }` the pass left behind, named by the field it updates. Empty means the
pass fired everywhere. -/
def residue : Expr → List String
  | .recordWith b fs => fs.map (·.1) ++ residue b ++ residueFields fs
  | .letIn _ v b => residue v ++ residue b
  | .ctor _ args => residues args
  | .app f args => residue f ++ residues args
  | .binop _ l r => residue l ++ residue r
  | .fn _ b => residue b
  | .letRecIn bs b => residueBinds bs ++ residue b
  | .seq a b => residue a ++ residue b
  | .ifThen c t e => residue c ++ residue t ++ residue e
  | .matchE s arms => residue s ++ residueArms arms
  | .tryWith b arms => residue b ++ residueArms arms
  | .record fs => residueFields fs
  | .field e _ => residue e
  | .setField e _ v => residue e ++ residue v
  | .tuple ps => residues ps
  | .listLit xs => residues xs
  | .mkRef e => residue e
  | .deref e => residue e
  | .assign r v => residue r ++ residue v
  | .raiseE e => residue e
  | .perform e => residue e
  | .continueK k v => residue k ++ residue v
  | .discontinueK k e => residue k ++ residue e
  | .matchWith c a _ _ r ex ef => residue c ++ residue a ++ residue r ++ residueArms ex
      ++ residueEffc ef
  | .tryWithEff c a _ ef => residue c ++ residue a ++ residueEffc ef
  | .annot e _ => residue e
  | .hole _ fill => residue fill
  | _ => []

def residues : List Expr → List String
  | [] => []
  | e :: rest => residue e ++ residues rest

def residueFields : List (String × Expr) → List String
  | [] => []
  | (_, e) :: rest => residue e ++ residueFields rest

def residueBinds : List (String × List String × Expr) → List String
  | [] => []
  | (_, _, e) :: rest => residue e ++ residueBinds rest

def residueArms : List Arm → List String
  | [] => []
  | .mk _ g b :: rest =>
      (match g with | Option.none => [] | Option.some ge => residue ge) ++ residue b
        ++ residueArms rest

def residueEffc : List Effc → List String
  | [] => []
  | .mk _ _ _ b :: rest => residue b ++ residueEffc rest

end

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

-- Request 1: fifteen Lean fields, in the Lean order, mangled.
-- Fifteen Lean fields plus one substitute: `yielding`, which the avatar carries because
-- `Cmd.loop` has none (DIVERGENCE 2).
#guard Avatar.runFiber.fields.length == 16
#guard (Avatar.runFiber.fields.filter (fun f =>
          match f.kind with | .substitute => false | _ => true)).length == 15
#guard Avatar.runFiber.fields.map (·.ocaml) ==
  ["id", "frame", "running", "parked", "pending", "finalizing", "exit_", "current_op_count",
   "max_ops_before_yield", "prevent_yield", "yield_override", "yielding", "observers",
   "children", "dispatcher", "context"]
#guard (Avatar.runFiber.fields.filter (·.isMutable)).length == 14

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
#guard ((renderDecl Avatar.interruptRecordDecl).splitOn ").frame).interrupted_cause <- ").length
  == 2
#guard ((renderDecl Avatar.interruptRecordDecl).splitOn ").frame).deferred_interrupt <- ").length
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
