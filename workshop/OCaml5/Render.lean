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
deriving Repr, Inhabited

/-- One variant constructor: `| C of t1 * t2`. -/
structure Ctor where
  name : String
  args : List Ty := []
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

private def renderTyBody (b : TyBody) : String :=
  match b with
  | .record fs => "{ " ++ String.intercalate "; " (fs.map renderField) ++ " }"
  | .variant cs => "\n  " ++ String.intercalate "\n  " (cs.map renderCtor)
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

#guard renderDecl Deep.parkedDecl ==
  "type parked =\n  | NotParked\n  | WithGuard of int"

#guard renderDecl Deep.stuckDecl == "exception Stuck_unknown_fiber of fiber_id"

#guard renderDecl Deep.effectsDecl ==
  "type _ Effect.t +=\n  | Fork : (unit -> unit) -> fiber_id Effect.t\n"
    ++ "  | Yield : unit Effect.t\n  | Await : fiber_id -> int Effect.t"

-- A record with `mutable` fields, and a mutually recursive `and` group.
#guard renderDecl Deep.runFiberDecl ==
  "type ('nu, 'b) run_fiber = { id : fiber_id; mutable running : bool; mutable parked : parked;"
    ++ " mutable pending : ('nu, 'b) pending list; mutable exit : 'b option;"
    ++ " mutable observers : observer list; mutable children : fiber_id list;"
    ++ " dispatcher : 'b dispatcher }"

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

end Ml
end OCaml5
