import OCaml5.Ml.Profile

/-!
# OCaml5.Ml.Check

Well-formedness of an `OCaml5.Ml.Module`, as decidable predicates with diagnostics, so that a
generated module is **checked before it is printed**.

The surface is untyped and will happily describe a module `ocamlc` rejects (`Syntax`'s
docstring). This module narrows the gap in the one direction a renderer can: it decides the
properties that are properties of the *syntax*, and leaves typing to `ocamlc`. What it decides:

| code | property |
| --- | --- |
| `unbound-value` | an unqualified value name with no binder and no declaration |
| `unbound-ctor` | an unqualified constructor with no declaration |
| `ctor-arity` | a constructor applied to the wrong number of arguments, in an expression or a pattern |
| `undetermined-param` | a type parameter no member of the declaration determines, and no variance annotation makes legal |
| `effc-abstract` | a handler whose answer type mentions `a`, the locally abstract type the `effc` binder introduces |
| `effc-unknown` | an `effc` clause on a constructor that is not a declared effect |
| `reperform-position` | a `reperform` outside tail position, which `ocamlc` refuses |
| `duplicate-field` | a record declaration, literal or pattern that names a label twice |
| `duplicate-ctor` | one variant that declares a constructor name twice |
| `duplicate-type` | one module that declares a type name twice |
| `duplicate-binding` | one `let … and …` group that binds a name twice |
| `bad-name` | a name outside the identifier profile of `OCaml5.Ml.Identifier`, a deriver included |

and, against an `OCaml5.Ml.Profile`, four more (`Check.profile`):

| code | property |
| --- | --- |
| `profile-banned` | a module the profile refuses outright: `Obj`, `Marshal`, `Domain`, … |
| `profile-module` | a qualified name whose module the profile does not admit |
| `profile-value` | an admitted module, an unlisted value of it |
| `profile-construct` | a syntactic form the profile does not admit |

## Two deliberate silences

**Qualified names are not checked.** `M.f` and `Effect.Unhandled` name something in another
compilation unit, and this module has no way to see it. Every check on a name therefore applies
only to unqualified ones. That is a real limit: a typo inside a qualified name reaches `ocamlc`.

**`Expr.raw` is opaque.** Verbatim text is not parsed, so nothing inside it is scoped, counted or
positioned. `rawSites` counts the occurrences, so a module that leans on `raw` can be told
apart from one that does not; a `raw` is not itself a diagnostic.

## The `reperform` rule

`ocamlc` compiles `%reperform` to `Kreperformterm` when its continuation `is_tailcall`, and calls
`fatal_error` otherwise (`bytegen.ml:796-804`). `tailPositions` below is the transcription of
which subterms inherit the polarity, and it is the same table as
`workshop/OCaml5/Compiler.lean`'s `admissibleAt` — the two are separate on purpose. `Compiler`
decides it for `OCaml5.Term`, the untyped machine language of the P5 spike, and imports the
spike's whole effect machinery to do it; this decides it for `Ml.Expr`, and imports nothing.
A package that is to stand on its own cannot depend on a spike's term language, so the notion is
transcribed and the correspondence is stated here rather than shared through an import.

The table, per form, with what `bytegen` does to the continuation:

| form | which subterms inherit | why |
| --- | --- | --- |
| `fun`, `function` body | always tail | a function body is compiled with `Kreturn` (`bytegen.ml:626-635`) |
| `let … in body` | `body`; the value is non-tail | `Llet` (`:636-639`) |
| `a; b` | `b`; `a` is non-tail | `Lsequence` (`:910-911`) |
| `if`, `match` | every branch and arm body; the scrutinee is non-tail | `make_branch` returns the `Kreturn` (`:78-83`) |
| `try b with h` | `h` only; `b` is **non-tail** | `Ltrywith` (`:895-907`) |
| everything else | nothing | `comp_args` pushes each operand |

A structure item's top is not a tail position, so a `let x = reperform …` is refused and a
`let f y = reperform …` is not.
-/

namespace OCaml5.Ml

/-! ## Diagnostics -/

/-- One well-formedness failure. `code` is one of the codes in the module docstring, `site` says
where — a declaration name, a binding name, or a path through the module — and `detail` says
what. All three are strings so that a diagnostic can be compared, sorted and pinned. -/
structure Diag where
  code : String
  site : String
  detail : String
deriving Repr, Inhabited, DecidableEq

/-- `code@site: detail`, for a `#guard` or a console line. -/
def Diag.toLine (d : Diag) : String := d.code ++ "@" ++ d.site ++ ": " ++ d.detail

instance : ToString Diag := ⟨Diag.toLine⟩

/-! ## The environment -/

/-- What a module makes available to its own expressions. Built from the module by
`Env.ofModule`, and extended by every binder as the checker descends. -/
structure Env where
  /-- Value names bound at the top level, plus the prelude, plus everything in scope. -/
  values : List String := []
  /-- Constructor names and their arity. -/
  ctors : List (String × Nat) := []
  /-- Record labels declared anywhere in the module. -/
  fields : List String := []
  /-- Type names declared in the module. -/
  types : List String := []
  /-- The constructors of `Effect.t` the module declares, with their arity. -/
  effects : List (String × Nat) := []
  /-- Set by an `open` or an `include`. Inside such a scope another compilation unit's
  unqualified names are visible and this module cannot see them, so `unbound-value` reporting is
  switched off rather than made to lie. It is the price of `open`, and it is why a generator
  that wants the check should qualify instead. -/
  openScope : Bool := false
deriving Repr, Inhabited

namespace Env

/-- The `Stdlib` names a generated module may use without declaring them. Deliberately short:
this is not a model of the standard library, it is the set a generator actually emits. Anything
else must be spelled qualified, which is not checked. -/
def preludeValues : List String :=
  ["ignore", "raise", "failwith", "invalid_arg", "ref", "not", "fst", "snd", "incr", "decr",
   "print_string", "print_endline", "print_newline", "print_int", "prerr_endline",
   "string_of_int", "int_of_string", "string_of_float", "float_of_int", "string_of_bool",
   "compare", "min", "max", "abs", "succ", "pred", "exit", "at_exit", "read_line",
   "char_of_int", "int_of_char", "fst", "snd"]

/-- The constructors every OCaml program has: the built-in data constructors and the exceptions
the runtime raises. -/
def preludeCtors : List (String × Nat) :=
  [("()", 0), ("true", 0), ("false", 0), ("[]", 0), ("::", 2), ("None", 0), ("Some", 1),
   ("Not_found", 0), ("Exit", 0), ("Failure", 1), ("Invalid_argument", 1), ("Sys_error", 1),
   ("Out_of_memory", 0), ("Stack_overflow", 0), ("Division_by_zero", 0), ("End_of_file", 0),
   ("Assert_failure", 1), ("Match_failure", 1), ("Undefined_recursive_module", 1)]

/-- A name that carries a `.` refers to another compilation unit and is not checked. -/
def isQualifiedName (n : String) : Bool := (n.splitOn ".").length > 1

/-- Add a value name. -/
def withValue (e : Env) (n : String) : Env := { e with values := n :: e.values }
/-- Add several. -/
def withValues (e : Env) (ns : List String) : Env := { e with values := ns ++ e.values }

def knowsValue (e : Env) (n : String) : Bool :=
  e.openScope || n == "_" || isQualifiedName n || e.values.contains n
    || preludeValues.contains n

/-- Enter the scope of an `open` or an `include`. -/
def opened (e : Env) : Env := { e with openScope := true }

private def lookupArity : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (k, v) :: rest, n => if k == n then some v else lookupArity rest n

/-- The declared arity of a constructor, or `none` when it is not declared here. -/
def ctorArity (e : Env) (n : String) : Option Nat :=
  match lookupArity e.ctors n with
  | some a => some a
  | none => match lookupArity e.effects n with
            | some a => some a
            | none => lookupArity preludeCtors n

def knowsCtor (e : Env) (n : String) : Bool :=
  isQualifiedName n || (e.ctorArity n).isSome

end Env

/-! ## Collecting declarations -/

private def ctorArityOf (c : Ctor) : Nat :=
  match c.inlineRecord with
  | some _ => 1
  | none => c.args.length

private def fieldsOfBody : TyBody → List String
  | .record fs => fs.map (·.name)
  | .variant cs => cs.flatMap fun c =>
      match c.inlineRecord with | some fs => fs.map (·.name) | none => []
  | _ => []

private def ctorsOfBody : TyBody → List (String × Nat)
  | .variant cs => cs.map fun c => (c.name, ctorArityOf c)
  | _ => []

mutual
private def bindNamesOfPat : Pat → List String
  | .wild => []
  | .var n => [n]
  | .int _ => []
  | .str _ => []
  | .char _ => []
  | .float _ => []
  | .ctor _ args => bindNamesOfPats args
  | .record fs => bindNamesOfPatFields fs
  | .recordOpen fs => bindNamesOfPatFields fs
  | .tuple ps => bindNamesOfPats ps
  | .listPat ps => bindNamesOfPats ps
  | .cons a b => bindNamesOfPat a ++ bindNamesOfPat b
  | .alias p n => n :: bindNamesOfPat p
  -- an or-pattern binds the same names on both sides, so one side suffices
  | .orPat a _ => bindNamesOfPat a
  | .constrained p _ => bindNamesOfPat p
  | .exnPat p => bindNamesOfPat p
  | .polyPat _ (some p) => bindNamesOfPat p
  | .polyPat _ none => []
  | .lazyPat p => bindNamesOfPat p

private def bindNamesOfPats : List Pat → List String
  | [] => []
  | p :: rest => bindNamesOfPat p ++ bindNamesOfPats rest

private def bindNamesOfPatFields : List (String × Pat) → List String
  | [] => []
  | (_, p) :: rest => bindNamesOfPat p ++ bindNamesOfPatFields rest
end

/-- The names a pattern binds, in the order they occur. -/
def patVars (p : Pat) : List String := bindNamesOfPat p

private def declaredIn : Decl → Env → Env
  | .types group, e =>
      group.foldl (init := e) fun acc d =>
        -- `[@@deriving …]` writes functions into this unit; the checker knows which
        -- (`Profile.derivedNames`), so a generated call to `compare_run_fiber` is in scope
        -- without anyone declaring it.
        { acc with types := d.name :: acc.types,
                   ctors := ctorsOfBody d.body ++ acc.ctors,
                   fields := fieldsOfBody d.body ++ acc.fields,
                   values := derivedNames d.name d.derivers ++ acc.values }
  | .exn n args, e => { e with ctors := (n, args.length) :: e.ctors }
  | .effects ctors, e =>
      { e with effects := ctors.map (fun c => (c.1, c.2.1.length)) ++ e.effects }
  | .typeExt _ _ cs _, e =>
      { e with effects := cs.map (fun c => (c.name, ctorArityOf c)) ++ e.effects,
               ctors := cs.map (fun c => (c.name, ctorArityOf c)) ++ e.ctors }
  | .letD _ binds, e => { e with values := binds.map (·.name) ++ e.values }
  | .letPatD p _, e => { e with values := patVars p ++ e.values }
  | .ext n _ _ _, e => { e with values := n :: e.values }
  | .attrD _ d, e => declaredIn d e
  | .moduleD n _ _ _, e => { e with types := n :: e.types }
  | .moduleAliasD n _, e => { e with types := n :: e.types }
  | _, e => e

/-- Everything a module declares, plus nothing else: `Env.preludeValues` and
`Env.preludeCtors` are consulted separately, so a module's own declarations are visible here. -/
def Env.ofModule (m : Module) : Env := m.items.foldl (fun e d => declaredIn d e) {}

/-! ## Tail positions -/

/-- Whether an expression sits where `ocamlc` compiles a tail call. -/
inductive TailPosition where
  | tail
  | nonTail
deriving Repr, Inhabited, DecidableEq

/-! ## The checker -/

private def dupesAux : List String → List String → List String → List String
  | [], _, bad => bad.reverse
  | n :: rest, seen, bad =>
      if seen.contains n && !bad.contains n then dupesAux rest (n :: seen) (n :: bad)
      else dupesAux rest (n :: seen) bad

/-- The names that occur more than once, each once, in first-duplicate order. -/
private def dupes (ns : List String) : List String := dupesAux ns [] []

private def dup (code site : String) (ns : List String) : List Diag :=
  (dupes ns).map fun n => { code := code, site := site, detail := "`" ++ n ++ "` twice" }

private def badName (site kind : String) (ok : String → Bool) (n : String) : List Diag :=
  if ok n then [] else [{ code := "bad-name", site := site, detail := kind ++ " `" ++ n ++ "`" }]

/-- A constructor is declared, and applied at its arity. A qualified name is not checked: it
names something in another compilation unit. -/
def checkCtorUse (env : Env) (site : String) (n : String) (given : Nat) : List Diag :=
  if Env.isQualifiedName n then []
  else
    match Env.ctorArity env n with
    | none => [{ code := "unbound-ctor", site := site, detail := "`" ++ n ++ "`" }]
    | some want =>
        if want == given then []
        else [{ code := "ctor-arity", site := site,
                detail := "`" ++ n ++ "` takes " ++ toString want ++ ", given "
                            ++ toString given }]

/-- The `effc` rule. `renderEffcClauses` emits `fun (type a) (eff : a Effect.t)` and annotates
the continuation `(a, answer) Effect.Deep.continuation`, where `a` is the **locally abstract**
type the binder introduced. If the answer type itself mentions `a` — as a variable `'a` or as a
constructor `a` — the two are confused, the GADT match no longer refines the clause bodies, and
every clause is forced to one answer type. The renderer cannot rename the binder without
changing every clause, so the rule is on the answer type, and it is checked. -/
def checkAnswer (site : String) (answer : Ty) : List Diag :=
  if Ty.mentionsVar "a" answer || Ty.mentionsCon "a" answer then
    [{ code := "effc-abstract", site := site,
       detail := "the answer type mentions `a`, which is the locally abstract type of the "
                   ++ "`effc` binder" }]
  else []

mutual

/-- Every failure in one expression, at scope `env` and tail position `tp`. -/
def checkExpr (env : Env) (site : String) (tp : TailPosition) : Expr → List Diag
  | .var n =>
      if env.knowsValue n then []
      else [{ code := "unbound-value", site := site, detail := "`" ++ n ++ "`" }]
  | .int _ => []
  | .str _ => []
  | .bool _ => []
  | .unit => []
  | .char _ => []
  | .float _ => []
  | .intOf _ => []
  | .raw _ => []
  | .ctor n args =>
      checkCtorUse env site n args.length ++ checkExprsN env site args
  | .polyCtor _ a => checkExprOpt env site a
  | .app f args => checkExpr env site .nonTail f ++ checkExprsN env site args
  | .appL f args => checkExpr env site .nonTail f ++ checkLabelled env site args
  | .binop _ l r => checkExpr env site .nonTail l ++ checkExpr env site .nonTail r
  | .fn ps b => checkExpr (env.withValues ps) site .tail b
  | .lam ps b =>
      checkParams env site ps ++ checkExpr (env.withValues (paramVars ps)) site .tail b
  | .functionE arms => checkArms env site tp arms
  | .letIn n v b => checkExpr env site .nonTail v ++ checkExpr (env.withValue n) site tp b
  | .letPat p v b =>
      checkPat env site p ++ checkExpr env site .nonTail v
        ++ checkExpr (env.withValues (patVars p)) site tp b
  | .letRecIn bs b =>
      let names := bs.map (·.1)
      let inner := env.withValues names
      dup "duplicate-binding" site names
        ++ checkLocalBinds inner site bs
        ++ checkExpr inner site tp b
  | .openIn _ b => checkExpr env.opened site tp b
  | .seq a b => checkExpr env site .nonTail a ++ checkExpr env site tp b
  | .ifThen c t f =>
      checkExpr env site .nonTail c ++ checkExpr env site tp t ++ checkExpr env site tp f
  | .ifThenOnly c t => checkExpr env site .nonTail c ++ checkExpr env site tp t
  | .whileE c b => checkExpr env site .nonTail c ++ checkExpr env site .nonTail b
  | .forE n lo hi _ b =>
      checkExpr env site .nonTail lo ++ checkExpr env site .nonTail hi
        ++ checkExpr (env.withValue n) site .nonTail b
  | .matchE s arms => checkExpr env site .nonTail s ++ checkArms env site tp arms
  | .tryWith b arms => checkExpr env site .nonTail b ++ checkArms env site tp arms
  | .record fs =>
      dup "duplicate-field" site (fs.map (·.1)) ++ checkFields env site fs
  | .recordWith b fs =>
      checkExpr env site .nonTail b ++ dup "duplicate-field" site (fs.map (·.1))
        ++ checkFields env site fs
  | .field e _ => checkExpr env site .nonTail e
  | .setField e _ v => checkExpr env site .nonTail e ++ checkExpr env site .nonTail v
  | .tuple ps => checkExprsN env site ps
  | .listLit xs => checkExprsN env site xs
  | .arrayLit xs => checkExprsN env site xs
  | .arrayGet a i => checkExpr env site .nonTail a ++ checkExpr env site .nonTail i
  | .arraySet a i v =>
      checkExpr env site .nonTail a ++ checkExpr env site .nonTail i ++ checkExpr env site .nonTail v
  | .mkRef e => checkExpr env site .nonTail e
  | .deref e => checkExpr env site .nonTail e
  | .raiseE e => checkExpr env site .nonTail e
  | .assertE e => checkExpr env site .nonTail e
  | .lazyE e => checkExpr env site .nonTail e
  | .perform e => checkExpr env site .nonTail e
  | .assign r v => checkExpr env site .nonTail r ++ checkExpr env site .nonTail v
  | .continueK k v => checkExpr env site .nonTail k ++ checkExpr env site .nonTail v
  | .discontinueK k e => checkExpr env site .nonTail k ++ checkExpr env site .nonTail e
  | .shallowContinue k v h =>
      checkExpr env site .nonTail k ++ checkExpr env site .nonTail v ++ checkExpr env site .nonTail h
  | .shallowDiscontinue k e h =>
      checkExpr env site .nonTail k ++ checkExpr env site .nonTail e ++ checkExpr env site .nonTail h
  -- the one form whose position matters: `bytegen.ml:796-804`.
  | .reperform e k l =>
      (match tp with
       | .tail => []
       | .nonTail =>
           [{ code := "reperform-position", site := site,
              detail := "outside tail position; ocamlc refuses it (bytegen.ml:796-804)" }])
        ++ checkExpr env site .nonTail e ++ checkExpr env site .nonTail k ++ checkExpr env site .nonTail l
  | .matchWith comp arg answer retcVar retc exnc effc =>
      checkExpr env site .nonTail comp ++ checkExpr env site .nonTail arg
        ++ checkAnswer site answer
        ++ checkExpr (env.withValue retcVar) site .nonTail retc
        ++ checkArms env site .nonTail exnc
        ++ checkEffc env site effc
  | .tryWithEff comp arg answer effc =>
      checkExpr env site .nonTail comp ++ checkExpr env site .nonTail arg
        ++ checkAnswer site answer ++ checkEffc env site effc
  | .matchWithK _ comp arg h =>
      checkExpr env site .nonTail comp ++ checkExpr env site .nonTail arg ++ checkExpr env site .nonTail h
  | .handler _ answer retc exnc effc =>
      checkAnswer site answer
        ++ (match retc with
            | none => []
            | some (v, r) => checkExpr (env.withValue v) site .nonTail r)
        ++ checkArms env site .nonTail exnc ++ checkEffc env site effc
  | .annot e _ => checkExpr env site tp e
  | .hole _ fill => checkExpr env site tp fill

def checkExprsN (env : Env) (site : String) : List Expr → List Diag
  | [] => []
  | e :: rest => checkExpr env site .nonTail e ++ checkExprsN env site rest

def checkLabelled (env : Env) (site : String) : List (ArgLabel × Expr) → List Diag
  | [] => []
  | (_, e) :: rest => checkExpr env site .nonTail e ++ checkLabelled env site rest

def checkExprOpt (env : Env) (site : String) : Option Expr → List Diag
  | none => []
  | some e => checkExpr env site .nonTail e

def checkFields (env : Env) (site : String) : List (String × Expr) → List Diag
  | [] => []
  | (_, e) :: rest => checkExpr env site .nonTail e ++ checkFields env site rest

def checkLocalBinds (env : Env) (site : String) :
    List (String × List String × Expr) → List Diag
  | [] => []
  | (_, ps, b) :: rest =>
      checkExpr (env.withValues ps) site .tail b ++ checkLocalBinds env site rest

/-- Arm bodies inherit the polarity of the `match` (`make_branch`, `bytegen.ml:78-83`). -/
def checkArms (env : Env) (site : String) (tp : TailPosition) : List Arm → List Diag
  | [] => []
  | .mk p g b :: rest =>
      let inner := env.withValues (patVars p)
      checkPat env site p
        ++ (match g with | none => [] | some ge => checkExpr inner site .nonTail ge)
        ++ checkExpr inner site tp b
        ++ checkArms env site tp rest

/-- An `effc` clause names a declared effect constructor, at its declared arity, and its body
sits under `Some (fun k -> …)` — a function body, hence a tail position. -/
def checkEffc (env : Env) (site : String) : List Effc → List Diag
  | [] => []
  | .mk name args k body :: rest =>
      let known := (Env.isQualifiedName name) ||
        ((env.effects.filter (fun c => c.1 == name)).length > 0)
      let arityDiag :=
        match Env.ctorArity env name with
        | some n => if n == args.length then []
                    else [{ code := "ctor-arity", site := site,
                            detail := "`" ++ name ++ "` takes " ++ toString n ++ ", given "
                                        ++ toString args.length }]
        | none => []
      (if known then [] else
        [{ code := "effc-unknown", site := site,
           detail := "`" ++ name ++ "` is not a declared effect constructor" }])
        ++ arityDiag
        ++ checkPats env site args
        ++ checkExpr ((env.withValues (args.flatMap patVars)).withValue k) site .tail body
        ++ checkEffc env site rest

def checkParams (env : Env) (site : String) : List Param → List Diag
  | [] => []
  | .mk _ p _ d :: rest =>
      checkPat env site p
        ++ (match d with | none => [] | some e => checkExpr env site .nonTail e)
        ++ checkParams env site rest

/-- Constructor existence and arity in a pattern, plus duplicate record labels. -/
def checkPat (env : Env) (site : String) : Pat → List Diag
  | .wild => []
  | .var _ => []
  | .int _ => []
  | .str _ => []
  | .char _ => []
  | .float _ => []
  | .ctor n args => checkCtorUse env site n args.length ++ checkPats env site args
  | .record fs =>
      dup "duplicate-field" site (fs.map (·.1)) ++ checkPatFields env site fs
  | .recordOpen fs =>
      dup "duplicate-field" site (fs.map (·.1)) ++ checkPatFields env site fs
  | .tuple ps => checkPats env site ps
  | .listPat ps => checkPats env site ps
  | .cons a b => checkPat env site a ++ checkPat env site b
  | .alias p _ => checkPat env site p
  | .orPat a b => checkPat env site a ++ checkPat env site b
  | .constrained p _ => checkPat env site p
  | .exnPat p => checkPat env site p
  | .polyPat _ (some p) => checkPat env site p
  | .polyPat _ none => []
  | .lazyPat p => checkPat env site p

def checkPats (env : Env) (site : String) : List Pat → List Diag
  | [] => []
  | p :: rest => checkPat env site p ++ checkPats env site rest

def checkPatFields (env : Env) (site : String) : List (String × Pat) → List Diag
  | [] => []
  | (_, p) :: rest => checkPat env site p ++ checkPatFields env site rest

/-- The names a parameter list binds. -/
def paramVars : List Param → List String
  | [] => []
  | .mk _ p _ _ :: rest => patVars p ++ paramVars rest

end

/-- The checker at a non-tail position: an operand. -/
def checkExprN (env : Env) (site : String) (e : Expr) : List Diag :=
  checkExpr env site .nonTail e


/-! ## Declarations -/

private def tysOfField (f : Field) : List Ty := [f.ty]

private def tysOfCtor (c : Ctor) : List Ty :=
  c.args ++ (match c.result with | none => [] | some t => [t])
    ++ (match c.inlineRecord with | none => [] | some fs => fs.map (·.ty))

private def tysOfBody : TyBody → List Ty
  | .record fs => fs.flatMap tysOfField
  | .variant cs => cs.flatMap tysOfCtor
  | .alias t => [t]
  | .abstract => []
  | .extensible => []

/-- A parameter no member determines is rejected by OCaml unless a variance annotation makes it
legal (§11.6). Three declarations are exempt: an abstract one and an extensible one determine
nothing and are always legal, and a **GADT** — a variant any of whose constructors carries its
own `result` type — determines its parameters by the constructors' return indices, which is the
whole point of the form (§9.9). -/
private def checkTypeDecl (d : TypeDecl) : List Diag :=
  let site := d.name
  let exempt := match d.body with
    | .abstract => true
    | .extensible => true
    | .variant cs => cs.any (fun c => c.result.isSome)
    | _ => false
  let tys := tysOfBody d.body
  let annotated := d.tparams.filter (fun p =>
    p.injective || (match p.variance with | .invariant => false | _ => true))
  let names :=
    if d.tparams.isEmpty then d.params else d.tparams.map (·.name)
  let undetermined :=
    if exempt then []
    else names.filter fun n =>
      !(tys.any (Ty.mentionsVar n)) && !(annotated.any (fun p => p.name == n))
  badName site "type name" isLowerIdent d.name
    ++ d.derivers.flatMap (badName site "deriver" isLowerIdent)
    ++ dup "duplicate-ctor" site
        (match d.body with | .variant cs => cs.map (·.name) | _ => [])
    ++ dup "duplicate-field" site
        (match d.body with | .record fs => fs.map (·.name) | _ => [])
    ++ (match d.body with
        | .variant cs => cs.flatMap fun c => badName site "constructor" isUpperIdent c.name
        | .record fs => fs.flatMap fun f => badName site "field" isLowerIdent f.name
        | _ => [])
    ++ undetermined.map fun n =>
        { code := "undetermined-param", site := site,
          detail := "`'" ++ n ++ "` is determined by no member and carries no variance" }

mutual

/-- Every failure in one structure item. -/
private def checkDecl (env : Env) : Decl → List Diag
  | .types group =>
      dup "duplicate-type" "module" (group.map (·.name)) ++ group.flatMap checkTypeDecl
  | .exn n _ => badName n "exception" isUpperIdent n
  | .effects ctors =>
      dup "duplicate-ctor" "effects" (ctors.map (·.1))
        ++ ctors.flatMap fun c => badName "effects" "effect constructor" isUpperIdent c.1
  | .letD _ binds =>
      dup "duplicate-binding" "let" (binds.map (·.name))
        ++ binds.flatMap fun b =>
             let inner :=
               (env.withValues (b.params.map (·.1))).withValues (paramVars b.lparams)
             -- A binding with parameters is a function, so its body is a tail position; a
             -- binding without is a structure item, and a structure item's top is not.
             let tp := if b.params.isEmpty && b.lparams.isEmpty then
                         TailPosition.nonTail else TailPosition.tail
             (if b.name == "()" || b.name == "_" then []
              else badName b.name "value name" isLowerIdent b.name)
               ++ checkExpr inner b.name tp b.body
  | .letPatD p v => checkPat env "let-pattern" p ++ checkExprN env "let-pattern" v
  | .ext n _ _ _ => badName n "external" isLowerIdent n
  | .openM n => badName n "module path" isModulePath n
  | .typeExt path _ cs _ =>
      dup "duplicate-ctor" path (cs.map (·.name))
        ++ cs.flatMap fun c => badName path "constructor" isUpperIdent c.name
  | .moduleD n _ _ body =>
      let inner := body.foldl (fun e d => declaredIn d e) env
      let inner := if body.any (fun d => match d with
                                         | .includeD _ => true
                                         | .openM _ => true
                                         | _ => false) then inner.opened else inner
      badName n "module name" isUpperIdent n ++ checkDecls inner body
  | .moduleAliasD n _ => badName n "module name" isUpperIdent n
  | .moduleTypeD n _ => badName n "module type name" isUpperIdent n
  | .attrD _ d => checkDecl env d
  | _ => []

private def checkDecls (env : Env) : List Decl → List Diag
  | [] => []
  | d :: rest => checkDecl env d ++ checkDecls env rest

end

/-- Every well-formedness failure in a module, in declaration order. Empty means the module
passes every check this file can decide; it does **not** mean `ocamlc` accepts it. -/
def checkModule (m : Module) : List Diag :=
  let env0 := Env.ofModule m
  let env := if m.items.any (fun d => match d with
                                      | .includeD _ => true
                                      | .openM _ => true
                                      | _ => false) then env0.opened else env0
  dup "duplicate-type" "module" env.types.reverse
    ++ checkDecls env m.items

/-- The module passes every decidable check. -/
def Module.wf (m : Module) : Bool := (checkModule m).isEmpty

/-- The proposition, for a `#guard`-free statement. Decidable because `Diag` has
`DecidableEq`. -/
def WellFormed (m : Module) : Prop := checkModule m = []

instance (m : Module) : Decidable (WellFormed m) :=
  inferInstanceAs (Decidable (checkModule m = []))

/-- Every diagnostic as one line, for a console. -/
def checkReport (m : Module) : String :=
  String.intercalate "\n" ((checkModule m).map Diag.toLine)

/-! ## Raw text, counted rather than checked -/

mutual
private def rawInExpr : Expr → Nat
  | .raw _ => 1
  | .ctor _ args => rawInExprs args
  | .app f args => rawInExpr f + rawInExprs args
  | .appL f args => rawInExpr f + rawInLabelled args
  | .binop _ l r => rawInExpr l + rawInExpr r
  | .fn _ b => rawInExpr b
  | .lam _ b => rawInExpr b
  | .functionE arms => rawInArms arms
  | .letIn _ v b => rawInExpr v + rawInExpr b
  | .letPat _ v b => rawInExpr v + rawInExpr b
  | .letRecIn bs b => rawInBinds bs + rawInExpr b
  | .openIn _ b => rawInExpr b
  | .seq a b => rawInExpr a + rawInExpr b
  | .ifThen c t e => rawInExpr c + rawInExpr t + rawInExpr e
  | .ifThenOnly c t => rawInExpr c + rawInExpr t
  | .whileE c b => rawInExpr c + rawInExpr b
  | .forE _ lo hi _ b => rawInExpr lo + rawInExpr hi + rawInExpr b
  | .matchE s arms => rawInExpr s + rawInArms arms
  | .tryWith b arms => rawInExpr b + rawInArms arms
  | .record fs => rawInFields fs
  | .recordWith b fs => rawInExpr b + rawInFields fs
  | .field e _ => rawInExpr e
  | .setField e _ v => rawInExpr e + rawInExpr v
  | .tuple ps => rawInExprs ps
  | .listLit xs => rawInExprs xs
  | .arrayLit xs => rawInExprs xs
  | .arrayGet a i => rawInExpr a + rawInExpr i
  | .arraySet a i v => rawInExpr a + rawInExpr i + rawInExpr v
  | .mkRef e => rawInExpr e
  | .deref e => rawInExpr e
  | .raiseE e => rawInExpr e
  | .assertE e => rawInExpr e
  | .lazyE e => rawInExpr e
  | .perform e => rawInExpr e
  | .annot e _ => rawInExpr e
  | .assign r v => rawInExpr r + rawInExpr v
  | .continueK k v => rawInExpr k + rawInExpr v
  | .discontinueK k e => rawInExpr k + rawInExpr e
  | .shallowContinue k v h => rawInExpr k + rawInExpr v + rawInExpr h
  | .shallowDiscontinue k e h => rawInExpr k + rawInExpr e + rawInExpr h
  | .reperform e k l => rawInExpr e + rawInExpr k + rawInExpr l
  | .matchWith c a _ _ r ex ef => rawInExpr c + rawInExpr a + rawInExpr r + rawInArms ex
      + rawInEffc ef
  | .tryWithEff c a _ ef => rawInExpr c + rawInExpr a + rawInEffc ef
  | .matchWithK _ c a h => rawInExpr c + rawInExpr a + rawInExpr h
  | .handler _ _ retc ex ef =>
      (match retc with | none => 0 | some (_, r) => rawInExpr r) + rawInArms ex + rawInEffc ef
  | .hole _ fill => rawInExpr fill
  | _ => 0

private def rawInLabelled : List (ArgLabel × Expr) → Nat
  | [] => 0
  | (_, e) :: rest => rawInExpr e + rawInLabelled rest
private def rawInExprs : List Expr → Nat
  | [] => 0
  | e :: rest => rawInExpr e + rawInExprs rest
private def rawInFields : List (String × Expr) → Nat
  | [] => 0
  | (_, e) :: rest => rawInExpr e + rawInFields rest
private def rawInBinds : List (String × List String × Expr) → Nat
  | [] => 0
  | (_, _, e) :: rest => rawInExpr e + rawInBinds rest
private def rawInArms : List Arm → Nat
  | [] => 0
  | .mk _ g b :: rest =>
      (match g with | none => 0 | some ge => rawInExpr ge) + rawInExpr b + rawInArms rest
private def rawInEffc : List Effc → Nat
  | [] => 0
  | .mk _ _ _ b :: rest => rawInExpr b + rawInEffc rest
end

/-- How many `Expr.raw` and `Decl.rawD` occurrences a module leans on: the part of it the
checker cannot see. -/
def rawSites (m : Module) : Nat :=
  m.items.foldl (init := 0) fun acc d =>
    acc + (match d with
           | .rawD _ => 1
           | .letD _ binds => binds.foldl (fun a b => a + rawInExpr b.body) 0
           | .letPatD _ v => rawInExpr v
           | _ => 0)

/-! ## The profile check

`OCaml5.Ml.Profile` says which constructs and which library values are representable in the Lean
model. `Check.profile` decides membership, and `Check.lawReport` says which of the profile's
named laws a module has come to depend on — the list seat W4 is proving under
`workshop/OCaml5/Lib/`. -/

namespace Check

private def bannedReason (p : Profile) (path : String) : Option String :=
  (p.banned.find? (fun b => b.1 == path || path.startsWith (b.1 ++ "."))).map (·.2)

/-- One qualified name, judged against the profile. The module prefix is tried longest-first —
`Base.Map.find` is `Base.Map`'s `find`, not `Base`'s `Map.find` — and a name whose prefix is not
an admitted module is reported once for its whole path. -/
private def judgePath (p : Profile) (kind : String) (n : String) : List Diag :=
  match splitPath n with
  | none => []
  | some (modPath, last) =>
      match bannedReason p modPath with
      | some why =>
          [{ code := "profile-banned", site := n, detail := "`" ++ modPath ++ "`: " ++ why }]
      | none =>
        match Profile.moduleOf p modPath with
        | none =>
            [{ code := "profile-module", site := n,
               detail := "`" ++ modPath ++ "` is not an admitted module of profile `"
                           ++ p.name ++ "`" }]
        | some m =>
            if kind == "value" then
              if (m.values.map (·.name)).contains last then []
              else [{ code := "profile-value", site := n,
                      detail := "`" ++ modPath ++ "` admits no value `" ++ last ++ "`" }]
            else if kind == "type" then
              if m.types.contains last then []
              else [{ code := "profile-value", site := n,
                      detail := "`" ++ modPath ++ "` admits no type `" ++ last ++ "`" }]
            else []

/-- Every place a module steps outside its profile: a banned module, an unadmitted module, an
unlisted value of an admitted one, or a construct the profile does not admit.

Constructor paths are judged as modules only: a constructor of an admitted module (`Effect.Deep`'s
own, `Sexplib0.Sexp.Atom`) is admitted without being listed, because a variant's constructors are
its type's and the type is already listed. -/
def profile (p : Profile) (m : Module) : List Diag :=
  let u := usageOf m
  u.valuePaths.flatMap (judgePath p "value")
    ++ u.typePaths.flatMap (judgePath p "type")
    ++ u.ctorPaths.flatMap (judgePath p "ctor")
    ++ u.modulePaths.flatMap (fun n =>
         match bannedReason p n with
         | some why => [{ code := "profile-banned", site := n,
                          detail := "`" ++ n ++ "`: " ++ why }]
         | none =>
             if (Profile.moduleOf p n).isSome then []
             else [{ code := "profile-module", site := n,
                     detail := "`" ++ n ++ "` is not an admitted module of profile `"
                                 ++ p.name ++ "`" }])
    ++ (u.forms.filter (fun f => !p.constructs.contains f)).map (fun f =>
         { code := "profile-construct", site := m.name,
           detail := "`" ++ f ++ "` is not an admitted construct of profile `" ++ p.name ++ "`" })

/-- The module is inside its profile. -/
def inProfile (p : Profile) (m : Module) : Bool := (profile p m).isEmpty

/-- The **named laws this module has come to depend on**, in profile order: every law of every
admitted library value the module actually names. This is the list seat W4 is proving; a name
here is stable whether or not it is yet a theorem. -/
def lawsUsed (p : Profile) (m : Module) : List String :=
  let u := usageOf m
  (u.valuePaths.flatMap fun n =>
     match splitPath n with
     | none => []
     | some (modPath, last) =>
         match Profile.moduleOf p modPath with
         | none => []
         | some lm =>
             (lm.values.filter (fun v => v.name == last)).flatMap (·.lawNames)).eraseDups

/-- One line per law the module depends on: its name, whether it is proved, and where. -/
def lawReport (p : Profile) (m : Module) : List String :=
  (lawsUsed p m).map fun n =>
    match lawOf n with
    | none => n ++ "  UNKNOWN LAW"
    | some l =>
        match l.site with
        | none => n ++ "  unproven — " ++ l.statement
        | some site => n ++ "  proved at " ++ site

end Check

end OCaml5.Ml
