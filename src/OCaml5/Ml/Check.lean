import OCaml5.Ml.Syntax
import OCaml5.Ml.Fold

/-!
# OCaml5.Ml.Check

Well-formedness of an `OCaml5.Ml.Module`, as decidable predicates with diagnostics, so that a
generated module is **checked before it is printed**. Each check is an algebra of the generated
fold (`OCaml5.Ml.Fold`): `patVarsAlg`, `tyVarsAlg`, `checkPatAlg`, `checkExprAlg` and
`checkDeclAlg`.

The surface is untyped and can describe a module `ocamlc` rejects (`Syntax`'s docstring). This
module narrows the gap in the one direction a renderer can: it decides the properties that are
properties of the *syntax*, and leaves typing to `ocamlc`. What it decides:

| code | property |
| --- | --- |
| `unbound-value` | an unqualified value name with no binder and no declaration |
| `unbound-ctor` | an unqualified constructor with no declaration |
| `ctor-arity` | a constructor applied to the wrong number of arguments, in an expression or a pattern |
| `unbound-tyvar` | a type variable a member mentions and the declaration's parameters do not bind |
| `duplicate-field` | a record declaration, literal or pattern that names a label twice |
| `duplicate-ctor` | one variant that declares a constructor name twice |
| `duplicate-type` | one module that declares a type name twice |
| `duplicate-binding` | one `let … and …` group that binds a name twice |
| `bad-name` | a name outside the identifier profile of `OCaml5.Ml.Identifier` |
| `shadowed-value` | a binder whose name is already in scope, only when the environment asks (`Env.noShadow`) |

## Two deliberate silences

**Qualified names are not checked.** `M.f` names something in another compilation unit, and this
module has no way to see it. Every check on a name therefore applies only to unqualified ones.
That is a real limit: a typo inside a qualified name reaches `ocamlc`.

**`Expr.raw` and `Decl.rawD` are opaque.** Verbatim text is not parsed, so nothing inside it is
scoped. A module that holds a `rawD` is checked with its value scope open (`checkModule`).
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
  /-- Value names bound at the top level, plus everything in scope. -/
  values : List String := []
  /-- Constructor names and their arity. -/
  ctors : List (String × Nat) := []
  /-- Record labels declared anywhere in the module. -/
  fields : List String := []
  /-- Type names declared in the module. -/
  types : List String := []
  /-- Set by a verbatim item. Inside such a scope another unit's unqualified names may be
  visible and this module cannot see them, so `unbound-value` reporting is switched off rather
  than made to lie. -/
  openScope : Bool := false
  /-- When set, a binder whose name is already in scope is a `shadowed-value` diagnostic: an
  enclosing binder, a value of `values`, or one of these protected names. Unset by default,
  because shadowing is ordinary OCaml. A generator whose contract gives every binder of a
  declaration its own name sets it, and then a reference cannot resolve to a binder other than
  the one the generator meant. -/
  noShadow : Option (List String) := none
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
   "char_of_int", "int_of_char", "max_int"]

/-- The constructors every OCaml program has: the built-in data constructors and the exceptions
the runtime raises. `Ok`/`Error` are `Stdlib.result`'s and belong here beside `Some`/`None`. -/
def preludeCtors : List (String × Nat) :=
  [("()", 0), ("true", 0), ("false", 0), ("[]", 0), ("::", 2), ("None", 0), ("Some", 1),
   ("Ok", 1), ("Error", 1),
   ("Not_found", 0), ("Exit", 0), ("Failure", 1), ("Invalid_argument", 1), ("Sys_error", 1),
   ("Out_of_memory", 0), ("Stack_overflow", 0), ("Division_by_zero", 0), ("End_of_file", 0),
   ("Assert_failure", 1), ("Match_failure", 1), ("Undefined_recursive_module", 1)]

/-- A name that carries a `.` refers to another compilation unit and is not checked. -/
def isQualifiedName (n : String) : Bool := n.contains '.'

/-- Add a value name. -/
def withValue (e : Env) (n : String) : Env := { e with values := n :: e.values }
/-- Add several. -/
def withValues (e : Env) (ns : List String) : Env := { e with values := ns ++ e.values }

def knowsValue (e : Env) (n : String) : Bool :=
  e.openScope || n == "_" || isQualifiedName n || e.values.contains n
    || preludeValues.contains n

/-- Enter the scope of a verbatim item. -/
def opened (e : Env) : Env := { e with openScope := true }

/-- The `shadowed-value` diagnostics of binding `ns` at this scope: empty unless `noShadow` is
set. The names of one batch are read in order, so a parameter that repeats an earlier one of
the same batch is a diagnostic too (`fun x x -> …`). `_` and `()` bind nothing. -/
def shadows (e : Env) (site : String) (ns : List String) : List Diag :=
  match e.noShadow with
  | none => []
  | some guarded =>
    (ns.foldl (init := (([] : List String), ([] : List Diag))) fun (seen, found) n =>
      if n == "_" || n == "()" then (seen, found)
      else if seen.contains n || e.values.contains n || guarded.contains n then
        (n :: seen, found ++ [{ code := "shadowed-value", site := site, detail := "`" ++ n ++ "`" }])
      else (n :: seen, found)).2

/-- The declared arity of a constructor, or `none` when it is not declared here. -/
def ctorArity (e : Env) (n : String) : Option Nat :=
  (e.ctors.lookup n).orElse fun _ => preludeCtors.lookup n

end Env

/-! ## Collecting declarations -/

/-- The names a pattern binds, in the order they occur. -/
def patVarsAlg : PatAlgebra (fun _ => List String) where
  pat_wild := []
  pat_var n := [n]
  pat_ctor _ args := args.flatten
  pat_record fs := (fs.map (·.2)).flatten
  pat_recordOpen fs := (fs.map (·.2)).flatten
  pat_tuple ps := ps.flatten
  pat_cons hd tl := hd ++ tl

/-- The names a pattern binds, in the order they occur. -/
def patVars (p : Pat) : List String := cata_pat patVarsAlg p

/-- Every type variable occurring in a type, in occurrence order and with repeats. -/
def tyVarsAlg : TyAlgebra (fun _ => List String) where
  ty_var n := [n]
  ty_con _ args := args.flatten
  ty_arrow a b := a ++ b
  ty_tuple ps := ps.flatten
  ty_anon := []

private def fieldsOfBody : TyBody → List String
  | .record fs => fs.map (·.name)
  | _ => []

private def ctorsOfBody : TyBody → List (String × Nat)
  | .variant cs => cs.map fun c => (c.name, c.args.length)
  | _ => []

/-! ## The checker -/

/-- The names that occur more than once, each once, in first-duplicate order. -/
private def dupes (ns : List String) : List String :=
  (ns.foldl (init := (([] : List String), ([] : List String))) fun (seen, bad) n =>
    if seen.contains n && !bad.contains n then (n :: seen, n :: bad) else (n :: seen, bad)).2.reverse

private def dup (code site : String) (ns : List String) : List Diag :=
  (dupes ns).map fun n => { code := code, site := site, detail := "`" ++ n ++ "` twice" }

private def badName (site kind : String) (ok : String → Bool) (n : String) : List Diag :=
  if ok n then [] else [{ code := "bad-name", site := site, detail := kind ++ " `" ++ n ++ "`" }]

/-- A constructor is declared, and applied at its arity. A qualified name is not checked: it
names something in another compilation unit. -/
def checkCtorUse (env : Env) (site : String) (n : String) (given : Nat) : List Diag :=
  if Env.isQualifiedName n then []
  else
    match env.ctorArity n with
    | none => [{ code := "unbound-ctor", site := site, detail := "`" ++ n ++ "`" }]
    | some want =>
        if want == given then []
        else [{ code := "ctor-arity", site := site,
                detail := "`" ++ n ++ "` takes " ++ toString want ++ ", given "
                            ++ toString given }]

/-- Constructor existence and arity in a pattern, plus duplicate record labels. -/
def checkPatAlg (site : String) : PatAlgebra (fun _ => Env → List Diag) where
  pat_wild := fun _ => []
  pat_var _ := fun _ => []
  pat_ctor n args := fun env => checkCtorUse env site n args.length ++ (args.map (· env)).flatten
  pat_record fs := fun env =>
    dup "duplicate-field" site (fs.map (·.1)) ++ (fs.map (·.2 env)).flatten
  pat_recordOpen fs := fun env =>
    dup "duplicate-field" site (fs.map (·.1)) ++ (fs.map (·.2 env)).flatten
  pat_tuple ps := fun env => (ps.map (· env)).flatten
  pat_cons hd tl := fun env => hd env ++ tl env

/-- Every failure in one expression at scope `env`, as the fold's algebra at one site. -/
def checkExprAlg (site : String) : ExprAlgebra (fun _ => Env → List Diag) where
  expr_var n := fun env =>
    if env.knowsValue n then [] else [{ code := "unbound-value", site := site, detail := "`" ++ n ++ "`" }]
  expr_int _ := fun _ => []
  expr_str _ := fun _ => []
  expr_bool _ := fun _ => []
  expr_unit := fun _ => []
  expr_ctor n args := fun env => checkCtorUse env site n args.length ++ (args.map (· env)).flatten
  expr_app f args := fun env => f env ++ (args.map (· env)).flatten
  expr_appL f args := fun env => f env ++ (args.map (·.2 env)).flatten
  expr_binop _ l r := fun env => l env ++ r env
  expr_fn ps b := fun env => env.shadows site ps ++ b (env.withValues ps)
  expr_letIn n v b := fun env => env.shadows site [n] ++ v env ++ b (env.withValue n)
  expr_letRec f ps v b := fun env =>
    let inner := env.withValue f
    env.shadows site [f] ++ inner.shadows site ps ++ v (inner.withValues ps) ++ b inner
  expr_ifThen c t e := fun env => c env ++ t env ++ e env
  -- An arm's pattern binds its variables over its body.
  expr_matchE s arms := fun env =>
    s env ++ (arms.map fun (p, b) =>
      let vars := patVars p
      env.shadows site vars ++ cata_pat (checkPatAlg site) p env ++ b (env.withValues vars)).flatten
  expr_record fs := fun env => dup "duplicate-field" site (fs.map (·.1)) ++ (fs.map (·.2 env)).flatten
  expr_field e _ := e
  expr_tuple ps := fun env => (ps.map (· env)).flatten
  expr_listLit items := fun env => (items.map (· env)).flatten
  expr_annot e _ := e
  expr_hole _ fill := fill
  expr_raw _ := fun _ => []
  expr_assertE e := e

/-- Every failure in one expression, at scope `env`. -/
def checkExpr (env : Env) (site : String) (e : Expr) : List Diag :=
  cata_expr (checkExprAlg site) e env

/-- The `shadowed-value` diagnostics of one binding taken alone: its parameters and every binder
of its body, against each other and against `guarded`. The scope starts empty, so a name of the
enclosing module counts only when `guarded` lists it: the caller says which free names the
binding means. Empty means that no binder of the binding hides another one or a guarded name. -/
def shadowDiags (guarded : List String) (b : Bind) : List Diag :=
  let env : Env := { noShadow := some guarded }
  let ps := b.params.map (·.1)
  env.shadows b.name ps
    ++ (checkExpr (env.withValues ps) b.name b.body).filter (·.code == "shadowed-value")

/-! ## Declarations -/

/-- A declaration's parameters are what bind its variables: a variable a member mentions and the
parameter list does not is `The type variable 'b is unbound in this type declaration`, and the
declaration does not compile. An abstract declaration has no members, so it is exempt. The
converse is not an error: an *unused* parameter, which OCaml accepts in a variant, a record and
an abbreviation alike. -/
private def checkTypeDecl (d : TypeDecl) : List Diag :=
  let site := d.name
  let tys : List Ty := match d.body with
    | .record fs => fs.map (·.ty)
    | .variant cs => cs.flatMap (·.args)
    | .alias t => [t]
    | .abstract => []
  let unbound := (tys.flatMap (cata_ty tyVarsAlg)).foldl
      (fun acc v => if d.params.contains v || acc.contains v then acc else acc ++ [v]) []
  badName site "type name" isLowerIdent d.name
    ++ dup "duplicate-ctor" site (match d.body with | .variant cs => cs.map (·.name) | _ => [])
    ++ dup "duplicate-field" site (match d.body with | .record fs => fs.map (·.name) | _ => [])
    ++ (match d.body with
        | .variant cs => cs.flatMap fun c => badName site "constructor" isUpperIdent c.name
        | .record fs => fs.flatMap fun f => badName site "field" isLowerIdent f.name
        | _ => [])
    ++ unbound.map fun n =>
        { code := "unbound-tyvar", site := site,
          detail := "`'" ++ n ++ "` is mentioned by a member and bound by no parameter" }

-- The rule both ways, at the shapes `ocamlopt` was run on: an unused parameter compiles, an
-- unbound one does not.
private def declOf (params : List String) (body : TyBody) : TypeDecl :=
  { name := "t", params := params, body := body }
private def variantOf (args : List Ty) : TyBody :=
  .variant [{ name := "A", args := args }, { name := "B" }]

#guard (checkTypeDecl (declOf ["a", "b"] (variantOf [.var "a"]))).isEmpty
#guard (checkTypeDecl (declOf ["a", "b"] (.alias (Ty.list (.var "a"))))).isEmpty
#guard (checkTypeDecl (declOf ["a"] (variantOf [.var "b"]))).map (·.code) == ["unbound-tyvar"]

/-- A structure item, as what it declares into the environment and what it fails at a scope.
A functor body is checked under its own declarations: the pair is the fold's two answers at
once. -/
abbrev Checked : DeclFam → Type := fun _ => (Env → Env) × (Env → List Diag)

/-- The declarations and the failures of one structure item. -/
def checkDeclAlg : DeclAlgebra Checked where
  decl_types group :=
    (fun e => group.foldl (init := e) fun acc d =>
        { acc with types := d.name :: acc.types, ctors := ctorsOfBody d.body ++ acc.ctors,
                   fields := fieldsOfBody d.body ++ acc.fields },
     fun _ => dup "duplicate-type" "module" (group.map (·.name)) ++ group.flatMap checkTypeDecl)
  decl_letD _ binds :=
    (fun e => { e with values := binds.map (·.name) ++ e.values },
     fun env => dup "duplicate-binding" "let" (binds.map (·.name))
        ++ binds.flatMap fun b =>
          (if b.name == "()" || b.name == "_" then []
           else badName b.name "value name" isLowerIdent b.name)
            ++ checkExpr (env.withValues (b.params.map (·.1))) b.name b.body)
  decl_comment _ := (id, fun _ => [])
  decl_rawD _ := (id, fun _ => [])
  decl_moduleD n _ body :=
    (fun e => { e with types := n :: e.types },
     fun env =>
       let inner := body.foldl (fun e d => d.1 e) env
       badName n "module name" isUpperIdent n ++ (body.map (·.2 inner)).flatten)
  decl_floatingAttrD _ := (id, fun _ => [])
  decl_blank := (id, fun _ => [])

/-- Everything a module declares at its top level. -/
def Env.ofModule (m : Module) : Env := m.items.foldl (fun e d => (cata_decl checkDeclAlg d).1 e) {}

/-- Every well-formedness failure in a module, in declaration order. Empty means the module
passes every check this file can decide; it does **not** mean `ocamlc` accepts it. A top-level
`rawD` is verbatim text this module does not parse, and what it binds is exactly as invisible,
so a module with one is checked with its value scope open. -/
def checkModule (m : Module) : List Diag :=
  let env0 := Env.ofModule m
  let env := if m.items.any (fun d => d matches .rawD _) then env0.opened else env0
  dup "duplicate-type" "module" env.types.reverse
    ++ (m.items.map fun d => (cata_decl checkDeclAlg d).2 env).flatten

end OCaml5.Ml
