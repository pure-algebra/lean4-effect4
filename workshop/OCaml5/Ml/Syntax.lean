import OCaml5.Ml.Identifier

/-!
# OCaml5.Ml.Syntax

The OCaml 5 surface as first-order data. This module owns **syntax only**: no rendering, no
checking, no knowledge of any effect system beyond the fact that `Effect` is a module in the
OCaml standard library with a known shape.

Precedent: `TypeScript.Syntax` in the estate's TypeScript target package — "the first-order
TypeScript syntax retained from Foldlab's target backend. This module owns syntax only.
Deterministic source rendering lives in `TypeScript.Render`." The same division holds here, with
the same consequence: a value of these types is target data, never the denotation of anything.

## Completeness

The fragment is what a *runtime port* needs — a hand-written OCaml runtime, of the size of
`workshop/OCaml5/avatar/deep_fibers.ml`, generated instead of typed. That is the whole of the
core language and the module language's declaration forms, and none of the object system, none of
`class`, no first-class modules, no `let module`, no polymorphic method types, and no attributes
other than the two a generator actually emits. Where a form is deliberately absent it is named in
the docstring of the type it would have belonged to.

Every constructor names the section of the OCaml 5.1.1 manual it renders.

## Two properties this data has, and one it does not

* **First order.** No binders as Lean functions, no `Type`-indexed families: a value of `Expr` is
  a tree of strings, so it can be compared, printed, diffed and stored.
* **Untyped.** The surface will happily describe a module `ocamlc` rejects. `OCaml5.Ml.Check`
  narrows that: it decides the well-formedness properties a renderer can decide (scoping, arity,
  duplicate labels, the `effc` rule, the `reperform` tail-position rule), and the rest is an
  executed check — `tools/ml-check.sh` renders and compiles.
-/

namespace OCaml5.Ml

/-! ## Argument labels (§11.7, "labeled arguments") -/

/-- A function-argument label. `~x:t` is `lbl`, `?x:t` is `opt`, and an unlabelled argument is
`nolabel`. The name is stored without its `~`/`?`. -/
inductive ArgLabel where
  /-- An ordinary positional argument. -/
  | nolabel
  /-- `~name:` — a labelled argument (§11.7). -/
  | lbl (name : String)
  /-- `?name:` — an optional argument (§11.7); its type is the `'a` of the `'a option` OCaml
  wraps it in, not the option itself. -/
  | opt (name : String)
deriving Repr, Inhabited, DecidableEq

/-! ## Types (§11.2, *Type expressions*) -/

/-- The variance annotation on a type parameter (§11.6, "type-param"): `+'a`, `-'a`, `'a`.
A parameter no constructor determines needs one, or OCaml rejects the declaration; that is what
makes a phantom parameter expressible. -/
inductive Variance where
  | invariant
  | covariant
  | contravariant
deriving Repr, Inhabited, DecidableEq

/-- The `[ … ]`, `[> … ]`, `[< … ]` forms of a polymorphic-variant type (§11.2, "polymorphic
variant type"). -/
inductive PolyKind where
  /-- `[ \`A | \`B of t ]` — exactly these tags. -/
  | exact
  /-- `[> \`A ]` — at least these tags. -/
  | atLeast
  /-- `[< \`A ]` — at most these tags. -/
  | atMost
deriving Repr, Inhabited, DecidableEq

/-- An OCaml type expression (§11.2). Type application is postfix, as OCaml writes it. -/
inductive Ty where
  /-- `'a` — a type variable (§11.2, "'ident"). Rendered with its `'`. -/
  | var (name : String)
  /-- A type constructor applied to its arguments, postfix: `int`, `'a list`,
  `('a, 'b) Effect.Deep.continuation`. The name may be qualified (§11.4). -/
  | con (name : String) (args : List Ty)
  /-- `t -> u` (§11.2, "typexpr -> typexpr"). -/
  | arrow (dom cod : Ty)
  /-- `t1 * t2 * …` (§11.2, "typexpr * typexpr"). -/
  | tuple (parts : List Ty)
  /-- `~x:t -> u` and `?x:t -> u` (§11.2, "label-name : typexpr -> typexpr"). `arrow` is the
  `nolabel` case, kept as its own constructor because it predates this one and every caller
  spells it. -/
  | larrow (label : ArgLabel) (dom cod : Ty)
  /-- A polymorphic-variant type (§11.2). Each row is a tag name without its backquote and the
  types of its argument, of which OCaml allows at most one. -/
  | polyVariant (kind : PolyKind) (rows : List (String × List Ty))
  /-- `_` — the anonymous type (§11.2, "_"), which is what `type _ Effect.t += …` and
  `(e : _)` are made of. -/
  | anon
  /-- `(t as 'a)` (§11.2, "typexpr as 'ident"): the constraint form that lets a declaration
  determine an otherwise-phantom parameter. -/
  | asVar (ty : Ty) (name : String)
deriving Repr, Inhabited

namespace Ty
def int : Ty := .con "int" []
def bool : Ty := .con "bool" []
def unit : Ty := .con "unit" []
def string : Ty := .con "string" []
def char : Ty := .con "char" []
def float : Ty := .con "float" []
def exn : Ty := .con "exn" []
def named (n : String) : Ty := .con n []
def list (t : Ty) : Ty := .con "list" [t]
def array (t : Ty) : Ty := .con "array" [t]
def option (t : Ty) : Ty := .con "option" [t]
def ref (t : Ty) : Ty := .con "ref" [t]
/-- `'a Effect.t` (`stdlib/effect.ml:14`). -/
def effect (t : Ty) : Ty := .con "Effect.t" [t]
/-- `('a, 'b) Effect.Deep.continuation` (`stdlib/effect.ml:46`). -/
def cont (a b : Ty) : Ty := .con "Effect.Deep.continuation" [a, b]
/-- `('a, 'b) Effect.Shallow.continuation` (`stdlib/effect.ml:100`). -/
def shallowCont (a b : Ty) : Ty := .con "Effect.Shallow.continuation" [a, b]
/-- `('a, 'b) Effect.Deep.handler` (`stdlib/effect.mli`, `Deep.handler`): `'a` is what the
computation returns and `'b` what the handler answers. -/
def deepHandler (a b : Ty) : Ty := .con "Effect.Deep.handler" [a, b]
/-- `'a Effect.Deep.effect_handler` (`stdlib/effect.mli`), the `effc`-only record
`Effect.Deep.try_with` takes. -/
def deepEffectHandler (a : Ty) : Ty := .con "Effect.Deep.effect_handler" [a]
/-- `('a, 'b) Effect.Shallow.handler` (`stdlib/effect.ml:120`). -/
def shallowHandler (a b : Ty) : Ty := .con "Effect.Shallow.handler" [a, b]

/-! Structural equality, hand-written: `Ty` nests through `List` and through
`List (String × List Ty)`, so the `DecidableEq` deriving handler does not apply. -/
mutual
def beq : Ty → Ty → Bool
  | .var a, .var b => a == b
  | .con a as', .con b bs => a == b && beqs as' bs
  | .arrow a b, .arrow c d => beq a c && beq b d
  | .tuple a, .tuple b => beqs a b
  | .larrow l a b, .larrow l' c d => l == l' && beq a c && beq b d
  | .polyVariant k rs, .polyVariant k' rs' => k == k' && beqRows rs rs'
  | .anon, .anon => true
  | .asVar t n, .asVar t' n' => beq t t' && n == n'
  | _, _ => false

def beqs : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as', b :: bs => beq a b && beqs as' bs
  | _, _ => false

def beqRows : List (String × List Ty) → List (String × List Ty) → Bool
  | [], [] => true
  | (n, a) :: as', (m, b) :: bs => n == m && beqs a b && beqRows as' bs
  | _, _ => false
end

/-! `mentionsVar name t`: whether a type variable of this name occurs anywhere in `t`. -/
mutual
def mentionsVar (name : String) : Ty → Bool
  | .var n => n == name
  | .con _ args => mentionsVars name args
  | .arrow a b => mentionsVar name a || mentionsVar name b
  | .tuple ps => mentionsVars name ps
  | .larrow _ a b => mentionsVar name a || mentionsVar name b
  | .polyVariant _ rows => mentionsRows name rows
  | .anon => false
  | .asVar t n => n == name || mentionsVar name t

def mentionsVars (name : String) : List Ty → Bool
  | [] => false
  | t :: rest => mentionsVar name t || mentionsVars name rest

def mentionsRows (name : String) : List (String × List Ty) → Bool
  | [] => false
  | (_, ts) :: rest => mentionsVars name ts || mentionsRows name rest
end

/-! `mentionsCon name t`: whether a type *constructor* of this name occurs anywhere in `t`. The
`effc` rule needs it: a locally abstract `type a` is spelled `.con "a" []`, not `.var "a"`. -/
mutual
def mentionsCon (name : String) : Ty → Bool
  | .var _ => false
  | .con n args => n == name || mentionsCons name args
  | .arrow a b => mentionsCon name a || mentionsCon name b
  | .tuple ps => mentionsCons name ps
  | .larrow _ a b => mentionsCon name a || mentionsCon name b
  | .polyVariant _ rows => mentionsConRows name rows
  | .anon => false
  | .asVar t _ => mentionsCon name t

def mentionsCons (name : String) : List Ty → Bool
  | [] => false
  | t :: rest => mentionsCon name t || mentionsCons name rest

def mentionsConRows (name : String) : List (String × List Ty) → Bool
  | [] => false
  | (_, ts) :: rest => mentionsCons name ts || mentionsConRows name rest
end
end Ty

instance : BEq Ty := ⟨Ty.beq⟩

/-! ## Patterns (§11.6, *Patterns*) -/

/-- An OCaml pattern (§11.6). -/
inductive Pat where
  /-- `_` (§11.6, "_"). -/
  | wild
  /-- A variable binding (§11.6, "value-name"). -/
  | var (name : String)
  /-- An integer literal pattern (§11.6, "constant"). -/
  | int (n : Nat)
  /-- A string literal pattern. -/
  | str (s : String)
  /-- A constructor pattern (§11.6, "constr pattern"); `≥ 2` arguments are rendered as one
  tuple, as OCaml requires. -/
  | ctor (name : String) (args : List Pat)
  /-- `{ f = p; … }` (§11.6, "{ field = pattern }"). -/
  | record (fields : List (String × Pat))
  /-- `(p1, p2, …)` (§11.6, "pattern , pattern"). -/
  | tuple (parts : List Pat)
  /-- `hd :: tl`, which `Pat.ctor` cannot spell because `::` is infix. -/
  | cons (hd tl : Pat)
  /-- `(p as x)` (§11.6, "pattern as value-name"). -/
  | alias (p : Pat) (name : String)
  /-- `(p1 | p2)` (§11.6, "pattern | pattern"). Both sides must bind the same variables. -/
  | orPat (a b : Pat)
  /-- A character literal pattern. -/
  | char (c : Char)
  /-- A float literal pattern, as the exact source text: see `Expr.float`. -/
  | float (repr : String)
  /-- `[p1; p2; …]` (§11.6, "[ pattern ; … ]"). -/
  | listPat (items : List Pat)
  /-- `{ f = p; _ }` — a record pattern that does not name every field (§11.6). The `_` is what
  keeps `warning 9` quiet on a record the generator only partly reads. -/
  | recordOpen (fields : List (String × Pat))
  /-- `(p : t)` (§11.6, "( pattern : typexpr )"). -/
  | constrained (p : Pat) (ty : Ty)
  /-- `exception p` (§11.6, "exception pattern"): the arm of a `match` that catches instead of
  matching. OCaml 5 allows it in `match`, which is how a handler catches without a `try`. -/
  | exnPat (p : Pat)
  /-- `` `Tag p `` — a polymorphic-variant pattern (§11.6). -/
  | polyPat (tag : String) (arg : Option Pat)
  /-- `lazy p` (§11.6). -/
  | lazyPat (p : Pat)
deriving Repr, Inhabited

namespace Pat
def unit : Pat := .ctor "()" []
def nil : Pat := .ctor "[]" []
def true_ : Pat := .ctor "true" []
def false_ : Pat := .ctor "false" []
def none_ : Pat := .ctor "None" []
def some_ (p : Pat) : Pat := .ctor "Some" [p]
end Pat

/-! ## Expressions (§11.7, *Expressions*)

Two families beyond the core language are here as first-class constructors rather than as
`raw` text, because a generated runtime is made of them and a checker has to see them:

* the **effect primitives** — `Effect.perform` (§`stdlib/effect.ml:16`) and the raw `%reperform`
  (`effect.ml:130-135`), which `Check` needs to see so it can decide the tail-position rule
  `ocamlc` enforces (`bytegen.ml:796-804`);
* the **handler records** — `Effect.Deep.handler` and `Effect.Shallow.handler`
  (`effect.ml:66-68,120-122`) as record literals in their own right, so a handler can be bound,
  passed and reused instead of being inlined at every `match_with`.
-/

/-- Deep or shallow: which of `stdlib/effect.ml`'s two handler families a form belongs to
(`effect.ml:60-98` and `:110-160`). -/
inductive HandlerKind where
  /-- `Effect.Deep` — the continuation carries its own handler. -/
  | deep
  /-- `Effect.Shallow` — the continuation is one-shot and the resumer supplies a handler. -/
  | shallow
deriving Repr, Inhabited, DecidableEq

/-- The module path of a handler family: `Effect.Deep` or `Effect.Shallow`. -/
def HandlerKind.path : HandlerKind → String
  | .deep => "Effect.Deep"
  | .shallow => "Effect.Shallow"

mutual

/-- An OCaml expression (§11.7). -/
inductive Expr : Type where
  /-- A value path (§11.4): `x`, `M.f`. -/
  | var (name : String)
  /-- A non-negative integer literal (§11.1). Use `intOf` for a negative one: `-1` is a prefix
  application in OCaml, not a literal. -/
  | int (n : Nat)
  /-- A string literal (§11.1). -/
  | str (s : String)
  /-- `true` / `false`. -/
  | bool (b : Bool)
  /-- `()` (§11.7, "( )"). -/
  | unit
  /-- A constructor applied to its arguments (§11.7, "constr expr"); `≥ 2` arguments become one
  tuple, as OCaml requires. -/
  | ctor (name : String) (args : List Expr)
  /-- Function application (§11.7, "expr { argument }+"), left-associative. -/
  | app (fn : Expr) (args : List Expr)
  /-- An infix application `l op r` (§11.7, "expr infix-op expr"). The operator's precedence and
  associativity are read off its first character, exactly as OCaml's grammar does. -/
  | binop (op : String) (l r : Expr)
  /-- `fun p1 p2 -> body` over plain parameter names; a parameter named `()` renders as the unit
  pattern. `lam` is the general form. -/
  | fn (params : List String) (body : Expr)
  /-- `let x = v in body` (§11.7, "let … in"). -/
  | letIn (name : String) (value body : Expr)
  /-- A local `let rec … and …` (§11.7). -/
  | letRecIn (binds : List (String × List String × Expr)) (body : Expr)
  /-- `a; b` (§11.7, "expr ; expr"). -/
  | seq (a b : Expr)
  /-- `if c then t else e` (§11.7). -/
  | ifThen (cond thenE elseE : Expr)
  /-- `match e with …` (§11.7). -/
  | matchE (scrut : Expr) (arms : List Arm)
  /-- `try e with …` (§11.7). -/
  | tryWith (body : Expr) (arms : List Arm)
  /-- `{ f = e; … }` (§11.7, "{ field = expr }"). -/
  | record (fields : List (String × Expr))
  /-- `{ base with f = e; … }` (§11.7, "{ expr with … }"). -/
  | recordWith (base : Expr) (fields : List (String × Expr))
  /-- `e.f` (§11.7, "expr . field"). -/
  | field (e : Expr) (name : String)
  /-- `e.f <- v` (§11.7, "expr . field <- expr"), the mutable-field write. -/
  | setField (e : Expr) (name : String) (v : Expr)
  /-- `(e1, e2, …)` (§11.7, "expr , expr"). -/
  | tuple (parts : List Expr)
  /-- `[e1; e2; …]` (§11.7, "[ expr ; … ]"). -/
  | listLit (items : List Expr)
  /-- `ref e` — `Stdlib.ref`. -/
  | mkRef (e : Expr)
  /-- `!e` — `Stdlib.(!)`, a prefix operator (§11.7, "prefix-symbol expr"). -/
  | deref (e : Expr)
  /-- `r := v` — `Stdlib.(:=)`. -/
  | assign (r v : Expr)
  /-- `raise e` (§11.7 via `Stdlib.raise`). -/
  | raiseE (e : Expr)
  /-- `Effect.perform e` (`stdlib/effect.ml:16`). -/
  | perform (e : Expr)
  /-- `Effect.Deep.continue k v` (`effect.ml:71`). -/
  | continueK (k v : Expr)
  /-- `Effect.Deep.discontinue k e` (`effect.ml:75`). -/
  | discontinueK (k e : Expr)
  /-- `Effect.Deep.match_with comp arg { retc; exnc; effc }` (`effect.ml:78-82`). `answer` is the
  handler's `'b`, which the `effc` clauses need to annotate their continuation with. -/
  | matchWith (comp arg : Expr) (answer : Ty) (retcVar : String) (retc : Expr)
      (exnc : List Arm) (effc : List Effc)
  /-- `Effect.Deep.try_with comp arg { effc }` (`effect.ml:84-91`): the identity `retc` and the
  re-raising `exnc` are the wrapper's, not ours. -/
  | tryWithEff (comp arg : Expr) (answer : Ty) (effc : List Effc)
  /-- `(e : t)` (§11.7, "( expr : typexpr )"). -/
  | annot (e : Expr) (ty : Ty)
  /-- A place the renderer refuses to fill. `note` says what the Lean side had; `fill` is what
  the hand-written module supplies in its place. Rendered as a comment followed by `fill`, so a
  hole is visible in the output and not only in the description. -/
  | hole (note : String) (fill : Expr)
  /-- Verbatim text, for anything this surface does not spell. `Check` cannot see inside it and
  says so rather than passing it silently. -/
  | raw (text : String)
  /-- A character literal (§11.1). -/
  | char (c : Char)
  /-- A float literal, as **exact source text** (§11.1, "float-literal").

  The O3 backend caveat: OCaml's three backends do not agree on the decimal spelling of a
  binary64, and `js_of_ocaml` reconstructs a JavaScript number from the literal's digits. A
  generator that formats a float itself therefore generates a program whose meaning depends on
  the host. So this constructor takes the literal's characters and never reformats them: the
  caller is responsible for a spelling that round-trips (a hexadecimal float literal, `0x1.8p1`,
  always does), and the renderer emits exactly those bytes. The same reasoning is why
  `TypeScript.Expr` has `float64Bits` rather than a `Float`. -/
  | float (repr : String)
  /-- A possibly negative integer literal: `-1` renders as `(-1)`, the prefix application, and a
  non-negative one as the bare literal. -/
  | intOf (n : Int)
  /-- `fun p1 p2 -> body` over full parameters: labelled, optional, pattern, annotated
  (§11.7, "fun { parameter }+ -> expr"). -/
  | lam (params : List Param) (body : Expr)
  /-- `function | p -> e | …` (§11.7, "function …"): the one-argument `match`. -/
  | functionE (arms : List Arm)
  /-- `let p = v in body` over a pattern (§11.7, "let pattern = expr in expr"). -/
  | letPat (pat : Pat) (value body : Expr)
  /-- `let open M in body` (§11.7, "let open module-path in expr"). -/
  | openIn (path : String) (body : Expr)
  /-- `assert e` (§11.7, "assert expr"). `assert false` is the idiom for an unreachable arm and
  is the one expression OCaml types at any type. -/
  | assertE (e : Expr)
  /-- `lazy e` (§11.7, "lazy expr"). -/
  | lazyE (e : Expr)
  /-- `[| e1; e2 |]` (§11.7, "[| expr ; … |]"). -/
  | arrayLit (items : List Expr)
  /-- `a.(i)` (§11.7, "expr .( expr )"). -/
  | arrayGet (arr idx : Expr)
  /-- `a.(i) <- v` (§11.7, "expr .( expr ) <- expr"). -/
  | arraySet (arr idx v : Expr)
  /-- `while c do body done` (§11.7). -/
  | whileE (cond body : Expr)
  /-- `for x = a to b do body done`, or `downto` when `down` (§11.7). -/
  | forE (name : String) (lo hi : Expr) (down : Bool) (body : Expr)
  /-- `` `Tag e `` — a polymorphic-variant expression (§11.7). -/
  | polyCtor (tag : String) (arg : Option Expr)
  /-- `if c then t` with no `else` (§11.7); `t` must have type `unit`. -/
  | ifThenOnly (cond thenE : Expr)
  /-- A handler record as a value: `{ retc; exnc; effc }` for `.deep`
  (`effect.ml:66-68`) and for `.shallow` (`effect.ml:120-122`). `retc` is `Option` because
  `Effect.Deep.try_with` takes a record with only `effc` (`effect.ml:84-91`); when it is `none`
  no `retc`/`exnc` field is emitted at all. -/
  | handler (kind : HandlerKind) (answer : Ty) (retc : Option (String × Expr))
      (exnc : List Arm) (effc : List Effc)
  /-- `Effect.Deep.match_with comp arg h` / `Effect.Shallow.continue_with` — the handler passed
  as an expression rather than inlined. -/
  | matchWithK (kind : HandlerKind) (comp arg h : Expr)
  /-- `Effect.Shallow.continue_with k v h` (`effect.ml:125`). -/
  | shallowContinue (k v h : Expr)
  /-- `Effect.Shallow.discontinue_with k e h` (`effect.ml:129`). -/
  | shallowDiscontinue (k e h : Expr)
  /-- Application with **labelled and optional arguments** (§11.7, "argument"): `f ~x:e ?y:e e`.
  `app` is the all-`nolabel` case, kept because every existing caller spells it. An `opt` label
  here passes the `'a option` itself, which is what `?y:e` means at a call site. -/
  | appL (fn : Expr) (args : List (ArgLabel × Expr))
  /-- The raw `%reperform` primitive (`effect.ml:130-135`), which forwards an effect to the next
  handler. Its whole reason for being a constructor and not an `app` is that `ocamlc` **refuses**
  it outside tail position (`bytegen.ml:796-804`), and `Check.tailPositions` decides that. -/
  | reperform (eff k lastFiber : Expr)

/-- One `match`/`try` arm, with an optional `when` guard (§11.7, "pattern-matching"). -/
inductive Arm : Type where
  | mk (pat : Pat) (guard : Option Expr) (body : Expr)

/-- One `effc` clause: an effect constructor, its argument patterns, the name the continuation is
bound to, and the body. Renders as `| C args -> Some (fun (k : (a, answer) continuation) -> …)`,
which is the shape `effect.ml:66-68` types the field at. -/
inductive Effc : Type where
  | mk (ctorName : String) (args : List Pat) (kBinder : String) (body : Expr)

/-- One `fun` parameter (§11.7, "parameter"): a label, a pattern, an optional type annotation,
and, for an optional argument, a default. -/
inductive Param : Type where
  | mk (label : ArgLabel) (pat : Pat) (ty : Option Ty) (default : Option Expr)

end

namespace Expr
instance : Inhabited Expr := ⟨Expr.unit⟩
/-- `f a b …` with `f` a name. -/
def call (f : String) (args : List Expr) : Expr := .app (.var f) args
/-- `ignore e`. -/
def ignoreE (e : Expr) : Expr := .app (.var "ignore") [e]
def none_ : Expr := .ctor "None" []
def some_ (e : Expr) : Expr := .ctor "Some" [e]
def nil : Expr := .ctor "[]" []
/-- A member call, `target.name args`, the way an OCaml module member is
reached: `Effect.Deep.continue k v` is `.call "Effect.Deep.continue" [k, v]`. -/
def method (target : String) (name : String) (args : List Expr) : Expr :=
  .app (.var (target ++ "." ++ name)) args
end Expr

namespace Param
/-- An unlabelled parameter, by name. -/
def pos (name : String) : Param := .mk .nolabel (.var name) none none
/-- An unlabelled parameter, by name, annotated. -/
def posT (name : String) (ty : Ty) : Param := .mk .nolabel (.var name) (some ty) none
/-- `~name` (§11.7, "~ label-name"). -/
def named (name : String) : Param := .mk (.lbl name) (.var name) none none
/-- `?name` (§11.7, "? label-name"). -/
def optional (name : String) : Param := .mk (.opt name) (.var name) none none
/-- `?(name = default)`. -/
def optionalD (name : String) (default : Expr) : Param :=
  .mk (.opt name) (.var name) none (some default)
/-- `()`. -/
def unit : Param := .mk .nolabel (.ctor "()" []) none none
end Param

/-! ## Type declarations (§11.6, *Type and exception definitions*) -/

/-- One record field (§11.6, "field-decl"). `isMutable` is the `mutable` keyword, which is how a
Lean `structure` field that a port updates in place is spelled. -/
structure Field where
  name : String
  ty : Ty
  isMutable : Bool := false
  /-- A trailing `(* … *)` on the field's own line, when the record is rendered wide. -/
  comment : Option String := none
  /-- Verbatim lines emitted above the field, when the record is rendered wide. A substitute
  field needs one: it has no Lean counterpart, so the only place to say why it exists is here. -/
  leading : List String := []
  /-- Single-`@` attributes on the field itself (§11.13): `[@default 0]`, `[@sexp.opaque]`,
  which is how `ppx_sexp_conv` and `ppx_fields_conv` are steered per field. -/
  attrs : List String := []
deriving Repr, Inhabited

/-- One variant constructor (§11.6, "constr-decl"): `| C of t1 * t2`.

`result` is the GADT form (§11.6, "constr-decl : … -> typexpr", and the manual's §9.9): when it
is given, the constructor renders as `| C : t1 -> t2 -> result` and the whole declaration is a
generalised algebraic datatype. That is the form `type _ Effect.t += E : u -> u Effect.t` is
made of, and the form a runtime port's instruction type wants. -/
structure Ctor where
  name : String
  args : List Ty := []
  /-- The GADT return type. `none` is an ordinary constructor of the type being declared. -/
  result : Option Ty := none
  /-- An inline record argument, `| C of { x : int }` (§11.6). Mutually exclusive with `args`;
  when both are given the inline record wins, because OCaml has no form that mixes them. -/
  inlineRecord : Option (List Field) := none
  /-- A trailing `(* … *)` on the constructor's own line. -/
  comment : Option String := none
  /-- Single-`@` attributes on the constructor itself (§11.13). -/
  attrs : List String := []
deriving Repr, Inhabited

/-- The right-hand side of a `type` declaration (§11.6, "type-representation"). -/
inductive TyBody where
  /-- `{ f : t; mutable g : u }`. -/
  | record (fields : List Field)
  /-- `| A | B of t`. -/
  | variant (ctors : List Ctor)
  /-- `type t = u` — an abbreviation (§11.6, "type-equation"). -/
  | alias (ty : Ty)
  /-- `type t` — an abstract type. -/
  | abstract
  /-- `type t = ..` — an extensible variant declaration (§11.6, "extensible variant types"),
  the declaration `type t += …` later adds to. `Effect.t` is one (`effect.ml:14`). -/
  | extensible
deriving Repr, Inhabited

/-- One type parameter of a declaration (§11.6, "type-param"): `'a`, `+'a`, `-'a`, `!'a`.

A parameter that no constructor determines is rejected by OCaml unless it is annotated, so a
**phantom parameter** is exactly a `TyParam` with a `variance` and no occurrence. `Check` reports
an un-annotated one rather than letting `ocamlc` do it. -/
structure TyParam where
  name : String
  variance : Variance := .invariant
  /-- `!'a`, the injectivity annotation (§11.6). -/
  injective : Bool := false
deriving Repr, Inhabited

/-- One `type` declaration (§11.6, "typedef"). A Lean `structure` becomes a `record`, a Lean
`inductive` a `variant`, and a group of them joined by `and` is a `Decl.types`.

`params` is the plain form, kept because every existing caller spells it; `tparams` is the
annotated form and **takes its place when it is non-empty**. Only `tparams` can express a
variance, so only `tparams` can express a phantom parameter. -/
structure TypeDecl where
  name : String
  params : List String := []
  body : TyBody
  /-- Takes the place of `params` when non-empty. -/
  tparams : List TyParam := []
  /-- The deriver names of a single `[@@deriving …]` attribute (§11.13, "attributes"), rendered
  as one comma-separated list after the body — `[@@deriving sexp, compare, equal, hash, fields,
  variants]`. It is its own field rather than one more `attrs` entry because it is the attribute
  a generated carrier always has and the one whose *contents* a consumer reads: `Fields.fold` is
  the field-by-field walk a simulation relation is stated over, and `Variants.to_rank` is the
  constructor order a port's diff needs. `janeDerivers` is the estate's standard set. -/
  derivers : List String := []
  /-- Any other `[@@…]` attribute, verbatim and one each: `[@@warning "-37"]`, `[@@boxed]`.
  Rendered after the `[@@deriving …]`. -/
  attrs : List String := []
deriving Repr, Inhabited

/-- The derivers every generated carrier of this estate carries
(`docs/research/2026-09-04-ocaml-packages-plan.md` §1, `ppx_jane`). `fields` is only legal on a
record and `variants` only on a variant, so a variant uses `janeVariantDerivers` and a record
`janeRecordDerivers`; `janeDerivers` is what they share. -/
def janeDerivers : List String := ["sexp", "compare", "equal", "hash"]
/-- `janeDerivers` plus `fields`, for a record. -/
def janeRecordDerivers : List String := janeDerivers ++ ["fields"]
/-- `janeDerivers` plus `variants`, for a variant. -/
def janeVariantDerivers : List String := janeDerivers ++ ["variants"]

/-- One `let` binding, possibly a function (§11.6, "value definition").

`params` is the plain form; `lparams` is the full one (labels, patterns, defaults) and **takes
its place when non-empty**, for the same reason `TypeDecl.tparams` does. -/
structure Bind where
  name : String
  params : List (String × Option Ty) := []
  result : Option Ty := none
  body : Expr
  /-- Takes the place of `params` when non-empty. -/
  lparams : List Param := []
  /-- Locally abstract types, `let f : type a. …` (§11.7, "locally abstract types"). This is
  what makes a `let` that handles effects check: the `effc` field is polymorphic in the effect's
  answer type, and only a locally abstract type can be refined by a GADT match. -/
  abstractTys : List String := []
  attrs : List String := []

/-! ## Module types and signatures (§11.9-§11.11) -/

mutual

/-- A module type (§11.9, *Module types*). -/
inductive ModTy : Type where
  /-- A named module type: `S`, `M.S`. -/
  | path (name : String)
  /-- `sig … end`. -/
  | sig (items : List SigItem)
  /-- `functor (X : S) -> T` (§11.9, "functor"). -/
  | functor (arg : String) (argTy : ModTy) (res : ModTy)
  /-- `S with type t = u` (§11.9, "module-type with type"). The constraint every functor
  application in a generated runtime needs, to say what the abstract type actually is. -/
  | withType (base : ModTy) (name : String) (params : List String) (ty : Ty)

/-- One item of a signature (§11.10, *Module specifications*). -/
inductive SigItem : Type where
  /-- `val f : t`. -/
  | val (name : String) (ty : Ty)
  /-- `type t = …` and `and`-groups. -/
  | types (group : List TypeDecl)
  /-- `exception E of t`. -/
  | exn (name : String) (args : List Ty)
  /-- `external f : t = "prim"`. -/
  | ext (name : String) (ty : Ty) (prim : String) (attrs : List String)
  /-- `module M : S`. -/
  | modS (name : String) (mt : ModTy)
  /-- `module type S = …`. -/
  | modTypeS (name : String) (mt : ModTy)
  /-- `include S`. -/
  | includeS (mt : ModTy)
  /-- `open M`. -/
  | openS (name : String)
  | commentS (text : String)
  | rawS (text : String)

end

/-! ## Structure items (§11.11, *Module implementations*) -/

/-- One structure item: what a compilation unit is a list of (§11.11). -/
inductive Decl where
  /-- `type a = … and b = …` (§11.6). -/
  | types (group : List TypeDecl)
  /-- `exception E of t1 * t2` (§11.6, "exception-definition"). -/
  | exn (name : String) (args : List Ty)
  /-- `type _ Effect.t += C : t1 -> t2 -> answer Effect.t`, one entry per constructor: the
  special case of `typeExt` that every effect declaration is. Kept as its own constructor
  because every existing caller spells it. -/
  | effects (ctors : List (String × List Ty × Ty))
  /-- `let [rec] f … and g …` (§11.11, "definition"). -/
  | letD (isRec : Bool) (binds : List Bind)
  /-- `external f : t = "prim"` (§11.12, *Language extensions*; the primitive name is the C
  symbol or the `%`-primitive, e.g. `"%perform"`). -/
  | ext (name : String) (ty : Ty) (prim : String) (attrs : List String := [])
  /-- `open M` (§11.11). -/
  | openM (name : String)
  /-- `(* text *)`. -/
  | comment (text : String)
  /-- Verbatim text. -/
  | rawD (text : String)
  /-- `type ('a, 'b) t += | C : … | D of …` — an extension of an extensible variant (§11.6,
  "extensible variant types"). `path` is the type being extended, which may be qualified
  (`Effect.t`); `params` are its parameters, and `_` is spelled by an empty name. -/
  | typeExt (path : String) (params : List TyParam) (ctors : List Ctor) (isPrivate : Bool := false)
  /-- `include M` (§11.11). -/
  | includeD (mt : ModTy)
  /-- `module M = struct … end`, `module M : S = struct … end`, and, with `params`,
  `module F (X : S) = struct … end` — the functor definition (§11.11). -/
  | moduleD (name : String) (params : List (String × ModTy)) (ascribe : Option ModTy)
      (body : List Decl)
  /-- `module M = N`, including a functor application `module M = F (X)` written as the target
  text. -/
  | moduleAliasD (name : String) (target : String)
  /-- `module type S = sig … end` (§11.11). -/
  | moduleTypeD (name : String) (mt : ModTy)
  /-- `[@@deriving …]`, `[@@warning …]` on the declaration it wraps (§11.13). -/
  | attrD (attrs : List String) (d : Decl)
  /-- A floating attribute, `[@@@warning "-32"]` (§11.13). -/
  | floatingAttrD (text : String)
  /-- `let p = e` over a pattern: the structure-item form of a destructuring `let`. -/
  | letPatD (pat : Pat) (value : Expr)
  /-- One blank line. Layout, not syntax; here so that a generated unit's paragraphing is data
  like everything else. -/
  | blank

/-! ## The root -/

/-- A compilation unit: a name, an optional header comment, and its structure items (§11.11).
`OCaml5.Ml.Render.render` turns one into the bytes of a `.ml` file.

The name is the unit's module name — `deep_fibers` for `deep_fibers.ml` — and is *not* rendered
into the file; OCaml takes a unit's module name from its file name. It is here so that a
generator can emit a file and a checker can report against a name. -/
structure Module where
  /-- The unit's own name, `Snake_case` or `snake_case`; the file it belongs in is
  `name ++ ".ml"`. -/
  name : String
  /-- A header comment, emitted first, without the `(* *)`. -/
  header : Option String := none
  items : List Decl

namespace Module
/-- A module with a "generated, do not edit" header. -/
def generated (name : String) (by_ : String) (items : List Decl) : Module :=
  { name := name, header := some ("Generated by " ++ by_ ++ ". Do not edit."), items := items }
end Module

end OCaml5.Ml
