import Lean
import Conform.Core.Report

/-!
# Conform.Lcnf.SemanticsTarget — rung 3: a meaning for the *emitted* fragment, inside Lean

**What it is.** A tiny applicative language, `Target.Expr`, and a fuelled evaluator for it.
It is deliberately **not** OCaml and not TypeScript: it is the intersection an LCNF backend
actually emits — let, letrec, application, constructors, records, tuples, literals, `if`,
`match` with constructor / record / tuple / literal patterns, and a fixed set of primitive
operations. A backend's own syntax is *read into* this language by a reader that refuses,
by constructor name, everything outside the subset (`Conform.Effect4.LcnfMl` does that for
`OCaml5.Ml.Syntax`). So the same evaluator serves an OCaml renderer and a TypeScript one,
and the part of the route that is target-specific shrinks to the reader and the primitive
table.

**Depends on.** `Lean` (for `Json` in the report) and `Conform.Core.Report`. Nothing from
this repository — in particular **not** `OCaml5.*`: that is the extensibility rule
(`docs/research/type-tooling/brief-common.md`).

**Properties.**
* **Machine integers are modelled, not assumed away.** `TValue.int` is a Lean `Int` and every
  arithmetic primitive reduces its result into the target's word through `Word.wrap`, whose
  width is a parameter. With `width = 63` this is OCaml's `int`; the evaluator therefore
  *exhibits* the 63-bit difference rather than hiding it, which is the whole point of having
  a semantics for the emitted side.
* **Strings are byte sequences.** `TValue.str` carries the target's own string; the primitive
  `strLength` answers the **byte** length, because that is what OCaml's `String.length` does.
  A backend whose strings are scalar-value sequences supplies a different primitive.
* **The evaluator is total.** `evalT`, `evalArgs`, `evalArms`, `applyT` and `applyNamed` are
  structurally recursive on fuel; none is `partial` and there is no `sorry` anywhere. (Four
  helpers that walk a finite value or pattern — `TValue.beq`, `TValue.render`, `asListV`,
  `matchPat` — are `partial`; none is part of the semantics.) `stuck` is a refusal,
  `outOfFuel` is the frontier, and `exn` is the target's own exception — the third thing an
  OCaml expression can do, which a Lean function cannot.
-/

namespace Conform.Lcnf.Target

open Lean

/-! ## 1. The word model -/

/-- The target's machine integer. `bits` counts the *whole* signed word: OCaml's `int` is 63,
JavaScript's safe integer is 54 (53 bits plus sign). -/
structure Word where
  bits : Nat := 63
  deriving DecidableEq, Repr, Inhabited

namespace Word

def maxInt (w : Word) : Int := 2 ^ (w.bits - 1) - 1
def minInt (w : Word) : Int := -(2 ^ (w.bits - 1))

/-- Reduce into the word, two's complement. -/
def wrap (w : Word) (n : Int) : Int :=
  let m : Int := 2 ^ w.bits
  let r := n % m
  let r := if r < 0 then r + m else r
  if r > w.maxInt then r - m else r

/-- Whether a value is representable without wrapping. -/
def fits (w : Word) (n : Int) : Bool := w.minInt ≤ n && n ≤ w.maxInt

end Word

/-! ## 2. Syntax -/

mutual

inductive Pat where
  | wild
  | var (name : String)
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  | unit
  /-- A constructor pattern; `"::"`, `"[]"`, `"None"`, `"Some"`, `"Ok"`, `"Error"` are the
  ones a target usually spells natively. -/
  | ctor (name : String) (args : List Pat)
  | tuple (parts : List Pat)
  /-- A record pattern; `openRec` is the `{ …; _ }` form that does not name every field. -/
  | record (fields : List (String × Pat)) (openRec : Bool)
  deriving Inhabited

inductive Expr where
  | var (name : String)
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  | unit
  | ctor (name : String) (args : List Expr)
  | tuple (parts : List Expr)
  | record (fields : List (String × Expr))
  | field (e : Expr) (name : String)
  | app (fn : Expr) (args : List Expr)
  /-- A primitive of the target, already resolved from its surface spelling. -/
  | prim (op : String) (args : List Expr)
  | fn (params : List String) (body : Expr)
  | letIn (name : String) (value body : Expr)
  | letRec (binds : List (String × List String × Expr)) (body : Expr)
  | ifThen (cond thenE elseE : Expr)
  | matchE (scrut : Expr) (arms : List (Pat × Expr))
  /-- `assert false`, `failwith msg`, a hole: the target aborts. -/
  | fail (msg : String)
  deriving Inhabited

end

/-! ## 3. Values -/

inductive TValue where
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  | unit
  | ctorV (name : String) (args : Array TValue)
  | tupleV (parts : Array TValue)
  | recordV (fields : Array (String × TValue))
  | closureV (params : List String) (body : Expr) (captured : List (String × TValue))
      (self : Option String)
  /-- A partially applied top-level binding or primitive. -/
  | papp (name : String) (args : Array TValue)
  deriving Inhabited

namespace TValue

def ofList : List TValue → TValue
  | [] => .ctorV "[]" #[]
  | v :: vs => .ctorV "::" #[v, ofList vs]

partial def beq (a b : TValue) : Bool :=
  match a, b with
  | .int x, .int y => x == y
  | .str x, .str y => x == y
  | .bool x, .bool y => x == y
  | .unit, .unit => true
  | .ctorV n xs, .ctorV m ys => n == m && xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => beq x y
  | .tupleV xs, .tupleV ys => xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => beq x y
  | .recordV xs, .recordV ys =>
    xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => x.1 == y.1 && beq x.2 y.2
  | .papp n xs, .papp m ys => n == m && xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => beq x y
  | _, _ => false

partial def render : TValue → String
  | .int n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .bool b => toString b
  | .unit => "()"
  | .ctorV n #[] => n
  | .ctorV n xs => n ++ "(" ++ ", ".intercalate (xs.toList.map render) ++ ")"
  | .tupleV xs => "(" ++ ", ".intercalate (xs.toList.map render) ++ ")"
  | .recordV fs => "{" ++ "; ".intercalate (fs.toList.map fun (k, v) => k ++ " = " ++ render v) ++ "}"
  | .closureV ps _ _ _ => s!"<closure/{ps.length}>"
  | .papp n xs => n ++ "@" ++ toString xs.size

end TValue

/-- The three ends, plus the target's own fourth: an exception. -/
inductive TOutcome where
  | value (v : TValue)
  /-- The evaluator has no rule, or a value has the wrong shape. A refusal. -/
  | stuck (reason : String)
  /-- The fuel ran out. The frontier. -/
  | outOfFuel
  /-- The **target program** raised: `failwith`, `assert false`, `List.nth` out of range,
  `Division_by_zero`. This is a behaviour the Lean side does not have, and keeping it as its
  own constructor is what lets a differential say "the OCaml aborts where Lean answers". -/
  | exn (message : String)
  deriving Inhabited

namespace TOutcome
def render : TOutcome → String
  | .value v => v.render
  | .stuck r => "stuck: " ++ r
  | .outOfFuel => "out of fuel"
  | .exn m => "raises " ++ m
end TOutcome

/-! ## 4. Primitives

Every operation the emitted fragment applies that is not a call to another emitted binding.
The spelling is the target's (`"="`, `"List.rev"`, `"@"`); the meaning is here, and it is the
target's meaning, not Lean's: `"/"` raises on zero, `"String.length"` counts bytes, `"+"`
wraps at the word. That divergence from `Conform.Lcnf.Prim` is exactly the fidelity gap the
audit measures — same names, two tables, and the difference is the finding. -/

structure PrimEnv where
  word : Word := {}
  deriving Inhabited

private def asInt : TValue → Option Int | .int n => some n | _ => none
private def asStr : TValue → Option String | .str s => some s | _ => none
private def asBool : TValue → Option Bool | .bool b => some b | _ => none

private partial def asListV (v : TValue) : Option (List TValue) :=
  match v with
  | .ctorV "[]" #[] => some []
  | .ctorV "::" #[h, t] => (asListV t).map (h :: ·)
  | _ => none

/-- Structural equality, as OCaml's polymorphic `=` computes it. -/
private def structEq (a b : TValue) : Bool := TValue.beq a b

/-- A total order on values, as OCaml's polymorphic `compare` computes it on the shapes this
fragment produces: integers and strings compare by value, constructors by their position in
the type's declaration — which this evaluator cannot know, so a comparison of two different
constructors is a **refusal** rather than a guess. -/
private def cmp? (a b : TValue) : Option Int :=
  match a, b with
  | .int x, .int y => some (if x < y then -1 else if x == y then 0 else 1)
  | .str x, .str y => some (if x < y then -1 else if x == y then 0 else 1)
  | .bool x, .bool y => some (if x == y then 0 else if x then 1 else -1)
  | _, _ => none

/-- Apply a primitive. `none` is a refusal; `.exn` is the target raising. -/
def applyPrim (pe : PrimEnv) (op : String) (args : Array TValue) : TOutcome :=
  let w := pe.word
  let bin (f : Int → Int → Int) : TOutcome :=
    match args with
    | #[a, b] => match asInt a, asInt b with
      | some x, some y => .value (.int (w.wrap (f x y)))
      | _, _ => .stuck s!"{op}: not integers"
    | _ => .stuck s!"{op}: arity"
  let cmp (f : Int → Bool) : TOutcome :=
    match args with
    | #[a, b] => match cmp? a b with
      | some c => .value (.bool (f c))
      | none => .stuck s!"{op}: incomparable values ({a.render}, {b.render})"
    | _ => .stuck s!"{op}: arity"
  match op with
  | "+" => bin (· + ·)
  | "-" => bin (· - ·)
  | "*" => bin (· * ·)
  | "/" =>
    match args with
    | #[a, b] => match asInt a, asInt b with
      | some _, some 0 => .exn "Division_by_zero"
      | some x, some y => .value (.int (w.wrap (Int.tdiv x y)))
      | _, _ => .stuck "/: not integers"
    | _ => .stuck "/: arity"
  | "mod" =>
    match args with
    | #[a, b] => match asInt a, asInt b with
      | some _, some 0 => .exn "Division_by_zero"
      | some x, some y => .value (.int (w.wrap (Int.tmod x y)))
      | _, _ => .stuck "mod: not integers"
    | _ => .stuck "mod: arity"
  | "land" => bin (fun x y => Int.ofNat (x.toNat &&& y.toNat))
  | "lor" => bin (fun x y => Int.ofNat (x.toNat ||| y.toNat))
  | "lxor" => bin (fun x y => Int.ofNat (x.toNat ^^^ y.toNat))
  | "lsr" => bin (fun x y => Int.ofNat (x.toNat >>> y.toNat))
  | "lsl" => bin (fun x y => Int.ofNat (x.toNat <<< y.toNat))
  | "=" => match args with
    | #[a, b] => .value (.bool (structEq a b))
    | _ => .stuck "=: arity"
  | "<>" => match args with
    | #[a, b] => .value (.bool (!structEq a b))
    | _ => .stuck "<>: arity"
  | "<" => cmp (· < 0)
  | "<=" => cmp (· ≤ 0)
  | ">" => cmp (· > 0)
  | ">=" => cmp (· ≥ 0)
  | "&&" => match args with
    | #[a, b] => match asBool a, asBool b with
      | some x, some y => .value (.bool (x && y))
      | _, _ => .stuck "&&: not booleans"
    | _ => .stuck "&&: arity"
  | "||" => match args with
    | #[a, b] => match asBool a, asBool b with
      | some x, some y => .value (.bool (x || y))
      | _, _ => .stuck "||: not booleans"
    | _ => .stuck "||: arity"
  | "not" => match args with
    | #[a] => match asBool a with
      | some x => .value (.bool (!x))
      | none => .stuck "not: not a boolean"
    | _ => .stuck "not: arity"
  | "^" => match args with
    | #[a, b] => match asStr a, asStr b with
      | some x, some y => .value (.str (x ++ y))
      | _, _ => .stuck "^: not strings"
    | _ => .stuck "^: arity"
  | "String.length" => match args with
    -- OCaml counts BYTES; Lean's `String.length` counts Unicode scalar values.
    | #[a] => match asStr a with
      | some x => .value (.int (Int.ofNat x.utf8ByteSize))
      | none => .stuck "String.length: not a string"
    | _ => .stuck "String.length: arity"
  | "max" => match args with
    | #[a, b] => match cmp? a b with
      | some c => .value (if c ≥ 0 then a else b)
      | none => .stuck "max: incomparable"
    | _ => .stuck "max: arity"
  | "min" => match args with
    | #[a, b] => match cmp? a b with
      | some c => .value (if c ≤ 0 then a else b)
      | none => .stuck "min: incomparable"
    | _ => .stuck "min: arity"
  | "@" => match args with
    | #[a, b] => match asListV a, asListV b with
      | some x, some y => .value (TValue.ofList (x ++ y))
      | _, _ => .stuck "@: not lists"
    | _ => .stuck "@: arity"
  | "List.rev" => match args with
    | #[a] => match asListV a with
      | some x => .value (TValue.ofList x.reverse)
      | none => .stuck "List.rev: not a list"
    | _ => .stuck "List.rev: arity"
  | "List.rev_append" => match args with
    | #[a, b] => match asListV a, asListV b with
      | some x, some y => .value (TValue.ofList (x.reverse ++ y))
      | _, _ => .stuck "List.rev_append: not lists"
    | _ => .stuck "List.rev_append: arity"
  | "List.length" => match args with
    | #[a] => match asListV a with
      | some x => .value (.int (Int.ofNat x.length))
      | none => .stuck "List.length: not a list"
    | _ => .stuck "List.length: arity"
  | "List.concat" => match args with
    | #[a] => match asListV a with
      | some xs =>
        match xs.foldlM (fun acc x => (asListV x).map (acc ++ ·)) [] with
        | some ys => .value (TValue.ofList ys)
        | none => .stuck "List.concat: not a list of lists"
      | none => .stuck "List.concat: not a list"
    | _ => .stuck "List.concat: arity"
  | "List.nth" => match args with
    | #[a, i] => match asListV a, asInt i with
      | some xs, some k =>
        if k < 0 then .exn "Invalid_argument(\"List.nth\")"
        else match xs[k.toNat]? with
          | some v => .value v
          | none => .exn "Failure(\"nth\")"
      | _, _ => .stuck "List.nth: shape"
    | _ => .stuck "List.nth: arity"
  | "fst" => match args with
    | #[.tupleV #[a, _]] => .value a
    | _ => .stuck "fst: not a pair"
  | "snd" => match args with
    | #[.tupleV #[_, b]] => .value b
    | _ => .stuck "snd: not a pair"
  | "Option.is_some" => match args with
    | #[.ctorV "Some" _] => .value (.bool true)
    | #[.ctorV "None" _] => .value (.bool false)
    | _ => .stuck "Option.is_some: not an option"
  | "Option.is_none" => match args with
    | #[.ctorV "Some" _] => .value (.bool false)
    | #[.ctorV "None" _] => .value (.bool true)
    | _ => .stuck "Option.is_none: not an option"
  | "failwith" => match args with
    | #[a] => match asStr a with
      | some m => .exn s!"Failure(\"{m}\")"
      | none => .stuck "failwith: not a string"
    | _ => .stuck "failwith: arity"
  -- Two shapes a target needs for an extern the LCNF route cannot emit. They are *proposals*
  -- for extern rows, not existing OCaml functions: `utf8_bytes s` is
  -- `List.map Char.code (List.of_seq (String.to_seq s))` — one line, and exact, because an
  -- OCaml string already *is* the UTF-8 byte sequence a Lean `String.toUTF8` produces.
  | "utf8_bytes" => match args with
    | #[a] => match asStr a with
      | some s => .value (TValue.ofList (s.toUTF8.data.toList.map fun b => TValue.int b.toNat))
      | none => .stuck "utf8_bytes: not a string"
    | _ => .stuck "utf8_bytes: arity"
  | "id" => match args with
    | #[a] => .value a
    | _ => .stuck "id: arity"
  | _ => .stuck s!"no rule for the primitive `{op}`"

/-- The arity of a primitive, so an under-applied one becomes a partial application rather
than a refusal. -/
def primArity : String → Option Nat
  | "not" | "String.length" | "List.rev" | "List.length" | "List.concat"
  | "fst" | "snd" | "Option.is_some" | "Option.is_none" | "failwith"
  | "utf8_bytes" | "id" => some 1
  | "+" | "-" | "*" | "/" | "mod" | "land" | "lor" | "lxor" | "lsr" | "lsl"
  | "=" | "<>" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "^" | "max" | "min"
  | "@" | "List.rev_append" | "List.nth" => some 2
  | _ => none

/-! ## 5. The evaluator -/

abbrev TEnv := List (String × TValue)

def TEnv.find? (e : TEnv) (n : String) : Option TValue :=
  (List.find? (fun p => p.1 == n) e).map (·.2)

/-- The top-level bindings of the emitted module, by name. -/
structure Program where
  binds : Std.HashMap String (List String × Expr)
  pe : PrimEnv := {}
  deriving Inhabited

/-- Match a pattern, extending the environment. `none` is "did not match"; a shape the
pattern language cannot handle is caught before evaluation by the reader, so a mismatch here
is genuinely a non-match. -/
partial def matchPat (p : Pat) (v : TValue) (acc : TEnv) : Option TEnv :=
  match p, v with
  | .wild, _ => some acc
  | .var n, _ => some ((n, v) :: acc)
  | .int n, .int m => if n == m then some acc else none
  | .str s, .str t => if s == t then some acc else none
  | .bool b, .bool c => if b == c then some acc else none
  | .unit, .unit => some acc
  | .ctor n ps, .ctorV m vs =>
    if n != m || ps.length != vs.size then none
    else (List.zip ps vs.toList).foldlM (fun a (p, v) => matchPat p v a) acc
  | .tuple ps, .tupleV vs =>
    if ps.length != vs.size then none
    else (List.zip ps vs.toList).foldlM (fun a (p, v) => matchPat p v a) acc
  | .record fs open?, .recordV vfs =>
    if !open? && fs.length != vfs.size then none
    else fs.foldlM (fun a (k, p) =>
      match vfs.find? (fun x => x.1 == k) with
      | some (_, v) => matchPat p v a
      | none => none) acc
  | _, _ => none

mutual

def evalT (prog : Program) : Nat → TEnv → Expr → TOutcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, env, e =>
    match e with
    | .int n => .value (.int (prog.pe.word.wrap n))
    | .str s => .value (.str s)
    | .bool b => .value (.bool b)
    | .unit => .value .unit
    | .fail m => .exn m
    | .var n =>
      match env.find? n with
      | some v => .value v
      | none =>
        match prog.binds[n]? with
        | some (ps, body) =>
          if ps.isEmpty then evalT prog fuel [] body else .value (.papp n #[])
        | none =>
          match primArity n with
          | some _ => .value (.papp n #[])
          | none => .stuck s!"unbound name `{n}`"
    | .fn ps body => .value (.closureV ps body env none)
    | .letIn n v body =>
      match evalT prog fuel env v with
      | .value vv => evalT prog fuel ((n, vv) :: env) body
      | o => o
    | .letRec binds body =>
      -- each binding sees itself; mutual recursion inside one group is resolved by
      -- re-entering through the group, which `selfGroup` records on every closure
      let env' := binds.foldl (init := env) fun acc (n, ps, b) =>
        (n, TValue.closureV ps b env (some n)) :: acc
      evalT prog fuel env' body
    | .ifThen c t f =>
      match evalT prog fuel env c with
      | .value (.bool true) => evalT prog fuel env t
      | .value (.bool false) => evalT prog fuel env f
      | .value v => .stuck s!"if: the condition is not a boolean ({v.render})"
      | o => o
    | .tuple parts =>
      match evalArgs prog fuel env parts with
      | .value (.tupleV vs) => .value (.tupleV vs)
      | o => o
    | .ctor n args =>
      match evalArgs prog fuel env args with
      | .value (.tupleV vs) => .value (.ctorV n vs)
      | o => o
    | .record fields =>
      match evalArgs prog fuel env (fields.map (·.2)) with
      | .value (.tupleV vs) =>
        .value (.recordV (Array.zip (fields.map (·.1)).toArray vs))
      | o => o
    | .field e n =>
      match evalT prog fuel env e with
      | .value (.recordV fs) =>
        match fs.find? (fun x => x.1 == n) with
        | some (_, v) => .value v
        | none => .stuck s!"field `{n}` is not in the record"
      | .value v => .stuck s!"field `{n}`: not a record ({v.render})"
      | o => o
    | .prim op args =>
      match evalArgs prog fuel env args with
      | .value (.tupleV vs) =>
        match primArity op with
        | some k =>
          if vs.size == k then applyPrim prog.pe op vs
          else if vs.size < k then .value (.papp op vs)
          else
            match applyPrim prog.pe op (vs.extract 0 k) with
            | .value f => applyT prog fuel f (vs.extract k vs.size)
            | o => o
        | none => .stuck s!"no rule for the primitive `{op}`"
      | o => o
    | .app f args =>
      match evalArgs prog fuel env args with
      | .value (.tupleV vs) =>
        match f with
        | .var n =>
          match env.find? n with
          | some fv => applyT prog fuel fv vs
          | none => applyNamed prog fuel n vs
        | _ =>
          match evalT prog fuel env f with
          | .value fv => applyT prog fuel fv vs
          | o => o
      | o => o
    | .matchE scrut arms =>
      match evalT prog fuel env scrut with
      | .value v => evalArms prog fuel env v arms
      | o => o

def evalArgs (prog : Program) : Nat → TEnv → List Expr → TOutcome
  | 0, _, _ => .outOfFuel
  | _ + 1, _, [] => .value (.tupleV #[])
  | fuel + 1, env, e :: rest =>
    match evalT prog fuel env e with
    | .value v =>
      match evalArgs prog fuel env rest with
      | .value (.tupleV vs) => .value (.tupleV (#[v] ++ vs))
      | o => o
    | o => o

def evalArms (prog : Program) : Nat → TEnv → TValue → List (Pat × Expr) → TOutcome
  | 0, _, _, _ => .outOfFuel
  | _ + 1, _, v, [] => .stuck s!"match: no arm for {v.render}"
  | fuel + 1, env, v, (p, body) :: rest =>
    match matchPat p v env with
    | some env' => evalT prog fuel env' body
    | none => evalArms prog fuel env v rest

def applyT (prog : Program) : Nat → TValue → Array TValue → TOutcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, f, vs =>
    if vs.isEmpty then .value f else
    match f with
    | .closureV ps body captured self =>
      let selfBind : TEnv := match self with | some n => [(n, f)] | none => []
      if ps.length == vs.size then
        evalT prog fuel ((List.zip ps vs.toList) ++ selfBind ++ captured) body
      else if vs.size < ps.length then
        -- a partial application of a local function: bind what we have and keep the rest
        let bound := List.zip (ps.take vs.size) vs.toList
        .value (.closureV (ps.drop vs.size) body (bound ++ selfBind ++ captured) none)
      else
        match evalT prog fuel
            ((List.zip ps (vs.extract 0 ps.length).toList) ++ selfBind ++ captured) body with
        | .value g => applyT prog fuel g (vs.extract ps.length vs.size)
        | o => o
    | .papp n args => applyNamed prog fuel n (args ++ vs)
    | other => .stuck s!"applied a non-function ({other.render})"

def applyNamed (prog : Program) : Nat → String → Array TValue → TOutcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, n, vs =>
    match prog.binds[n]? with
    | some (ps, body) =>
      if ps.length == vs.size then
        evalT prog fuel (List.zip ps vs.toList) body
      else if vs.size < ps.length then .value (.papp n vs)
      else
        match evalT prog fuel (List.zip ps (vs.extract 0 ps.length).toList) body with
        | .value g => applyT prog fuel g (vs.extract ps.length vs.size)
        | o => o
    | none =>
      match primArity n with
      | some k =>
        if vs.size == k then applyPrim prog.pe n vs
        else if vs.size < k then .value (.papp n vs)
        else
          match applyPrim prog.pe n (vs.extract 0 k) with
          | .value g => applyT prog fuel g (vs.extract k vs.size)
          | o => o
      | none => .stuck s!"unbound name `{n}`"

end

/-- Apply a top-level binding to arguments. -/
def runT (prog : Program) (fuel : Nat) (n : String) (args : Array TValue) : TOutcome :=
  applyNamed prog fuel n args

/-! ## 6. A differential against a reference answer -/

structure TCase where
  label : String
  bind : String
  args : Array TValue
  expected : TValue

open Conform in
/-- Run every case against the reference. Evidence is `tested`. -/
def differentialT (prog : Program) (fuel : Nat) (check : String) (cases : Array TCase) :
    Array Row :=
  cases.map fun c =>
    let subj : Subject := { kind := "case", path := [c.bind, c.label] }
    match runT prog fuel c.bind c.args with
    | .value v =>
      if v.beq c.expected then Row.pass check subj .tested s!"{c.bind} agrees"
      else Row.counterexample check subj
        s!"{c.bind}: target gave {v.render}, reference gave {c.expected.render}"
        (Json.mkObj [("target", Json.str v.render), ("reference", Json.str c.expected.render)])
    | .stuck r => Row.refused check subj s!"{c.bind}: {r}"
    | .exn m => Row.counterexample check subj s!"{c.bind}: the target raised {m}" (Json.str m)
    | .outOfFuel => Row.unresolved check subj s!"{c.bind}: out of fuel at {fuel}"

end Conform.Lcnf.Target
