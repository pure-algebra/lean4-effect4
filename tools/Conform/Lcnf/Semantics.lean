import Lean
import Conform.Lcnf.Validity

/-!
# Conform.Lcnf.Semantics — rung 2: a meaning for the mono `Code .pure` fragment, inside Lean

**What it is.** A fuelled interpreter for mono-phase LCNF over a first-order value domain,
and the primitive table that is its only assumption. Given an environment, the interpreter
evaluates a `Decl .pure` applied to argument values by reading the declaration's own `Code`;
it descends into every callee that has a mono body, so the **only** constants it needs a rule
for are the ones with no body at all — the genuine `@[extern]`s. That table, `PrimTable`, is
therefore not a convenience: it is the *specification* of what any backend for this fragment
must implement, and it is small (nine rows carry `Effect4.Program.Ty`'s whole closure).

**Depends on.** `Lean`, `Conform.Lcnf.Validity` (for `stripRedArg`). Nothing from this
repository; roots, primitives and marshalling arrive as arguments.

**Properties.**
* **The evaluator is total.** `evalCode`, `evalLetValue`, `evalConst`, `applyValue`,
  `applyPrim` and `selectAlt` are structurally recursive on a `Nat` fuel; none is `partial`
  and there is no `sorry` anywhere. (Five helpers that walk a finite `Value` or a finite
  `Code` for printing, comparison or name collection — `Value.toList?`, `Value.beq`,
  `Value.render`, `arrayOfList`, `constNames` — are `partial`; none of them is part of the
  semantics.) Running out of fuel is `Outcome.outOfFuel`, the machine's *frontier* — distinct
  from `Outcome.stuck`, a *refusal* (a rule the interpreter does not have, a value of the
  wrong shape), and distinct from `Value.erased`, which is *absent data*. Three things, three
  names (`brief-common.md`).
* **First-order.** `Value` holds constructor trees, naturals, strings, arrays and code
  closures. A closure carries a `Code .pure` and an association list, not a Lean function, so
  a `Value` can be printed, compared and put in a report.
* **The primitive table is data.** `Prim` is an inductive and `Prim.apply` is one total
  function over it, so the table can be rendered into the manifest and lined up row by row
  against a target's builtin table. Nothing in this file stores a Lean function.
* **Constructor arity is the compiler's.** A construction takes `numParams` erased arguments
  and then exactly `numFields` field arguments, and a `cases` alternative binds exactly
  `numFields` parameters — `Check.Pure.checkCases` (`LCNF/Check.lean:225-236`) enforces both,
  so construction and destruction agree *by the compiler's own invariant* rather than by this
  file's convention. That is the representation-coherence property X2's TypeScript emitter
  lacked (`2026-09-09-seat-types-tooling.md` §5.5).
-/

namespace Conform.Lcnf

open Lean Compiler LCNF

/-! ## 1. The value domain -/

/-- A first-order runtime value of the mono fragment.

`Array` and `ByteArray` are one form: `ByteArray` is the one-field structure
`⟨data : Array UInt8⟩` and the compiler treats both as runtime builtins that are never
unwrapped (`LCNF/Util.lean:40-47`), so `ByteArray.data` is the identity here and the
identification is exact rather than a convenience. -/
inductive Value where
  /-- A type argument or a proof: `◾`. Absent data. -/
  | erased
  /-- `Nat`, and every `UIntN`/`USize`, whose mono representation is a natural. -/
  | nat (n : Nat)
  /-- A Lean `String`: a sequence of Unicode scalar values. -/
  | str (s : String)
  /-- A `ByteArray` or an `Array α`. -/
  | array (elems : Array Value)
  /-- A constructor application: the constructor's name and **all** of its fields, in order,
  with an erased field held as `.erased`. -/
  | ctor (name : Name) (fields : Array Value)
  /-- A local function or join point: its parameters, its body, the environment it captured,
  and (for a recursive local function) its own binder, re-bound on entry. -/
  | closure (params : Array FVarId) (body : Code .pure) (captured : List (FVarId × Value))
      (self : Option FVarId)
  /-- An under-applied global constant. -/
  | papp (head : Name) (args : Array Value)
  deriving Inhabited

namespace Value

/-- `Bool` as the constructor it is at mono. -/
def bool (b : Bool) : Value := .ctor (if b then ``Bool.true else ``Bool.false) #[]

def ofList : List Value → Value
  | [] => .ctor ``List.nil #[]
  | v :: vs => .ctor ``List.cons #[v, ofList vs]

def ofNatList (ns : List Nat) : Value := ofList (ns.map Value.nat)

def toNat? : Value → Option Nat
  | .nat n => some n
  | _ => none

def toStr? : Value → Option String
  | .str s => some s
  | _ => none

def toBool? : Value → Option Bool
  | .ctor n #[] => if n == ``Bool.true then some true else if n == ``Bool.false then some false else none
  | _ => none

partial def toList? (v : Value) : Option (List Value) :=
  match v with
  | .ctor n #[] => if n == ``List.nil then some [] else none
  | .ctor n #[h, t] => if n == ``List.cons then (toList? t).map (h :: ·) else none
  | _ => none

/-- Structural equality on the data part. Two closures are never equal (a closure is not
data); the caller compares only first-order results. -/
partial def beq (a b : Value) : Bool :=
  match a, b with
  | .erased, .erased => true
  | .nat x, .nat y => x == y
  | .str x, .str y => x == y
  | .array xs, .array ys => xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => beq x y
  | .ctor n xs, .ctor m ys => n == m && xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => beq x y
  | .papp n xs, .papp m ys => n == m && xs.size == ys.size && (Array.zip xs ys).all fun (x, y) => beq x y
  | _, _ => false

/-- A one-line spelling, for report messages. -/
partial def render : Value → String
  | .erased => "◾"
  | .nat n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .array xs => "#[" ++ ", ".intercalate (xs.toList.map render) ++ "]"
  | .ctor n #[] => n.toString
  | .ctor n xs => n.toString ++ "(" ++ ", ".intercalate (xs.toList.map render) ++ ")"
  | .closure ps _ _ _ => s!"<closure/{ps.size}>"
  | .papp n xs => n.toString ++ "@" ++ toString xs.size

end Value

/-- The three things an evaluation can end as. -/
inductive Outcome where
  /-- A value. -/
  | value (v : Value)
  /-- The interpreter refused: a rule it does not have, or a value of the wrong shape. The
  string names which. -/
  | stuck (reason : String)
  /-- The fuel ran out. The machine's frontier: not an answer and not a refusal. -/
  | outOfFuel
  deriving Inhabited

namespace Outcome
def value? : Outcome → Option Value
  | .value v => some v
  | _ => none

def render : Outcome → String
  | .value v => v.render
  | .stuck r => "stuck: " ++ r
  | .outOfFuel => "out of fuel"
end Outcome

/-! ## 2. The primitive table

The constants with no mono body. Every row is a claim about what the Lean constant means,
and this inductive **is** the claim: it is data, it can be printed, and it can be lined up
against a target's builtin table row by row (which is what the fidelity classes of
`Conform.Effect4.Lcnf` do for OCaml). -/

inductive Prim where
  | natAdd | natSub | natMul | natDiv | natMod | natPow
  | natShiftLeft | natShiftRight | natLand | natLor | natXor
  /-- `Nat.decEq`, `Nat.beq`: `Decidable (n = m)` is `Bool` at mono. -/
  | natDecEq
  | natDecLt | natDecLe
  | natSucc | natPred
  | boolNot | boolAnd | boolOr | boolDecEq
  | strAppend | strDecEq | strLength
  /-- `String.toUTF8 : String → ByteArray`, as the array of its UTF-8 bytes. -/
  | strToUTF8
  /-- A coercion that is the identity on this value domain: `ByteArray.data`,
  `UInt8.toNat`, `USize.toNat`, `UInt8.toUInt64`, … -/
  | identity
  /-- `UIntN.ofNat`: reduce mod `2 ^ bits`. -/
  | uintOfNat (bits : Nat)
  | arrayToList | listToArray | arrayMkEmpty | arrayPush | arraySize
  /-- `Array.uget`/`get!`/`fget`: Lean's `get!` answers a default on an out-of-range index;
  this row is *stuck* there instead, because "the default of the element type" is not
  something the value domain can produce. A stuck row is a refusal a report can carry; a
  wrong answer is not. -/
  | arrayGet
  | listLength
  deriving DecidableEq, Repr, Inhabited

namespace Prim

/-- How many **relevant** (non-erased) arguments the row takes. -/
def arity : Prim → Nat
  | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natPow => 2
  | .natShiftLeft | .natShiftRight | .natLand | .natLor | .natXor => 2
  | .natDecEq | .natDecLt | .natDecLe => 2
  | .natSucc | .natPred => 1
  | .boolNot => 1
  | .boolAnd | .boolOr | .boolDecEq => 2
  | .strAppend | .strDecEq => 2
  | .strLength | .strToUTF8 => 1
  | .identity => 1
  | .uintOfNat _ => 1
  | .arrayToList | .listToArray | .arrayMkEmpty | .arraySize | .listLength => 1
  | .arrayPush | .arrayGet => 2

private def natBin (f : Nat → Nat → Nat) (a b : Value) : Option Value := do
  return .nat (f (← a.toNat?) (← b.toNat?))

private def natCmp (f : Nat → Nat → Bool) (a b : Value) : Option Value := do
  return .bool (f (← a.toNat?) (← b.toNat?))

private def boolBin (f : Bool → Bool → Bool) (a b : Value) : Option Value := do
  return .bool (f (← a.toBool?) (← b.toBool?))

private partial def arrayOfList (v : Value) : Option (Array Value) := do
  return (← v.toList?).toArray

/-- The meaning of a row on relevant arguments. `none` is a refusal: the wrong number of
arguments, or an argument of the wrong shape. -/
def apply : Prim → Array Value → Option Value
  | .natAdd, #[a, b] => natBin (· + ·) a b
  | .natSub, #[a, b] => natBin (· - ·) a b
  | .natMul, #[a, b] => natBin (· * ·) a b
  | .natDiv, #[a, b] => natBin (· / ·) a b
  | .natMod, #[a, b] => natBin (· % ·) a b
  | .natPow, #[a, b] => natBin (· ^ ·) a b
  | .natShiftLeft, #[a, b] => natBin (· <<< ·) a b
  | .natShiftRight, #[a, b] => natBin (· >>> ·) a b
  | .natLand, #[a, b] => natBin (· &&& ·) a b
  | .natLor, #[a, b] => natBin (· ||| ·) a b
  | .natXor, #[a, b] => natBin (· ^^^ ·) a b
  | .natDecEq, #[a, b] => natCmp (· == ·) a b
  | .natDecLt, #[a, b] => natCmp (· < ·) a b
  | .natDecLe, #[a, b] => natCmp (· ≤ ·) a b
  | .natSucc, #[a] => do return .nat ((← a.toNat?) + 1)
  | .natPred, #[a] => do return .nat ((← a.toNat?) - 1)
  | .boolNot, #[a] => do return .bool (!(← a.toBool?))
  | .boolAnd, #[a, b] => boolBin (· && ·) a b
  | .boolOr, #[a, b] => boolBin (· || ·) a b
  | .boolDecEq, #[a, b] => boolBin (· == ·) a b
  | .strAppend, #[a, b] => do return .str ((← a.toStr?) ++ (← b.toStr?))
  | .strDecEq, #[a, b] => do return .bool ((← a.toStr?) == (← b.toStr?))
  | .strLength, #[a] => do return .nat (← a.toStr?).length
  | .strToUTF8, #[a] => do
      return .array (((← a.toStr?).toUTF8.data).map fun b => Value.nat b.toNat)
  | .identity, #[a] => some a
  | .uintOfNat bits, #[a] => do return .nat ((← a.toNat?) % (2 ^ bits))
  | .arrayToList, #[a] => match a with
    | .array xs => some (Value.ofList xs.toList)
    | _ => none
  | .listToArray, #[a] => do return .array (← arrayOfList a)
  | .arrayMkEmpty, #[_] => some (.array #[])
  | .arrayPush, #[a, x] => match a with
    | .array xs => some (.array (xs.push x))
    | _ => none
  | .arraySize, #[a] => match a with
    | .array xs => some (.nat xs.size)
    | _ => none
  | .arrayGet, #[a, i] => match a, i with
    | .array xs, .nat k => xs[k]?
    | _, _ => none
  | .listLength, #[a] => do return .nat (← a.toList?).length
  | _, _ => none

protected def toString : Prim → String
  | .uintOfNat bits => s!"uintOfNat {bits}"
  | p => (repr p).pretty.replace "Conform.Lcnf.Prim." ""

instance : ToString Prim := ⟨Prim.toString⟩

end Prim

/-- A primitive table: pure data. Lookup strips a `_redArg` suffix, as the compiler's own
`reduceArity` twins require and as `OCaml5.Lcnf.builtin?` does. -/
abbrev PrimTable := List (Name × Prim)

def PrimTable.lookup? (t : PrimTable) (n : Name) : Option Prim :=
  let n := stripRedArg n
  (List.find? (fun p => p.1 == n) t).map (·.2)

/-! ## 3. The interpreter -/

/-- An association-list environment, keyed on the `FVarId`s the mono phase normalised
(`saveMono` runs `normalizeFVarIds`, `Passes.lean:66-74`) and which `Decl.check` guarantees
are unique inside one declaration. -/
abbrev Env := List (FVarId × Value)

def Env.find? (e : Env) (id : FVarId) : Option Value :=
  (List.find? (fun p => p.1 == id) e).map (·.2)

/-- What the interpreter reads. `decls` is a snapshot of the mono declarations it may
descend into; it is a plain map so the interpreter is pure. -/
structure Ctx where
  /-- Constructor arities: name ↦ (numParams, numFields). -/
  ctors : Std.HashMap Name (Nat × Nat)
  /-- Mono declarations by name, already `_redArg`-resolved by the caller. -/
  decls : Std.HashMap Name (Decl .pure)
  /-- The primitives: the constants with no body. -/
  prims : PrimTable
  /-- Names the caller wants treated as primitive even though they have a body — used to
  audit a target's builtin table against the bodies it short-circuits. -/
  shortCircuit : PrimTable := []

/-- An argument, resolved against the environment. -/
def argValue (env : Env) : Arg .pure → Except String Value
  | .erased => .ok .erased
  | .type _ => .ok .erased
  | .fvar id =>
    match env.find? id with
    | some v => .ok v
    | none => .error s!"unbound free variable {id.name}"

def argValues (env : Env) (as : Array (Arg .pure)) : Except String (Array Value) :=
  as.foldlM (init := #[]) fun acc a => do return acc.push (← argValue env a)

/-- The relevant (non-erased) arguments, for a primitive. -/
def relevant (vs : Array Value) : Array Value :=
  vs.filter fun | .erased => false | _ => true

mutual

/-- Evaluate a `Code .pure` under an environment. Structurally recursive on `fuel`. -/
def evalCode (ctx : Ctx) : Nat → Env → Code .pure → Outcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, env, code =>
    match code with
    | .return x =>
      match env.find? x with
      | some v => .value v
      | none => .stuck s!"return: unbound {x.name}"
    | .unreach _ => .stuck "unreach"
    | .let decl k =>
      match evalLetValue ctx fuel env decl.value with
      | .value v => evalCode ctx fuel ((decl.fvarId, v) :: env) k
      | o => o
    | .fun decl k =>
      let cl : Value := .closure (decl.params.map (·.fvarId)) decl.value env (some decl.fvarId)
      evalCode ctx fuel ((decl.fvarId, cl) :: env) k
    | .jp decl k =>
      let cl : Value := .closure (decl.params.map (·.fvarId)) decl.value env none
      evalCode ctx fuel ((decl.fvarId, cl) :: env) k
    | .jmp j args =>
      match env.find? j with
      | none => .stuck s!"jmp: unbound join point {j.name}"
      | some f =>
        match argValues env args with
        | .error e => .stuck e
        | .ok vs => applyValue ctx fuel f vs
    | .cases cs =>
      match env.find? cs.discr with
      | none => .stuck s!"cases: unbound discriminant {cs.discr.name}"
      | some (.ctor cname fields) =>
        match selectAlt cs.alts cname with
        | some (.alt _ ps k) =>
          if ps.size == fields.size then
            let env' := (Array.zip (ps.map (·.fvarId)) fields).toList ++ env
            evalCode ctx fuel env' k
          else
            .stuck s!"cases: alternative {cname} binds {ps.size} parameters but the value has {fields.size} fields"
        | some (.default k) => evalCode ctx fuel env k
        | none => .stuck s!"cases: no alternative for {cname} on {cs.typeName}"
      | some v => .stuck s!"cases on {cs.typeName}: the discriminant is not a constructor value ({v.render})"

/-- Evaluate a `LetValue`. -/
def evalLetValue (ctx : Ctx) : Nat → Env → LetValue .pure → Outcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, env, v =>
    match v with
    | .lit (.nat n) => .value (.nat n)
    | .lit (.str s) => .value (.str s)
    | .lit (.uint8 n) => .value (.nat n.toNat)
    | .lit (.uint16 n) => .value (.nat n.toNat)
    | .lit (.uint32 n) => .value (.nat n.toNat)
    | .lit (.uint64 n) => .value (.nat n.toNat)
    | .lit (.usize n) => .value (.nat n.toNat)
    | .erased => .value .erased
    | .proj typeName i s =>
      match env.find? s with
      | some (.ctor _ fields) =>
        match fields[i]? with
        | some f => .value f
        | none => .stuck s!"proj {typeName} #{i}: the value has {fields.size} fields"
      | some other => .stuck s!"proj {typeName} #{i}: not a constructor value ({other.render})"
      | none => .stuck s!"proj: unbound {s.name}"
    | .fvar f args =>
      match env.find? f with
      | none => .stuck s!"unbound {f.name}"
      | some fv =>
        if args.isEmpty then .value fv
        else
          match argValues env args with
          | .error e => .stuck e
          | .ok vs => applyValue ctx fuel fv vs
    | .const n _ args =>
      match argValues env args with
      | .error e => .stuck e
      | .ok vs => evalConst ctx fuel n vs

/-- Apply a global constant to already-evaluated arguments. -/
def evalConst (ctx : Ctx) : Nat → Name → Array Value → Outcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, n, vs =>
    -- a constructor: build the value, keeping exactly its fields
    match ctx.ctors[n]? with
    | some (numParams, numFields) =>
      if vs.size == numParams + numFields then
        .value (.ctor n (vs.extract numParams (numParams + numFields)))
      else if vs.size < numParams + numFields then
        .value (.papp n vs)
      else
        .stuck s!"constructor {n} applied to {vs.size} arguments, expected {numParams + numFields}"
    | none =>
    -- a short-circuited constant: the caller's table wins over the body
    match ctx.shortCircuit.lookup? n with
    | some p => applyPrim p n vs
    | none =>
    -- exact name only: a `reduceArity` wrapper and its `_redArg` twin have **different**
    -- arities, so substituting one for the other would mis-bind the parameters. Both are in
    -- `ctx.decls` under their own names (`Ctx.ofClosure`), and the wrapper's own body is the
    -- call to the twin.
    match ctx.decls[n]? with
    | some d =>
      match d.value with
      | .extern _ =>
        match ctx.prims.lookup? n with
        | some p => applyPrim p n vs
        | none => .stuck s!"no primitive rule for the extern {n}"
      | .code body =>
        if vs.size == d.params.size then
          evalCode ctx fuel (Array.zip (d.params.map (·.fvarId)) vs).toList body
        else if vs.size < d.params.size then
          .value (.papp n vs)
        else
          -- over-applied: run the declaration, then apply the result to the rest
          match evalCode ctx fuel (Array.zip (d.params.map (·.fvarId)) (vs.extract 0 d.params.size)).toList body with
          | .value f => applyValue ctx fuel f (vs.extract d.params.size vs.size)
          | o => o
    | none =>
      match ctx.prims.lookup? n with
      | some p => applyPrim p n vs
      | none => .stuck s!"no mono declaration and no primitive rule for {n}"

/-- Apply a value to arguments: a closure, a partial application, or a refusal. -/
def applyValue (ctx : Ctx) : Nat → Value → Array Value → Outcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, f, vs =>
    match f with
    | .closure ps body captured self =>
      -- a nullary local function is called with one unit-like argument in a target; here it
      -- is called with none, so an argument count of 0 against 0 parameters is the normal case
      if ps.size == vs.size then
        let selfBind : Env := match self with | some id => [(id, f)] | none => []
        evalCode ctx fuel ((Array.zip ps vs).toList ++ selfBind ++ captured) body
      else if vs.size < ps.size then
        .stuck s!"a local function of arity {ps.size} applied to {vs.size} arguments (LCNF jumps are saturated)"
      else
        .stuck s!"a local function of arity {ps.size} applied to {vs.size} arguments"
    | .papp head args => evalConst ctx fuel head (args ++ vs)
    | other => .stuck s!"applied a non-function ({other.render}) to {vs.size} arguments"

/-- A primitive row, on the relevant arguments. -/
def applyPrim : Prim → Name → Array Value → Outcome := fun p n vs =>
  let rel := relevant vs
  if rel.size != p.arity then
    .stuck s!"primitive {n} ({p}) takes {p.arity} relevant arguments, got {rel.size}"
  else
    match p.apply rel with
    | some v => .value v
    | none => .stuck s!"primitive {n} ({p}) refused its arguments: {", ".intercalate (rel.toList.map Value.render)}"

/-- The alternative for a constructor name, or the default. -/
def selectAlt (alts : Array (Alt .pure)) (cname : Name) : Option (Alt .pure) :=
  match alts.find? (fun | .alt c _ _ => c == cname | .default _ => false) with
  | some a => some a
  | none => alts.find? (fun | .default _ => true | .alt .. => false)

end

/-! ## 4. Driving a declaration -/

/-- Every constant a body names, as a `LetValue.const` head or as an `Alt.alt` constructor:
the superset from which the constructor arities are read. -/
private partial def constNames (c : Code .pure) (acc : Array Name) : Array Name :=
  match c with
  | .let decl k =>
    let acc := match decl.value with | .const n _ _ => acc.push n | _ => acc
    constNames k acc
  | .fun decl k | .jp decl k => constNames k (constNames decl.value acc)
  | .jmp _ _ | .return _ | .unreach _ => acc
  | .cases cs => cs.alts.foldl (init := acc) fun acc alt =>
      match alt with
      | .default k => constNames k acc
      | .alt c _ k => constNames k (acc.push c)

/-- Build a context from an environment and a set of declarations, resolving `_redArg`
wrappers to their twins so a call to either lands on the code. -/
def Ctx.ofClosure (env : Environment) (names : Array Name) (prims : PrimTable)
    (shortCircuit : PrimTable := []) : Ctx := Id.run do
  let mut decls : Std.HashMap Name (Decl .pure) := {}
  let mut ctors : Std.HashMap Name (Nat × Nat) := {}
  for n in names do
    -- the name itself, its `reduceArity` wrapper and its twin, each under its OWN name and
    -- with its OWN arity: a caller may reference either, and only the wrapper's body knows
    -- which of its parameters the twin kept.
    for m in #[n, stripRedArg n, n ++ redArgSuffix] do
      unless decls.contains m do
        if let some d := getDeclCore? env monoExt m then
          decls := decls.insert m d
  -- every constructor the environment knows that these declarations could build or match
  for (_, d) in decls.toList do
    for c in ctorNames d do
      if let some (.ctorInfo ci) := env.find? c then
        ctors := ctors.insert c (ci.numParams, ci.numFields)
  return { ctors, decls, prims, shortCircuit }
where
  ctorNames (d : Decl .pure) : Array Name :=
    match d.value with
    | .code code => constNames code #[]
    | .extern _ => #[]

/-- Apply a named declaration to argument values. -/
def run (ctx : Ctx) (fuel : Nat) (n : Name) (args : Array Value) : Outcome :=
  evalConst ctx fuel n args

/-! ## 5. A differential, as a report

A generic harness: a list of named cases, each an expected `Value` and a call. It is the
shape rung 2's validation takes, and rung 3's will take the same one against a target. -/

/-- One differential case. -/
structure Case where
  /-- The row's name, for the report subject. -/
  label : String
  /-- The declaration to run. -/
  decl : Name
  /-- The arguments, already marshalled into the value domain. -/
  args : Array Value
  /-- What the compiled Lean function answered, marshalled the same way. -/
  expected : Value

/-- Run every case, and report. Evidence is `tested`: a finite run over named inputs. -/
def differential (ctx : Ctx) (fuel : Nat) (check : String) (cases : Array Case) : Array Row :=
  cases.map fun c =>
    let subj : Subject := { kind := "case", path := [c.decl.toString, c.label] }
    match run ctx fuel c.decl c.args with
    | .value v =>
      if v.beq c.expected then
        Row.pass check subj .tested s!"{c.decl} agrees"
      else
        Row.counterexample check subj s!"{c.decl}: interpreter gave {v.render}, Lean gave {c.expected.render}"
          (Json.mkObj [ ("args", Json.arr (c.args.map fun a => Json.str a.render))
                      , ("interpreter", Json.str v.render), ("lean", Json.str c.expected.render) ])
    | .stuck r =>
      Row.refused check subj s!"{c.decl}: {r}"
        (Json.mkObj [("args", Json.arr (c.args.map fun a => Json.str a.render))])
    | .outOfFuel =>
      Row.unresolved check subj s!"{c.decl}: out of fuel at {fuel}"

end Conform.Lcnf
