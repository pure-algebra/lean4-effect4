import Lean
import OCaml5.Ml.Syntax
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Types

/-!
# OCaml5.Lcnf.Translate

**What it is.** Mono-phase LCNF (`Lean.Compiler.LCNF.Decl`, `Code`, `LetValue`, `Alt`) to
`OCaml5.Ml.Syntax` declarations, one Lean definition to one OCaml `let`, plus the call-graph
closure that decides *which* definitions to translate and the strongly-connected-component
ordering that decides how to emit them.

**Depends on.** `OCaml5.Lcnf.Dump` (`monoDecl?`), `OCaml5.Lcnf.Naming`,
`OCaml5.Lcnf.Types` (`builtinTy?`), `OCaml5.Ml.Syntax`, `Lean.Compiler.LCNF.Basic`
(`Code.collectUsed`).

**Properties.**
* **Scoping is by `FVarId`.** Every binder gets an OCaml name unique within its declaration
  (base name, then `_1`, `_2`, …), so two LCNF variables that share a binder name — the
  rule, not the exception, after `cases` on records — can never capture each other —
  *by construction*; *tested* on `Dispatcher.insert` (the field `priority` versus the
  parameter `priority`) and on `List.mapTR.loop._at_.RunMachine.update.spec_0` (fifteen
  fields bound twice).
* **ANF is preserved.** A `let` is a `let`, a `cases` is a `match` in tail position, a join
  point is a local function; no expression is duplicated or inlined — *by construction*.
* **Erasure is explicit.** A `◾` argument to a constructor or a builtin is dropped (it is a
  type or a proof, and `Types` dropped the field); a `◾` argument anywhere else is `()`, so
  the arity of a call is always the arity LCNF wrote — *by construction*.
* **Nothing is silently lost.** A construct without a rule becomes an `Expr.hole` — rendered
  `(* HOLE: … *)` — and a line in `todos`; a callee without a mono decl is listed in
  `missing`; a callee beyond the cap in `frontier` — *by construction*.
* **The `_redArg` fold.** `reduceArity` splits `f` into a wrapper and `f._redArg`; the twin is
  translated under `f`'s OCaml name and the wrapper is not emitted, so the output has one
  function per Lean definition — *tested* (every target of `Fibers.lean`).

## The rules

| LCNF construct | OCaml |
| --- | --- |
| `Decl` params `(x : T)…`, type `T₁ → … → R` | `let [rec] f (x : T)… : R =`, with `◾`/`lcAny` as `_` and an all-`_` annotation omitted |
| `let x := v; k` | `let x = v in k` |
| `fun f ps := b; k` / `jp j ps := b; k` | `let f = fun ps -> b in k`; `let rec` when `b` mentions `f`; no params → `fun () ->` |
| `jmp j args` | `j args`; no args → `j ()` |
| `cases x : T` on `Bool` | `if x then … else …` |
| `cases x : T`, other | `match (x : (_,…) t) with` (annotated with the type, so OCaml's record disambiguation never guesses) |
| `\| C.mk f₁ … fₙ =>` on a `structure` | `\| { f₁ = f₁; …; _ } ->` binding only the fields the arm uses |
| `\| C.c a₁ … aₙ =>` on an `inductive` | `\| C_c (a₁, …, aₙ) ->`, `_` for an unused field |
| `\| List.nil`/`cons`/`Option.none`/`some`/`Prod.mk`/`Except.ok`/`error` | `[]`, `h :: t`, `None`, `Some x`, `(a, b)`, `Ok x`, `Error e` |
| `\| _ =>` | `\| _ ->` |
| `return x` | `x` |
| `⊥` (`unreach`) | `assert false` |
| `LetValue.lit (nat n)` / `(str s)` | `n` (63-bit caveat) / `"s"` |
| `LetValue.erased` | `()` |
| `LetValue.proj T i s` on a `structure` | `s.fᵢ`; `Prod` → `fst`/`snd`; else a hole |
| `LetValue.fvar f args` | `f args`, `◾` as `()` |
| `LetValue.const C.mk ◾… fields` (structure ctor) | `({ f₁ = …; … } : (_,…) t)`, erased fields dropped |
| `LetValue.const C.c ◾… args` (inductive ctor) | `C_c (args)`; `List`/`Option`/`Prod`/`Bool`/`Except` natively |
| `LetValue.const g args`, `g` in the builtin table | the table's form: `Nat.decEq` → `=`, `Nat.decLt` → `<`, `Nat.sub` → `max 0 (a - b)`, `List.appendTR` → `@`, `List.reverse` → `List.rev`, `List.reverseAux` → `List.rev_append`, `List.instDecidableEqNil` → `= []`, `Array.mkEmpty` → `[]`, `Array.toList` → identity, `List.foldl._at_.Array.appendList.spec_0` → `@`, … (`builtin?`) |
| `LetValue.const g args`, other | `g' args` with `g' = globalName g`; `g` enqueued for translation |
| `g._redArg` | translated under `globalName g`; the wrapper `g` is skipped |
| `Decl.value = extern` | a hole |
-/

namespace OCaml5.Lcnf

open Lean Compiler LCNF

/-! ## Mono types as annotations -/

/-- A mono-phase LCNF type as an OCaml type annotation: `lcAny`/`lcErased` are `_`. -/
partial def monoTy (e : Lean.Expr) : Ml.Ty :=
  match e with
  | .forallE _ d b _ => .arrow (monoTy d) (monoTy b)
  | _ =>
    if e.isErased || e.isAny then .anon
    else
      let fn := e.getAppFn
      let args := (e.getAppArgs.map monoTy).toList
      match fn with
      | .const n _ => (builtinTy? n args).getD (.con (OCaml5.Lcnf.typeName n) args)
      | _ => .anon

/-- Every non-builtin type constant in a mono type: what needs at least a placeholder. -/
partial def monoTyConsts (e : Lean.Expr) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .forallE _ d b _ => monoTyConsts b (monoTyConsts d acc)
  | _ =>
    let fn := e.getAppFn
    let acc := e.getAppArgs.foldl (fun acc a => monoTyConsts a acc) acc
    match fn with
    | .const n _ => if isBuiltinType n || e.isErased || e.isAny then acc else acc.push n
    | _ => acc

/-- Whether an annotation says anything at all. -/
def tyIsAnon : Ml.Ty → Bool
  | .anon => true
  | _ => false

/-! ## The builtin table -/

/-- `n._redArg` → `n`. -/
def stripRedArg : Name → Name
  | .str p "_redArg" => p
  | n => n

/-- A builtin: its arity over *relevant* (non-erased) arguments and the OCaml form. -/
abbrev Builtin := Nat × (List Ml.Expr → Ml.Expr)

private def bin (op : String) : Builtin :=
  (2, fun | [a, b] => .binop op a b | _ => .unit)
private def call1 (f : String) : Builtin :=
  (1, fun | [a] => Ml.Expr.call f [a] | _ => .unit)
private def call2 (f : String) : Builtin :=
  (2, fun | [a, b] => Ml.Expr.call f [a, b] | _ => .unit)
private def call3 (f : String) : Builtin :=
  (3, fun | [a, b, c] => Ml.Expr.call f [a, b, c] | _ => .unit)

/-- The Lean constants with a native OCaml spelling. Names are unchecked literals: several
are specialisations that only exist in the target's environment. -/
def builtin? (n : Name) : Option Builtin :=
  match stripRedArg n with
  -- Nat (63-bit caveat throughout)
  | `Nat.decEq | `Nat.beq | `instDecidableEqNat => some (bin "=")
  | `Nat.decLt | `Nat.blt => some (bin "<")
  | `Nat.decLe | `Nat.ble => some (bin "<=")
  | `Nat.add => some (bin "+")
  | `Nat.mul => some (bin "*")
  | `Nat.div => some (bin "/")
  | `Nat.mod => some (bin "mod")
  | `Nat.sub => some (2, fun
      | [a, b] => Ml.Expr.call "max" [.int 0, .binop "-" a b]
      | _ => .unit)
  | `Nat.succ => some (1, fun | [a] => .binop "+" a (.int 1) | _ => .unit)
  | `Nat.pred => some (1, fun | [a] => Ml.Expr.call "max" [.int 0, .binop "-" a (.int 1)] | _ => .unit)
  -- Bool
  | `Bool.decEq | `instDecidableEqBool => some (bin "=")
  | `Bool.not | `not => some (call1 "not")
  | `Bool.and | `and => some (bin "&&")
  | `Bool.or | `or => some (bin "||")
  -- String
  | `String.decEq | `instDecidableEqString => some (bin "=")
  | `String.append => some (bin "^")
  | `String.length => some (call1 "String.length")
  -- List
  | `List.appendTR | `List.append => some (bin "@")
  | `List.reverse => some (call1 "List.rev")
  | `List.reverseAux => some (call2 "List.rev_append")
  | `List.length | `List.lengthTR => some (call1 "List.length")
  | `List.instDecidableEqNil | `List.isEmpty => some (1, fun | [l] => .binop "=" l Ml.Expr.nil | _ => .unit)
  -- `[BEq α]` is a one-field structure: mono passes the `beq` function itself as a relevant
  -- argument, so both take three
  | `List.elem => some (3, fun
      | [inst, a, l] => Ml.Expr.call "List.exists" [.app inst [a], l]
      | _ => .unit)
  | `List.contains => some (3, fun
      | [inst, l, a] => Ml.Expr.call "List.exists" [.app inst [a], l]
      | _ => .unit)
  | `List.map | `List.mapTR => some (call2 "List.map")
  | `List.filter | `List.filterTR => some (call2 "List.filter")
  | `List.foldl => some (call3 "List.fold_left")
  -- Lean takes the list first, OCaml the predicate first
  | `List.all => some (2, fun | [l, p] => Ml.Expr.call "List.for_all" [p, l] | _ => .unit)
  | `List.any => some (2, fun | [l, p] => Ml.Expr.call "List.exists" [p, l] | _ => .unit)
  | `List.find? => some (call2 "List.find_opt")
  | `List.flatten | `List.flattenTR => some (call1 "List.concat")
  | `List.filterMap | `List.filterMapTR => some (call2 "List.filter_map")
  -- Array as list: the LCNF route's shim
  | `Array.mkEmpty | `Array.emptyWithCapacity => some (1, fun _ => Ml.Expr.nil)
  | `Array.toList | `List.toArray => some (1, fun | [a] => a | _ => .unit)
  | `Array.push => some (2, fun | [a, x] => .binop "@" a (.listLit [x]) | _ => .unit)
  | `Array.size => some (call1 "List.length")
  | `Array.appendList | `List.foldl._at_.Array.appendList.spec_0 => some (bin "@")
  -- Option
  | `Option.isSome => some (call1 "Option.is_some")
  | `Option.isNone => some (call1 "Option.is_none")
  | `Option.getD => some (2, fun
      | [o, d] => .appL (.var "Option.value") [(.nolabel, o), (.lbl "default", d)]
      | _ => .unit)
  | `Option.map => some (call2 "Option.map")
  | `Option.bind => some (call2 "Option.bind")
  -- Prod
  | `Prod.fst => some (call1 "fst")
  | `Prod.snd => some (call1 "snd")
  -- panics
  | `panic | `panicCore => some (call1 "failwith")
  | _ => none

/-- Apply a builtin to its relevant arguments: saturated, eta-expanded when under-applied,
applied to the rest when over-applied. -/
def applyBuiltin (b : Builtin) (args : List Ml.Expr) : Ml.Expr :=
  let (arity, mk) := b
  if args.length == arity then mk args
  else if args.length < arity then
    let extra := (List.range (arity - args.length)).map fun i => s!"_b{i + 1}"
    .fn extra (mk (args ++ extra.map Ml.Expr.var))
  else
    .app (mk (args.take arity)) (args.drop arity)

/-! ## The translation state -/

structure St where
  /-- Free variable → its unique OCaml name. -/
  names : Std.HashMap FVarId String := {}
  /-- OCaml base name → the last suffix handed out. -/
  used : Std.HashMap String Nat := {}
  /-- Global constants called, in order of first call. -/
  calls : Array Name := #[]
  /-- Inductives destructed or constructed: these need a full OCaml declaration. -/
  realTypes : Array Name := #[]
  /-- Type constants in annotations: these need at least a placeholder. -/
  mentioned : Array Name := #[]
  /-- Constructs without a rule, as `<decl>: <what>`. -/
  todos : Array String := #[]

/-- The translation monad: the environment to read constructors from, the state above. -/
abbrev TM := ReaderT Environment (StateM St)

/-- OCaml names the builtin forms use unqualified, which a local must not shadow. -/
def preUsed : List String := ["max", "fst", "snd", "not", "failwith", "ignore", "ref"]

/-- A unique OCaml name from a base. -/
def fresh (base : String) : TM String := do
  let s ← get
  match s.used[base]? with
  | none =>
    set { s with used := s.used.insert base 0 }
    return base
  | some k =>
    let mut k := k + 1
    while s.used.contains s!"{base}_{k}" do k := k + 1
    let name := s!"{base}_{k}"
    set { s with used := (s.used.insert base k).insert name 0 }
    return name

/-- Bind a free variable to a fresh OCaml name. -/
def bindVar (id : FVarId) (n : Name) : TM String := do
  let name ← fresh (localName n)
  modify fun s => { s with names := s.names.insert id name }
  return name

/-- The OCaml name of a bound free variable. -/
def nameOf (id : FVarId) : TM String := do
  return (← get).names.getD id s!"_unbound_{id.name}"

def todo (msg : String) : TM Unit :=
  modify fun s => { s with todos := s.todos.push msg }

def noteCall (n : Name) : TM Unit :=
  modify fun s => { s with calls := if s.calls.contains n then s.calls else s.calls.push n }

def noteReal (n : Name) : TM Unit :=
  modify fun s => { s with realTypes := if s.realTypes.contains n then s.realTypes else s.realTypes.push n }

def noteMentioned (ns : Array Name) : TM Unit :=
  modify fun s => { s with mentioned := ns.foldl (fun acc n => if acc.contains n then acc else acc.push n) s.mentioned }

/-- The binder names of a constructor's fields, from its type. -/
partial def ctorFieldNames (ci : ConstructorVal) : Array Name :=
  go ci.type ci.numParams #[]
where
  go : Lean.Expr → Nat → Array Name → Array Name
    | .forallE n _ b _, 0, acc => go b 0 (acc.push n)
    | .forallE _ _ b _, k + 1, acc => go b k acc
    | .mdata _ e, k, acc => go e k acc
    | _, _, acc => acc

/-- The `reduceArity` wrapper shape: `let _x := f._redArg …; return _x`. -/
def redArgTarget? (d : LCNF.Decl .pure) : Option Name :=
  match d.value with
  | .code (.let decl (.return r)) =>
    match decl.value with
    | .const callName _ _ =>
      if callName == d.name ++ `_redArg && r == decl.fvarId then some callName else none
    | _ => none
  | _ => none

/-- When `n` is a `reduceArity` wrapper, the indices of the parameters its `_redArg` twin
kept — read off the wrapper's own body, exactly as `ToMono.argsToMonoRedArg` does — so that
a call to `n` (an unsaturated one, which is the only kind mono code makes) passes the twin
the arguments it takes. Pure: `monoExt` is read through `getDeclCore?`. -/
def wrapperKeep? (env : Environment) (n : Name) : Option (Array Nat) := do
  let d ← getDeclCore? env monoExt n
  let _ ← redArgTarget? d
  let .code (.let decl _) := d.value | none
  let .const _ _ callArgs := decl.value | none
  let keep := callArgs.filterMap fun
    | .fvar id => d.params.findIdx? (·.fvarId == id)
    | _ => none
  return keep

/-- `(_, …, _) t` for an inductive, as an annotation. -/
def tyOfInd (env : Environment) (ind : Name) : Ml.Ty :=
  match env.find? ind with
  | some (.inductInfo info) => .con (OCaml5.Lcnf.typeName ind) (List.replicate info.numParams .anon)
  | _ => .con (OCaml5.Lcnf.typeName ind) []

/-- The inductives OCaml spells natively; a `cases` on one is not annotated. -/
def nativeInductives : List Name :=
  [``List, ``Option, ``Bool, ``Prod, ``Except, ``Unit, ``PUnit, ``Nat]

/-! ## Arguments and values -/

/-- A relevant argument, or `none` for an erased one. -/
def argExpr? : Arg .pure → TM (Option Ml.Expr)
  | .erased => return none
  | .type _ => return none
  | .fvar id => return some (.var (← nameOf id))

/-- An argument in a position that must be filled: erased becomes `()`. -/
def argExpr (a : Arg .pure) : TM Ml.Expr := do
  return (← argExpr? a).getD .unit

/-- A constructor application. -/
def ctorApp (ci : ConstructorVal) (args : Array (Arg .pure)) : TM Ml.Expr := do
  let fieldArgs := args.extract ci.numParams args.size
  let rel ← fieldArgs.toList.filterMapM argExpr?
  match ci.name, rel with
  | ``List.nil, [] => return Ml.Expr.nil
  | ``List.cons, [h, t] => return .binop "::" h t
  | ``Option.none, [] => return Ml.Expr.none_
  | ``Option.some, [x] => return Ml.Expr.some_ x
  | ``Bool.true, [] => return .bool true
  | ``Bool.false, [] => return .bool false
  | ``Prod.mk, [a, b] => return .tuple [a, b]
  | ``Except.ok, [x] => return .ctor "Ok" [x]
  | ``Except.error, [e] => return .ctor "Error" [e]
  | ``PUnit.unit, [] => return .unit
  | ``Nat.zero, [] => return .int 0
  | ``Nat.succ, [a] => return .binop "+" a (.int 1)
  | _, _ =>
    let env ← read
    noteReal ci.induct
    if isStructure env ci.induct then
      let names := ctorFieldNames ci
      let mut fields : List (String × Ml.Expr) := []
      for a in fieldArgs, n in names do
        if let some e ← argExpr? a then
          fields := fields ++ [(fieldName n.toString, e)]
      return .annot (.record fields) (tyOfInd env ci.induct)
    else
      return .ctor (OCaml5.Lcnf.ctorName ci.induct (shortName ci.name)) rel

/-- A `LetValue`. -/
def letValueExpr (declName : Name) (v : LetValue .pure) : TM Ml.Expr := do
  match v with
  | .lit (.nat n) => return .int n
  | .lit (.str s) => return .str s
  | .lit (.uint8 n) => return .int n.toNat
  | .lit (.uint16 n) => return .int n.toNat
  | .lit (.uint32 n) => return .int n.toNat
  | .lit (.uint64 n) => return .int n.toNat
  | .lit (.usize n) => return .int n.toNat
  | .erased => return .unit
  | .proj typeName i s =>
    let env ← read
    let sv := Ml.Expr.var (← nameOf s)
    if typeName == ``Prod then
      return Ml.Expr.call (if i == 0 then "fst" else "snd") [sv]
    else
      let ctor? := match env.find? typeName with
        | some (.inductInfo info) =>
          match info.ctors with
          | [c] => match env.find? c with
            | some (.ctorInfo ci) => some ci
            | _ => none
          | _ => none
        | _ => none
      match ctor? with
      | some ci =>
        if isStructure env typeName then
          let names := ctorFieldNames ci
          noteReal typeName
          return .field sv (fieldName (names[i]?.getD (Name.mkSimple s!"_{i}")).toString)
        else
          todo s!"{declName}: proj on {typeName} #{i} (a single-constructor inductive that is not a structure)"
          return .hole s!"proj {typeName} #{i}" (.assertE (.bool false))
      | none =>
        todo s!"{declName}: proj on {typeName} #{i} (not a structure)"
        return .hole s!"proj {typeName} #{i}" (.assertE (.bool false))
  | .fvar f args =>
    let fv := Ml.Expr.var (← nameOf f)
    if args.isEmpty then return fv
    return .app fv (← args.toList.mapM argExpr)
  | .const n _ args =>
    let env ← read
    match env.find? n with
    | some (.ctorInfo ci) => ctorApp ci args
    | _ =>
      match builtin? n with
      | some b => return applyBuiltin b (← args.toList.filterMapM argExpr?)
      | none =>
        noteCall n
        let g := Ml.Expr.var (globalName n)
        -- a wrapper is called under its twin's name: pass the twin what it kept
        let args := match wrapperKeep? env n with
          | some keep => keep.filterMap fun i => args[i]?
          | none => args
        if args.isEmpty then return g
        return .app g (← args.toList.mapM argExpr)

/-! ## Patterns -/

/-- The pattern of a `cases` alternative, binding the parameters the arm uses. -/
def altPat (ctor : Name) (ps : Array (LCNF.Param .pure)) (usedVars : FVarIdHashSet) :
    TM Ml.Pat := do
  let env ← read
  -- bind (only) the used, relevant parameters
  let mut pats : Array (Option Ml.Pat) := #[]
  for p in ps do
    if p.type.isErased then
      pats := pats.push none
    else if usedVars.contains p.fvarId then
      pats := pats.push (some (.var (← bindVar p.fvarId p.binderName)))
    else
      pats := pats.push (some .wild)
  let rel := pats.toList.filterMap id
  match ctor, rel with
  | ``List.nil, [] => return Ml.Pat.nil
  | ``List.cons, [h, t] => return .cons h t
  | ``Option.none, [] => return Ml.Pat.none_
  | ``Option.some, [x] => return Ml.Pat.some_ x
  | ``Bool.true, [] => return Ml.Pat.true_
  | ``Bool.false, [] => return Ml.Pat.false_
  | ``Prod.mk, [a, b] => return .tuple [a, b]
  | ``Except.ok, [x] => return .ctor "Ok" [x]
  | ``Except.error, [e] => return .ctor "Error" [e]
  | ``PUnit.unit, [] => return Ml.Pat.unit
  | _, _ =>
    match env.find? ctor with
    | some (.ctorInfo ci) =>
      noteReal ci.induct
      if isStructure env ci.induct then
        let names := ctorFieldNames ci
        let mut fields : List (String × Ml.Pat) := []
        let mut omitted := false
        for p? in pats, n in names do
          match p? with
          | some (.var v) => fields := fields ++ [(fieldName n.toString, .var v)]
          | some _ => omitted := true
          | none => pure ()
        if fields.isEmpty then return .wild
        return if omitted then .recordOpen fields else .record fields
      else
        return .ctor (OCaml5.Lcnf.ctorName ci.induct (shortName ctor)) rel
    | _ =>
      todo s!"alternative on unknown constructor {ctor}"
      return .wild

/-! ## Code -/

mutual

/-- A `Code` in tail position. -/
partial def code (declName : Name) (c : Code .pure) : TM Ml.Expr := do
  match c with
  | .let decl k =>
    let v ← letValueExpr declName decl.value
    let x ← bindVar decl.fvarId decl.binderName
    return .letIn x v (← code declName k)
  | .fun decl k => localFun declName decl k
  | .jp decl k => localFun declName decl k
  | .jmp j args =>
    let jv := Ml.Expr.var (← nameOf j)
    if args.isEmpty then return .app jv [.unit]
    return .app jv (← args.toList.mapM argExpr)
  | .return x => return .var (← nameOf x)
  | .unreach _ => return .assertE (.bool false)
  | .cases cs =>
    let d ← nameOf cs.discr
    if cs.typeName == ``Bool then
      let mut t? : Option Ml.Expr := none
      let mut f? : Option Ml.Expr := none
      let mut dflt? : Option Ml.Expr := none
      for alt in cs.alts do
        match alt with
        | .alt ``Bool.true _ k => t? := some (← code declName k)
        | .alt ``Bool.false _ k => f? := some (← code declName k)
        | .alt _ _ k => dflt? := some (← code declName k)
        | .default k => dflt? := some (← code declName k)
      match t?.orElse (fun _ => dflt?), f?.orElse (fun _ => dflt?) with
      | some t, some f => return .ifThen (.var d) t f
      | _, _ =>
        todo s!"{declName}: cases on Bool with a missing arm"
        return .hole "cases on Bool with a missing arm" (.assertE (.bool false))
    else
      let env ← read
      let scrut : Ml.Expr :=
        if nativeInductives.contains cs.typeName then .var d
        else .annot (.var d) (tyOfInd env cs.typeName)
      unless nativeInductives.contains cs.typeName do noteReal cs.typeName
      let mut arms : List Ml.Arm := []
      for alt in cs.alts do
        match alt with
        | .default k => arms := arms ++ [.mk .wild none (← code declName k)]
        | .alt ctor ps k =>
          let pat ← altPat ctor ps k.collectUsed
          arms := arms ++ [.mk pat none (← code declName k)]
      return .matchE scrut arms

/-- A local function or join point, then the rest. -/
partial def localFun (declName : Name) (decl : FunDecl .pure) (k : Code .pure) : TM Ml.Expr := do
  let f ← bindVar decl.fvarId decl.binderName
  let ps ← decl.params.toList.mapM fun p => bindVar p.fvarId p.binderName
  let ps := if ps.isEmpty then ["()"] else ps
  let recursive := decl.value.collectUsed.contains decl.fvarId
  let body ← code declName decl.value
  let rest ← code declName k
  if recursive then return .letRecIn [(f, ps, body)] rest
  return .letIn f (.fn ps body) rest

end

/-! ## Declarations -/

/-- One translated definition. -/
structure Translated where
  /-- The Lean constant whose code was translated (a `_redArg` twin when there is one). -/
  leanName : Name
  /-- The Lean constant the OCaml name stands for (the wrapper when there is one). -/
  userName : Name
  ocamlName : String
  bind : Ml.Bind
  /-- Global constants called. -/
  callees : Array Name
  /-- The LCNF signature, for the reader. -/
  signature : String
  recursive : Bool

instance : Inhabited Ml.Bind := ⟨{ name := "_", body := .unit }⟩
instance : Inhabited Translated :=
  ⟨{ leanName := .anonymous, userName := .anonymous, ocamlName := "_", bind := default,
     callees := #[], signature := "", recursive := false }⟩

/-- Translate one mono decl under an OCaml name. -/
def translateDecl (env : Environment) (d : LCNF.Decl .pure) (userName : Name) (ocamlName : String) :
    Translated × St :=
  let act : TM Translated := do
    -- reserve the names the builtin forms use
    modify fun s => { s with used := preUsed.foldl (fun m n => m.insert n 0) s.used }
    let mut params : List (String × Option Ml.Ty) := []
    for p in d.params do
      let x ← bindVar p.fvarId p.binderName
      noteMentioned (monoTyConsts p.type)
      let t := monoTy p.type
      params := params ++ [(x, if tyIsAnon t then none else some t)]
    -- the result type: the decl type with the parameters peeled off
    let mut rty := d.type
    for _ in [:d.params.size] do
      match rty with
      | .forallE _ _ b _ => rty := b
      | _ => pure ()
    noteMentioned (monoTyConsts rty)
    let result := monoTy rty
    let body ← match d.value with
      | .code c => code d.name c
      | .extern _ => do
        todo s!"{d.name}: extern"
        pure (Ml.Expr.hole s!"extern {d.name}" (.assertE (.bool false)))
    let b : Ml.Bind := { name := ocamlName, params := params,
                         result := if tyIsAnon result then none else some result, body := body }
    let callees := (← get).calls
    let sig := s!"{d.name}{sketchParams d.params} : {sketchType rty}"
    return { leanName := d.name, userName := userName, ocamlName := ocamlName, bind := b,
             callees := callees, signature := sig,
             recursive := d.recursive || callees.contains d.name }
  Id.run ((act env).run {})

/-- What the closure produced. -/
structure Closure where
  decls : Array Translated := #[]
  /-- Callees left untranslated by the cap. -/
  frontier : Array Name := #[]
  /-- Callees with no mono decl (an `extern`, an `implemented_by`, a `noncomputable`). -/
  missing : Array Name := #[]
  /-- Wrappers referenced directly (an unsaturated call): the twin's arity may differ. -/
  wrapperRefs : Array Name := #[]
  realTypes : Array Name := #[]
  mentioned : Array Name := #[]
  todos : Array String := #[]

private def pushNew (a : Array Name) (n : Name) : Array Name :=
  if a.contains n then a else a.push n

/-- Translate `roots` and, transitively, every non-builtin constant they call, up to `cap`
declarations. -/
def translateClosure (roots : Array Name) (cap : Nat := 60) : CoreM Closure := do
  let env ← getEnv
  let mut c : Closure := {}
  let mut done : NameSet := {}
  let mut queue : Array Name := roots
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if done.contains n then continue
    if (builtin? n).isSome then continue
    if env.find? n matches some (.ctorInfo _) then continue
    if c.decls.size ≥ cap then
      c := { c with frontier := pushNew c.frontier n }
      continue
    done := done.insert n
    let d? ← monoDecl? n
    if d?.isNone then
      c := { c with missing := pushNew c.missing n }
      continue
    let d := d?.get!
    -- the wrapper folds onto its twin
    let mut d := d
    let mut userName := n
    match redArgTarget? d with
    | some twin =>
      done := done.insert twin
      if let some dt ← monoDecl? twin then d := dt
    | none =>
      -- a twin reached directly: its wrapper is the user-facing name
      userName := stripRedArg n
      if userName != n then done := done.insert userName
    let (t, st) := translateDecl env d userName (globalName userName)
    c := { c with
      decls := c.decls.push t,
      realTypes := st.realTypes.foldl pushNew c.realTypes,
      mentioned := st.mentioned.foldl pushNew c.mentioned,
      todos := c.todos ++ st.todos }
    for callee in st.calls do
      unless done.contains callee do
        -- a direct reference to a wrapper that has a twin: note it, translate the twin
        if stripRedArg callee == callee then
          if (← monoDecl? (callee ++ `_redArg)).isSome then
            c := { c with wrapperRefs := pushNew c.wrapperRefs callee }
        queue := queue.push callee
  return c

/-! ## Emission: strongly connected components, dependencies first -/

private structure Tarjan where
  index : Nat := 0
  indices : Array (Option Nat)
  low : Array Nat
  onStack : Array Bool
  stack : Array Nat := #[]
  sccs : Array (Array Nat) := #[]

private partial def strongconnect (adj : Array (Array Nat)) (v : Nat) : StateM Tarjan Unit := do
  modify fun s => { s with
    indices := s.indices.set! v (some s.index), low := s.low.set! v s.index,
    index := s.index + 1, stack := s.stack.push v, onStack := s.onStack.set! v true }
  for w in adj[v]! do
    let s ← get
    match s.indices[w]! with
    | none =>
      strongconnect adj w
      modify fun s => { s with low := s.low.set! v (min s.low[v]! s.low[w]!) }
    | some iw =>
      if s.onStack[w]! then
        modify fun s => { s with low := s.low.set! v (min s.low[v]! iw) }
  let s ← get
  if s.low[v]! == s.indices[v]!.getD 0 then
    let mut comp : Array Nat := #[]
    let mut st := s.stack
    let mut onStack := s.onStack
    let mut go := true
    while go do
      match st.back? with
      | none => go := false
      | some w =>
        st := st.pop
        onStack := onStack.set! w false
        comp := comp.push w
        if w == v then go := false
    set { s with stack := st, onStack := onStack, sccs := s.sccs.push comp.reverse }

/-- The declarations as OCaml structure items: one `let`/`let rec` per component, a
component's dependencies before it, and an origin comment above each. -/
def emit (ds : Array Translated) : List Ml.Decl :=
  let n := ds.size
  let byName : Std.HashMap String Nat := ds.foldl (init := {}) fun m t =>
    m.insert t.ocamlName m.size
  -- adjacency by OCaml name (a wrapper and its twin share one)
  let adj : Array (Array Nat) := ds.map fun t =>
    t.callees.filterMap fun c => byName[globalName c]?
  let init : Tarjan := { indices := Array.replicate n none, low := Array.replicate n 0,
                         onStack := Array.replicate n false }
  let run : StateM Tarjan Unit := do
    for v in [:n] do
      if (← get).indices[v]!.isNone then strongconnect adj v
  let (_, s) := Id.run (run.run init)
  s.sccs.toList.flatMap fun comp =>
    let binds := comp.toList.map fun v => ds[v]!.bind
    let isRec := comp.size > 1 || comp.any fun v => ds[v]!.recursive
    let origin := String.intercalate "\n   " (comp.toList.map fun v => ds[v]!.signature)
    [.comment ("LCNF mono: " ++ origin), .letD isRec binds, .blank]

end OCaml5.Lcnf
