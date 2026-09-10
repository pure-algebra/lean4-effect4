import Lean
import Conform.Lcnf.Index
import OCaml5.Ml.Syntax
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Native

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

/-- Map a mono type expression to an OCaml type. Inductive type arguments are filtered
by `typeParameterIndices` to match the declared OCaml type arity. -/
partial def monoTy (env : Environment) (ex : Externs) (tn : TypeNames) (e : Lean.Expr) : Ml.Ty :=
  match e with
  | .forallE _ d b _ => .arrow (monoTy env ex tn d) (monoTy env ex tn b)
  | _ =>
    if e.isErased || e.isAny then .anon
    else
      let fn := e.getAppFn
      let rawArgs := e.getAppArgs.toList
      let args := match fn with
        | .const n _ =>
          match env.find? n with
          | some (.inductInfo info) =>
            match typeParameterIndices n rawArgs.length info.type with
            | .ok indices => indices.toList.filterMap (fun i => rawArgs[i]?) |>.map (monoTy env ex tn)
            | .error _ => rawArgs.map (monoTy env ex tn)
          | _ => rawArgs.map (monoTy env ex tn)
        | _ => rawArgs.map (monoTy env ex tn)
      match fn with
      | .const n _ =>
        match ex.tys[n]? with
        | some chain => applyChain chain args
        | none =>
          match ex.elemChain? n rawArgs with
          | some chain => applyChain chain args
          | none => (builtinTy? n args).getD (.con (OCaml5.Lcnf.typeNameIn tn n) args)
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

/-- The 63-bit rule for `Nat.pow`: `a ^ b` computed by repeated multiplication that **saturates
at `max_int`** instead of wrapping. `Nat` is unbounded and OCaml's `int` is 63-bit, so a
faithful `a ** b` does not exist; a wrapping one is worse than a saturating one, because
`Effect4.Store.Val.wf`'s `… < 2 ^ 64` would then read as `… < 0` and answer `false` for every
value — a silently wrong `Api.ofBytes`, not a compile error. Saturating makes `2 ^ 64` read as
`max_int`, and every list OCaml can hold is shorter than `max_int`, so the guard keeps its
meaning. Recorded in `ocaml/gen/NOTES.md` §5. -/
private def powClamped (a b : Ml.Expr) : Ml.Expr :=
  .letRecIn
    [("_pow_clamped", ["_pa", "_pb"],
      .ifThen (.binop "=" (.var "_pb") (.int 0)) (.int 1)
        (.letIn "_ph"
          (Ml.Expr.call "_pow_clamped" [.var "_pa", .binop "-" (.var "_pb") (.int 1)])
          (.ifThen (.binop "=" (.var "_pa") (.int 0)) (.int 0)
            (.ifThen (.binop ">" (.var "_ph") (.binop "/" (.var "max_int") (.var "_pa")))
              (.var "max_int")
              (.binop "*" (.var "_ph") (.var "_pa"))))))]
    (Ml.Expr.call "_pow_clamped" [a, b])

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
  | `Nat.div => some (2, fun | [a, b] => .ifThen (.binop "=" b (.int 0)) (.int 0) (.binop "/" a b) | _ => .unit)
  | `Nat.mod => some (2, fun | [a, b] => .ifThen (.binop "=" b (.int 0)) a (.binop "mod" a b) | _ => .unit)
  | `Nat.sub => some (2, fun
      | [a, b] => Ml.Expr.call "max" [.int 0, .binop "-" a b]
      | _ => .unit)
  | `Nat.succ => some (1, fun | [a] => .binop "+" a (.int 1) | _ => .unit)
  | `Nat.pred => some (1, fun | [a] => Ml.Expr.call "max" [.int 0, .binop "-" a (.int 1)] | _ => .unit)
  -- The 63-bit rule. `Nat.pow` is `@[extern]`, so without a row it becomes a hole; with the
  -- obvious `a ** b` (a float operator) or a plain multiplication loop it *overflows silently*,
  -- and `Effect4.Store.Val.wf`'s `… < 2 ^ 64` would then read as `… < 0` and answer `false` for
  -- every value. The row clamps at `max_int`: `2 ^ 64` becomes `max_int`, and every list OCaml
  -- can hold is shorter than that, so the guard means what it means in Lean.
  | `Nat.pow => some (2, fun
      | [a, b] => powClamped a b
      | _ => .unit)
  -- Clamp the multiplication too; clamping only the power still allowed a wrap.
  | `Nat.shiftLeft => some (2, fun
      | [a, b] => .letIn "_shift_scale" (powClamped (.int 2) b)
        (.ifThen (.binop "=" a (.int 0)) (.int 0)
          (.ifThen (.binop ">" (.var "_shift_scale") (.binop "/" (.var "max_int") a))
            (.var "max_int") (.binop "*" a (.var "_shift_scale"))))
      | _ => .unit)
  -- `a >>> b` and `a &&& b`; OCaml's shifts are undefined at ≥ 63, so the shift is clamped.
  | `Nat.shiftRight => some (2, fun
      | [a, b] => .ifThen (.binop ">=" b (.int 63)) (.int 0) (.binop "lsr" a b)
      | _ => .unit)
  | `Nat.land => some (bin "land")
  | `Nat.lor => some (bin "lor")
  | `Nat.xor => some (bin "lxor")
  -- UInt8 as `int` (`Types.builtinTy?`): equality, the truncating injection, the identity out
  | `UInt8.decEq | `instDecidableEqUInt8 | `UInt8.beq => some (bin "=")
  | `UInt8.ofNat | `UInt8.ofNatLT =>
    some (1, fun | [a] => .binop "land" a (.int 255) | _ => .unit)
  | `UInt8.ofNatTruncate | `UInt8.ofNatClamp => some (1, fun | [a] => Ml.Expr.call "min" [a, .int 255] | _ => .unit)
  | `UInt8.toNat | `UInt8.toUInt64 | `UInt8.toUInt32 =>
    some (1, fun | [a] => a | _ => .unit)
  -- Bool
  | `Bool.decEq | `instDecidableEqBool => some (bin "=")
  | `Bool.not | `not => some (call1 "not")
  | `Bool.and | `and => some (bin "&&")
  | `Bool.or | `or => some (bin "||")
  -- String
  | `String.decEq | `instDecidableEqString => some (bin "=")
  | `String.append => some (bin "^")
  | `String.length => some (call1 "lcnf_utf8_length")
  | `String.toUTF8 => some (call1 "lcnf_utf8_bytes")
  | `ByteArray.data => some (1, fun | [a] => a | _ => .unit)
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
      | [inst, l, a] => Ml.Expr.call "List.exists" [.fn ["_elem"] (.app inst [a, .var "_elem"]), l]
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
  -- `USize` is the shim's index type, so it is `int` like every other `Nat`; `Array.uget`'s
  -- erased `α` and bounds proof are dropped, leaving the list lookup. Without these four rows
  -- `List.setTR.go`'s `Array.foldrMUnsafe.fold` is four `extern` holes, so `List.set` — and
  -- therefore `DeferredStore.setCell` and `RefHeap.set` — is `assert false` at run time.
  | `USize.ofNat | `USize.toNat | `USize.ofNatLT => some (1, fun | [a] => a | _ => .unit)
  | `USize.decEq | `USize.beq => some (bin "=")
  | `USize.sub => some (2, fun
      | [a, b] => Ml.Expr.call "max" [.int 0, .binop "-" a b]
      | _ => .unit)
  | `USize.add => some (bin "+")
  | `Array.uget | `Array.fget => some (call2 "List.nth")
  | `Array.get! => some (3, fun
      | [defaultValue, a, i] => .ifThen (.binop "<" i (Ml.Expr.call "List.length" [a]))
          (Ml.Expr.call "List.nth" [a, i]) defaultValue
      | _ => .unit)
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
  /-- `fn` extern rows this declaration used, by the row's own Lean name. -/
  usedExterns : Array Name := #[]
  /-- OCaml names an extern row hands to a hand body as a leading argument. They are ordinary
  generated declarations, so they must be **emitted before** this one: `emit` adds the edge. -/
  externDeps : Array String := #[]
  /-- Free variables whose value is a *carrier* rather than the list Lean writes, by the
  carrier's key. A value enters the set at a `field`-row projection, at a `carg` parameter and
  at the result of a carrier operation, and leaves it through `to_list`. -/
  carrier : Std.HashMap FVarId String := {}
  /-- Free variables bound to a list literal: `none` is `[]`, `some e` is `[e]`. It is what
  tells `x ++ ys` from `x ++ [i]`, i.e. `append` from `snoc`. -/
  listLit : Std.HashMap FVarId (Option Ml.Expr) := {}
  /-- `ops` rows this declaration used, as `<carrier>#<op>`. -/
  usedOps : Array String := #[]
  /-- `carg` rows this declaration used, by the declaration the row names. -/
  usedCargs : Array Name := #[]
  /-- Every place a carrier had to be turned back into the Lean list, as `<site>`. Each one is
  an O(depth) copy; the report prints them so a missing `carg` row is visible rather than
  silently slow. -/
  toLists : Array String := #[]

/-- What a translation reads: the environment constructors are looked up in, and the decided
OCaml names of the type constants whose short name is claimed twice (`TypeNames`). Both halves
are fixed for a whole run, so an annotation, a constructor and a type declaration can never
disagree about which Lean type an OCaml name means. -/
structure TCtx where
  env : Environment
  tn : TypeNames := {}
  /-- The `Extract Constant` table (`OCaml5.Lcnf.Externs`). -/
  ex : Externs := {}

/-- The translation monad: the context above, the state above. -/
abbrev TM := ReaderT TCtx (StateM St)

/-- The environment. -/
def readEnv : TM Environment := return (← read).env
/-- The decided type-name map. -/
def readTypeNames : TM TypeNames := return (← read).tn
/-- The extern table. -/
def readExterns : TM Externs := return (← read).ex

/-- OCaml names the builtin forms use unqualified, which a local must not shadow. -/
def preUsed : List String :=
  ["max", "fst", "snd", "not", "failwith", "ignore", "ref", "max_int", "_pow_clamped", "_pa",
   "_pb", "_ph"]

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
def ctorFieldNames (ci : ConstructorVal) : Array Name :=
  go (ci.numParams + ci.numFields) ci.type #[] |>.extract ci.numParams (ci.numParams + ci.numFields)
where
  go : Nat → Lean.Expr → Array Name → Array Name
    | 0, _, acc => acc
    | k + 1, .forallE n _ b _, acc => go k b (acc.push n)
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

/-- The wrapper's own parameters, when `n` is a `reduceArity` wrapper: what an unsaturated
reference to `n` must be eta-expanded back to. -/
def wrapperParams? (env : Environment) (n : Name) : Option (Array (LCNF.Param .pure)) := do
  let d ← getDeclCore? env monoExt n
  let _ ← redArgTarget? d
  return d.params

/-- `(_, …, _) t` for an inductive, as an annotation. -/
def tyOfInd (ex : Externs) (tn : TypeNames) (env : Environment) (ind : Name) : Ml.Ty :=
  let params := match env.find? ind with
    | some (.inductInfo info) => List.replicate
        ((typeParameterIndices ind info.numParams info.type).toOption.getD #[]).size Ml.Ty.anon
    | _ => []
  match ex.tys[ind]? with
  | some chain => applyChain chain params
  | none => .con (OCaml5.Lcnf.typeNameIn tn ind) params

/-! ## Arguments and values -/

/-- A relevant argument, or `none` for an erased one. -/
def argExpr? : Arg .pure → TM (Option Ml.Expr)
  | .erased => return none
  | .type _ => return none
  | .fvar id => return some (.var (← nameOf id))

/-- An argument in a position that must be filled: erased becomes `()`. -/
def argExpr (a : Arg .pure) : TM Ml.Expr := do
  return (← argExpr? a).getD .unit

/-! ## Carriers

A `field` extern row changes a field's *type*, so the value read out of it is no longer the
Lean list: it is the carrier. `carrier` tracks which local variables hold one, and three
rules follow — the operations Lean applies to the list become the carrier's own (`x ++ [i]`
is `snoc`), a position that needs the list gets `to_list`, and a position that is itself the
carrier (another `field` row, a `carg` parameter, an extern row's argument, a join point)
gets the value raw. A rule that is wrong is an `ocamlopt` type error, never silence: that is
the same argument the `field` rows themselves rest on (lane G, G-1). -/

/-- The carrier a variable holds, if it holds one. -/
def carrierOfId? (id : FVarId) : TM (Option String) := return (← get).carrier[id]?

/-- The carrier an argument holds. -/
def argCarrier? : Arg .pure → TM (Option String)
  | .fvar id => carrierOfId? id
  | _ => return none

/-- Note that a variable holds a carrier. -/
def setCarrier (id : FVarId) (c : String) : TM Unit :=
  modify fun s => { s with carrier := s.carrier.insert id c }

/-- One operation of a carrier, applied; `none` when the table has no row for it. -/
def carrierOp? (c op : String) (args : List Ml.Expr) : TM (Option Ml.Expr) := do
  let ex ← readExterns
  match ex.op? c op with
  | none => return none
  | some f =>
    let deps := f.spec.filterMap fun | .lit d => some d | _ => none
    modify fun s =>
      { s with usedOps := if s.usedOps.contains s!"{c}#{op}" then s.usedOps
                          else s.usedOps.push s!"{c}#{op}",
               externDeps := deps.foldl (fun a d => if a.contains d then a else a.push d)
                               s.externDeps }
    return some (f.build args)

/-- A carrier back as the Lean list, for a position that is not a carrier position. Every one
of these is an O(depth) copy and every one is reported. -/
def useAsList (site : String) (c : String) (e : Ml.Expr) : TM Ml.Expr := do
  modify fun s => { s with toLists := s.toLists.push s!"{site} [{c}]" }
  match ← carrierOp? c "to_list" [e] with
  | some e' => return e'
  | none =>
    todo s!"carrier {c} has no `to_list` op row, needed at {site}"
    return e

/-- An argument of a *generated* callee: raw when the callee's `carg` row says that parameter
carries the carrier, `to_list` otherwise. -/
def argFor (g : Name) (i : Nat) (a : Arg .pure) : TM Ml.Expr := do
  let e ← argExpr a
  match ← argCarrier? a with
  | none => return e
  | some c =>
    let ex ← readExterns
    if ex.cargAt? g i == some c then return e
    else useAsList s!"{g} #{i}" c e

/-- Every argument of a generated callee, by position. -/
def argsFor (g : Name) (as : List (Arg .pure)) : TM (List Ml.Expr) := do
  let mut out : List Ml.Expr := []
  let mut i := 0
  for a in as do
    out := out ++ [← argFor g i a]
    i := i + 1
  return out

/-- A constructor application. -/
def ctorApp (ci : ConstructorVal) (args : Array (Arg .pure)) : TM Ml.Expr := do
  let ex ← readExterns
  let fieldArgs := args.extract ci.numParams args.size
  let fnames := ctorFieldNames ci
  -- a relevant field takes the carrier raw iff a `field` row gives that field this carrier
  let mut rel : List Ml.Expr := []
  let mut named : List (String × Ml.Expr) := []
  for a in fieldArgs, fn in fnames do
    if let some e ← argExpr? a then
      let e ← match ← argCarrier? a with
        | none => pure e
        | some c =>
          if ex.fieldCarrier? ci.induct fn.toString == some c then pure e
          else useAsList s!"{ci.name}.{fn}" c e
      rel := rel ++ [e]
      named := named ++ [(fieldName fn.toString, e)]
  if let some native := Native.expression ci.name rel then return native
  else
    let env ← readEnv
    noteReal ci.induct
    if isStructure env ci.induct then
      -- every field erased: the type is the abbreviation `unit` (`Types.lean`), the value `()`
      if named.isEmpty then return .unit
      return .annot (.record named) (tyOfInd (← readExterns) (← readTypeNames) env ci.induct)
    else
      return .ctor (OCaml5.Lcnf.ctorNameIn (← readTypeNames) ci.induct (shortName ci.name)) rel

/-- Whether a `let` binds a list literal, and which: `some none` is `[]`, `some (some e)` is
the one-element `[e]`. It is the difference between `snoc` and `append` (`p.path ++ [i]` is
three LCNF lets: `nil`, `cons i nil`, `append path that`). -/
def listFact? (v : LetValue .pure) : TM (Option (Option Ml.Expr)) := do
  match v with
  | .const n _ args =>
    -- `[]`, and the empty accumulator the tail-recursion transform writes as an `Array`
    -- (`List.takeTR.go l l n #[]`; `Types.builtinTy?` reads `Array` as `list`)
    if n == ``List.nil || n == ``Array.mkEmpty || n == ``Array.emptyWithCapacity
       || n == ``Array.empty then return some none
    else if n == ``List.cons then
      match args.toList.drop 1 with
      | [h, .fvar t] =>
        match (← get).listLit[t]? with
        | some none => return some (some (← argExpr h))
        | _ => return none
      | _ => return none
    else return none
  | _ => return none

/-- An argument in a position that needs the Lean list. -/
def argAsList (site : String) (a : Arg .pure) : TM (Option Ml.Expr) := do
  match ← argExpr? a with
  | none => return none
  | some e =>
    match ← argCarrier? a with
    | none => return some e
    | some c => return some (← useAsList site c e)

/-- The relevant (non-erased) arguments of a call, as the variables they are. -/
private def relIds (args : Array (Arg .pure)) : List FVarId :=
  args.toList.filterMap fun | .fvar id => some id | _ => none

private def varOf (id : FVarId) : TM Ml.Expr := return .var (← nameOf id)

/-- The Lean list operation `n`, applied to a value that is a **carrier**, as the carrier's
own operation. This is the second half of the seam (`docs/research/
2026-09-08-engine-prof-chain.md` §5.2, gap 2): a `fn` row can rename a function, but
`p.path ++ [i]` is written *inline* in nine declarations that must stay generated, so the
table cannot reach it and this rule must.

`x ++ [i]` is `snoc`, `x ++ ys` is `append`, `x ++ []` is `x`; `List.length`, `env[i]?`
(`List.get?Internal`) and `List.take` (as the mono phase writes it, `List.takeTR.go l l n []`)
are the carrier's own. Anything else falls through and the value is turned back into the list,
which is correct and slow, and is reported. -/
def carrierRewrite? (n : Name) (args : Array (Arg .pure)) :
    TM (Option (Ml.Expr × Option String)) := do
  let base := stripRedArg n
  let s := base.toString
  let ids := relIds args
  let st ← get
  match ids with
  | [x, y] =>
    if base == ``List.append || base == ``List.appendTR then
      match ← carrierOfId? x with
      | none => return none
      | some c =>
        let xe ← varOf x
        match st.listLit[y]? with
        | some none => return some (xe, some c)
        | some (some e) => return (← carrierOp? c "snoc" [xe, e]).map (·, some c)
        | none => return (← carrierOp? c "append" [xe, ← varOf y]).map (·, some c)
    else if s.endsWith "List.get?Internal" || s.endsWith "List.get?"
         || s.endsWith "List.getElem?" then
      match ← carrierOfId? x with
      | none => return none
      | some c => return (← carrierOp? c "get" [← varOf x, ← varOf y]).map (·, none)
    else if s.endsWith "List.take" || s.endsWith "List.takeTR" then
      -- Lean takes the count first
      match ← carrierOfId? y with
      | none => return none
      | some c => return (← carrierOp? c "take" [← varOf y, ← varOf x]).map (·, some c)
    else return none
  | [x] =>
    if base == ``List.length || base == ``List.lengthTR then
      match ← carrierOfId? x with
      | none => return none
      | some c => return (← carrierOp? c "length" [← varOf x]).map (·, none)
    else return none
  | [l, xs, k, acc] =>
    -- `List.take n l` after the tail-recursion transform: `takeTR.go l l n #[]`. Only that
    -- shape is the carrier's `take`; any other is left alone (and then typed wrong, loudly).
    if s.endsWith "List.takeTR.go" then
      match ← carrierOfId? l with
      | none => return none
      | some c =>
        if xs != l then return none
        match st.listLit[acc]? with
        | some none => return (← carrierOp? c "take" [← varOf l, ← varOf k]).map (·, some c)
        | _ => return none
    else return none
  | _ => return none

/-- A `LetValue`, and the carrier its value holds when it holds one. -/
def letValueExpr (declName : Name) (v : LetValue .pure) : TM (Ml.Expr × Option String) := do
  match v with
  -- The 63-bit rule, literal half: a `Nat` literal OCaml's `int` cannot hold (`2 ^ 62` and up,
  -- the folded `2 ^ 64` of `Val.wf` among them) is `max_int`, not an out-of-range literal
  -- OCaml refuses. Same reading as the `Nat.pow` row; see `ocaml/gen/NOTES.md` §5.
  | .lit (.nat n) => return (if n ≥ 4611686018427387904 then .var "max_int" else .int n, none)
  | .lit (.str s) => return (.str s, none)
  | .lit (.uint8 n) => return (.int n.toNat, none)
  | .lit (.uint16 n) => return (.int n.toNat, none)
  | .lit (.uint32 n) => return (.int n.toNat, none)
  | .lit (.uint64 n) => return (.int n.toNat, none)
  | .lit (.usize n) => return (.int n.toNat, none)
  | .erased => return (.unit, none)
  | .proj typeName i s =>
    let env ← readEnv
    let sv := Ml.Expr.var (← nameOf s)
    if typeName == ``Prod then
      return (Ml.Expr.call (if i == 0 then "fst" else "snd") [sv], none)
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
          let fld := (names[i]?.getD (Name.mkSimple s!"_{i}")).toString
          -- reading a `field`-row field is where a carrier enters a declaration
          return (.field sv (fieldName fld), (← readExterns).fieldCarrier? typeName fld)
        else
          todo s!"{declName}: proj on {typeName} #{i} (a single-constructor inductive that is not a structure)"
          return (.hole s!"proj {typeName} #{i}" (.assertE (.bool false)), none)
      | none =>
        todo s!"{declName}: proj on {typeName} #{i} (not a structure)"
        return (.hole s!"proj {typeName} #{i}" (.assertE (.bool false)), none)
  | .fvar f args =>
    let fv := Ml.Expr.var (← nameOf f)
    -- a rename carries the carrier with it; a local call (a join point) takes it raw, and
    -- OCaml infers the join point's parameter type from the call
    if args.isEmpty then return (fv, ← carrierOfId? f)
    return (.app fv (← args.toList.mapM argExpr), none)
  | .const n _ args =>
    let env ← readEnv
    -- `Extract Constant`: the row wins over the constructor rule and over `builtin?`, so a
    -- carrier's own constructor (`Dispatcher.mk`, `MemoMap.mk`) can be re-spelled too. Erased
    -- arguments — the type parameters among them — are dropped, as they are for a builtin.
    -- A row takes a carrier argument RAW: the hand body is written against the signature.
    let exx ← readExterns
    let relCount : Nat := args.foldl (fun (c : Nat) a => match a with | .fvar _ => c + 1 | _ => c) 0
    match exx.fn? n (some relCount) with
    | some f =>
      let key := (exx.fnRowKey? n (some relCount)).getD n
      let deps := f.spec.filterMap fun | .lit d => some d | _ => none
      modify fun s =>
        { s with usedExterns := if s.usedExterns.contains key then s.usedExterns
                                else s.usedExterns.push key,
                 externDeps := deps.foldl (fun a d => if a.contains d then a else a.push d)
                                 s.externDeps }
      return (f.apply (← args.toList.filterMapM argExpr?), none)
    | none =>
    -- a Lean list operation applied to a carrier is the carrier's own operation
    match ← carrierRewrite? n args with
    | some r => return r
    | none =>
    match env.find? n with
    | some (.ctorInfo ci) => return (← ctorApp ci args, none)
    | _ =>
      match builtin? n with
      | some b =>
        let as ← args.toList.filterMapM (argAsList s!"{declName}: builtin {n}")
        return (applyBuiltin b as, none)
      | none =>
        noteCall n
        let g := Ml.Expr.var (globalName n)
        -- A wrapper is called under its twin's name, so the call passes the twin exactly the
        -- parameters the wrapper kept. When the reference is *unsaturated* — mono LCNF passes
        -- `Effect4.Machine.finExit` itself as an argument of type `FinName → Exit → Exit`, and
        -- the twin `finExit._redArg` takes only the `FinName` — the twin has the wrong arity at
        -- that position, so it is eta-expanded back to the wrapper's: the missing relevant
        -- parameters become `fun` binders, the missing erased ones `()`, and the ones the twin
        -- kept are handed on. (`api_gen.ml:5036`, `ScopeStore.addFinalizer`'s `run`.)
        match wrapperKeep? env n with
        | none =>
          if args.isEmpty then return (g, none)
          else return (.app g (← argsFor n args.toList), none)
        | some keep =>
          let wparams := (wrapperParams? env n).getD #[]
          if args.size ≥ wparams.size then
            let kept := keep.filterMap fun i => args[i]?
            let extra := args.toList.drop wparams.size
            let allKept := kept.toList ++ extra
            if allKept.isEmpty then return (g, none)
            return (.app g (← argsFor n allKept), none)
          -- eta-expand: one OCaml binder per missing relevant parameter, `()` per erased one
          let mut binders : List String := []
          let mut extra : Std.HashMap Nat Ml.Expr := {}
          for i in [args.size:wparams.size] do
            if wparams[i]!.type.isErased then
              extra := extra.insert i .unit
            else
              let b ← fresh "_eta"
              binders := binders ++ [b]
              extra := extra.insert i (.var b)
          let mut kept : List Ml.Expr := []
          for i in keep do
            if h : i < args.size then kept := kept ++ [← argExpr args[i]]
            else kept := kept ++ [extra.getD i .unit]
          let body := if kept.isEmpty then g else .app g kept
          if binders.isEmpty then return (body, none)
          return (.fn binders body, none)

/-! ## Patterns -/

/-- The pattern of a `cases` alternative, binding the parameters the arm uses. -/
def altPat (ctor : Name) (ps : Array (LCNF.Param .pure)) (usedVars : FVarIdHashSet) :
    TM Ml.Pat := do
  let env ← readEnv
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
  if let some native := Native.pattern ctor rel then return native
  else
    match env.find? ctor with
    | some (.ctorInfo ci) =>
      noteReal ci.induct
      if isStructure env ci.induct then
        let names := ctorFieldNames ci
        let ex ← readExterns
        let mut fields : List (String × Ml.Pat) := []
        let mut omitted := false
        for p? in pats, n in names, p in ps do
          -- binding a `field`-row field is the other place a carrier enters a declaration
          if let some c := ex.fieldCarrier? ci.induct n.toString then
            if p? matches some (.var _) then setCarrier p.fvarId c
          match p? with
          | some (.var v) => fields := fields ++ [(fieldName n.toString, .var v)]
          | some _ => omitted := true
          | none => pure ()
        if fields.isEmpty then return .wild
        return if omitted then .recordOpen fields else .record fields
      else
        return .ctor (OCaml5.Lcnf.ctorNameIn (← readTypeNames) ci.induct (shortName ctor)) rel
    | _ =>
      todo s!"alternative on unknown constructor {ctor}"
      return .wild

/-! ## Code -/

mutual

/-- A `Code` in tail position. -/
partial def code (declName : Name) (c : Code .pure) : TM Ml.Expr := do
  match c with
  | .let decl k =>
    let (v, carr?) ← letValueExpr declName decl.value
    let lit? ← listFact? decl.value
    let x ← bindVar decl.fvarId decl.binderName
    if let some c := carr? then setCarrier decl.fvarId c
    if let some f := lit? then
      modify fun s => { s with listLit := s.listLit.insert decl.fvarId f }
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
      let env ← readEnv
      let tn ← readTypeNames
      let exx ← readExterns
      let scrut : Ml.Expr :=
        if Native.owns cs.typeName then .var d
        else .annot (.var d) (tyOfInd exx tn env cs.typeName)
      unless Native.owns cs.typeName do noteReal cs.typeName
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
  /-- OCaml names an extern row hands to a hand body: an emission-order dependency. -/
  externDeps : Array String := #[]
  /-- The LCNF signature, for the reader. -/
  signature : String
  recursive : Bool

instance : Inhabited Ml.Bind := ⟨{ name := "_", body := .unit }⟩
instance : Inhabited Translated :=
  ⟨{ leanName := .anonymous, userName := .anonymous, ocamlName := "_", bind := default,
     callees := #[], signature := "", recursive := false }⟩

/-- Translate one mono decl under an OCaml name. -/
def translateDecl (env : Environment) (d : LCNF.Decl .pure) (userName : Name) (ocamlName : String)
    (tn : TypeNames := {}) (ex : Externs := {}) : Translated × St :=
  let act : TM Translated := do
    -- reserve the names the builtin forms use
    modify fun s => { s with used := preUsed.foldl (fun m n => m.insert n 0) s.used }
    let mut params : List (String × Option Ml.Ty) := []
    let mut i := 0
    for p in d.params do
      let x ← bindVar p.fvarId p.binderName
      noteMentioned (monoTyConsts p.type)
      let t := monoTy env ex tn p.type
      -- a `carg` row: this parameter carries a carrier, not the list. It is what an
      -- inter-procedural analysis would infer (`blockExit`'s `env` is one because its callers
      -- pass one) and what the table states instead.
      let t ← match ex.cargChain? d.name i p.binderName.toString with
        | none => pure t
        | some chain => do
          setCarrier p.fvarId (chainKey chain)
          let ckey := (ex.cargRowKey? d.name).getD (stripRedArg d.name)
          modify fun s =>
            { s with usedCargs := if s.usedCargs.contains ckey then s.usedCargs
                                  else s.usedCargs.push ckey }
          pure (carrierAnnot chain t)
      params := params ++ [(x, if tyIsAnon t then none else some t)]
      i := i + 1
    -- the result type: the decl type with the parameters peeled off
    let mut rty := d.type
    for _ in [:d.params.size] do
      match rty with
      | .forallE _ _ b _ => rty := b
      | _ => pure ()
    noteMentioned (monoTyConsts rty)
    -- a declaration that takes a carrier may return one at a position no chain can spell
    -- (`Option (Prod (List Nat) (List Val))`), so its result annotation is dropped and OCaml
    -- infers it.
    let result := if (ex.carg? d.name).isSome then Ml.Ty.anon else monoTy env ex tn rty
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
             callees := callees, externDeps := (← get).externDeps, signature := sig,
             recursive := d.recursive || callees.contains d.name }
  Id.run ((act { env := env, tn := tn, ex := ex }).run {})

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
  /-- `fn` extern rows a translated declaration actually hit (G10's ledger). -/
  usedExterns : Array Name := #[]
  /-- `ops` rows a rewrite used, as `<carrier>#<op>`. -/
  usedOps : Array String := #[]
  /-- `carg` rows a declaration used. -/
  usedCargs : Array Name := #[]
  /-- Every place a carrier was turned back into the Lean list. -/
  toLists : Array String := #[]

private def pushNew (a : Array Name) (n : Name) : Array Name :=
  if a.contains n then a else a.push n

/-- Translate `roots` and, transitively, every non-builtin constant they call, up to `cap`
declarations. -/
def translateClosure (roots : Array Name) (cap : Nat := 60) (tn : TypeNames := {})
    (ex : Externs := {}) : CoreM Closure := do
  let env ← getEnv
  let mono := Conform.Lcnf.persistedMonoIndex env
  let mut c : Closure := {}
  let mut done : NameSet := {}
  let mut queue : Array Name := roots
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if done.contains n then continue
    let arity := (mono.findIn? env n).map (fun d => d.params.size)
    if ex.hasFn n arity then continue
    if (builtin? n).isSome then continue
    if env.find? n matches some (.ctorInfo _) then continue
    if c.decls.size ≥ cap then
      c := { c with frontier := pushNew c.frontier n }
      continue
    done := done.insert n
    let d? := mono.findIn? env n
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
      if let some dt := mono.findIn? env twin then d := dt
    | none =>
      -- a twin reached directly: its wrapper is the user-facing name
      userName := stripRedArg n
      if userName != n then done := done.insert userName
    let (t, st) := translateDecl env d userName (globalName userName) tn ex
    c := { c with
      decls := c.decls.push t,
      realTypes := st.realTypes.foldl pushNew c.realTypes,
      mentioned := st.mentioned.foldl pushNew c.mentioned,
      usedExterns := st.usedExterns.foldl pushNew c.usedExterns,
      usedOps := st.usedOps.foldl (fun a o => if a.contains o then a else a.push o) c.usedOps,
      usedCargs := st.usedCargs.foldl pushNew c.usedCargs,
      toLists := c.toLists ++ st.toLists,
      todos := c.todos ++ st.todos }
    for callee in st.calls do
      unless done.contains callee do
        -- a direct reference to a wrapper that has a twin: note it, translate the twin
        if stripRedArg callee == callee then
          if (mono.findIn? env (callee ++ `_redArg)).isSome then
            c := { c with wrapperRefs := pushNew c.wrapperRefs callee }
        queue := queue.push callee
  return c

/-! ## Emission: strongly connected components, dependencies first -/

/-- Pure OCaml primitive implementations. Strings admitted by this profile are valid UTF-8;
`ByteArray` and `Array UInt8` both use a byte list. These definitions are emitted by the
production backend and are part of the manifest, never patched into a generated file. -/
def primitivePrelude : List Ml.Decl := [
  .rawD "let lcnf_utf8_bytes s = List.init (String.length s) (fun i -> Char.code (String.get s i))",
  .rawD "let lcnf_utf8_length s = String.fold_left (fun n c -> if Char.code c land 192 = 128 then n else n + 1) 0 s",
  .blank]

/-- Dependencies first on the translated-name graph. Wrapper/twin aliases and the
extern leading-argument dependencies use this same graph. Duplicate output names are a
refusal before any map insertion, because overwriting a vertex loses a declaration. -/
def emissionGroups (ds : Array Translated) : Except String (List (List Nat)) := do
  let mut byName : Std.HashMap String Nat := {}
  for i in [:ds.size] do
    let name := ds[i]!.ocamlName
    if byName.contains name then throw s!"duplicate emitted name: {name}"
    byName := byName.insert name i
  let adj := ds.map fun t =>
    (t.callees.filterMap fun c => byName[globalName c]?) ++
      t.externDeps.filterMap fun n => byName[n]?
  return Lean.SCC.scc (List.range ds.size) (fun i => adj[i]!.toList)

/-- One binding group per component, preserving input/successor order and origin comments. -/
def emit (ds : Array Translated) : Except String (List Ml.Decl) := do
  let groups ← emissionGroups ds
  return primitivePrelude ++ groups.flatMap fun comp =>
    let binds := comp.map fun v => ds[v]!.bind
    let isRec := comp.length > 1 || comp.any fun v => ds[v]!.recursive
    let origin := String.intercalate "\n   " (comp.map fun v => ds[v]!.signature)
    [.comment ("LCNF mono: " ++ origin), .letD isRec binds, .blank]

end OCaml5.Lcnf
