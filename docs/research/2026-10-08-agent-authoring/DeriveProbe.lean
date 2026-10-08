import Effect4.Modules.Step
import Effect4.Laws.Modules.Step
import Effect4.Schema.Modeled.Derive

/-! Probe DERIVE-1, part 1: the certificate bank. One lemma per construct of the fragment, each
stating a step's value against `Modeled.toC` of the Lean term it was derived from. -/

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules

namespace DeriveProbe.Cert

variable {Γ : List Ty} {vs : Inputs Leaves.refused Γ}

local notation "R" => Leaves.refused
local notation "⌜" x "⌝" => Modeled.toC x

/-- Congruence in two arguments; the probe's own, since the core has none. -/
theorem congr2 {α β γ : Sort _} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := by
  subst ha hb
  rfl

/-- A Boolean fact the condition `≤` needs: `!(y < x)` decides `x ≤ y`. -/
theorem leB (x y : Nat) : (!decide (y < x)) = decide (x ≤ y) :=
  (decide_not ..).symm.trans (decide_eq_decide.mpr Nat.not_lt)

theorem nat (n : Nat) : (Step.nat n : Step Γ .nat).eval R vs = ⌜n⌝ := rfl
theorem bool (b : Bool) : (Step.bool b : Step Γ .bool).eval R vs = ⌜b⌝ := rfl
theorem unit : (Step.unit : Step Γ .unit).eval R vs = ⌜()⌝ := rfl

theorem add {a b : Step Γ .nat} {x y : Nat} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.add a b).eval R vs = ⌜x + y⌝ :=
  congr2 (fun (p q : Nat) => p + q) ha hb

theorem sub {a b : Step Γ .nat} {x y : Nat} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.sub a b).eval R vs = ⌜x - y⌝ :=
  congr2 (fun (p q : Nat) => p - q) ha hb

theorem andB {a b : Step Γ .bool} {x y : Bool} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.and a b).eval R vs = ⌜x && y⌝ :=
  congr2 (fun (p q : Bool) => p && q) ha hb

theorem orB {a b : Step Γ .bool} {x y : Bool} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.or a b).eval R vs = ⌜x || y⌝ :=
  congr2 (fun (p q : Bool) => p || q) ha hb

theorem notB {a : Step Γ .bool} {x : Bool} (ha : a.eval R vs = ⌜x⌝) :
    (Step.not a).eval R vs = ⌜!x⌝ :=
  congrArg (fun (p : Bool) => !p) ha

/-! ### Conditions: a proposition decided -/

theorem le {a b : Step Γ .nat} {x y : Nat} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.not (Step.lt b a)).eval R vs = decide (x ≤ y) := by
  exact (congr2 (fun (p q : Nat) => !decide (q < p)) ha hb).trans (leB x y)

theorem lt {a b : Step Γ .nat} {x y : Nat} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.lt a b).eval R vs = decide (x < y) :=
  congr2 (fun (p q : Nat) => decide (p < q)) ha hb

theorem eqN {a b : Step Γ .nat} {x y : Nat} (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.eq a b).eval R vs = decide (x = y) :=
  congr2 (fun (p q : Nat) => decide (p = q)) ha hb

theorem isZero {a : Step Γ .nat} {x : Nat} (ha : a.eval R vs = ⌜x⌝) :
    (Step.isZero a).eval R vs = decide (x = 0) :=
  congrArg (fun (p : Nat) => decide (p = 0)) ha

theorem isTrue {c : Step Γ .bool} {x : Bool} (h : c.eval R vs = ⌜x⌝) :
    c.eval R vs = decide (x = true) :=
  h.trans (by cases x <;> rfl)

theorem and {a b : Step Γ .bool} {p q : Prop} [Decidable p] [Decidable q]
    (ha : a.eval R vs = decide p) (hb : b.eval R vs = decide q) :
    (Step.and a b).eval R vs = decide (p ∧ q) :=
  (congr2 (fun (u v : Bool) => u && v) ha hb).trans (Bool.decide_and ..).symm

theorem or {a b : Step Γ .bool} {p q : Prop} [Decidable p] [Decidable q]
    (ha : a.eval R vs = decide p) (hb : b.eval R vs = decide q) :
    (Step.or a b).eval R vs = decide (p ∨ q) :=
  (congr2 (fun (u v : Bool) => u || v) ha hb).trans (Bool.decide_or ..).symm

theorem not {a : Step Γ .bool} {p : Prop} [Decidable p] (ha : a.eval R vs = decide p) :
    (Step.not a).eval R vs = decide ¬p :=
  (congrArg (fun (u : Bool) => !u) ha).trans (decide_not ..).symm

/-! ### The choice -/

theorem ite {α : Type} [Modeled α] {c : Step Γ .bool} {a b : Step Γ (Modeled.ty (α := α))}
    {p : Prop} [Decidable p] {x y : α}
    (hc : c.eval R vs = decide p) (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.ite c a b).eval R vs = ⌜if p then x else y⌝ := by
  by_cases h : p
  · exact ((Step.eval_ite R vs c a b).trans
      (congrArg (fun (z : Bool) => cond z (a.eval R vs) (b.eval R vs))
        (hc.trans (decide_eq_true h)))).trans (ha.trans (congrArg Modeled.toC (if_pos h)).symm)
  · exact ((Step.eval_ite R vs c a b).trans
      (congrArg (fun (z : Bool) => cond z (a.eval R vs) (b.eval R vs))
        (hc.trans (decide_eq_false h)))).trans (hb.trans (congrArg Modeled.toC (if_neg h)).symm)

/-! ### Products and options -/

theorem pair {α β : Type} [Modeled α] [Modeled β] {a : Step Γ (Modeled.ty (α := α))}
    {b : Step Γ (Modeled.ty (α := β))} {x : α} {y : β}
    (ha : a.eval R vs = ⌜x⌝) (hb : b.eval R vs = ⌜y⌝) :
    (Step.pair a b).eval R vs = ⌜(x, y)⌝ :=
  congr2 Prod.mk ha hb

theorem some {α : Type} [Modeled α] {a : Step Γ (Modeled.ty (α := α))} {x : α}
    (ha : a.eval R vs = ⌜x⌝) : (Step.some a).eval R vs = ⌜Option.some x⌝ :=
  congrArg Option.some ha

/-! ### Lists -/

theorem len {α : Type} [Modeled α] {a : Step Γ (.list (Modeled.ty (α := α)))} {xs : List α}
    (ha : a.eval R vs = ⌜xs⌝) : (Step.len a).eval R vs = ⌜xs.length⌝ :=
  (congrArg (fun (l : List (Carrier (Modeled.ty (α := α)))) => l.length) ha).trans (List.length_map _)

theorem append {α : Type} [Modeled α] {a b : Step Γ (.list (Modeled.ty (α := α)))}
    {xs ys : List α} (ha : a.eval R vs = ⌜xs⌝) (hb : b.eval R vs = ⌜ys⌝) :
    (Step.append a b).eval R vs = ⌜xs ++ ys⌝ :=
  (congr2 (fun (l m : List (Carrier (Modeled.ty (α := α)))) => l ++ m) ha hb).trans (List.map_append ..).symm

theorem take {α : Type} [Modeled α] {a : Step Γ (.list (Modeled.ty (α := α)))} {n : Step Γ .nat}
    {xs : List α} {k : Nat} (ha : a.eval R vs = ⌜xs⌝) (hn : n.eval R vs = ⌜k⌝) :
    (Step.take a n).eval R vs = ⌜xs.take k⌝ :=
  (congr2 (fun (l : List (Carrier (Modeled.ty (α := α)))) (m : Nat) => List.take m l) ha hn).trans (List.map_take ..).symm

theorem drop {α : Type} [Modeled α] {a : Step Γ (.list (Modeled.ty (α := α)))} {n : Step Γ .nat}
    {xs : List α} {k : Nat} (ha : a.eval R vs = ⌜xs⌝) (hn : n.eval R vs = ⌜k⌝) :
    (Step.drop a n).eval R vs = ⌜xs.drop k⌝ :=
  (congr2 (fun (l : List (Carrier (Modeled.ty (α := α)))) (m : Nat) => List.drop m l) ha hn).trans (List.map_drop ..).symm

theorem emptyLike {α : Type} [Modeled α] {a : Step Γ (.list (Modeled.ty (α := α)))} :
    (Step.emptyLike a).eval R vs = ⌜([] : List α)⌝ := rfl

/-! ### Records: the reading and the overwrite, against the carrier -/

theorem get {fs : List (String × Bool × Ty)} {t : Ty} {r : Step Γ (.record fs)} {f : FieldRef fs t}
    {c : CarrierAt R (.record fs)} (hr : r.eval R vs = c) : (Step.get r f).eval R vs = f.get c :=
  congrArg f.get hr

theorem set {fs : List (String × Bool × Ty)} {t : Ty} {r : Step Γ (.record fs)} {f : FieldRef fs t}
    {v : Step Γ t} {c : CarrierAt R (.record fs)} {w : CarrierAt R t}
    (hr : r.eval R vs = c) (hv : v.eval R vs = w) : (Step.set r f v).eval R vs = f.set c w :=
  congr2 f.set hr hv

end DeriveProbe.Cert

/-! Probe DERIVE-1, part 2: the derivation. It walks an ordinary Lean function of `Modeled`
values and writes the step and its certificate, composed from part 1's lemmas. The kernel checks
the certificate. A construct outside the fragment refuses with the subterm. -/

namespace DeriveProbe.Meta
open Lean Meta Elab Term Command
open Effect4.Schema (Modeled)

structure Ctx where
  vars : Array Expr
  inputs : Array Expr
  gamma : Expr
  vs : Expr

def R : Expr := mkConst ``Effect4.Schema.Model.Leaves.refused

def tyOf (T : Expr) : MetaM Expr := mkAppOptM ``Effect4.Schema.Modeled.ty #[T, none]
def toCOf (x : Expr) : MetaM Expr := mkAppM ``Effect4.Schema.Modeled.toC #[x]
def evalOf (ctx : Ctx) (step : Expr) : MetaM Expr :=
  mkAppM ``Effect4.Modules.Step.eval #[R, ctx.vs, step]

/-- A certificate stated against `toC e`, checked by definitional unfolding first. -/
def ascribe (ctx : Ctx) (step cert e : Expr) : MetaM Expr := do
  let goal ← mkEq (← evalOf ctx step) (← toCOf e)
  unless ← isDefEq (← inferType cert) goal do
    throwError "derive_step: the certificate does not unfold to its statement at {← ppExpr e}"
  mkExpectedTypeHint cert goal

def refuse {α : Type} (e : Expr) (why : String) : MetaM α := do
  throwError "derive_step: {why}: {← ppExpr e}"

/-- The position of a structure's projection in its derived carrier, read from `modeledToC`. -/
def fieldPosition (structName proj : Name) : MetaM Nat := do
  let some (.defnInfo d) := (← getEnv).find? (structName ++ `modeledToC)
    | throwError "derive_step: {structName} has no derived Modeled instance"
  lambdaTelescope d.value fun _ body => do
    let rec go : Nat → Nat → Expr → MetaM Nat
      | 0, _, _ => throwError "derive_step: {proj} is not a field of {structName}'s carrier"
      | fuel + 1, k, e => do
        unless e.isAppOfArity ``Prod.mk 4 do
          throwError "derive_step: {proj} is not a field of {structName}'s carrier"
        if (e.getArg! 2).getUsedConstants.contains proj then return k
        go fuel (k + 1) (e.getArg! 3)
    go 4096 0 body

/-- The positional field reference at `k`, elaborated against `FieldRef fs t`. -/
def fieldRef (k : Nat) (expected : Expr) : TermElabM Expr := do
  let rec stx : Nat → MetaM (TSyntax `term)
    | 0 => `(Effect4.Schema.FieldRef.here _ _ _)
    | j + 1 => do `(Effect4.Schema.FieldRef.there _ _ _ $(← stx j))
  let e ← elabTermEnsuringType (← stx k) expected
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def cert (n : Name) (args : Array Expr) : MetaM Expr := mkAppM (`DeriveProbe.Cert ++ n) args

/-- A generic lemma of the bank at explicit Lean types: `Γ` and `vs`, then `types`, then `holes`
implicit arguments left to unification, then the children's certificates. -/
def certT (n : Name) (types : Array Expr) (holes : Nat) (proofs : Array Expr) : MetaM Expr :=
  mkAppOptM (`DeriveProbe.Cert ++ n)
    (#[none, none] ++ types.map some ++ (Array.replicate holes none) ++ proofs.map some)

mutual
/-- The step of a value, and its certificate `step.eval R vs = toC e`. -/
def reify : Nat → Ctx → Expr → TermElabM (Expr × Expr)
  | 0, _, e => refuse e "the derivation's depth bound"
  | fuel + 1, ctx, e => do
  let e ← instantiateMVars e
  -- an argument of the model function
  if let some i := ctx.vars.findIdx? (· == e) then
    let step ← mkAppM ``Effect4.Modules.Step.var #[ctx.inputs[i]!]
    return (step, ← ascribe ctx step (← mkEqRefl (← evalOf ctx step)) e)
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName?, args.size with
  | some ``OfNat.ofNat, 3 =>
    unless ← isDefEq args[0]! (mkConst ``Nat) do refuse e "a numeral of another type"
    let n := args[1]!
    let step ← mkAppOptM ``Effect4.Modules.Step.nat #[ctx.gamma, n]
    return (step, ← ascribe ctx step (← mkAppOptM ``DeriveProbe.Cert.nat #[ctx.gamma, ctx.vs, n]) e)
  | some ``Bool.true, 0 | some ``Bool.false, 0 =>
    let step ← mkAppOptM ``Effect4.Modules.Step.bool #[ctx.gamma, e]
    return (step, ← ascribe ctx step (← mkAppOptM ``DeriveProbe.Cert.bool #[ctx.gamma, ctx.vs, e]) e)
  | some ``HAdd.hAdd, 6 => binary fuel ctx e ``Effect4.Modules.Step.add `add args[4]! args[5]!
  | some ``HSub.hSub, 6 => binary fuel ctx e ``Effect4.Modules.Step.sub `sub args[4]! args[5]!
  | some ``and, 2 => binary fuel ctx e ``Effect4.Modules.Step.and `andB args[0]! args[1]!
  | some ``or, 2 => binary fuel ctx e ``Effect4.Modules.Step.or `orB args[0]! args[1]!
  | some ``not, 1 =>
    let (sa, ha) ← reify fuel ctx args[0]!
    let step ← mkAppM ``Effect4.Modules.Step.not #[sa]
    return (step, ← ascribe ctx step (← cert `notB #[ha]) e)
  | some ``ite, 5 =>
    let (sc, hc) ← reifyCond fuel ctx args[1]!
    let (sa, ha) ← reify fuel ctx args[3]!
    let (sb, hb) ← reify fuel ctx args[4]!
    let step ← mkAppM ``Effect4.Modules.Step.ite #[sc, sa, sb]
    return (step, ← ascribe ctx step (← certT `ite #[args[0]!] 8 #[hc, ha, hb]) e)
  | some ``Prod.mk, 4 =>
    let (sa, ha) ← reify fuel ctx args[2]!
    let (sb, hb) ← reify fuel ctx args[3]!
    let step ← mkAppM ``Effect4.Modules.Step.pair #[sa, sb]
    return (step, ← ascribe ctx step (← certT `pair #[args[0]!, args[1]!] 6 #[ha, hb]) e)
  | some ``Option.some, 2 =>
    let (sa, ha) ← reify fuel ctx args[1]!
    let step ← mkAppM ``Effect4.Modules.Step.some #[sa]
    return (step, ← ascribe ctx step (← certT `some #[args[0]!] 3 #[ha]) e)
  | some ``List.length, 2 =>
    let (sa, ha) ← reify fuel ctx args[1]!
    let step ← mkAppM ``Effect4.Modules.Step.len #[sa]
    return (step, ← ascribe ctx step (← certT `len #[args[0]!] 3 #[ha]) e)
  | some ``HAppend.hAppend, 6 =>
    let some elem := (← whnf args[0]!).app1? ``List | refuse e "an append of another type"
    let (sa, ha) ← reify fuel ctx args[4]!
    let (sb, hb) ← reify fuel ctx args[5]!
    let step ← mkAppM ``Effect4.Modules.Step.append #[sa, sb]
    return (step, ← ascribe ctx step (← certT `append #[elem] 5 #[ha, hb]) e)
  | some ``List.take, 3 => listCut fuel ctx e ``Effect4.Modules.Step.take `take args
  | some ``List.drop, 3 => listCut fuel ctx e ``Effect4.Modules.Step.drop `drop args
  | some c, _ =>
    let env ← getEnv
    if let some info := env.getProjectionFnInfo? c then
      unless info.fromClass == false && args.size == info.numParams + 1 do
        refuse e "a projection of a class or a partial application"
      let some structName := env.getProjectionStructureName? c | refuse e "an unknown structure"
      let k ← fieldPosition structName c
      let (sr, hr) ← reify fuel ctx args[info.numParams]!
      let recTy ← whnf (← tyOf (← inferType args[info.numParams]!))
      unless recTy.isAppOfArity ``Effect4.Program.Ty.record 1 do refuse e "a structure with no record type"
      let fieldTy ← tyOf (← inferType e)
      let f ← fieldRef k (← mkAppM ``Effect4.Schema.FieldRef #[recTy.getArg! 0, fieldTy])
      let step ← mkAppM ``Effect4.Modules.Step.get #[sr, f]
      return (step, ← ascribe ctx step
        (← mkAppOptM ``DeriveProbe.Cert.get #[none, none, none, none, none, f, none, hr]) e)
    if let some (.ctorInfo ci) := env.find? c then
      if isStructure env ci.induct then return ← construct fuel ctx e ci
    if let some e' ← unfoldDefinition? e then
      return ← reify fuel ctx e'.headBeta
    refuse e "a construct outside the step fragment"
  | none, _ => refuse e "a construct outside the step fragment"

/-- `List.take` and `List.drop`: the list, the count, the step, and its certificate. -/
def listCut : Nat → Ctx → Expr → Name → Name → Array Expr → TermElabM (Expr × Expr)
  | 0, _, e, _, _, _ => refuse e "the derivation's depth bound"
  | fuel + 1, ctx, e, stepName, certName, args => do
  let (sa, ha) ← reify fuel ctx args[2]!
  let (sn, hn) ← reify fuel ctx args[1]!
  let step ← mkAppM stepName #[sa, sn]
  return (step, ← ascribe ctx step (← certT certName #[args[0]!] 5 #[ha, hn]) e)

/-- A binary construct: both children, the step, and its certificate lemma. -/
def binary : Nat → Ctx → Expr → Name → Name → Expr → Expr → TermElabM (Expr × Expr)
  | 0, _, e, _, _, _, _ => refuse e "the derivation's depth bound"
  | fuel + 1, ctx, e, stepName, certName, a, b => do
  let (sa, ha) ← reify fuel ctx a
  let (sb, hb) ← reify fuel ctx b
  let step ← mkAppM stepName #[sa, sb]
  return (step, ← ascribe ctx step (← cert certName #[ha, hb]) e)

/-- A structure built from a base value's fields: one overwrite for each field that changes. An
empty list in a list field is the base field's `emptyLike`. -/
def construct : Nat → Ctx → Expr → ConstructorVal → TermElabM (Expr × Expr)
  | 0, _, e, _ => refuse e "the derivation's depth bound"
  | fuel + 1, ctx, e, ci => do
  let env ← getEnv
  let fields := getStructureFields env ci.induct
  let vals := e.getAppArgs.extract ci.numParams e.getAppArgs.size
  -- the base: the value whose projection supplies some field unchanged
  let projOf (i : Nat) (v : Expr) : Option Expr :=
    match getProjFnForField? env ci.induct fields[i]! with
    | some p => if v.isAppOf p && v.getAppNumArgs ≥ 1 then some v.appArg! else none
    | none => none
  let some base := (List.range vals.size).findSome? (fun i => projOf i vals[i]!)
    | refuse e "a structure built from no base value (record construction lands with `record_step%`)"
  let (sBase, hBase) ← reify fuel ctx base
  let recTy ← whnf (← tyOf (← inferType e))
  let mut step := sBase
  let mut prf := hBase
  for i in [0:vals.size] do
    let v := vals[i]!
    if projOf i v == some base then continue
    let some p := getProjFnForField? env ci.induct fields[i]! | refuse e "a field with no projection"
    let k ← fieldPosition ci.induct p
    let fieldTy ← tyOf (← inferType v)
    let f ← fieldRef k (← mkAppM ``Effect4.Schema.FieldRef #[recTy.getArg! 0, fieldTy])
    let mut sv := sBase
    let mut hv := hBase
    if v.isAppOfArity ``List.nil 1 then
      let old ← mkAppM ``Effect4.Modules.Step.get #[sBase, f]
      sv ← mkAppM ``Effect4.Modules.Step.emptyLike #[old]
      let elem := v.getArg! 0
      hv ← ascribe ctx sv (← mkAppOptM ``DeriveProbe.Cert.emptyLike
        #[some ctx.gamma, some ctx.vs, some elem, none, some old]) v
    else
      let (sv', hv') ← reify fuel ctx v
      sv := sv'
      hv := hv'
    step ← mkAppM ``Effect4.Modules.Step.set #[step, f, sv]
    prf ← mkAppOptM ``DeriveProbe.Cert.set #[none, none, none, none, none, f, none, none, none, prf, hv]
  return (step, ← ascribe ctx step prf e)

/-- The Boolean step of a decided proposition, and its certificate `step.eval R vs = decide p`. -/
def reifyCond : Nat → Ctx → Expr → TermElabM (Expr × Expr)
  | 0, _, p => refuse p "the derivation's depth bound"
  | fuel + 1, ctx, p => do
  let p ← instantiateMVars p
  let args := p.getAppArgs
  match p.getAppFn.constName?, args.size with
  | some ``LE.le, 4 => do
    let (sa, ha) ← reify fuel ctx args[2]!
    let (sb, hb) ← reify fuel ctx args[3]!
    let step ← mkAppM ``Effect4.Modules.Step.not #[← mkAppM ``Effect4.Modules.Step.lt #[sb, sa]]
    return (step, ← cert `le #[ha, hb])
  | some ``LT.lt, 4 => do
    let (sa, ha) ← reify fuel ctx args[2]!
    let (sb, hb) ← reify fuel ctx args[3]!
    return (← mkAppM ``Effect4.Modules.Step.lt #[sa, sb], ← cert `lt #[ha, hb])
  | some ``Eq, 3 => do
    if ← isDefEq args[0]! (mkConst ``Bool) then
      unless args[2]!.isConstOf ``Bool.true do refuse p "a Boolean equation other than `b = true`"
      let (sb, hb) ← reify fuel ctx args[1]!
      return (sb, ← cert `isTrue #[hb])
    let (sa, ha) ← reify fuel ctx args[1]!
    let (sb, hb) ← reify fuel ctx args[2]!
    return (← mkAppM ``Effect4.Modules.Step.eq #[sa, sb], ← cert `eqN #[ha, hb])
  | some ``And, 2 => do
    let (sa, ha) ← reifyCond fuel ctx args[0]!
    let (sb, hb) ← reifyCond fuel ctx args[1]!
    return (← mkAppM ``Effect4.Modules.Step.and #[sa, sb], ← cert `and #[ha, hb])
  | some ``Or, 2 => do
    let (sa, ha) ← reifyCond fuel ctx args[0]!
    let (sb, hb) ← reifyCond fuel ctx args[1]!
    return (← mkAppM ``Effect4.Modules.Step.or #[sa, sb], ← cert `or #[ha, hb])
  | some ``Not, 1 => do
    let (sa, ha) ← reifyCond fuel ctx args[0]!
    return (← mkAppM ``Effect4.Modules.Step.not #[sa], ← cert `not #[ha])
  | _, _ => refuse p "a condition outside the fragment"
end

/-- `derive_step f as X`: the step `X` of the Lean function `f`, and `X_eval`, its value
equation against `f` through `Modeled.toC`, with a certificate the kernel checks. -/
syntax (name := deriveStep) "derive_step " ident " as " ident : command

@[command_elab deriveStep] def elabDeriveStep : CommandElab := fun stx => do
  let fId := stx[1]
  let xId := stx[3]
  liftTermElabM do
    let fn ← realizeGlobalConstNoOverloadWithInfo fId
    let some (.defnInfo d) := (← getEnv).find? fn | throwError "derive_step: {fn} is not a definition"
    let x := (← getCurrNamespace) ++ xId.getId
    lambdaTelescope d.value fun args body => do
      let tys ← args.mapM fun a => do tyOf (← inferType a)
      let gamma ← mkListLit (mkConst ``Effect4.Program.Ty) tys.toList
      -- the inputs, by position
      let mut inputs := #[]
      for i in [0:args.size] do
        let rest ← mkListLit (mkConst ``Effect4.Program.Ty) (tys.toList.drop (i + 1))
        let mut inp ← mkAppM ``Effect4.Modules.Input.here #[tys[i]!, rest]
        for j' in [0:i] do
          let j := i - 1 - j'
          inp ← mkAppM ``Effect4.Modules.Input.there #[tys[j]!, inp]
        inputs := inputs.push inp
      let vsRaw ← args.foldrM (fun a acc => do mkAppM ``Prod.mk #[← toCOf a, acc]) (mkConst ``Unit.unit)
      let vs ← mkExpectedTypeHint vsRaw (← mkAppM ``Effect4.Modules.Inputs #[R, gamma])
      let ctx : Ctx := { vars := args, inputs, gamma, vs }
      let (step, certificate) ← reify 4096 ctx body
      if step.hasFVar then throwError "derive_step: the step depends on a value of an argument"
      let resTy ← tyOf (← inferType body)
      let stepTy ← mkAppM ``Effect4.Modules.Step #[gamma, resTy]
      addAndCompile <| .defnDecl {
        name := x, levelParams := [], type := stepTy, value := step, hints := .abbrev,
        safety := .safe }
      let lhs ← mkAppM ``Effect4.Modules.Step.eval #[R, vs, mkConst x]
      let stmt ← mkForallFVars args (← mkEq lhs (← toCOf (mkAppN (mkConst fn) args)))
      let prf ← mkLambdaFVars args certificate
      addDecl <| .thmDecl {
        name := x ++ `eval_eq, levelParams := [], type := stmt, value := prf }
      logInfo m!"derived {x} : {← ppExpr stepTy} and {x ++ `eval_eq}"

end DeriveProbe.Meta

/-! Probe DERIVE-1, part 3: three models written as ordinary Lean, and their derived steps. -/

namespace DeriveProbe.Demo
open Effect4.Schema (Modeled)
open Effect4.Modules

/-- Semaphore's counting state, as a person would write it. -/
structure Sem where
  permits : Nat
  taken : Nat
  deriving Modeled, Repr

/-- rc.112 `Semaphore.takeIfAvailable`, as a model. -/
def takeIfAvailable (need : Nat) (s : Sem) : Bool × Sem :=
  if need ≤ s.permits - s.taken then (true, { s with taken := s.taken + need }) else (false, s)

derive_step takeIfAvailable as takeStep

#check @takeStep.eval_eq
example : takeStep.normal = true := rfl
example : takeStep.canonical = true := rfl

/-- The Latch's state, as a person would write it. -/
structure Latch where
  isOpen : Bool
  waiters : List Nat
  pending : List Nat
  scheduled : Bool
  deriving Modeled, Repr

/-- rc.112 `closeUnsafe`. -/
def close (s : Latch) : Bool × Latch :=
  if s.isOpen then (true, { s with isOpen := false }) else (false, s)

derive_step close as closeStep
#check @closeStep.eval_eq

/-- The state after a wake: opened for `open`, as it is for `release`. -/
def opened (setOpen : Bool) (s : Latch) : Latch := if setOpen then { s with isOpen := true } else s

/-- rc.112 `open` and `release`, each with `scheduleUnsafe`. -/
def wake (setOpen : Bool) (s : Latch) : (Bool × Bool) × Latch :=
  if s.isOpen then ((false, false), s)
  else if s.waiters.length = 0 then ((true, false), opened setOpen s)
  else if s.scheduled then
    ((true, false), opened setOpen { s with pending := s.pending ++ s.waiters, waiters := [] })
  else ((true, true), opened setOpen { s with pending := s.waiters, scheduled := true, waiters := [] })

derive_step wake as wakeStep
#check @wakeStep.eval_eq
example : wakeStep.normal = true := rfl

-- A control: a list built from nothing refuses, with its subterm. Codex's `Step.nil` lifts it.
def flush (s : Latch) : Latch × List Nat :=
  if s.scheduled then ({ s with pending := [], scheduled := false }, s.pending) else (s, [])

/-- error: derive_step: a construct outside the step fragment: [] -/
#guard_msgs in
derive_step flush as flushStep

-- The certificates rest on no axiom beyond the semantic ceiling.
#print axioms takeStep.eval_eq
#print axioms closeStep.eval_eq
#print axioms wakeStep.eval_eq

end DeriveProbe.Demo
