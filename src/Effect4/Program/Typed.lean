import Effect4.Program.Native

/-!
# Program.Typed — the value typing of the native cut (slice 1, lane 1)

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §2. Packet:
`Test/contracts/program-denotation.contract.md`, ENSURES 1–9. Batteries:
`Test/Program/TypedContract.lean` (the guards and the rows `E4-TYPED-CE-001`,
`E4-TYPED-CE-002`) and `Test/Program/TypedAxiomReport.lean`.

This module says which machine values (`src/Effect4/Machine/Stores.lean` `Val`) inhabit which
types of the program language (`src/Effect4/Program/Eff.lean` `Ty`), and proves three things
about the native route (`src/Effect4/Program/Native.lean`): a term that types
(`src/Effect4/Program/Typing.lean` `termTy`) and evaluates (`evalTerm`) evaluates to a value of
its type; a term that types and carries no `str` literal evaluates; and a request value of a
`sync` row's request type decodes to a store operation (`NativeOp.syncOpOf`). Everything is
first-order and in `Type 0`; the only `String` operation is `BEq String` on a handle target,
which is at the ceiling (`src/Effect4/Program/Config.lean` header records the same fact).

Refusals of the value typing, each a `false` of `Val.hasTy` and not a silent one:

* `TYPED-FB-INT` — `.int` has no inhabitant: `Val.nat` is a `.nat`. `Ty.render` sends both to
  `number`; the printer's identification is not the typing's (`E4-TYPED-CE-002`).
* `TYPED-FB-STRING` — `.string` has no inhabitant: strings are not machine values on the
  native route (`Native.lean:48-55`), so a `str` literal types and does not evaluate
  (`E4-TYPED-CE-001`), which is why totality carries `Term.noStr`.
* `.option`, `.except`, `.causeOf`, `.never` and an unknown handle target have no inhabitant
  in this cut.
* `TYPED-FB-CAUSE` — `Val.exitErr` inhabits every `.exitOf _ _` whatever its cause: the error
  column is not checked in this slice (plan §7).

Two facts of this toolchain shape the spelling. Core v4.33.1 has no `List.Forall₂` and this
tree carries no Mathlib, so `Fits` is its own two-constructor inductive of that shape. And
`Val.hasTy` descends on the value in the exit and list arms and on the type in the union arm,
so its recursion is well-founded, not structural: a closed instance is settled by
`simp [Val.hasTy]` or by a `#guard`, never by `decide` or `rfl`.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## Values against types -/

/-- Which values inhabit which types of the native cut (plan §2.1, ENSURES 1). One arm per
`(Val, Ty)` pair the cut can produce: the scalars (`Stores.lean:150-153`); the four handle
kinds against their spellings, `Val.cell` against `NativeOp.refTy` and `Val.promise` against
`NativeOp.deferredTy` (`Native.lean:133-134`), `Val.scopeHandle` against `Ty.scope` and
`Val.context` against `Ty.context` (`Eff.lean:144-147`); the fiber handle and the snapshot
(`Stores.lean:155-158`); the reified exits (`:167-170`); the two-cell list `Val.tuple` builds
(`Native.lean:34-36`) against `.prod`; the list cells (`Stores.lean:171-176`) against `.list`;
and a union as the disjunction of its members. The last arm is every refusal named in the
module header. -/
def Val.hasTy : Val → Ty → Bool
  | Val.unit, .unit => true
  | Val.nat _, .nat => true
  | Val.bool _, .bool => true
  | Val.cell _, .handle target => target == "Ref.Ref<number>"
  | Val.promise _, .handle target => target == "Deferred.Deferred<number, number>"
  | Val.scopeHandle _, .handle target => target == "Scope.Scope"
  | Val.context _, .handle target => target == "Context.Context<unknown>"
  | Val.fiber _, .fiberOf _ _ => true
  | Val.fibers _, .list (.fiberOf _ _) => true
  | Val.exitOk v, .exitOf a _ => Val.hasTy v a
  | Val.exitErr _, .exitOf _ _ => true
  | Val.exitCons a (Val.exitCons b Val.exitNil), .prod ta tb => Val.hasTy a ta && Val.hasTy b tb
  | Val.exitNil, .list _ => true
  | Val.exitCons h t, .list ty => Val.hasTy h ty && Val.hasTy t (.list ty)
  | v, .union l r => Val.hasTy v l || Val.hasTy v r
  | _, _ => false

/-! ### Inversions

What a value must be, given its type: the shapes `NativeOp.syncOpOf` (`Native.lean:208-232`)
and the atoms (`Native.lean:59-70`) pattern-match on. -/

/-- A `.unit` is `Val.unit`. -/
theorem Val.hasTy_unit_inv {v : Val} (h : Val.hasTy v .unit = true) : v = Val.unit := by
  cases v <;> simp_all [Val.hasTy]

/-- A `.nat` is a `Val.nat`. -/
theorem Val.hasTy_nat_inv {v : Val} (h : Val.hasTy v .nat = true) : ∃ n, v = Val.nat n := by
  cases v <;> simp_all [Val.hasTy]

/-- A `.bool` is a `Val.bool`. -/
theorem Val.hasTy_bool_inv {v : Val} (h : Val.hasTy v .bool = true) : ∃ b, v = Val.bool b := by
  cases v <;> simp_all [Val.hasTy]

/-- A `NativeOp.refTy` is a `Val.cell`: the three other handle spellings differ from
`"Ref.Ref<number>"`, decided on the literals. -/
theorem Val.hasTy_refTy_inv {v : Val} (h : Val.hasTy v NativeOp.refTy = true) :
    ∃ k, v = Val.cell k := by
  cases v <;> simp_all [Val.hasTy, NativeOp.refTy]

/-- A `NativeOp.deferredTy` is a `Val.promise`. -/
theorem Val.hasTy_deferredTy_inv {v : Val} (h : Val.hasTy v NativeOp.deferredTy = true) :
    ∃ k, v = Val.promise k := by
  cases v <;> simp_all [Val.hasTy, NativeOp.deferredTy]

/-- A `.prod a b` is the two-cell list of an `a` and a `b`. -/
theorem Val.hasTy_prod_inv {v : Val} {a b : Ty} (h : Val.hasTy v (.prod a b) = true) :
    ∃ x y, v = Val.exitCons x (Val.exitCons y Val.exitNil) ∧
      Val.hasTy x a = true ∧ Val.hasTy y b = true := by
  cases v <;> try (simp [Val.hasTy] at h; done)
  rename_i x t
  cases t <;> try (simp [Val.hasTy] at h; done)
  rename_i y u
  cases u <;> try (simp [Val.hasTy] at h; done)
  simp [Val.hasTy] at h
  exact ⟨x, y, rfl, h.1, h.2⟩

/-! ## Environments -/

/-- A positional environment fits a typing environment: `List.Forall₂` of `hasTy` (plan §2.1,
ENSURES 2), spelled as its own inductive of the same two constructors because core v4.33.1
carries no `List.Forall₂` and this tree carries no Mathlib. -/
inductive Fits : List Val → TyEnv → Prop
  | nil : Fits [] []
  | cons {v : Val} {t : Ty} {env : List Val} {tys : TyEnv} :
      Val.hasTy v t = true → Fits env tys → Fits (v :: env) (t :: tys)

/-- The value at a position has the type at that position (plan §2.2). -/
theorem Fits.get? {env : List Val} {tys : TyEnv} (h : Fits env tys) {i : Nat} {v : Val}
    {t : Ty} (hv : env[i]? = some v) (ht : tys[i]? = some t) : Val.hasTy v t = true := by
  induction h generalizing i with
  | nil => simp at hv
  | cons hvt _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv ht
      subst hv; subst ht; exact hvt
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv ht
      exact ih hv ht

/-- The two environments have one length (plan §2.2). -/
theorem Fits.length {env : List Val} {tys : TyEnv} (h : Fits env tys) :
    env.length = tys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Appending an answer of the answer's type keeps the fit (plan §2.2): D1's convention, every
node passes its scope forward and an answer is appended (`Eff.lean:17-19`). -/
theorem Fits.append {env : List Val} {tys : TyEnv} (h : Fits env tys) {v : Val} {t : Ty}
    (hvt : Val.hasTy v t = true) : Fits (env ++ [v]) (tys ++ [t]) := by
  induction h with
  | nil => exact Fits.cons hvt Fits.nil
  | cons hx _ ih => exact Fits.cons hx ih

/-- A fit against one type is one value of that type. -/
theorem Fits.singleton_inv {vs : List Val} {t : Ty} (h : Fits vs [t]) :
    ∃ v, vs = [v] ∧ Val.hasTy v t = true := by
  cases h with
  | cons hv hrest => cases hrest; exact ⟨_, rfl, hv⟩

/-- A fit against two types is two values of those types. -/
theorem Fits.pair_inv {vs : List Val} {a b : Ty} (h : Fits vs [a, b]) :
    ∃ x y, vs = [x, y] ∧ Val.hasTy x a = true ∧ Val.hasTy y b = true := by
  cases h with
  | cons hx hrest =>
    cases hrest with
    | cons hy hrest' => cases hrest'; exact ⟨_, _, rfl, hx, hy⟩

/-! ## Literals -/

mutual
  /-- No `str` literal anywhere in a term: the one literal `Lit.toVal` refuses
  (`Native.lean:51-55`; plan §2.1, ENSURES 3). -/
  def Term.noStr : Term → Bool
    | .var _ => true
    | .lit (.str _) => false
    | .lit _ => true
    | .app _ args => Terms.noStr args
  /-- `Term.noStr` over every term of the list. -/
  def Terms.noStr : Terms → Bool
    | .nil => true
    | .cons head tail => Term.noStr head && Terms.noStr tail
end

/-- A literal's value has the literal's type (`Native.lean:51-55` against `Eff.lean:203-207`;
plan §2.2, ENSURES 4). -/
theorem Lit.toVal_hasTy (l : Lit) (v : Val) (h : l.toVal = some v) : Val.hasTy v l.ty = true := by
  cases l with
  | unit => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]
  | nat n => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]
  | bool b => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]
  | str s => simp [Lit.toVal] at h

/-- Every literal but `str` evaluates (`Native.lean:55` is the one `none`; ENSURES 4). -/
theorem Lit.toVal_isSome (l : Lit) (h : ∀ s, l ≠ .str s) : l.toVal.isSome = true := by
  cases l with
  | str s => exact absurd rfl (h s)
  | _ => rfl

/-! ## Atoms -/

/-- A typed atom application answers a value of the answer type (`nativeAtomTy`,
`Native.lean:73-84`, against `nativeAtom`, `:59-70`; plan §2.2, ENSURES 5). `pair` answers
`Val.tuple [a, b]`, the `.prod` shape of `hasTy`; `fst` and `snd` read that shape back. -/
theorem nativeAtom_typed (atom : String) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : nativeAtomTy atom tys = some ty) (hfit : Fits vs tys) :
    ∃ v, nativeAtom atom vs = some v ∧ Val.hasTy v ty = true := by
  unfold nativeAtomTy at hty
  split at hty
  · -- succ
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- pred
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- isZero
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- not
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨b, rfl⟩ := Val.hasTy_bool_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- add
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- lt
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- eq
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- pair
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    exact ⟨_, rfl, by simp [Val.tuple, Val.hasTy, hx, hy]⟩
  · -- fst
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    exact ⟨x, rfl, hx⟩
  · -- snd
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨x, y, rfl, _, hy⟩ := Val.hasTy_prod_inv hv
    exact ⟨y, rfl, hy⟩
  · -- the refusal
    simp at hty

/-! ## Terms -/

/-- `termTy` on an application is the atom's type at the arguments' types
(`Typing.lean:63-65`), as an `Option.bind`. -/
theorem termTy_app (tys : TyEnv) (atom : String) (args : Terms) :
    termTy nativeSignature tys (.app atom args) =
      (termsTy nativeSignature tys args).bind (nativeAtomTy atom) := rfl

/-- `termsTy` on a cons (`Typing.lean:68-71`), as nested `Option.bind`s. -/
theorem termsTy_cons (tys : TyEnv) (head : Term) (tail : Terms) :
    termsTy nativeSignature tys (.cons head tail) =
      (termTy nativeSignature tys head).bind fun t =>
        (termsTy nativeSignature tys tail).bind fun rest => some (t :: rest) := rfl

/-- `evalTerm` on an application is the atom at the arguments' values (`Native.lean:91-93`). -/
theorem evalTerm_app (env : List Val) (atom : String) (args : Terms) :
    evalTerm env (.app atom args) = (evalTerms env args).bind (nativeAtom atom) := rfl

/-- `evalTerms` on a cons (`Native.lean:96-99`). -/
theorem evalTerms_cons (env : List Val) (head : Term) (tail : Terms) :
    evalTerms env (.cons head tail) =
      (evalTerm env head).bind fun v =>
        (evalTerms env tail).bind fun rest => some (v :: rest) := rfl

mutual
/-- Under `Fits`, a term that types and evaluates evaluates to a value of its type
(plan §2.2, ENSURES 6): `Fits.get?` at a variable, `Lit.toVal_hasTy` at a literal,
`nativeAtom_typed` at an application, with `nativeSignature.atomOf = nativeAtomTy` by `rfl`. -/
theorem evalTerm_hasTy (t : Term) (env : List Val) (tys : TyEnv) (ty : Ty) (v : Val)
    (hfit : Fits env tys) (hty : termTy nativeSignature tys t = some ty)
    (hev : evalTerm env t = some v) : Val.hasTy v ty = true := by
  cases t with
  | var i => exact hfit.get? hev hty
  | lit l =>
    have hty' : some l.ty = some ty := hty
    cases hty'
    exact Lit.toVal_hasTy l v hev
  | app atom args =>
    rw [termTy_app] at hty
    obtain ⟨tl, hts, hatom⟩ := Option.bind_eq_some_iff.mp hty
    rw [evalTerm_app] at hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨v', hv', hty'⟩ :=
      nativeAtom_typed atom tl ty vs hatom (evalTerms_hasTy args env tys tl vs hfit hts hvs)
    rw [hv'] at hv
    cases hv
    exact hty'
termination_by structural t
/-- The list form of `evalTerm_hasTy`: the values fit the types (ENSURES 6). -/
theorem evalTerms_hasTy (ts : Terms) (env : List Val) (tys : TyEnv) (tl : List Ty)
    (vs : List Val) (hfit : Fits env tys) (hty : termsTy nativeSignature tys ts = some tl)
    (hev : evalTerms env ts = some vs) : Fits vs tl := by
  cases ts with
  | nil =>
    have hty' : some ([] : List Ty) = some tl := hty
    have hev' : some ([] : List Val) = some vs := hev
    cases hty'; cases hev'
    exact Fits.nil
  | cons head tail =>
    rw [termsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp hty'
    cases hcons
    rw [evalTerms_cons] at hev
    obtain ⟨v1, hv1, hev'⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨vrest, hvrest, hvcons⟩ := Option.bind_eq_some_iff.mp hev'
    cases hvcons
    exact Fits.cons (evalTerm_hasTy head env tys t1 v1 hfit ht1 hv1)
      (evalTerms_hasTy tail env tys rest vrest hfit hrest hvrest)
termination_by structural ts
end

mutual
/-- Under `Fits` and `noStr`, a term that types evaluates (plan §2.2, ENSURES 7): the
lengths agree at a variable (`Fits.length`), `Lit.toVal_isSome` at a literal, and
`nativeAtom_typed` at an application over the fitted argument values. -/
theorem evalTerm_isSome (t : Term) (env : List Val) (tys : TyEnv) (ty : Ty)
    (hfit : Fits env tys) (hty : termTy nativeSignature tys t = some ty)
    (hns : Term.noStr t = true) : (evalTerm env t).isSome = true := by
  cases t with
  | var i =>
    have hty' : tys[i]? = some ty := hty
    have hlt : i < env.length := hfit.length ▸ (List.getElem?_eq_some_iff.mp hty').1
    show (env[i]?).isSome = true
    cases hv : env[i]? with
    | none => exact absurd hlt (Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hv))
    | some _ => rfl
  | lit l =>
    show l.toVal.isSome = true
    apply Lit.toVal_isSome
    intro s hs
    subst hs
    simp [Term.noStr] at hns
  | app atom args =>
    rw [termTy_app] at hty
    obtain ⟨tl, hts, hatom⟩ := Option.bind_eq_some_iff.mp hty
    have hns' : Terms.noStr args = true := hns
    obtain ⟨vs, hvs⟩ :=
      Option.isSome_iff_exists.mp (evalTerms_isSome args env tys tl hfit hts hns')
    obtain ⟨v', hv', _⟩ :=
      nativeAtom_typed atom tl ty vs hatom (evalTerms_hasTy args env tys tl vs hfit hts hvs)
    rw [evalTerm_app, hvs]
    show (nativeAtom atom vs).isSome = true
    rw [hv']
    rfl
termination_by structural t
/-- The list form of `evalTerm_isSome` (ENSURES 7). -/
theorem evalTerms_isSome (ts : Terms) (env : List Val) (tys : TyEnv) (tl : List Ty)
    (hfit : Fits env tys) (hty : termsTy nativeSignature tys ts = some tl)
    (hns : Terms.noStr ts = true) : (evalTerms env ts).isSome = true := by
  cases ts with
  | nil => rfl
  | cons head tail =>
    rw [termsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, _⟩ := Option.bind_eq_some_iff.mp hty'
    have hns' : (Term.noStr head && Terms.noStr tail) = true := hns
    obtain ⟨hnsh, hnst⟩ : Term.noStr head = true ∧ Terms.noStr tail = true := by
      simpa using hns'
    obtain ⟨v1, hv1⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome head env tys t1 hfit ht1 hnsh)
    obtain ⟨vrest, hvrest⟩ :=
      Option.isSome_iff_exists.mp (evalTerms_isSome tail env tys rest hfit hrest hnst)
    rw [evalTerms_cons, hv1]
    show ((evalTerms env tail).bind fun rest => some (v1 :: rest)).isSome = true
    rw [hvrest]
    rfl
termination_by structural ts
end

/-! ## Rows -/

/-- A request value of a `sync` row's request type decodes to a store operation
(plan §2.2, ENSURES 8): the twenty rows of `NativeOp.row` (`Native.lean:145-203`) against the
patterns of `NativeOp.syncOpOf` (`:208-232`), each request shape recovered by the inversions
above. -/
theorem syncOpOf_isSome (op : NativeOp) (v : Val)
    (hv : Val.hasTy v (NativeOp.row op).request = true)
    (hk : (NativeOp.row op).kind = .sync) : (NativeOp.syncOpOf op v).isSome = true := by
  cases op with
  | refMake =>
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    rfl
  | refGet =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refSet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    rfl
  | refGetAndSet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    rfl
  | refSetAndGet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    rfl
  | refUpdate f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refGetAndUpdate f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refUpdateAndGet f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refUpdateSome f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refGetAndUpdateSome f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refUpdateSomeAndGet f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refModify f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refModifySome f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | deferredMake =>
    obtain rfl := Val.hasTy_unit_inv hv
    rfl
  | deferredIsDone =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hv
    rfl
  | deferredPoll =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hv
    rfl
  | deferredSucceed =>
    obtain ⟨x, y, rfl, hx, hy⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    rfl
  | deferredFail =>
    obtain ⟨x, y, rfl, hx, hy⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    rfl
  | deferredAwait => simp [NativeOp.row] at hk
  | scopeMake strategy =>
    cases strategy with
    | sequential =>
      obtain rfl := Val.hasTy_unit_inv hv
      rfl
    | parallel =>
      obtain rfl := Val.hasTy_unit_inv hv
      rfl

/-- An `async` row never decodes to a store operation (plan §2.2, ENSURES 9): the one async
row is `deferredAwait` (`Native.lean:195-197`), which `syncOpOf` sends to `none` on every
value (`:232`). -/
theorem syncOpOf_async_none (op : NativeOp) (v : Val) (hk : (NativeOp.row op).kind = .async) :
    NativeOp.syncOpOf op v = none := by
  cases op with
  | deferredAwait => cases v <;> rfl
  | scopeMake strategy => cases strategy <;> simp [NativeOp.row] at hk
  | _ => simp [NativeOp.row] at hk

end Effect4.Program
