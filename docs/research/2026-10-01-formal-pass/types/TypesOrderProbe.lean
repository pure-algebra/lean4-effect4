import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Typed.Membership
import Effect4.Program.Typing
import Effect4.Program.Admission

/-!
# Seat TYPES, formal pass (2026-10-01): the order the checker uses, and the one `Fits` reads

Research probe, outside every root; nothing imports it. It reads the tree's own `Ty`, `Ty.sub`,
`Ty.normalize`, `CTy`, `Val.hasTy`, `Typed.Fits`, `initialWorld` and `effTy`.

Question. DI-15 (amended 2026-09-11) says "identity is subtyping-equivalence" and that on
canonical types mutual subtyping is equality. The checker compares types at its subsumption
points after normalizing both sides (`rowTy`, `HasTy.provideService`, `HasTy.iterate`). The
typed state's value judgment `Fits` compares a handle's declared type with the raw `Ty.sub`
(`FiberDeclared`, `RefDeclared`/`Equiv`, `PromiseDeclared`). Are the two orders the same?

§1 (proved). The normalized order `subN a b := sub (normalize a) (normalize b)` is a preorder,
contains the raw order, and its kernel is exactly equality of normal forms: `Ty/≡N` is the
partial order `CTy`, with `normalize` the quotient map and canonical forms its representatives.

§2 (proved, RED CONTROL for "raw mutual subtyping is that equivalence"). The raw order does
not see product distribution: `T := prod (nat | string) unit` is not below its own normal
form, though both normalize to the same canonical type.

§3 (proved, RED CONTROL for "Fits is closed under the checker's order" and for "Fits is
invariant under normalization"). A fiber declared at `T` fits `fiberOf T never` and does not
fit `fiberOf (normalize T) never`; a cell declared at the canonical `normalize T` fits
`refOf (normalize T)` and does not fit `refOf T`. Each pair is one type in the checker's order.

§4 (tested, `#guard`). The checker gives a fork the raw answer `prod (nat | string) unit` (the
`pair` scheme does not normalize, `NativeAtom.lean:21-25`) and accepts an annotated loop whose
cursor annotation is the canonical form of that handle type. The typed state would have to type
the cursor at the annotation, which §3 shows `Fits` refuses.
-/

set_option autoImplicit false

namespace Research.TypesSeat

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed
open Effect4.Machine.Env (Requirement)

/-! ## §1 The normalized order -/

/-- The order the checker compares at: both sides canonical. -/
def subN (a b : Ty) : Bool := Ty.sub a.normalize b.normalize

theorem subN_refl (a : Ty) : subN a a = true := Ty.sub_refl _

theorem subN_trans {a b c : Ty} (hab : subN a b = true) (hbc : subN b c = true) :
    subN a c = true :=
  Ty.sub_trans _ _ _ hab hbc

/-- The raw order is contained in the normalized one (`sub_normalize_of_sub`, one-way). -/
theorem sub_le_subN {a b : Ty} (h : Ty.sub a b = true) : subN a b = true :=
  Ty.sub_normalize_of_sub a b h

/-- **The kernel of the normalized order is equality of normal forms.** So `Ty` modulo mutual
`subN` is `CTy`, ordered by `sub` (a partial order, `CTy.instIsPartialOrder`), with `join` its
least upper bound (`CTy.instLawfulOrderSup`). -/
theorem subN_equiv_iff (a b : Ty) :
    (subN a b = true ∧ subN b a = true) ↔ a.normalize = b.normalize := by
  constructor
  · rintro ⟨hab, hba⟩
    exact congrArg Subtype.val (Ty.sub_antisymm_canonical (CTy.ofRaw a) (CTy.ofRaw b) hab hba)
  · intro h
    unfold subN
    rw [h]
    exact ⟨Ty.sub_refl _, Ty.sub_refl _⟩

/-- The quotient map: `CTy.ofRaw` identifies exactly the `subN`-equivalent types. -/
theorem ofRaw_eq_iff (a b : Ty) :
    CTy.ofRaw a = CTy.ofRaw b ↔ (subN a b = true ∧ subN b a = true) := by
  rw [subN_equiv_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-! ## §2 Raw mutual subtyping is strictly finer (red control) -/

/-- `nat | string` as the checker builds it (`Ty.join .nat .string` unfolds to this). -/
abbrev u : Ty := Ty.normalize (.union .nat .string)

/-- A product over a union: what `pair(x, undefined)` types at when `x : nat | string`. -/
abbrev T : Ty := .prod u .unit

theorem join_eq_u : Ty.join .nat .string = u := rfl

theorem hasTy_nat_u : Val.hasTy (.nat 0) u = true := by
  rw [hasTy_normalize]
  rfl

theorem hasTy_str_u : Val.hasTy (.str "s") u = true := by
  rw [hasTy_normalize]
  rfl

/-- Nothing narrower than `nat | string` among its own factors: read semantically, through
`hasTy_sub`, so no evaluation of the well-founded `sub` is needed. -/
theorem sub_u_factor_false (x : Ty) (hx : x = .never ∨ x = .nat ∨ x = .string) :
    Ty.sub u x = false := by
  cases h : Ty.sub u x with
  | false => rfl
  | true =>
    exfalso
    have hn := hasTy_sub u x (.nat 0) [] h hasTy_nat_u
    have hs := hasTy_sub u x (.str "s") [] h hasTy_str_u
    rcases hx with rfl | rfl | rfl
    · exact absurd hn (by decide)
    · exact absurd hs (by decide)
    · exact absurd hn (by decide)

/-- A factor of a type is `never` or one of its members. -/
theorem mem_factors {t x : Ty} (h : x ∈ t.factors) : x = .never ∨ x ∈ t.members := by
  unfold Ty.factors at h
  split at h
  · exact Or.inl (List.mem_singleton.mp h)
  · exact Or.inr h

/-- The factors of `u` are `never`, `nat` or `string`. -/
theorem u_factor {x : Ty} (h : x ∈ u.normalize.factors) :
    x = .never ∨ x = .nat ∨ x = .string := by
  rw [Ty.normalize_idem] at h
  rcases mem_factors h with h | h
  · exact Or.inl h
  · rw [Ty.OrderProof.members_normalize_union] at h
    have hm := ((Ty.mem_normalizeRow x _).mp h).1
    change x ∈ [Ty.nat] ++ [Ty.string] at hm
    rcases List.mem_append.mp hm with h1 | h1
    · exact Or.inr (Or.inl (List.mem_singleton.mp h1))
    · exact Or.inr (Or.inr (List.mem_singleton.mp h1))

/-- **Red control.** `T` is not below its own normal form in the raw order, though
`T.normalize = T.normalize.normalize`: raw mutual subtyping is not the identity of `CTy`. -/
theorem T_not_sub_normal : Ty.sub T T.normalize = false := by
  cases h : Ty.sub T T.normalize with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨y, hy, hTy⟩ :=
      (Ty.OrderProof.sub_iff_members Ty.sub_trans T T.normalize).mp h T
        (show T ∈ T.members from List.mem_singleton_self T)
    rw [Ty.OrderProof.members_normalize_prod] at hy
    have hy' := ((Ty.mem_normalizeRow y _).mp hy).1
    unfold Ty.productMembers at hy'
    obtain ⟨x, hx, hy2⟩ := List.mem_flatMap.mp hy'
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy2
    rw [Ty.sub_args_prod] at hTy
    simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hTy
    rw [sub_u_factor_false x (u_factor hx)] at hTy
    exact Bool.noConfusion hTy.1

/-- The two are one type in the checker's order. -/
theorem T_subN_equiv : subN T T.normalize = true ∧ subN T.normalize T = true :=
  (subN_equiv_iff _ _).mpr (Ty.normalize_idem T).symm

/-- And the raw order sees only one direction. -/
theorem normal_sub_T : Ty.sub T.normalize T = true := by
  apply (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mpr
  intro x hx
  refine ⟨T, List.mem_singleton_self T, ?_⟩
  rw [Ty.OrderProof.members_normalize_prod] at hx
  have hx' := ((Ty.mem_normalizeRow x _).mp hx).1
  unfold Ty.productMembers at hx'
  obtain ⟨a, ha, hx2⟩ := List.mem_flatMap.mp hx'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx2
  have hau : Ty.sub a u = true := by
    rcases mem_factors ha with rfl | hm
    · exact Ty.OrderProof.sub_never u
    · rw [Ty.normalize_idem] at hm
      exact Ty.OrderProof.member_sub_self hm
  have hbu : b = .unit := by
    change b ∈ [Ty.unit] at hb
    exact List.mem_singleton.mp hb
  subst hbu
  exact Ty.OrderProof.sub_prod_mono a .unit u .unit hau (Ty.sub_refl _)

/-! ## §3 `Fits` reads the raw order (red controls on the tree's own judgment) -/

/-- The root declared at the raw product: what a fork of `succeed (pair x undefined)` declares. -/
def rt : EffTy := ⟨T, .never, Requirement.empty⟩

def w0 : Typed.World := initialWorld rt

theorem w0_root : w0.Γ Api.root = some rt := by
  simp only [w0, initialWorld, tableInsert, if_pos]

/-- The handle fits its declared (raw) type. -/
theorem fits_fiber_raw : Fits w0 (Val.fiber Api.root) (.fiberOf T .never) :=
  ⟨rt, w0_root, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Red control.** It does not fit the canonical form of the same type, although
`fiberOf T never` and `fiberOf (normalize T) never` are one type in the checker's order. -/
theorem not_fits_fiber_normal : ¬ Fits w0 (Val.fiber Api.root) (.fiberOf T.normalize .never) := by
  intro h
  change FiberDeclared w0 Api.root T.normalize .never at h
  obtain ⟨fty, hΓ, ha, _⟩ := h
  rw [w0_root] at hΓ
  cases hΓ
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub_normal] at ha'
  exact Bool.noConfusion ha'

theorem fiber_types_equiv :
    subN (.fiberOf T .never) (.fiberOf T.normalize .never) = true ∧
      subN (.fiberOf T.normalize .never) (.fiberOf T .never) = true := by
  apply (subN_equiv_iff _ _).mpr
  show Ty.fiberOf T.normalize Ty.never = Ty.fiberOf T.normalize.normalize Ty.never
  rw [Ty.normalize_idem]

/-- A world that declares a cell at the CANONICAL form: the careful implementation. -/
def w1 : Typed.World := { initialWorld rt with Ρ := fun _ => some T.normalize }

theorem fits_cell_normal : Fits w1 (Val.cell ⟨0⟩) (.refOf T.normalize) :=
  ⟨T.normalize, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Red control.** The same cell does not fit the raw spelling of its own declared type:
invariance (`Equiv`) needs the raw order both ways, and §2 refutes one of them. -/
theorem not_fits_cell_raw : ¬ Fits w1 (Val.cell ⟨0⟩) (.refOf T) := by
  intro h
  change RefDeclared w1 ⟨0⟩ T at h
  obtain ⟨t', hΡ, _, hback⟩ := h
  have ht : t' = T.normalize := (Option.some.inj hΡ).symm
  subst ht
  rw [T_not_sub_normal] at hback
  exact Bool.noConfusion hback

theorem cell_types_equiv :
    subN (.refOf T) (.refOf T.normalize) = true ∧ subN (.refOf T.normalize) (.refOf T) = true := by
  apply (subN_equiv_iff _ _).mpr
  show Ty.refOf T.normalize = Ty.refOf T.normalize.normalize
  rw [Ty.normalize_idem]

/-- Contrast: the executable shape check IS invariant (`hasTy_normalize`, coarse at handles). -/
theorem hasTy_invariant (v : Val) (alloc : List String) :
    Val.hasTy v (Ty.refOf T).normalize alloc = Val.hasTy v (.refOf T) alloc :=
  hasTy_normalize _ v alloc

/-! ## §4 The checker reaches it (tested) -/

def forkOpts : Supervision.ForkOptions := ⟨false, false, .inherit⟩

/-- `x := if true then 1 else "x"`; `f := fork(succeed(pair(x, undefined)))`;
`iterate` with the cursor ANNOTATED at the canonical form of `f`'s type, starting from `f`. -/
def prog : NativeEff :=
  .bind (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.str "x"))))
    (.bind (.withFiber (.fork (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))
        forkOpts))
      (.iterate (some (.fiberOf T.normalize .never)) (.var 1) (.lit (.bool false)) (.var 2)
        (.lit .unit) (.succeed (.lit .unit))))

-- the fork body's answer is the RAW product, not its canonical form
#guard effTy (nativeSignature) [u]
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil)))) =
  some ⟨T, .never, Requirement.empty⟩
#guard T.normalize ≠ T
-- the checker accepts the loop (its premise compares the normalized forms)
#guard (effTy (nativeSignature) [] prog).isSome
#guard (effTy (nativeSignature) [] prog).map (·.answer) = some .unit
-- the two orders on the pair the loop rule compares
#guard subN (.fiberOf T .never) (.fiberOf T.normalize .never)
#guard !Ty.sub (.fiberOf T .never) (.fiberOf T.normalize .never)

/-! ## §5 Answer joining normalizes (no annotation needed)

`EffTy.joinAnswer a b = some (Ty.join a b)` and `Ty.join a b = normalize (union a b)`, so every
construct that joins answers (`select`, `catchCause`, `catchIf`, `matchCause`, a race) types its
answer at a canonical form. Even `join a a` is `normalize a`. -/

/-- **Red control.** The fiber fits each arm's answer and does not fit their join. -/
theorem not_fits_join : ¬ Fits w0 (Val.fiber Api.root) (Ty.join (.fiberOf T .never) (.fiberOf T .never)) := by
  rw [Ty.join_self]
  exact not_fits_fiber_normal

/-- `if true then f else f`, with `f` the forked handle of §4. -/
def selectProg : NativeEff :=
  .select (.lit (.bool true)) .bool (.succeed (.var 1)) (.succeed (.var 1))

-- tested: each arm answers the raw handle type, the select answers its canonical form
#guard effTy (nativeSignature) [u, .fiberOf T .never] (.succeed (.var 1)) =
  some ⟨.fiberOf T .never, .never, Requirement.empty⟩
#guard (effTy (nativeSignature) [u, .fiberOf T .never] selectProg).map (·.answer) =
  some (.fiberOf T.normalize .never)

/-! ## §6 The smallest amendment's handle arms (proved)

Compare declarations in the checker's order. The arms then cannot see the spelling of a type,
only its canonical form, and the §3 red controls turn green. (The structural arms, union and
product, are `hasTy_normalize`'s proof with `fits_sub` in place of `hasTy_sub`: reading.) -/

theorem subN_normalize_right (x a : Ty) : subN x a.normalize = subN x a := by
  unfold subN
  rw [Ty.normalize_idem]

theorem subN_normalize_left (a x : Ty) : subN a.normalize x = subN a x := by
  unfold subN
  rw [Ty.normalize_idem]

/-- `FiberDeclared` at the checker's order. -/
def FiberDeclaredN (w : Typed.World) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ subN fty.answer a = true ∧ subN fty.error e = true

/-- `Equiv` at the checker's order. -/
def EquivN (declared t : Ty) : Prop := subN declared t = true ∧ subN t declared = true

theorem fiberDeclaredN_normalize (w : Typed.World) (id : FiberId) (a e : Ty) :
    FiberDeclaredN w id a.normalize e.normalize ↔ FiberDeclaredN w id a e := by
  unfold FiberDeclaredN
  simp only [subN_normalize_right]

theorem equivN_normalize (declared t : Ty) : EquivN declared t.normalize ↔ EquivN declared t := by
  unfold EquivN
  rw [subN_normalize_right, subN_normalize_left]

/-- The raw order transports into the checker's order, so `fits_sub`'s handle cases survive. -/
theorem fiberDeclaredN_sub {w : Typed.World} {id : FiberId} {a b e : Ty}
    (h : FiberDeclaredN w id a e) (hab : Ty.sub a b = true) : FiberDeclaredN w id b e := by
  obtain ⟨fty, hΓ, ha, he⟩ := h
  exact ⟨fty, hΓ, subN_trans ha (sub_le_subN hab), he⟩

/-- **The §3 red control, green under the amendment.** -/
theorem fiberDeclaredN_w0 : FiberDeclaredN w0 Api.root T.normalize .never :=
  ⟨rt, w0_root, (T_subN_equiv).1, subN_refl _⟩

/-! ## §7 M5's premise holds and its conclusion meets the false leaf (no host, no annotation)

`child` is closed and joins inside itself, so its certificate is forced and raw; the root forks
it at the empty environment and returns the handle through a `select`, so the root's type is
the canonical form. The loaded reference code is walked below with the answers the typed
derivation must cover (tested); the leaf it reaches is false at every world that declares the
fork at its certificate (proved). That `TypedState` at load requires a derivation of the root's
code at the root's type is reading (`SavedOk` with an empty stack, `fiberPre`'s `BodyTyped`). -/

/-- `x := if true then 1 else "x"; succeed(pair(x, undefined))`, closed. -/
def child : NativeEff :=
  .bind (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.str "x"))))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))

/-- Fork `child`, then `if true then f else f`. -/
def prog3 : NativeEff :=
  .bind (.withFiber (.fork child forkOpts))
    (.select (.lit (.bool true)) .bool (.succeed (.var 0)) (.succeed (.var 0)))

/-- The root's checked type (the canonical form). -/
def rootTy3 : EffTy := ⟨.fiberOf T.normalize .never, .never, Requirement.empty⟩

-- tested: the child's certificate at the empty environment is the raw product
#guard effTy (nativeSignature) [] child = some ⟨T, .never, Requirement.empty⟩
-- tested: M5's premises hold: the program checks, at the canonical answer, and is closed
#guard Api.typeOf prog3 [] = some rootTy3
#guard rootTy3.answer.closed && rootTy3.error.closed
-- tested: admission accepts it (no host row, no `int`)
#guard (match admitProgram prog3 [] with | .ok _ => true | .error _ => false)

open Effect4.Program.Sched in
/-- The answers a typed derivation must cover: the fork answers fiber 1, a construction `[]`,
a checkpoint `()`, a guard its body's exit (the body stops at `unguard`). -/
def walk : Nat → RProgram → Option ExitV
  | 0, _ => none
  | _ + 1, .pure ex => some ex
  | _ + 1, .vis (.inr (.unguard ex)) _ => some ex
  | n + 1, .vis (.inr .construction) k => walk n (k [])
  | n + 1, .vis (.inr (.suspend _)) k => walk n (k Val.unit)
  | n + 1, .vis (.inr (.fork _ _ _)) k => walk n (k (Val.fiber ⟨1⟩))
  | n + 1, .vis (.inr (.guard_ _)) k =>
    match walk n (k none) with
    | some ex => walk n (k (some ex))
    | none => none
  | _ + 1, _ => none

open Effect4.Program.Sched in
/-- The fork's body point, found the same way. -/
def forkPoint : Nat → RProgram → Option Point
  | 0, _ => none
  | _ + 1, .vis (.inr (.fork (.at_ p) _ _)) _ => some p
  | n + 1, .vis (.inr (.guard_ _)) k => forkPoint n (k none)
  | n + 1, .vis (.inr .construction) k => forkPoint n (k [])
  | n + 1, .vis (.inr (.suspend _)) k => forkPoint n (k Val.unit)
  | _ + 1, _ => none

open Effect4.Program.Sched in
-- tested: the loaded root code (`loadR`'s, `RuntimeR.lean:41-46`) forks `child` at the empty
-- environment, and, answered as above, finishes with the handle itself
#guard (forkPoint 50 (denoteR prog3 prog3 (rootPoint 100))).map (·.env) = some []
open Effect4.Program.Sched in
#guard (forkPoint 50 (denoteR prog3 prog3 (rootPoint 100))).map (·.path) = some [0, 0, 0]
#guard Node.at_ (.eff prog3) [0, 0, 0] = some (.eff child)
open Effect4.Program.Sched in
#guard walk 50 (denoteR prog3 prog3 (rootPoint 100)) = some (.success (Val.fiber ⟨1⟩))

/-- **Red control (proved).** The leaf: at every world declaring the fork at `child`'s
certificate, the handle's successful exit does not fit the root's checked type. -/
theorem prog3_leaf_false (w : Typed.World) (id : FiberId)
    (hΓ : w.Γ id = some ⟨T, .never, Requirement.empty⟩) :
    ¬ FitsExit w rootTy3 (.success (Val.fiber id)) := by
  intro h
  rw [fitsExit_success_iff] at h
  change FiberDeclared w id T.normalize .never at h
  obtain ⟨fty, hΓ', ha, _⟩ := h
  rw [hΓ] at hΓ'
  cases hΓ'
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub_normal] at ha'
  exact Bool.noConfusion ha'

/-- Under the amendment the same leaf holds (the declaration compared in the checker's order). -/
theorem prog3_leaf_amended (w : Typed.World) (id : FiberId)
    (hΓ : w.Γ id = some ⟨T, .never, Requirement.empty⟩) :
    FiberDeclaredN w id T.normalize .never := by
  exact ⟨⟨T, .never, Requirement.empty⟩, hΓ, (T_subN_equiv).1, subN_refl _⟩

end Research.TypesSeat

#print axioms Research.TypesSeat.prog3_leaf_false
#print axioms Research.TypesSeat.prog3_leaf_amended
#print axioms Research.TypesSeat.subN_normalize_right
#print axioms Research.TypesSeat.fiberDeclaredN_normalize
#print axioms Research.TypesSeat.equivN_normalize
#print axioms Research.TypesSeat.fiberDeclaredN_sub
#print axioms Research.TypesSeat.fiberDeclaredN_w0
#print axioms Research.TypesSeat.not_fits_join
#print axioms Research.TypesSeat.subN_trans
#print axioms Research.TypesSeat.sub_le_subN
#print axioms Research.TypesSeat.subN_equiv_iff
#print axioms Research.TypesSeat.ofRaw_eq_iff
#print axioms Research.TypesSeat.sub_u_factor_false
#print axioms Research.TypesSeat.T_not_sub_normal
#print axioms Research.TypesSeat.T_subN_equiv
#print axioms Research.TypesSeat.normal_sub_T
#print axioms Research.TypesSeat.fits_fiber_raw
#print axioms Research.TypesSeat.not_fits_fiber_normal
#print axioms Research.TypesSeat.fiber_types_equiv
#print axioms Research.TypesSeat.fits_cell_normal
#print axioms Research.TypesSeat.not_fits_cell_raw
#print axioms Research.TypesSeat.cell_types_equiv
#print axioms Research.TypesSeat.hasTy_invariant
