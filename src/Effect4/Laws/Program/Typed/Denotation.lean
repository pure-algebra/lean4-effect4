import Effect4.Laws.Program.Typed.Seq
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Decision
import Effect4.Laws.Program.Admit

/-!
# Laws.Program.Typed.Denotation — M5's fundamental property (decisions rows 148, 170, 175)

`DenotesTyped` (`Typed/Assembly.lean`): for a program whose layer references are well formed, a
checked point denotes, at the node its path names, a program typed at the point's certificate,
at every world whose service table is the source's. This module proves it arm by arm over
`denoteR`'s equations (`DenoteR.lean`, `denoteR_zero` … `denoteR_provideService`), each arm a
`TypedProg` derivation built from the checker's inversion (`Typing/CheckInversion.lean`) and
the rows' pres and posts as `Typed/Residual.lean` states them, and assembles them by induction on
the point's fuel.

The tools, in order:

* **The node and its checked children.** A point's node is checked through the expansion's
  rounds (`PointTyped`, row 153 (b)); the rounds commute with every constructor
  (`Eff.expandIn_bind`, …), so the checker's inversion at a node gives each child's verdict at
  the child's path, and the child point is typed (`pointTyped_child`).
* **Terms.** A term the checker types evaluates, in an environment typed at the world, to a
  value that fits its type (`evalTerm_progress`): `evalTerm_fits`'s soundness with progress at
  the world's allocation table, which the coarse `evalTerm_isSome` (at the empty table) cannot
  give for an environment holding an external handle.
* **Sequencing.** `seq_typed` (`Typed/Seq.lean`) and its general form `guardBind_typed`; widening
  along the checker's order (`typedProg_widen`).

Every arm's lemma takes the typings of the children it denotes as hypotheses, so the arms are
independent of the induction's form.
-/

set_option autoImplicit false

namespace Effect4.Program

/-! ## The expansion's rounds commute with the constructors

`Eff.expandIn root e` runs `root`'s rounds on the subterm `e` (`ReferenceTyping.lean`); one round
is a fold, so it commutes with every constructor by `rfl`, and the rounds commute by induction
over their list, as `Eff.expandIn_acquireRelease` does. -/

section Rounds

variable (orig : Node NativeOp)

private abbrev rounds (xs : List Nat) (e : NativeEff) : NativeEff :=
  xs.foldl (fun acc _ => Eff.expandRound orig acc) e

private theorem rounds_one : ∀ (C : NativeEff → NativeEff),
    (∀ a, Eff.expandRound orig (C a) = C (Eff.expandRound orig a)) →
    ∀ (xs : List Nat) (a : NativeEff), rounds orig xs (C a) = C (rounds orig xs a)
  | _, _, [], _ => rfl
  | C, hC, _ :: xs, a => by
    show rounds orig xs (Eff.expandRound orig (C a)) = C (rounds orig xs (Eff.expandRound orig a))
    rw [hC]
    exact rounds_one C hC xs _

private theorem rounds_two : ∀ (C : NativeEff → NativeEff → NativeEff),
    (∀ a b, Eff.expandRound orig (C a b) = C (Eff.expandRound orig a) (Eff.expandRound orig b)) →
    ∀ (xs : List Nat) (a b : NativeEff),
      rounds orig xs (C a b) = C (rounds orig xs a) (rounds orig xs b)
  | _, _, [], _, _ => rfl
  | C, hC, _ :: xs, a, b => by
    show rounds orig xs (Eff.expandRound orig (C a b)) =
      C (rounds orig xs (Eff.expandRound orig a)) (rounds orig xs (Eff.expandRound orig b))
    rw [hC]
    exact rounds_two C hC xs _ _

private theorem rounds_three : ∀ (C : NativeEff → NativeEff → NativeEff → NativeEff),
    (∀ a b c, Eff.expandRound orig (C a b c) =
      C (Eff.expandRound orig a) (Eff.expandRound orig b) (Eff.expandRound orig c)) →
    ∀ (xs : List Nat) (a b c : NativeEff),
      rounds orig xs (C a b c) = C (rounds orig xs a) (rounds orig xs b) (rounds orig xs c)
  | _, _, [], _, _, _ => rfl
  | C, hC, _ :: xs, a, b, c => by
    show rounds orig xs (Eff.expandRound orig (C a b c)) =
      C (rounds orig xs (Eff.expandRound orig a)) (rounds orig xs (Eff.expandRound orig b))
        (rounds orig xs (Eff.expandRound orig c))
    rw [hC]
    exact rounds_three C hC xs _ _ _

private theorem rounds_fix : ∀ (e : NativeEff), Eff.expandRound orig e = e →
    ∀ (xs : List Nat), rounds orig xs e = e
  | _, _, [] => rfl
  | e, he, _ :: xs => by
    show rounds orig xs (Eff.expandRound orig e) = e
    rw [he]
    exact rounds_fix e he xs

end Rounds

variable (root : NativeEff)

theorem Eff.expandIn_bind (a b : NativeEff) :
    Eff.expandIn root (.bind a b) = .bind (Eff.expandIn root a) (Eff.expandIn root b) :=
  rounds_two _ Eff.bind (fun _ _ => rfl) _ a b

theorem Eff.expandIn_suspend (b : NativeEff) :
    Eff.expandIn root (.suspend b) = .suspend (Eff.expandIn root b) :=
  rounds_one _ Eff.suspend (fun _ => rfl) _ b

theorem Eff.expandIn_select (s : Term) (d : Decision) (a0 a1 : NativeEff) :
    Eff.expandIn root (.select s d a0 a1) =
      .select s d (Eff.expandIn root a0) (Eff.expandIn root a1) :=
  rounds_two _ (Eff.select s d) (fun _ _ => rfl) _ a0 a1

theorem Eff.expandIn_exit (b : NativeEff) :
    Eff.expandIn root (.exit b) = .exit (Eff.expandIn root b) :=
  rounds_one _ Eff.exit (fun _ => rfl) _ b

theorem Eff.expandIn_catchCause (b h : NativeEff) :
    Eff.expandIn root (.catchCause b h) = .catchCause (Eff.expandIn root b) (Eff.expandIn root h) :=
  rounds_two _ Eff.catchCause (fun _ _ => rfl) _ b h

theorem Eff.expandIn_catchIf (test : Term) (b h : NativeEff) :
    Eff.expandIn root (.catchIf test b h) =
      .catchIf test (Eff.expandIn root b) (Eff.expandIn root h) :=
  rounds_two _ (Eff.catchIf test) (fun _ _ => rfl) _ b h

theorem Eff.expandIn_matchCause (b v c : NativeEff) :
    Eff.expandIn root (.matchCause b v c) =
      .matchCause (Eff.expandIn root b) (Eff.expandIn root v) (Eff.expandIn root c) :=
  rounds_three _ Eff.matchCause (fun _ _ _ => rfl) _ b v c

theorem Eff.expandIn_onExit (b f : NativeEff) :
    Eff.expandIn root (.onExit b f) = .onExit (Eff.expandIn root b) (Eff.expandIn root f) :=
  rounds_two _ Eff.onExit (fun _ _ => rfl) _ b f

theorem Eff.expandIn_uninterruptible (b : NativeEff) :
    Eff.expandIn root (.uninterruptible b) = .uninterruptible (Eff.expandIn root b) :=
  rounds_one _ Eff.uninterruptible (fun _ => rfl) _ b

theorem Eff.expandIn_interruptible (b : NativeEff) :
    Eff.expandIn root (.interruptible b) = .interruptible (Eff.expandIn root b) :=
  rounds_one _ Eff.interruptible (fun _ => rfl) _ b

theorem Eff.expandIn_scoped (b : NativeEff) :
    Eff.expandIn root (.scoped b) = .scoped (Eff.expandIn root b) :=
  rounds_one _ Eff.scoped (fun _ => rfl) _ b

theorem Eff.expandIn_provideService (key : ServiceKey) (value : Term) (b : NativeEff) :
    Eff.expandIn root (.provideService key value b) =
      .provideService key value (Eff.expandIn root b) :=
  rounds_one _ (Eff.provideService key value) (fun _ => rfl) _ b

theorem Eff.expandIn_iterate (cursorTy : Option Ty) (initial test step result : Term)
    (b : NativeEff) :
    Eff.expandIn root (.iterate cursorTy initial test step result b) =
      .iterate cursorTy initial test step result (Eff.expandIn root b) :=
  rounds_one _ (Eff.iterate cursorTy initial test step result) (fun _ => rfl) _ b

theorem Eff.expandIn_fork (b : NativeEff) (options : Supervision.ForkOptions) :
    Eff.expandIn root (.withFiber (.fork b options)) =
      .withFiber (.fork (Eff.expandIn root b) options) :=
  rounds_one _ (fun b => Eff.withFiber (.fork b options)) (fun _ => rfl) _ b

theorem Eff.expandIn_forkIn (b : NativeEff) (options : Supervision.ForkOptions) (scope : Term) :
    Eff.expandIn root (.withFiber (.forkIn b options scope)) =
      .withFiber (.forkIn (Eff.expandIn root b) options scope) :=
  rounds_one _ (fun b => Eff.withFiber (.forkIn b options scope)) (fun _ => rfl) _ b

theorem Eff.expandIn_forkScoped (b : NativeEff) (options : Supervision.ForkOptions) :
    Eff.expandIn root (.withFiber (.forkScoped b options)) =
      .withFiber (.forkScoped (Eff.expandIn root b) options) :=
  rounds_one _ (fun b => Eff.withFiber (.forkScoped b options)) (fun _ => rfl) _ b

/-- A node the rounds leave alone is its own expansion: one round fixes it. -/
theorem Eff.expandIn_of_round (e : NativeEff) (h : Eff.expandRound (Node.eff root) e = e) :
    Eff.expandIn root e = e :=
  rounds_fix _ e h _

end Effect4.Program

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-! ## Environments, nodes and worlds -/

/-- The empty environment is typed at every world (moved here from `Typed/Assembly.lean`, which
imports this module). -/
theorem envTyped_nil (w : World) : EnvTyped w [] [] := by
  refine ⟨rfl, fun i ty v h _ => ?_⟩
  rw [List.getElem?_nil] at h
  cases h

/-- A typed environment extended by a value of the extending type (moved here from
`Typed/Assembly.lean`, which imports this module). -/
theorem envTyped_append {w : World} {env : List Ty} {vals : List Val} {ty : Ty} {v : Val}
    (h : EnvTyped w env vals) (hv : Fits w v ty) : EnvTyped w (env ++ [ty]) (vals ++ [v]) := by
  refine ⟨by simp only [List.length_append, h.1, List.length_singleton], fun i t x ht hx => ?_⟩
  by_cases hi : i < env.length
  · rw [List.getElem?_append_left hi] at ht
    rw [List.getElem?_append_left (h.1 ▸ hi)] at hx
    exact h.2 i t x ht hx
  · have hge : env.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge] at ht
    rw [List.getElem?_append_right (h.1 ▸ hge)] at hx
    rw [← h.1] at hx
    cases hk : i - env.length with
    | zero =>
      rw [hk] at ht hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hx
      subst ht hx
      exact hv
    | succ k =>
      rw [hk] at ht
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at ht
      cases ht

/-- The node at a child's path is the node's child there (`Agreement.Node.at_append`). -/
theorem node_at_child {root : NativeEff} {path : List Nat} {e : NativeEff} {i : Nat}
    {c : Node NativeOp} (hat : Node.at_ (.eff root) path = some (.eff e))
    (hc : (Node.eff e).child i = some c) : Node.at_ (.eff root) (path ++ [i]) = some c := by
  rw [Agreement.Node.at_append, hat]
  exact hc

/-- The world order keeps the service table, so a later world is one `J` ranges over too. -/
theorem serviceTy_leHost {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    (tie : w.serviceTy = root.sig.serviceTy) : w'.serviceTy = root.sig.serviceTy :=
  (le_serviceTy ord.1).trans tie

/-- A completed view typed at a world stays typed at every later one. -/
theorem completed_mono {w w' : World} (ord : w.leHost w') {completed : List (FiberId × ExitV)}
    (h : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) :
    ∀ q ∈ completed, ∃ fty, w'.Γ q.1 = some fty ∧ ExitOk w' fty q.2 := fun q hq => by
  obtain ⟨fty, hfty, hex⟩ := h q hq
  exact ⟨fty, ord.1.2.1 _ _ hfty, strongExit_mono _ _ _ _ ord hex⟩

/-- A checked child: the node's child at index `i`, checked at the child's path in the child's
environment, at a point whose path is the child's and whose view is typed. -/
theorem pointTyped_child {src : ProgramSource} {w : World} {path : List Nat} {e c : NativeEff}
    {i : Nat} {env : List Ty} {q : Point} {ty : EffTy}
    (hat : Node.at_ (.eff src.program) path = some (.eff e))
    (hc : (Node.eff e).child i = some (.eff c)) (hpath : q.path = path ++ [i])
    (hcheck : Checker.check src.signature env (path ++ [i]) (Eff.expandIn src.program c) = .ok ty)
    (henv : EnvTyped w env q.env)
    (hview : ∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2) :
    PointTyped src w q ty :=
  ⟨c, env, hpath ▸ node_at_child hat hc, hpath ▸ hcheck, henv, hview⟩

/-! ## Terms evaluate at a world (progress beside `evalTerm_fits`)

`evalTerm_fits` (`Typed/Admission.lean`) is soundness: a typed term that evaluates evaluates to a
member of its type. The denotation also needs progress: every `none` branch of a term's
evaluation in `denoteR` is the wrong-shape exit, which no exit type admits. The coarse
`evalTerm_isSome` (`Laws/Program/Typed.lean`) reads `Val.hasTy` at the empty allocation table,
where no external handle has a type, so it cannot see an environment holding one; progress is
proved here at membership, atom by atom, through the allocation-general lemmas where the coarse
tree has them (`projectProduct_typed`, `queryTag_typed`, `queryError_typed`, read at the world's
table through `fits_hasTy`). -/

theorem FitsAll.getElem? {w : World} {vs : List Val} {tys : List Ty} (h : FitsAll w vs tys) :
    ∀ {i : Nat} {t : Ty}, tys[i]? = some t → ∃ v, vs[i]? = some v ∧ Fits w v t := by
  induction h with
  | nil => intro i t ht; cases ht
  | cons hv _ ih =>
    intro i t ht
    cases i with
    | zero =>
      cases ht
      exact ⟨_, rfl, hv⟩
    | succ i => exact ih ht

private theorem progress_of_mono {a : NativeAtom} {params : List Ty} {answer : Ty}
    (hs : (NativeAtom.spec a).scheme = .mono params answer)
    (hev : ∀ (w : World) (vs : List Val), FitsAll w vs params →
      (NativeAtom.eval a vs).isSome = true) (w : World) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : a.typeOf tys = some ty) (hfit : FitsAll w vs tys) :
    (NativeAtom.eval a vs).isSome = true := by
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply, NativeAtom.monoApply] at hty
  split at hty
  · next hguard => exact hev w vs (hfit.sub hguard.1 hguard.2)
  · exact nomatch hty

private theorem progress_of_poly {a : NativeAtom} {params : List Ty} {answer : Ty} {join : Bool}
    (hs : (NativeAtom.spec a).scheme = .poly params answer join)
    (hvv : ∀ p ∈ params, Ty.valueVars p = true)
    (hev : ∀ (w : World) (σ : Ty.Subst) (vs : List Val),
      FitsAll w vs (params.map (Ty.instantiate σ)) → (NativeAtom.eval a vs).isSome = true)
    (w : World) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : a.typeOf tys = some ty) (hfit : FitsAll w vs tys) :
    (NativeAtom.eval a vs).isSome = true := by
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply] at hty
  obtain ⟨σ, hmatch, _⟩ := Option.map_eq_some_iff.mp hty
  exact hev w σ vs (FitsAll.instantiate hvv hmatch hfit)

private theorem progress_of_shape {a : NativeAtom} (shape : NativeAtom.Shape)
    (hs : (NativeAtom.spec a).scheme = .mono shape.params shape.answer)
    (hev : shape.holds a) (w : World) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : a.typeOf tys = some ty) (hfit : FitsAll w vs tys) :
    (NativeAtom.eval a vs).isSome = true := by
  refine progress_of_mono hs ?_ w tys ty vs hty hfit
  intro w vs hfit
  cases shape with
  | nat1 | natTest =>
    obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
    obtain ⟨m, rfl⟩ := fits_nat_inv hx
    obtain ⟨_, he⟩ := hev m
    rw [he]
    rfl
  | bool1 =>
    obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
    obtain ⟨b, rfl⟩ := fits_bool_inv hx
    obtain ⟨_, he⟩ := hev b
    rw [he]
    rfl
  | nat2 | natRel =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := fits_nat_inv hx
    obtain ⟨k, rfl⟩ := fits_nat_inv hy
    obtain ⟨_, he⟩ := hev m k
    rw [he]
    rfl
  | bool2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨p, rfl⟩ := fits_bool_inv hx
    obtain ⟨q, rfl⟩ := fits_bool_inv hy
    obtain ⟨_, he⟩ := hev p q
    rw [he]
    rfl
  | strTest =>
    obtain ⟨x, y, rfl, hx, _⟩ := hfit.pair_inv
    obtain ⟨t, rfl⟩ := fits_string_inv hx
    obtain ⟨_, he⟩ := hev t y
    rw [he]
    rfl
  | str2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨s, rfl⟩ := fits_string_inv hx
    obtain ⟨t, rfl⟩ := fits_string_inv hy
    obtain ⟨_, he⟩ := hev s t
    rw [he]
    rfl

/-- A list value's elements, read back: what the list atoms evaluate on. -/
private theorem asList_of_fits {w : World} {v : Val} {a : Ty} (h : Fits w v (.list a)) :
    ∃ xs, Val.asList? v = some xs := by
  obtain ⟨xs, hxs, _⟩ := (fits_list_iff w v a).mp h
  exact ⟨xs, hxs⟩

/-- **Atom progress at a world** (proved): at argument types an atom accepts, values that fit
them at a world make the atom answer. With `atomFits` (`Membership.lean`) the answer fits. -/
theorem atom_progress (a : NativeAtom) (w : World) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : a.typeOf tys = some ty) (hfit : FitsAll w vs tys) :
    (NativeAtom.eval a vs).isSome = true := by
  cases a with
  | succ => exact progress_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | pred => exact progress_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | isZero => exact progress_of_shape .natTest rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | boolNot => exact progress_of_shape .bool1 rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | add => exact progress_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | lt => exact progress_of_shape .natRel rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | boolOr => exact progress_of_shape .bool2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | boolAnd => exact progress_of_shape .bool2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | tagIs => exact progress_of_shape .strTest rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | mul => exact progress_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | natSub => exact progress_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | natDiv => exact progress_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | natMod => exact progress_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | strConcat => exact progress_of_shape .str2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | strings =>
    simp only [NativeAtom.typeOf, NativeAtom.spec, NativeAtom.Scheme.apply] at hty
    split at hty
    · next hall =>
      have hstr : ∀ v ∈ vs, ∃ s, v = Val.str s :=
        fun v hv => fits_string_inv (hfit.all_sub hall v hv)
      show (stringsAtom vs).isSome = true
      rw [stringsAtom, if_pos]
      · rfl
      · rw [List.all_eq_true]
        intro v hv
        obtain ⟨s, rfl⟩ := hstr v hv
        rfl
    · exact nomatch hty
  | eq =>
    simp only [NativeAtom.typeOf, NativeAtom.spec, NativeAtom.Scheme.apply] at hty
    obtain ⟨params, answer, hmem, heq⟩ := NativeAtom.findSome?_monoApply hty
    simp only [NativeAtom.monoApply] at heq
    split at heq
    · next hguard =>
      have hp := hfit.sub hguard.1 hguard.2
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hmem
      · obtain ⟨x, y, rfl, hx, hy⟩ := hp.pair_inv
        obtain ⟨m, rfl⟩ := fits_nat_inv hx
        obtain ⟨n, rfl⟩ := fits_nat_inv hy
        rfl
      · obtain ⟨x, y, rfl, hx, hy⟩ := hp.pair_inv
        obtain ⟨s, rfl⟩ := fits_string_inv hx
        obtain ⟨t, rfl⟩ := fits_string_inv hy
        rfl
    · exact nomatch heq
  | pair =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨u, v, rfl, _, _⟩ := hfit.pair_inv
    rfl
  | fst | snd =>
    simp only [NativeAtom.typeOf, NativeAtom.spec, NativeAtom.Scheme.apply,
      NativeAtom.CustomScheme.apply, NativeAtom.projectRule] at hty
    split at hty
    · obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
      obtain ⟨r, he, _⟩ := NativeAtom.projectProduct_typed _ _ _ v _ hty (fits_hasTy w _ v hv)
      exact Option.isSome_iff_exists.mpr ⟨r, he⟩
    all_goals exact nomatch hty
  | causeIsFail | causeIsDie | causeIsInterrupt =>
    simp only [NativeAtom.typeOf, NativeAtom.spec, NativeAtom.Scheme.apply,
      NativeAtom.CustomScheme.apply, NativeAtom.causeTestRule] at hty
    split at hty
    · obtain ⟨error, hdomain, _⟩ := Option.map_eq_some_iff.mp hty
      obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
      obtain ⟨_, he, _⟩ := queryTag_typed _ value _ error _ hdomain (fits_hasTy w _ value hv)
      show (queryTag _ value).isSome = true
      rw [he]
      rfl
    all_goals exact nomatch hty
  | causeError =>
    simp only [NativeAtom.typeOf, NativeAtom.spec, NativeAtom.Scheme.apply,
      NativeAtom.CustomScheme.apply, NativeAtom.causeErrorRule] at hty
    split at hty
    · obtain ⟨error, hdomain, _⟩ := Option.map_eq_some_iff.mp hty
      obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
      obtain ⟨_, he, _⟩ := queryError_typed value _ error _ hdomain (fits_hasTy w _ value hv)
      show (queryError value).isSome = true
      rw [he]
      rfl
    all_goals exact nomatch hty
  | isSome =>
    refine progress_of_mono rfl (fun w vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    rcases fits_option_inv hv with rfl | ⟨u, rfl, _⟩
    · rfl
    · rfl
  | getOrElse =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨u, f, rfl, hu, _⟩ := hfit.pair_inv
    rcases fits_option_inv hu with rfl | ⟨x, rfl, _⟩
    · rfl
    · rfl
  | ite =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨c, t, f, rfl, hc, _, _⟩ := hfit.triple_inv
    obtain ⟨b, rfl⟩ := fits_bool_inv hc
    cases b <;> rfl
  | optSome =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨v, rfl, _⟩ := hfit.singleton_inv
    rfl
  | optNone =>
    refine progress_of_mono rfl (fun w vs hfit => ?_) w tys ty vs hty hfit
    cases hfit.nil_inv
    rfl
  | listNil =>
    refine progress_of_mono rfl (fun w vs hfit => ?_) w tys ty vs hty hfit
    cases hfit.nil_inv
    rfl
  | listCons =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨x, l, rfl, _, hl⟩ := hfit.pair_inv
    obtain ⟨elems, he⟩ := asList_of_fits hl
    simp only [NativeAtom.eval, he, Option.map_some, Option.isSome_some]
  | listGet =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨l, i, rfl, hl, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := fits_nat_inv hi
    obtain ⟨elems, he⟩ := asList_of_fits hl
    simp only [NativeAtom.eval, he, Option.map_some, Option.isSome_some]
  | listLength =>
    refine progress_of_mono rfl (fun w vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨l, rfl, hl⟩ := hfit.singleton_inv
    obtain ⟨elems, he⟩ := asList_of_fits hl
    simp only [NativeAtom.eval, he, Option.map_some, Option.isSome_some]
  | listAppend =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨l, r, rfl, hl, hr⟩ := hfit.pair_inv
    obtain ⟨front, hf⟩ := asList_of_fits hl
    obtain ⟨back, hb⟩ := asList_of_fits hr
    simp only [NativeAtom.eval, hf, hb, Option.bind_some, Option.map_some, Option.isSome_some]

section TermProgress

variable {sig : Signature NativeOp} {w : World} {vals : List Val} {env : List Ty}

mutual
/-- **Term progress at a world** (proved): a term the checker types, over values that fit their
types at a world, evaluates, and its value fits the term's type (`atomFits`). Under any signature
whose atoms are the native table's; the const-generic flag is the signature's own. -/
theorem evalTerm_progress (hatom : sig.atomOf = nativeAtomTy) (hfit : FitsAll w vals env) :
    ∀ (t : Term) (ty : Ty), termTy sig env t = some ty →
      ∃ v, evalTerm vals t = some v ∧ Fits w v ty
  | .var i, ty, hty => hfit.getElem? hty
  | .lit l, ty, hty => by
    have hty' : some (litArgTy false l) = some ty := hty
    cases hty'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Lit.toVal_isSome l)
    exact ⟨v, hv, fits_lit w false l v hv⟩
  | .app atom args, ty, hty => by
    have hty' : (argsTy sig env (sig.constAtom atom) args).bind (sig.atomOf atom) = some ty := hty
    obtain ⟨tl, hts, hatomTy⟩ := Option.bind_eq_some_iff.mp hty'
    rw [hatom] at hatomTy
    obtain ⟨vs, hvs, hfitvs⟩ := evalTerms_progress hatom hfit (sig.constAtom atom) args tl hts
    unfold nativeAtomTy at hatomTy
    obtain ⟨named, hname, hnamedTy⟩ := Option.bind_eq_some_iff.mp hatomTy
    obtain ⟨v, hv⟩ :=
      Option.isSome_iff_exists.mp (atom_progress named w tl ty vs hnamedTy hfitvs)
    refine ⟨v, ?_, atomFits named w tl ty vs v hnamedTy hfitvs hv⟩
    show (evalTerms vals args).bind (nativeAtom atom) = some v
    rw [hvs]
    show (NativeAtom.ofName? atom).bind (fun a => a.eval vs) = some v
    rw [hname]
    exact hv
termination_by t => sizeOf t

/-- The argument list's form. -/
theorem evalTerms_progress (hatom : sig.atomOf = nativeAtomTy) (hfit : FitsAll w vals env) :
    ∀ (const : Bool) (ts : Terms) (tl : List Ty),
      argsTy sig env const ts = some tl → ∃ vs, evalTerms vals ts = some vs ∧ FitsAll w vs tl
  | _, .nil, tl, hty => by
    have hty' : some ([] : List Ty) = some tl := hty
    cases hty'
    exact ⟨[], rfl, .nil⟩
  | const, .cons head tail, tl, hty => by
    rw [argsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp hty'
    cases hcons
    obtain ⟨vrest, hvrest, hfitrest⟩ := evalTerms_progress hatom hfit const tail rest hrest
    have hhead : ∃ v1, evalTerm vals head = some v1 ∧ Fits w v1 t1 := by
      rcases argTy_cases _ _ _ head t1 ht1 with ⟨value, rfl, rfl⟩ | ht1'
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Lit.toVal_isSome value)
        exact ⟨v, hv, fits_lit w const value v hv⟩
      · exact evalTerm_progress hatom hfit head t1 ht1'
    obtain ⟨v1, hv1, hfit1⟩ := hhead
    refine ⟨v1 :: vrest, ?_, .cons hfit1 hfitrest⟩
    show ((evalTerm vals head).bind fun v =>
        (evalTerms vals tail).bind fun rest => some (v :: rest)) = some (v1 :: vrest)
    rw [hv1, Option.bind_some, hvrest, Option.bind_some]
termination_by _ ts => sizeOf ts
end

end TermProgress

/-- Term progress in the environment judgment `PointTyped` reads, under a source's signature. -/
theorem evalTerm_progress_env {src : ProgramSource} {w : World} {env : List Ty}
    {vals : List Val} (henv : EnvTyped w env vals) {t : Term} {ty : Ty}
    (hty : termTy src.signature env t = some ty) :
    ∃ v, evalTerm vals t = some v ∧ Fits w v ty :=
  evalTerm_progress rfl (fitsAll_of_pointwise henv.1 henv.2) t ty hty

/-- An admitted error value is represented: its error image reads back (`valOfErr_errOf_supported`
at the world's allocation table), so it is not the payload-discarding `boom`. -/
theorem valOfErr_errOf_fits {w : World} {e : Ty} {v : Val} (hs : admittedErrTy e = true)
    (hv : Fits w v e) : valOfErr (errOf v) = some v :=
  valOfErr_errOf_supported e v _ hs (fits_hasTy w e v hv)

/-- A defect made from an admitted error value is not a shape defect. -/
theorem shapeFree_die_of_fits {w : World} {e : Ty} {v : Val} (hs : admittedErrTy e = true)
    (hv : Fits w v e) : ShapeFree (Cause.die (Defect.ofError (errOf v)) : CauseV) := by
  have hval := valOfErr_errOf_fits hs hv
  intro r hr
  simp only [Cause.die, List.mem_singleton] at hr
  subst hr
  cases herr : errOf v with
  | boom =>
    rw [herr] at hval
    exact nomatch hval
  | tag n => exact ⟨nofun, nofun⟩
  | tagged t m => exact ⟨nofun, nofun⟩
  | text s => exact ⟨nofun, nofun⟩

/-- **Cause progress at a world** (proved): a cause term the checker types at an error column
evaluates, in a typed environment, to a cause whose typed failures fit the column and which no
shape defect enters. -/
theorem causeOf_progress {src : ProgramSource} {w : World} {env : List Ty} {vals : List Val}
    (henv : EnvTyped w env vals) :
    ∀ (c : CauseTerm) (e : Ty), causeTy src.signature env c = some e →
      ∃ cause, causeOf vals c = some cause ∧ FitsCause w e cause ∧ ShapeFree cause
  | .fail error, e, h => by
    rw [causeTy_fail] at h
    obtain ⟨e', he', hadm⟩ := Option.bind_eq_some_iff.mp h
    split at hadm
    · next hs =>
      cases hadm
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv he'
      refine ⟨Cause.fail (errOf v), by simp only [causeOf, hv, Option.map_some], ?_, ?_⟩
      · intro r hr
        simp only [Cause.fail, List.mem_singleton] at hr
        subst hr
        exact ⟨v, valOfErr_errOf_fits hs hfit, hfit⟩
      · intro r hr
        simp only [Cause.fail, List.mem_singleton] at hr
        subst hr
        trivial
    · exact nomatch hadm
  | .die defect, e, h => by
    rw [causeTy_die] at h
    obtain ⟨d, hd, hadm⟩ := Option.bind_eq_some_iff.mp h
    split at hadm
    · next hs =>
      cases hadm
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hd
      refine ⟨Cause.die (Defect.ofError (errOf v)), by simp only [causeOf, hv, Option.map_some],
        ?_, shapeFree_die_of_fits hs hfit⟩
      intro r hr
      simp only [Cause.die, List.mem_singleton] at hr
      subst hr
      trivial
    · exact nomatch hadm
  | .interrupt none, e, h => by
    have h' : some Ty.never = some e := h
    cases h'
    refine ⟨Cause.interrupt none, rfl, ?_, ?_⟩
    · intro r hr
      simp only [Cause.interrupt, List.mem_singleton] at hr
      subst hr
      trivial
    · intro r hr
      simp only [Cause.interrupt, List.mem_singleton] at hr
      subst hr
      trivial
  | .interrupt (some who), e, h => by
    have h' : ((termTy src.signature env who).bind fun t =>
        if t = .nat then some Ty.never else none) = some e := h
    obtain ⟨t, ht, hnat⟩ := Option.bind_eq_some_iff.mp h'
    split at hnat
    · next htn =>
      cases hnat
      subst htn
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv ht
      obtain ⟨n, rfl⟩ := fits_nat_inv hfit
      refine ⟨Cause.interrupt (some ⟨n⟩), by simp only [causeOf, hv], ?_, ?_⟩
      · intro r hr
        simp only [Cause.interrupt, List.mem_singleton] at hr
        subst hr
        trivial
      · intro r hr
        simp only [Cause.interrupt, List.mem_singleton] at hr
        subst hr
        trivial
    · exact nomatch hnat
  | .both left right, e, h => by
    have h' : ((causeTy src.signature env left).bind fun l =>
        (causeTy src.signature env right).bind fun r => some (l.join r)) = some e := h
    obtain ⟨l, hl, h''⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨r, hr, hjoin⟩ := Option.bind_eq_some_iff.mp h''
    cases hjoin
    obtain ⟨cl, hcl, hfl, hsl⟩ := causeOf_progress henv left l hl
    obtain ⟨cr, hcr, hfr, hsr⟩ := causeOf_progress henv right r hr
    refine ⟨Cause.combine cl cr, ?_, ?_, ?_⟩
    · simp only [causeOf, hcl, hcr]
      rfl
    · intro reason hmem
      rcases (Cause.mem_combine reason cl cr).mp hmem with hm | hm
      · exact causeFits_map (fun x hx => fits_join_left w l r x hx) hfl reason hm
      · exact causeFits_map (fun x hx => fits_join_right w l r x hx) hfr reason hm
    · intro reason hmem
      rcases (Cause.mem_combine reason cl cr).mp hmem with hm | hm
      · exact hsl reason hm
      · exact hsr reason hm

/-! ## The administrative operations

The counted suspend answers nothing the program reads, the construction answers the completed
view (which the point typing then carries, row 175), and a frontier is never answered: each is a
fiber row whose continuation the post fixes. -/

/-- A checked point's node: the checker's verdict on its expansion in a typed environment, and the
typed completed view. -/
theorem PointTyped.at_node {src : ProgramSource} {w : World} {p : Point} {ty : EffTy}
    {e : NativeEff} (hpt : PointTyped src w p ty)
    (hat : Node.at_ (.eff src.program) p.path = some (.eff e)) :
    ∃ env, Checker.check src.signature env p.path (Eff.expandIn src.program e) = .ok ty ∧
      EnvTyped w env p.env ∧ (∀ q ∈ p.completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) := by
  obtain ⟨e', env, hat', hcheck, henv, hview⟩ := hpt
  rw [hat] at hat'
  cases hat'
  exact ⟨env, hcheck, henv, hview⟩

/-- A live frontier is typed at every type: its post admits no answer (fuel exhaustion is not an
exit, DB-04). -/
theorem pending_typed (root : ProgramSource) (w : World) (ty : EffTy) (reason : PendingReason)
    (q : Point) : TypedProg root w ty (pending reason q) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun _ _ _ post => (post : False).elim)

/-- The counted suspend: its continuation at every later world. -/
theorem suspendR_typed (root : ProgramSource) {w : World} {ty : EffTy} {q : Point}
    {body : RProgram} (h : ∀ w', w.leHost w' → TypedProg root w' ty body) :
    TypedProg root w ty (suspendR q body) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' o _ _ => h w' o)

/-- The construction: its continuation at every later world, at every completed view the post
admits, the view a constructed point carries (`PointTyped`'s fourth conjunct). -/
theorem constructR_typed (root : ProgramSource) {w : World} {ty : EffTy}
    {k : List (FiberId × ExitV) → RProgram}
    (h : ∀ w', w.leHost w' → ∀ completed,
      (∀ q ∈ completed, ∃ fty, w'.Γ q.1 = some fty ∧ ExitOk w' fty q.2) →
        TypedProg root w' ty (k completed)) : TypedProg root w ty (constructR k) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' o ans post => h w' o ans post)

/-! ## Arms: terms and `pure` -/

section TermArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy}

/-- **No fuel**: the frontier at the point. -/
theorem denoteR_zero_typed (e : NativeEff) (hzero : p.fuel = 0) :
    TypedProg root w ty (denoteR root.program e p) := by
  rw [denoteR_zero _ _ _ hzero]
  exact pending_typed root w ty _ p

/-- **`succeed`**: the term's value, which fits the term's type (`evalTerm_progress_env`). -/
theorem succeed_arm {t : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.succeed t)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteR root.program (.succeed t) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨t', hty, rfl⟩ := Checker.inv_succeed _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  rw [denoteR_succeed _ _ hfuel, hv]
  exact .pure (strongExit_success w _ v hfit)

/-- **`fail`**: the failure of the term's value, an admitted error that reads back
(`valOfErr_errOf_fits`). -/
theorem fail_arm {t : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.fail t)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteR root.program (.fail t) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨e, hty, hadm, rfl⟩ := Checker.inv_fail _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  rw [denoteR_fail _ _ hfuel, hv]
  refine .pure ⟨(fitsExit_failure_iff _ _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
  all_goals
    simp only [Cause.fail, List.mem_singleton] at hr
    subst hr
  · exact ⟨v, valOfErr_errOf_fits hadm hfit, hfit⟩
  · trivial
  · trivial

/-- **`failCause`**: the evaluated cause, whose failures fit the column and which no shape defect
enters (`causeOf_progress`). -/
theorem failCause_arm {c : CauseTerm} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.failCause c)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteR root.program (.failCause c) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨e, hty, rfl⟩ := Checker.inv_failCause _ _ _ _ _ hcheck
  obtain ⟨cause, hc, hfits, hshape⟩ := causeOf_progress henv c e hty
  rw [denoteR_failCause _ _ hfuel, hc]
  exact .pure ⟨(fitsExit_failure_iff _ _ _).mpr ⟨hfits, hshape⟩, hshape⟩

/-- **`sync`**: the counted step answering the term's value, which fits the term's type. -/
theorem sync_arm {t : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.sync t)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteR root.program (.sync t) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨t', hty, rfl⟩ := Checker.inv_sync _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  rw [denoteR_sync _ _ hfuel, hv]
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' o ans post => ?_)
  have hans : ans = v := post
  exact .pure (strongExit_success w' _ ans (by rw [hans]; exact fits_mono o hfit))

/-- **`yieldNow`**: the park answers `unit` (`fiberPost`'s `yieldNow` arm). -/
theorem yieldNow_arm {priority : Nat} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.yieldNow priority)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.yieldNow priority) p) := by
  obtain ⟨env, hcheck, _, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_yieldNow _ _ _ _ _ hcheck
  subst hty
  rw [denoteR_yieldNow _ _ hfuel]
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_)
  have hans : ans = Val.unit := post
  subst hans
  exact .pure (strongExit_success w' _ _ trivial)

end TermArms

/-! ## Arms: `bind`, `select` and the scoped shapes

An arm reads the induction through its children only: a child's denotation is typed at every
world `J` ranges over and every point at the child's path with the arm's remaining fuel
(`ChildDenotes`). The continuations a guard runs are typed at later worlds, so a child is used at
the world its point is built at, with the point's environment and view moved there. -/

/-- The induction, read at one child: at every world `J` ranges over, every point with fuel `f`
at the child's path that the point typing admits denotes a typed program. -/
def ChildDenotes (root : ProgramSource) (f : Nat) (c : NativeEff) (path : List Nat) : Prop :=
  ∀ (w : World), w.serviceTy = root.sig.serviceTy → ∀ (q : Point) (ty : EffTy),
    q.fuel = f → q.path = path → PointTyped root w q ty → TypedProg root w ty (denoteR root.program c q)

/-- A child point's fuel, at a positive budget. -/
theorem child_fuel_eq {p : Point} {f : Nat} (hfuel : p.fuel = f + 1) (i : Nat) :
    (p.child i).fuel = f := by
  rw [Point.child_fuel, hfuel, Nat.add_sub_cancel]

theorem childWith_fuel_eq {p : Point} {f : Nat} (hfuel : p.fuel = f + 1) (i : Nat) (v : Val) :
    (p.childWith i v).fuel = f := by
  rw [Point.childWith_fuel, hfuel, Nat.add_sub_cancel]

section ScopedArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`bind`**: `seq_typed`'s shape (`seqGuard_typed`): the first child at its type, the second at
every later world on every value the first's answer column admits, constructed with the view at
its invocation, widened to the join of the errors. -/
theorem bind_arm {a b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.bind a b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (ha : ChildDenotes root f a (p.path ++ [0])) (hb : ChildDenotes root f b (p.path ++ [1])) :
    TypedProg root w ty (denoteR root.program (.bind a b) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_bind] at hcheck
  obtain ⟨tf, tr, hcf, hcr, rfl⟩ := Checker.inv_bind _ _ _ _ _ _ hcheck
  rw [denoteR_bind _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine seqGuard_typed root (mid := tf)
    (ha w htie (p.child 0) tf (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcf henv hview))
    (Ty.subN_join_left _ _) (fun w' o v hv => ?_)
  refine constructR_typed root (fun w'' o' completed hc => ?_)
  have o'' := leHost_trans _ _ _ o o'
  refine typedProg_widen root (T := tr) (Ty.subN_refl _) (Ty.subN_join_right _ _) ?_
  exact hb w'' (serviceTy_leHost o'' htie) _ tr (childWith_fuel_eq hfuel 1 v) rfl
    (pointTyped_child hat rfl rfl hcr
      (envTyped_append (envTyped_mono o'' henv) (fits_mono o' hv)) hc)

end ScopedArms

/-! ### The value-decided fork (`select`) -/

/-- What a decision's chosen arm binds, at the arm's environment extension: nothing against
nothing, one value fitting one type (`Decision.BoundTyped`'s membership form). -/
def BoundFits (w : World) : Option Val → List Ty → Prop
  | none, [] => True
  | some x, [ty] => Fits w x ty
  | _, _ => False

/-- **A typed scrutinee decides** (proved): the membership form of `Decision.decide_typed`
(`Laws/Program/Decision.lean`). A tag hit's payload fits the payload type (`fits_tagPayload`); a
miss is a member of the residual (`Ty.diffTag`), since a tagged member it fit would make it a hit
(`Ty.hasTy_of_not_tagged`). -/
theorem decide_fits {w : World} {d : Decision} {t : Ty} {e0 e1 : List Ty} {v : Val}
    (harms : d.arms t = some (e0, e1)) (hv : Fits w v t) :
    ∃ first bound, d.decide v = some (first, bound) ∧
      BoundFits w bound (if first then e0 else e1) := by
  cases d with
  | bool =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i ht
      subst ht
      simp only [Option.some.injEq, Prod.mk.injEq] at harms
      obtain ⟨rfl, rfl⟩ := harms
      obtain ⟨b, rfl⟩ := fits_bool_inv hv
      exact ⟨b, none, rfl, by cases b <;> trivial⟩
    · exact nomatch harms
  | option =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i a hnorm
      simp only [Option.some.injEq, Prod.mk.injEq] at harms
      obtain ⟨rfl, rfl⟩ := harms
      have hv' := (fits_normalize w t v).mpr hv
      rw [hnorm] at hv'
      rcases fits_option_inv hv' with rfl | ⟨x, rfl, hx⟩
      · exact ⟨true, none, rfl, trivial⟩
      · exact ⟨false, some x, rfl, hx⟩
    · exact nomatch harms
  | tag name =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i hcol
      cases hP : Ty.payloadTy name t.normalize with
      | none =>
        rw [hP] at harms
        exact nomatch harms
      | some P =>
        rw [hP] at harms
        simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at harms
        obtain ⟨rfl, rfl⟩ := harms
        have hvc : Fits w v t.normalize := (fits_normalize w t v).mpr hv
        cases hp : Val.tagPayload? name v with
        | some payload =>
          exact ⟨true, some payload, by simp only [Decision.decide, hp],
            fits_tagPayload hcol hvc hp hP⟩
        | none =>
          refine ⟨false, some v, by simp only [Decision.decide, hp], ?_⟩
          show Fits w v (Ty.diffTag name t.normalize)
          obtain ⟨m, hm, hvm⟩ := (fits_members w v _).mpr hvc
          unfold Ty.diffTag
          rw [fits_ofMembers]
          refine ⟨m, List.mem_filter.mpr ⟨hm, ?_⟩, hvm⟩
          cases htag : Ty.isTagged name m
          · rfl
          · have hhit := Ty.hasTy_of_not_tagged name m v _ htag (fits_hasTy w m v hvm)
            simp only [NativeAtom.tagHit_eq, hp, Option.isSome_none, Bool.false_eq_true] at hhit
    · exact nomatch harms

theorem childBind_path (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).path = q.path ++ [i] := by
  cases b <;> rfl

theorem childBind_env (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).env = q.env ++ b.toList := by
  cases b with
  | none => exact (List.append_nil _).symm
  | some v => rfl

theorem childBind_completed (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).completed = q.completed := by
  cases b <;> rfl

/-- The environment a decision's chosen arm runs in is typed at the arm's extension. -/
theorem envTyped_bound {w : World} {env : List Ty} {vals : List Val} {extra : List Ty}
    {b : Option Val} (h : EnvTyped w env vals) (hb : BoundFits w b extra) :
    EnvTyped w (env ++ extra) (vals ++ b.toList) := by
  cases b with
  | none =>
    cases extra with
    | nil =>
      simp only [List.append_nil, Option.toList]
      exact h
    | cons _ _ => exact (hb : False).elim
  | some x =>
    cases extra with
    | nil => exact (hb : False).elim
    | cons t rest =>
      cases rest with
      | nil => exact envTyped_append h hb
      | cons _ _ => exact (hb : False).elim

section ScopedArms2

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`suspend`**: the counted step, then the body constructed with the view at its invocation. -/
theorem suspend_arm {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.suspend b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) :
    TypedProg root w ty (denoteR root.program (.suspend b) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_suspend] at hcheck
  have hcb := Checker.inv_suspend _ _ _ _ _ hcheck
  rw [denoteR_suspend _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine suspendR_typed root (fun w' o => constructR_typed root (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  exact hb w'' (serviceTy_leHost o'' htie) _ ty (child_fuel_eq hfuel 0) rfl
    (pointTyped_child hat rfl rfl hcb (envTyped_mono o'' henv) hc)

/-- **`select`**: the counted step, the scrutinee decides (`decide_fits`), and the chosen arm runs
at its point with the value it binds, widened to the join of the arms. -/
theorem select_arm {s : Term} {d : Decision} {a0 a1 : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.select s d a0 a1)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (h0 : ChildDenotes root f a0 (p.path ++ [0])) (h1 : ChildDenotes root f a1 (p.path ++ [1])) :
    TypedProg root w ty (denoteR root.program (.select s d a0 a1) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_select] at hcheck
  obtain ⟨sty, ⟨e0, e1⟩, t0, t1, hsty, harms, hc0, hc1, rfl⟩ :=
    Checker.inv_select _ _ _ _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hsty
  rw [denoteR_select _ _ _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine suspendR_typed root (fun w' o => constructR_typed root (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  have htie'' := serviceTy_leHost o'' htie
  obtain ⟨first, bound, hdec, hbound⟩ := decide_fits harms (fits_mono o'' hfit)
  show TypedProg root w'' _ (match (evalTerm p.env s).bind d.decide with
    | some (true, bound) => denoteR root.program a0 ({ p with completed }.childBind 0 bound)
    | some (false, bound) => denoteR root.program a1 ({ p with completed }.childBind 1 bound)
    | none => .pure badShapeExit)
  rw [hv, Option.bind_some, hdec]
  cases first with
  | true =>
    refine typedProg_widen root (T := t0) (Ty.subN_join_left _ _) (Ty.subN_join_left _ _) ?_
    refine h0 w'' htie'' _ t0 (by rw [Point.childBind_fuel]; rw [hfuel]; rfl)
      (childBind_path _ _ _) ?_
    refine pointTyped_child hat rfl (childBind_path _ _ _) hc0 ?_
      (by rw [childBind_completed]; exact hc)
    rw [childBind_env]
    exact envTyped_bound (envTyped_mono o'' henv) hbound
  | false =>
    refine typedProg_widen root (T := t1) (Ty.subN_join_right _ _) (Ty.subN_join_right _ _) ?_
    refine h1 w'' htie'' _ t1 (by rw [Point.childBind_fuel]; rw [hfuel]; rfl)
      (childBind_path _ _ _) ?_
    refine pointTyped_child hat rfl (childBind_path _ _ _) hc1 ?_
      (by rw [childBind_completed]; exact hc)
    rw [childBind_env]
    exact envTyped_bound (envTyped_mono o'' henv) hbound

end ScopedArms2

/-! ### Handlers, regions, masks and loops -/

/-- A caught cause, bound as a value, fits the handler's `Cause<E>` when its failures fit `E`. -/
theorem fits_exitErr_causeOf {w : World} {e : Ty} {c : CauseV} (h : FitsCause w e c) :
    Fits w (Val.exitErr c) (.causeOf e) := by
  show (match Val.cause? (Val.exitErr c) with
    | some c' => CauseFits (fun x => Fits w x e) c'
    | none => False)
  rw [Val.cause?_exitErr]
  exact h

/-- A member of the context type is a fiber context whose services fit: no handle kind is
spelled with the context target. -/
theorem fits_context_inv {w : World} {v : Val} (h : Fits w v Ty.context) :
    ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services := by
  cases v with
  | handle kind index =>
    have h' : HandleFits w kind index Ty.contextTarget := h
    unfold HandleFits at h'
    split at h'
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact h'.elim
  | _ =>
    obtain ⟨_, ctx, hctx, hsvc, _⟩ := h
    exact ⟨ctx, hctx, hsvc⟩

/-- `never` is below every type in the checker's order. -/
theorem subN_never (t : Ty) : Ty.subN .never t = true := Ty.OrderProof.sub_never _

/-- The context read, typed at the context type. -/
theorem getContext_typed (root : ProgramSource) (w : World) :
    TypedProg root w (EffTy.pure Ty.context) (fiberValR .getContext rfl) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.handle Ty.contextTarget) rfl
    (fun w' _ ans post => .pure (strongExit_success w' _ ans post))

/-- The denotation at a node the fiber action table resolves: `denoteAction` at that action. -/
theorem denoteAction_of (root : NativeEff) (p : Point) {a : NAction}
    (hact : actionAt root p = some a) : denoteAction root p = denoteFiberAction root p a := by
  unfold denoteAction
  rw [hact]

section ScopedArms3

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`catchCause`**: the `onFailure` shape (`catchGuard_typed`): the handler at every failure the
body admits, the caught cause bound at `Cause<E>`, widened to the join of the answers. -/
theorem catchCause_arm {b h : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.catchCause b h)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hh : ChildDenotes root f h (p.path ++ [1])) :
    TypedProg root w ty (denoteR root.program (.catchCause b h) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_catchCause] at hcheck
  obtain ⟨tb, th, hcb, hch, rfl⟩ := Checker.inv_catchCause _ _ _ _ _ _ hcheck
  rw [denoteR_catchCause _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine catchGuard_typed root (mid := tb)
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview))
    (Ty.subN_join_left _ _) (fun w' o c hc => ?_)
  refine constructR_typed root (fun w'' o' completed hcomp => ?_)
  have o'' := leHost_trans _ _ _ o o'
  refine typedProg_widen root (T := th) (Ty.subN_join_right _ _) (Ty.subN_refl _) ?_
  exact hh w'' (serviceTy_leHost o'' htie) _ th (childWith_fuel_eq hfuel 1 (Val.exitErr c)) rfl
    (pointTyped_child hat rfl rfl hch (envTyped_append (envTyped_mono o'' henv)
      (fits_exitErr_causeOf (fitsExit_failure_cause (strongExit_mono _ _ _ _ o' hc).1))) hcomp)

/-- **`matchCause`**: the `all` shape (`allGuard_typed`): the value arm on a success, the cause
arm on a failure, each widened to the join. -/
theorem matchCause_arm {b v c : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.matchCause b v c)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hv : ChildDenotes root f v (p.path ++ [1]))
    (hc : ChildDenotes root f c (p.path ++ [2])) :
    TypedProg root w ty (denoteR root.program (.matchCause b v c) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_matchCause] at hcheck
  obtain ⟨tb, tv, tc, hcb, hcv, hcc, rfl⟩ := Checker.inv_matchCause _ _ _ _ _ _ _ hcheck
  rw [denoteR_matchCause _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine allGuard_typed root (mid := tb) (fun ex => by cases ex <;> rfl)
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview)) (fun w' o ex hex => ?_)
  cases ex with
  | success x =>
    refine constructR_typed root (fun w'' o' completed hcomp => ?_)
    have o'' := leHost_trans _ _ _ o o'
    refine typedProg_widen root (T := tv) (Ty.subN_join_left _ _) (Ty.subN_join_left _ _) ?_
    exact hv w'' (serviceTy_leHost o'' htie) _ tv (childWith_fuel_eq hfuel 1 x) rfl
      (pointTyped_child hat rfl rfl hcv (envTyped_append (envTyped_mono o'' henv)
        (fits_mono o' hex.1)) hcomp)
  | failure cause =>
    refine constructR_typed root (fun w'' o' completed hcomp => ?_)
    have o'' := leHost_trans _ _ _ o o'
    refine typedProg_widen root (T := tc) (Ty.subN_join_right _ _) (Ty.subN_join_right _ _) ?_
    exact hc w'' (serviceTy_leHost o'' htie) _ tc (childWith_fuel_eq hfuel 2 (Val.exitErr cause)) rfl
      (pointTyped_child hat rfl rfl hcc (envTyped_append (envTyped_mono o'' henv)
        (fits_exitErr_causeOf (fitsExit_failure_cause (strongExit_mono _ _ _ _ o' hex).1)))
        hcomp)

/-- **`onExit`**: the region (`onExit_typed`): the body at its type, the finalizer on every exit
the body admits, the exit bound as `Exit<A, E>`. -/
theorem onExit_arm {b fin : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.onExit b fin)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hf : ChildDenotes root f fin (p.path ++ [1])) :
    TypedProg root w ty (denoteR root.program (.onExit b fin) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_onExit] at hcheck
  obtain ⟨tb, tf, hcb, hcf, rfl⟩ := Checker.inv_onExit _ _ _ _ _ _ hcheck
  rw [denoteR_onExit _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine onExit_typed root (b := tb) (f := tf) (Ty.subN_refl _) (Ty.subN_join_left _ _)
    (Ty.subN_join_right _ _)
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview)) (fun w' o ex hex => ?_)
  refine constructR_typed root (fun w'' o' completed hcomp => ?_)
  have o'' := leHost_trans _ _ _ o o'
  exact hf w'' (serviceTy_leHost o'' htie) _ tf (childWith_fuel_eq hfuel 1 (reifyExitVal ex)) rfl
    (pointTyped_child hat rfl rfl hcf (envTyped_append (envTyped_mono o'' henv)
      (fitsExit_mono o' hex.1)) hcomp)

/-- **`scoped`**: the scoped region's row, its body the child at the body's type; the exit it
answers is typed at the body's columns, which the region's type keeps. -/
theorem scoped_arm {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.scoped b)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.scoped b) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_scoped] at hcheck
  obtain ⟨tb, hcb, rfl⟩ := Checker.inv_scoped _ _ _ _ _ hcheck
  rw [denoteR_scoped _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) tb (pointTyped_child hat rfl rfl hcb henv hview)
    (fun _ _ _ post => .pure post)

/-- **`gen`**: the counted step, then the generator entry at the point itself, whose row the
point's typing meets. -/
theorem gen_arm {body : Stmts NativeOp} (hfuel : p.fuel = f + 1)
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.gen body) p) := by
  rw [denoteR_gen _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  exact suspendR_typed root (fun w' o => TypedProg.fiber (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) ty
    (pointTyped_mono o hpt) (fun _ _ _ post => .pure post))

/-- **`iterate`**: the counted step, the initial cursor (`evalTerm_progress_env`), then the loop
entry at the point itself. -/
theorem iterate_arm {cursorTy : Option Ty} {initial test step result : Term} {body : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.iterate cursorTy initial test step result body)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.iterate cursorTy initial test step result body) p) := by
  obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_iterate] at hcheck
  obtain ⟨c0, _, _, _, hc0, _⟩ := Checker.inv_iterate _ _ _ _ _ _ _ _ _ _ hcheck
  obtain ⟨cursor, hcursor, _⟩ := evalTerm_progress_env henv hc0
  rw [denoteR_iterate _ _ _ _ _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), hcursor]
  exact suspendR_typed root (fun w' o => TypedProg.fiber (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) ty
    (pointTyped_mono o hpt) (fun _ _ _ post => .pure post))

/-- **`uninterruptible`**: the mask row over the body at the child, at the body's type. -/
theorem uninterruptible_arm {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.uninterruptible b)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.uninterruptible b) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_uninterruptible] at hcheck
  have hcb := Checker.inv_uninterruptible _ _ _ _ _ hcheck
  have hact : actionAt root.program p =
      some (WithFiberAction.setInterruptible (resolve root.program (p.child 0)) false) := by
    unfold actionAt
    rw [hat]
  rw [denoteR_uninterruptible _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f),
    denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty (BodyTyped.at_ _ _ (pointTyped_child hat rfl rfl hcb henv hview))
    (fun _ _ _ post => .pure post)

/-- **`interruptible`**: as `uninterruptible`, with the flag set. -/
theorem interruptible_arm {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.interruptible b)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.interruptible b) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_interruptible] at hcheck
  have hcb := Checker.inv_interruptible _ _ _ _ _ hcheck
  have hact : actionAt root.program p =
      some (WithFiberAction.setInterruptible (resolve root.program (p.child 0)) true) := by
    unfold actionAt
    rw [hat]
  rw [denoteR_interruptible _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f),
    denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty (BodyTyped.at_ _ _ (pointTyped_child hat rfl rfl hcb henv hview))
    (fun _ _ _ post => .pure post)

/-- **`acquireRelease`**: the context read (`seqGuard_typed`), then the masked acquire at the
point itself (`Body.acquireIn`), whose row is the node's own type. -/
theorem acquireRelease_arm {a r : NativeEff} (hfuel : p.fuel = f + 1)
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.acquireRelease a r) p) := by
  rw [denoteR_acquireRelease _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine seqGuard_typed root (getContext_typed root w) (subN_never _) (fun w' o v hv => ?_)
  obtain ⟨ctx, hctx, _⟩ := fits_context_inv hv
  show TypedProg root w' ty (match Val.context? v with
    | some ctx => .vis (.inr (.mask false (.acquireIn p ctx))) Effects.Program.pure
    | none => .pure badShapeExit)
  rw [hctx]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty (BodyTyped.acquireIn _ _ _ (pointTyped_mono o hpt))
    (fun _ _ _ post => .pure post)

end ScopedArms3

/-! ### The conditional handler (`catchIf`) -/

/-- **A cause with no selected failure has no typed failure** (proved): the first `Fail` of a
cause whose failures are represented is selected, so a cause none is selected from carries only
defects and interruptions and fits every error column (the membership form of
`causeAdmits_of_firstErrorValue_none`, `Laws/Program/Residual.lean`). -/
theorem fitsCause_of_firstErrorValue_none {w : World} {e e' : Ty} {cause : CauseV}
    (hc : FitsCause w e cause) (hnone : firstErrorValue? cause = none) :
    FitsCause w e' cause := by
  intro r hr
  cases r with
  | fail err ann =>
    exfalso
    cases hfirst : firstFailure? cause with
    | none =>
      have hno := List.findSome?_eq_none_iff.mp hfirst (.fail err ann) hr
      exact nomatch hno
    | some error =>
      obtain ⟨reason, hmem, hreason⟩ := List.exists_of_findSome?_eq_some hfirst
      have hfit := hc reason hmem
      cases reason with
      | die _ _ => exact nomatch hreason
      | interrupt _ _ => exact nomatch hreason
      | fail actual annotations =>
        have heq : actual = error := Option.some.inj hreason
        subst heq
        obtain ⟨v, hv, _⟩ := hfit
        have hsel : firstErrorValue? cause = some v := by
          show (firstFailure? cause).bind valOfErr = some v
          rw [hfirst, Option.bind_some, hv]
        rw [hnone] at hsel
        exact nomatch hsel
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- A caught value is the cause's first failure's value. -/
theorem firstErrorValue?_of_caught {env : List Val} {test : Term} {cause : CauseV}
    {value : Val} (h : caughtErrorValue? env test cause = some value) :
    firstErrorValue? cause = some value := by
  unfold caughtErrorValue? at h
  cases hfirst : firstErrorValue? cause with
  | none =>
    rw [hfirst] at h
    exact nomatch h
  | some first =>
    rw [hfirst] at h
    change (if evalTerm (env ++ [first]) test = some (.bool true) then some first else none) =
      some value at h
    split at h
    · cases h
      rfl
    · exact nomatch h

/-- **A missed conditional handler's rethrow fits the error bound** (proved): the membership
form of `catchIf_miss_error_admits` (`Laws/Program/Residual.lean`). A literal `true` test catches
every selected failure; a tag test whose residual is empty catches every one (`Ty.diffTag_sound`);
otherwise the bound keeps the body's column. -/
theorem catchIf_miss_fits {w : World} {env : List Val} {test : Term} {be he : Ty}
    {cause : CauseV} (hc : FitsCause w be cause)
    (hmiss : caughtErrorValue? env test cause = none) :
    FitsCause w (catchIfError test env.length be he) cause := by
  unfold catchIfError
  split
  · rename_i htrue
    subst htrue
    cases hvalue : firstErrorValue? cause with
    | none => exact fitsCause_of_firstErrorValue_none hc hvalue
    | some value =>
      unfold caughtErrorValue? at hmiss
      rw [hvalue] at hmiss
      change (if evalTerm (env ++ [value]) (.lit (.bool true)) = some (.bool true) then some value
        else none) = none at hmiss
      rw [if_pos (show evalTerm (env ++ [value]) (.lit (.bool true)) = some (.bool true) from rfl)]
        at hmiss
      exact nomatch hmiss
  · split
    · rename_i tag htag
      split
      · rename_i hnever
        cases hvalue : firstErrorValue? cause with
        | none => exact fitsCause_of_firstErrorValue_none hc hvalue
        | some value =>
          have hv := fits_firstErrorValue hc hvalue
          rw [tagTest?_sound test env.length tag htag] at hmiss
          unfold caughtErrorValue? at hmiss
          rw [hvalue] at hmiss
          change (if evalTerm (env ++ [value]) (tagTest tag env.length) = some (.bool true)
            then some value else none) = none at hmiss
          rw [evalTerm_tagTest] at hmiss
          have hfalse : NativeAtom.tagHit tag value = false := by
            cases h : NativeAtom.tagHit tag value
            · rfl
            · rw [h, if_pos rfl] at hmiss
              exact nomatch hmiss
          have hbad := Ty.diffTag_sound tag be.normalize value _
            (by rw [hasTy_normalize]; exact fits_hasTy w be value hv)
            (by rw [NativeAtom.eval_tagIs, hfalse])
          rw [hnever] at hbad
          exact nomatch hbad
      · exact causeFits_map (fun x hx => fits_join_left w be he x hx) hc
    · exact causeFits_map (fun x hx => fits_join_left w be he x hx) hc

/-- The handler's error column is below the conditional handler's bound. -/
theorem subN_catchIfError (test : Term) (caught : Nat) (be he : Ty) :
    Ty.subN he (catchIfError test caught be he) = true := by
  unfold catchIfError
  split
  · exact Ty.subN_refl _
  · split
    · split
      · exact Ty.subN_refl _
      · exact Ty.subN_join_right _ _
    · exact Ty.subN_join_right _ _

section CatchIfArm

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`catchIf`**: the `onFailure` shape: on a failure the body admits, the first failure's value
is caught when the test holds (the handler runs with it bound at the body's error column),
otherwise the cause is rethrown, which the conditional bound admits (`catchIf_miss_fits`). -/
theorem catchIf_arm {test : Term} {b h : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.catchIf test b h)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hh : ChildDenotes root f h (p.path ++ [1])) :
    TypedProg root w ty (denoteR root.program (.catchIf test b h) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_catchIf] at hcheck
  obtain ⟨tb, th, hcb, _, hch, rfl⟩ := Checker.inv_catchIf _ _ _ _ _ _ _ hcheck
  rw [denoteR_catchIf _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine catchGuard_typed root (mid := tb)
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview))
    (Ty.subN_join_left _ _) (fun w' o cause hc => ?_)
  refine constructR_typed root (fun w'' o' completed hcomp => ?_)
  have o'' := leHost_trans _ _ _ o o'
  have hc'' := strongExit_mono _ _ _ _ o' hc
  have hcf := fitsExit_failure_cause hc''.1
  show TypedProg root w'' _ (match caughtErrorValue? p.env test cause with
    | some value => denoteR root.program h ({ p with completed }.childWith 1 value)
    | none => .pure (.failure cause))
  cases hcaught : caughtErrorValue? p.env test cause with
  | some value =>
    have hvfit := fits_firstErrorValue hcf (firstErrorValue?_of_caught hcaught)
    refine typedProg_widen root (T := th) (Ty.subN_join_right _ _)
      (subN_catchIfError test env.length tb.error th.error) ?_
    exact hh w'' (serviceTy_leHost o'' htie) _ th (childWith_fuel_eq hfuel 1 value) rfl
      (pointTyped_child hat rfl rfl hch (envTyped_append (envTyped_mono o'' henv) hvfit) hcomp)
  | none =>
    have hlen : env.length = p.env.length := henv.1
    have hmiss := catchIf_miss_fits (he := th.error) hcf hcaught
    rw [← hlen] at hmiss
    exact .pure ⟨(fitsExit_failure_iff _ _ _).mpr ⟨hmiss, hc''.2⟩, hc''.2⟩

end CatchIfArm

end Effect4.Program.Typed
