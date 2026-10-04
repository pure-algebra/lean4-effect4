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

/-- The rounds on a race's spine (`Effs`), entrant by entrant. -/
private abbrev effsRounds (xs : List Nat) (es : Effs NativeOp) : Effs NativeOp :=
  xs.foldl (fun acc _ => Effs.expandRound orig acc) es

private theorem rounds_raceAll : ∀ (xs : List Nat) (es : Effs NativeOp),
    rounds orig xs (.withFiber (.raceAll es)) = .withFiber (.raceAll (effsRounds orig xs es))
  | [], _ => rfl
  | _ :: xs, es => rounds_raceAll xs (Effs.expandRound orig es)

private theorem effsRounds_nil : ∀ (xs : List Nat), effsRounds orig xs .nil = .nil
  | [] => rfl
  | _ :: xs => effsRounds_nil xs

private theorem effsRounds_cons : ∀ (xs : List Nat) (h : NativeEff) (t : Effs NativeOp),
    effsRounds orig xs (.cons h t) = .cons (rounds orig xs h) (effsRounds orig xs t)
  | [], _, _ => rfl
  | _ :: xs, h, t => effsRounds_cons xs (Eff.expandRound orig h) (Effs.expandRound orig t)

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

/-- A race's expansion is the race of its spine's rounds (private: the spine's rounds are no
definition of the tree; `raceAll_arm` reads them entrant by entrant). -/
private theorem Eff.expandIn_raceAll (es : Effs NativeOp) :
    Eff.expandIn root (.withFiber (.raceAll es)) =
      .withFiber (.raceAll
        (effsRounds (Node.eff root) (List.range ((root.refSites []).length + 1)) es)) :=
  rounds_raceAll _ _ es

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
theorem node_at_child {root : NativeEff} {path : List Nat} {n : Node NativeOp} {i : Nat}
    {c : Node NativeOp} (hat : Node.at_ (.eff root) path = some n)
    (hc : n.child i = some c) : Node.at_ (.eff root) (path ++ [i]) = some c := by
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
  | .record fields names values, ty, hty => by
    obtain ⟨types, ht, hc⟩ := termTy_record_inv hty
    obtain ⟨vs, hvs, hfitvs⟩ := evalTerms_progress hatom hfit true values types ht
    obtain ⟨out, hout, hfitout⟩ := record_build_fits hc hfitvs
    refine ⟨out, ?_, hfitout⟩
    show (evalTerms vals values).bind (Machine.Record.build names) = some out
    rw [hvs, Option.bind_some, hout]
  | .field mode target name, ty, hty => by
    have ht : (termTy sig env target).bind (fun ty => Record.fieldType (mode = .optional) ty name) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨value, he, hfitvalue⟩ := evalTerm_progress hatom hfit target targetType ht
    obtain ⟨out, hout, hfitout⟩ := record_fieldType_fits hc hfitvalue
    refine ⟨out, ?_, hfitout⟩
    show (evalTerm vals target).bind (fun value => Machine.Record.read (mode = .optional) value name) = some out
    rw [he, Option.bind_some, hout]
  | .recordSet target name replacement, ty, hty => by
    have ht : ((termTy sig env target).bind fun targetType =>
      (argTy sig env true replacement).bind fun replacementType =>
      Record.setType targetType name replacementType) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨replacementType, hr, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨value, he, hfitvalue⟩ := evalTerm_progress hatom hfit target targetType ht
    have hnext : ∃ next, evalTerm vals replacement = some next ∧ Fits w next replacementType := by
      rcases argTy_cases _ _ _ replacement replacementType hr with ⟨l, rfl, rfl⟩ | hr
      · obtain ⟨next, hn⟩ := Option.isSome_iff_exists.mp (Lit.toVal_isSome l)
        exact ⟨next, hn, fits_lit w true l next hn⟩
      · exact evalTerm_progress hatom hfit replacement replacementType hr
    obtain ⟨next, hn, hnext⟩ := hnext
    obtain ⟨out, hout, hfitout⟩ := record_setType_fits hc hfitvalue hnext
    refine ⟨out, ?_, hfitout⟩
    show ((evalTerm vals target).bind fun value => (evalTerm vals replacement).bind
      fun next => Machine.Record.set value name next) = some out
    rw [he, Option.bind_some, hn, Option.bind_some, hout]
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
point's typing and its generator node meet. -/
theorem gen_arm {body : Stmts NativeOp} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.gen body)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.gen body) p) := by
  rw [denoteR_gen _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  exact suspendR_typed root (fun w' o => TypedProg.fiber (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) ty
    ⟨pointTyped_mono o hpt, body, hat⟩ (fun _ _ _ post => .pure post))

/-- **`iterate`**: the counted step, the initial cursor (`evalTerm_progress_env`), then the loop
entry at the point itself, its cursor at the loop's checked cursor type (`LoopPointTyped`,
decisions row 190 (b)): the initial term's type is below it (`Checker.inv_iterate`). -/
theorem iterate_arm {cursorTy : Option Ty} {initial test step result : Term} {body : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.iterate cursorTy initial test step result body)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.iterate cursorTy initial test step result body) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  have checked := hcheck
  rw [Eff.expandIn_iterate] at hcheck
  obtain ⟨c0, _, _, _, hc0, _, _, _, _, hsub0, _, _⟩ := Checker.inv_iterate _ _ _ _ _ _ _ _ _ _ hcheck
  obtain ⟨cursor, hcursor, hfit⟩ := evalTerm_progress_env henv hc0
  have pre : LoopPointTyped root w p ty cursor := ⟨cursorTy, initial, test, step, result, body, env,
    c0, hat, checked, henv, hview, hc0, fits_subN w (a := c0) (b := cursorTy.getD c0) hsub0 cursor hfit⟩
  rw [denoteR_iterate _ _ _ _ _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), hcursor]
  exact suspendR_typed root (fun w' o => TypedProg.fiber (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) ty
    (loopPointTyped_mono o pre) (fun _ _ _ post => .pure post))

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
point itself (`Body.acquireIn`), whose row is the node's own type; the body names the node and
the context read, whose services fit (`fits_context_inv`). -/
theorem acquireRelease_arm {a r : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.acquireRelease a r)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.acquireRelease a r) p) := by
  rw [denoteR_acquireRelease _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine seqGuard_typed root (getContext_typed root w) (subN_never _) (fun w' o v hv => ?_)
  obtain ⟨ctx, hctx, hsvc⟩ := fits_context_inv hv
  show TypedProg root w' ty (match Val.context? v with
    | some ctx => .vis (.inr (.mask false (.acquireIn p ctx))) Effects.Program.pure
    | none => .pure badShapeExit)
  rw [hctx]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty (BodyTyped.acquireIn _ _ _ (pointTyped_mono o hpt) ⟨a, r, hat⟩ hsvc)
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

/-! ## Arms: the fiber rows

`awaitFiber` and the sixteen fiber actions (`withFiber`). An action's node is resolved by
`actionAt` (`Program/Compile.lean`), which reads the action's terms at the point; every branch it
refuses is excluded by term progress at the checker's types, since the refusal's pre is `False`
(`fiberPre`). A fiber handle's type is read through `fiberTy_eq_some` (`Typed/Membership.lean`,
row 132), a value at it through `fiber_of_fits`, and a list of fibers as `actionAt` decodes one
(`fibers_of_fits`). The rows whose entries compare in raw `Ty.sub` (`awaitAll`, `awaitAllFailFast`,
`raceAll`; decisions row 137) are met at a raw union of the declared columns, which lies below the
checker's columns in its order (`unionFold_subN`). -/

/-! ### Fiber handles, views and raw unions -/

/-- A member of a fiber handle type is a fiber handle declared below its columns (the `fiberOf`
arm of `Fits`). -/
theorem fiber_of_fits {w : World} {x : Val} {a e : Ty} (h : Fits w x (.fiberOf a e)) :
    ∃ index, x = Value.fiber index ∧ FiberDeclared w ⟨index⟩ a e := by
  simp only [Fits] at h
  split at h
  · rename_i index
    exact ⟨index, rfl, h⟩
  · exact h.elim

/-- A completed exit the view answers to a join (`Point.awaitExit`): the view's entry for the
target. -/
theorem awaitExit_join {p : Point} {id : FiberId} {exit : ExitV}
    (h : p.awaitExit id .joinEffect = some exit) :
    ∃ entry ∈ p.completed, entry.1 = id ∧ exit = entry.2 := by
  unfold Point.awaitExit at h
  obtain ⟨entry, hfind, hmap⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hfind
  simp only [decide_eq_true_eq] at hp
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hp, hmap.symm⟩

/-- A completed exit the view answers to an await by value: the view's entry for the target,
reified. -/
theorem awaitExit_value {p : Point} {id : FiberId} {exit : ExitV}
    (h : p.awaitExit id .awaitValue = some exit) :
    ∃ entry ∈ p.completed, entry.1 = id ∧ exit = .success (reifyExitVal entry.2) := by
  unfold Point.awaitExit at h
  obtain ⟨entry, hfind, hmap⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hfind
  simp only [decide_eq_true_eq] at hp
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hp, hmap.symm⟩

/-- The view's entry for a fiber whose handle fits `(a, e)` fits `(a, e)`: the entry is typed at
the fiber's declared type (`PointTyped`'s view, row 175), which is below the handle's columns. -/
theorem view_exitOk {w : World} {completed : List (FiberId × ExitV)} {index : Nat} {a e : Ty}
    {entry : FiberId × ExitV}
    (hview : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2)
    (hmem : entry ∈ completed) (hid : entry.1 = ⟨index⟩) (hdecl : FiberDeclared w ⟨index⟩ a e)
    (req : Env.Requirement) : ExitOk w ⟨a, e, req⟩ entry.2 := by
  obtain ⟨fty, hΓ, hex⟩ := hview entry hmem
  obtain ⟨fty', hΓ', ha, he⟩ := hdecl
  rw [hid, hΓ'] at hΓ
  cases hΓ
  exact exitOk_widen ha he hex

/-- The checker's order on exit types is the order on their columns. -/
theorem subN_exitOf {a e a' e' : Ty} (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true) :
    Ty.subN (.exitOf a e) (.exitOf a' e') = true := by
  unfold Ty.subN at ha he
  show Ty.sub (.exitOf a.normalize e.normalize) (.exitOf a'.normalize e'.normalize) = true
  rw [Ty.sub_args_exitOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, ha, he]

/-- The checker's order on lists of exits is the order on the exits' columns. -/
theorem subN_listExitOf {a e a' e' : Ty} (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true) :
    Ty.subN (.list (.exitOf a e)) (.list (.exitOf a' e')) = true := by
  have hx := subN_exitOf ha he
  unfold Ty.subN at hx
  show Ty.sub (.list (Ty.exitOf a e).normalize) (.list (Ty.exitOf a' e').normalize) = true
  rw [Ty.sub_args_list]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, hx]

/-- Raw `sub` places each operand below a union of it: a union's members are its operands'
(`Ty.members`), and raw `sub` reads members (`Ty.OrderProof.sub_iff_members`). -/
theorem sub_union_self_left (a b : Ty) : Ty.sub a (.union a b) = true :=
  (Ty.OrderProof.sub_iff_members Ty.sub_trans a _).mpr fun x hx =>
    ⟨x, List.mem_append_left _ hx, Ty.sub_refl x⟩

theorem sub_union_self_right (a b : Ty) : Ty.sub b (.union a b) = true :=
  (Ty.OrderProof.sub_iff_members Ty.sub_trans b _).mpr fun x hx =>
    ⟨x, List.mem_append_right _ hx, Ty.sub_refl x⟩

/-- A raw union is below every bound of its operands in the checker's order
(`Ty.OrderProof.sub_normalize_union_le`). -/
theorem subN_union_le {a b c : Ty} (hac : Ty.subN a c = true) (hbc : Ty.subN b c = true) :
    Ty.subN (.union a b) c = true :=
  Ty.OrderProof.sub_normalize_union_le Ty.sub_trans a b c.normalize hac hbc

/-- Every column of a list is raw-below the raw union of the list's columns. -/
theorem sub_unionFold {α : Type} (f : α → Ty) :
    ∀ (xs : List α) (x : α), x ∈ xs →
      Ty.sub (f x) (xs.foldr (fun y acc => Ty.union (f y) acc) .never) = true
  | [], _, hx => nomatch hx
  | y :: ys, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sub_union_self_left _ _
    · exact Ty.sub_trans _ _ _ (sub_unionFold f ys x hx) (sub_union_self_right _ _)

/-- The raw union of a list's columns is below every bound of the columns in the checker's
order. -/
theorem unionFold_subN {α : Type} (f : α → Ty) (c : Ty) :
    ∀ (xs : List α), (∀ x ∈ xs, Ty.subN (f x) c = true) →
      Ty.subN (xs.foldr (fun y acc => Ty.union (f y) acc) .never) c = true
  | [], _ => subN_never c
  | y :: ys, h => subN_union_le (h y List.mem_cons_self)
      (unionFold_subN f c ys fun x hx => h x (List.mem_cons_of_mem y hx))

/-- **The await-all certificate** (proved): for targets whose handles fit `(a, e)`, the raw unions
of their declared columns meet the rows' raw entries (`fiberPre`'s `awaitAll` and
`awaitAllFailFast` arms) and lie below `(a, e)` in the checker's order. -/
theorem awaitAllCert {w : World} {ids : List FiberId} {a e : Ty}
    (hdecl : ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e)) :
    ∃ A E, (∀ t ∈ ids, ∃ fty, w.Γ t = some fty ∧ fty.answer.sub A = true ∧
        fty.error.sub E = true) ∧ Ty.subN A a = true ∧ Ty.subN E e = true := by
  have hcol : ∀ t ∈ ids, ∃ fty, w.Γ t = some fty ∧ Ty.subN fty.answer a = true ∧
      Ty.subN fty.error e = true := fun t ht => hdecl t ht
  refine ⟨ids.foldr (fun y acc => Ty.union (((w.Γ y).map EffTy.answer).getD .never) acc) .never,
    ids.foldr (fun y acc => Ty.union (((w.Γ y).map EffTy.error).getD .never) acc) .never,
    fun t ht => ?_, unionFold_subN _ _ ids fun t ht => ?_, unionFold_subN _ _ ids fun t ht => ?_⟩
  · obtain ⟨fty, hΓ, -, -⟩ := hcol t ht
    have ha := sub_unionFold (fun y => ((w.Γ y).map EffTy.answer).getD .never) ids t ht
    have he := sub_unionFold (fun y => ((w.Γ y).map EffTy.error).getD .never) ids t ht
    simp only [hΓ, Option.map_some, Option.getD_some] at ha he
    exact ⟨fty, hΓ, ha, he⟩
  · obtain ⟨fty, hΓ, ha, -⟩ := hcol t ht
    simp only [hΓ, Option.map_some, Option.getD_some]
    exact ha
  · obtain ⟨fty, hΓ, -, he⟩ := hcol t ht
    simp only [hΓ, Option.map_some, Option.getD_some]
    exact he

/-- A list of fiber handles read element by element: each handle answers its fiber. -/
theorem mapM_fibers {w : World} {a e : Ty} {g : Val → Option FiberId}
    (hg : ∀ index, g (Value.fiber index) = some ⟨index⟩) :
    ∀ (xs : List Val), (∀ x ∈ xs, Fits w x (.fiberOf a e)) →
      ∃ ids, xs.mapM g = some ids ∧ ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e)
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | x :: xs, h => by
    obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits (h x List.mem_cons_self)
    obtain ⟨ids, hids, hfits⟩ := mapM_fibers hg xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨⟨index⟩ :: ids, ?_, fun id hid => ?_⟩
    · simp only [List.mapM_cons, hg, hids]
      rfl
    · rcases List.mem_cons.mp hid with rfl | hid
      · exact hdecl
      · exact hfits id hid

/-- A list of fiber handles read element by element, at the reader's answer. -/
theorem mapM_fibers_eq {w : World} {a e : Ty} {g : Val → Option FiberId} {xs : List Val}
    {res : Option (List FiberId)} (heq : xs.mapM g = res)
    (hg : ∀ index, g (Value.fiber index) = some ⟨index⟩)
    (hall : ∀ x ∈ xs, Fits w x (.fiberOf a e)) :
    ∃ ids, res = some ids ∧ ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e) := by
  obtain ⟨ids, hids, hfits⟩ := mapM_fibers hg xs hall
  exact ⟨ids, heq.symm.trans hids, hfits⟩

/-- **A value at a list of fiber handles** (proved): a list whose elements fit, or a snapshot whose
handles the handle image reads back, each declared (the two shapes `Fits`' list arm reads,
`fits_list_iff`). `actionAt` decodes a list of fibers by these two shapes (its `handles`,
`Program/Compile.lean`). -/
theorem fibers_of_fits {w : World} {v : Val} {a e : Ty} (h : Fits w v (.list (.fiberOf a e))) :
    (∃ xs, v = .list xs ∧ ∀ x ∈ xs, Fits w x (.fiberOf a e)) ∨
      ∃ hs ids, v = Value.fiberSnapshot hs ∧
        (Store.Image.list Value.fiberHandle).ofVal hs = some ids ∧
          ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp h
  rcases Val.asList?_exact hxs with rfl | rfl
  · exact .inl ⟨xs, rfl, hall⟩
  · obtain ⟨ids, hsnap, hmap⟩ := Option.map_eq_some_iff.mp hxs
    refine .inr ⟨.list xs, ids, rfl, hsnap, fun id hid => hall _ ?_⟩
    rw [← hmap]
    exact List.mem_map_of_mem hid

/-- A row answering `unit` continued by its answer is typed at `pure unit`. -/
theorem unitAnswer_typed (root : ProgramSource) {w : World} {ans : Val} (h : ans = Val.unit) :
    TypedProg root w (EffTy.pure .unit) (.pure (.success ans)) := by
  subst h
  exact .pure (strongExit_success w _ _ trivial)

/-- The ambient scope's read, typed at the scope type (`fiberPost`'s `ambientScope` arm). -/
theorem ambientScope_typed (root : ProgramSource) (w : World) :
    TypedProg root w (EffTy.pure Ty.scope) (fiberValR .ambientScope rfl) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial
    (fun w' _ ans post => .pure (strongExit_success w' _ ans post))

/-- A value at an exit type decodes as an exit (`exitOfVal`, the exit image read back). -/
theorem exitOfVal_of_fits {w : World} {v : Val} {a e : Ty} (h : Fits w v (.exitOf a e)) :
    ∃ ex, exitOfVal v = some ex := by
  simp only [Fits] at h
  split at h
  · rename_i x
    exact ⟨_, exitOfVal_exitOk x⟩
  · rename_i written
    split at h
    · rename_i c hc
      refine ⟨.failure c, ?_⟩
      rw [causeImage.ofVal_exact hc]
      exact exitOfVal_exitErr c
    · exact h.elim
  · exact h.elim

/-- The checked entrants of a race: each entrant's point is typed at its own checked type, raw
below the raw unions of the entrants' columns, which lie below the race's checked columns in
the checker's order. Private: the spine's rounds (`effsRounds`) are no definition of the tree. -/
private theorem raceEntrants_typed {root : ProgramSource} {w : World} {env : List Ty} :
    ∀ (es : Effs NativeOp) (q : Point) (T : EffTy),
      Node.at_ (.eff root.program) q.path = some (.effs es) →
      Checker.checkEffs root.signature env q.path
          (effsRounds (Node.eff root.program)
            (List.range ((root.program.refSites []).length + 1)) es) = .ok T →
      EnvTyped w env q.env →
      (∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2) →
      ∃ A E, (∀ r ∈ entrantPoints es q, ∃ ty, PointTyped root w r ty ∧
          ty.answer.sub A = true ∧ ty.error.sub E = true) ∧
        Ty.subN A T.answer = true ∧ Ty.subN E T.error = true
  | .nil, _, T, _, hc, _, _ => by
    rw [effsRounds_nil] at hc
    have hT := Checker.inv_effs_nil _ _ _ _ hc
    subst hT
    exact ⟨.never, .never, fun r hr => absurd hr List.not_mem_nil, subN_never _, subN_never _⟩
  | .cons h t, q, T, hat, hc, henv, hview => by
    rw [effsRounds_cons] at hc
    obtain ⟨H, R, hch, hct, rfl⟩ := Checker.inv_effs_cons _ _ _ _ _ _ hc
    obtain ⟨A, E, hrest, hA, hE⟩ :=
      raceEntrants_typed t (q.child 1) R (node_at_child hat rfl) hct henv hview
    refine ⟨.union H.answer A, .union H.error E, fun r hr => ?_,
      subN_union_le (Ty.subN_join_left _ _) (Ty.subN_trans hA (Ty.subN_join_right _ _)),
      subN_union_le (Ty.subN_join_left _ _) (Ty.subN_trans hE (Ty.subN_join_right _ _))⟩
    simp only [entrantPoints, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨H, ⟨h, env, node_at_child hat rfl, hch, henv, hview⟩, sub_union_self_left _ _,
        sub_union_self_left _ _⟩
    · obtain ⟨ty, hpt, ha, he⟩ := hrest r hr
      exact ⟨ty, hpt, Ty.sub_trans _ _ _ ha (sub_union_self_right _ _),
        Ty.sub_trans _ _ _ he (sub_union_self_right _ _)⟩

section FiberArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy}

/-- **`awaitFiber`**: the target is a fiber handle (`fiberTy_eq_some`, term progress); a completed
target answers from the view, which is typed at its declared type (row 175); a running one is the
await row, whose post answers at the declared type, below the handle's columns
(`await_fits`; by value, `subN_exitOf`). -/
theorem awaitFiber_arm {t : Term} {mode : Supervision.ObserverMode} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.awaitFiber t mode)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.awaitFiber t mode) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  rw [denoteR_awaitFiber _ _ _ hfuel]
  cases mode with
  | joinEffect =>
    obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_join _ _ _ _ _ hcheck
    rw [fiberTy_eq_some hfib] at hty
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
    obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
    rw [hv]
    show TypedProg root w _ (match p.awaitExit ⟨index⟩ .joinEffect with
      | some exit => .pure exit
      | none => .vis (.inr (.await ⟨index⟩ .joinEffect)) Effects.Program.pure)
    cases hawait : p.awaitExit ⟨index⟩ .joinEffect with
    | some exit =>
      obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_join hawait
      exact .pure (view_exitOk hview hmem hid hdecl _)
    | none =>
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () ?_ (fun w' o ans post => ?_)
      · obtain ⟨fty, hΓ, -, -⟩ := hdecl
        show (w.Γ ⟨index⟩).isSome = true
        rw [hΓ]
        rfl
      · obtain ⟨fty', hΓ', hex⟩ := post
        exact .pure ⟨await_fits hfit o hΓ' hex.1 _, hex.2⟩
  | awaitValue =>
    obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_await _ _ _ _ _ hcheck
    rw [fiberTy_eq_some hfib] at hty
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
    obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
    rw [hv]
    show TypedProg root w _ (match p.awaitExit ⟨index⟩ .awaitValue with
      | some exit => .pure exit
      | none => .vis (.inr (.await ⟨index⟩ .awaitValue)) fun v => .pure (.success v))
    cases hawait : p.awaitExit ⟨index⟩ .awaitValue with
    | some exit =>
      obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_value hawait
      exact .pure (strongExit_success w _ _ (view_exitOk hview hmem hid hdecl .empty).1)
    | none =>
      obtain ⟨fty, hΓ, ha, he⟩ := hdecl
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () ?_ (fun w' o ans post => ?_)
      · show (w.Γ ⟨index⟩).isSome = true
        rw [hΓ]
        rfl
      · obtain ⟨fty', hΓ', hans⟩ := post
        rw [o.1.2.1 _ _ hΓ] at hΓ'
        cases hΓ'
        exact .pure (strongExit_success w' _ _ (fits_subN w' (subN_exitOf ha he) ans hans))

/-- **`fork`**: the body's point is typed at its checked type (the row's pre is the body's
typing); the post's fiber is declared at that type, so its handle fits the fiber type. -/
theorem fork_arm {b : NativeEff} {options : Supervision.ForkOptions}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.fork b options))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_fork] at hcheck
  obtain ⟨q, hcq, rfl⟩ :=
    Checker.inv_action_fork _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  have hact : actionAt root.program p = some (WithFiberAction.fork
      (resolve root.program ((p.child 0).child 0)) options (p.child 0).path) := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  have hbody : PointTyped root w ((p.child 0).child 0) q :=
    ⟨b, env, node_at_child (node_at_child hat rfl) rfl, hcq, henv, hview⟩
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) q (BodyTyped.at_ _ _ hbody) (fun w' _ ans post => ?_)
  obtain ⟨id, rfl, hΓ⟩ := post
  exact .pure (strongExit_success w' _ _ ⟨q, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩)

/-- **`forkIn`**: as `fork`, the scope term a present scope's handle (`fits_scope_inv`). -/
theorem forkIn_arm {b : NativeEff} {options : Supervision.ForkOptions} {scope : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.forkIn b options scope))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_forkIn] at hcheck
  obtain ⟨q, hcq, hscope, rfl⟩ :=
    Checker.inv_action_forkIn _ _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hscope
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv hfit
  have hact : actionAt root.program p = some (WithFiberAction.forkIn
      (resolve root.program ((p.child 0).child 0)) options sc (p.child 0).path) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv]
    rfl
  rw [denoteAction_of _ _ hact]
  have hbody : PointTyped root w ((p.child 0).child 0) q :=
    ⟨b, env, node_at_child (node_at_child hat rfl) rfl, hcq, henv, hview⟩
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) q ⟨hbody, hlive⟩ (fun w' _ ans post => ?_)
  obtain ⟨id, rfl, hΓ⟩ := post
  exact .pure (strongExit_success w' _ _ ⟨q, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩)

/-- **`forkScoped`**: the ambient scope's read (`seqGuard_typed`), then `forkIn` on the handle it
answers, a present scope's (`fits_scope_inv`). -/
theorem forkScoped_arm {b : NativeEff} {options : Supervision.ForkOptions}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.forkScoped b options))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_forkScoped] at hcheck
  obtain ⟨q, hcq, rfl⟩ :=
    Checker.inv_action_forkScoped _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  have hact : actionAt root.program p = some WithFiberAction.ambientScope := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  have hbody : PointTyped root w ((p.child 0).child 0) q :=
    ⟨b, env, node_at_child (node_at_child hat rfl) rfl, hcq, henv, hview⟩
  simp only [denoteFiberAction]
  rw [hat]
  simp only []
  refine seqGuard_typed root (ambientScope_typed root w) (subN_never _) (fun w' o v hv => ?_)
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv hv
  show TypedProg root w' _ (.vis (.inr (.forkIn ((p.child 0).child 0) options sc (p.child 0).path))
    fun v => .pure (.success v))
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) q ⟨pointTyped_mono o hbody, hlive⟩ (fun w'' _ ans post => ?_)
  obtain ⟨id, rfl, hΓ⟩ := post
  exact .pure (strongExit_success w'' _ _ ⟨q, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩)

/-- **`runIn`**: a declared fiber and a present scope (the row's pre), answering `unit`. -/
theorem runIn_arm {target scope : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.runIn target scope))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨handle, pair, hty, hfib, hscope, rfl⟩ :=
    Checker.inv_action_runIn _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  rw [fiberTy_eq_some hfib] at hty
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  obtain ⟨index, rfl, fty, hΓ, -, -⟩ := fiber_of_fits hfit
  obtain ⟨u, hu, hufit⟩ := evalTerm_progress_env henv hscope
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv hufit
  have hact : actionAt root.program p = some (WithFiberAction.runIn ⟨index⟩ sc) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, hu]
    rfl
  rw [denoteAction_of _ _ hact]
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () ⟨?_, hlive⟩ (fun w' _ ans post => unitAnswer_typed root post)
  show (w.Γ ⟨index⟩).isSome = true
  rw [hΓ]
  rfl

/-- **`interrupt`**: the target a fiber handle; the row answers `unit`. -/
theorem interrupt_arm {target : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.interrupt target))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨handle, pair, hty, hfib, rfl⟩ :=
    Checker.inv_action_interrupt _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  rw [fiberTy_eq_some hfib] at hty
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  obtain ⟨index, rfl, fty, hdecl, -⟩ := fiber_of_fits hfit
  have hact : actionAt root.program p = some (WithFiberAction.interrupt ⟨index⟩) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv]
    rfl
  rw [denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () (show (w.Γ ⟨index⟩).isSome = true by rw [hdecl]; rfl)
    (fun w' _ ans post => unitAnswer_typed root post)

/-- **`interruptScoped`**: as `interrupt`. -/
theorem interruptScoped_arm {target : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.interruptScoped target))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨handle, pair, hty, hfib, rfl⟩ :=
    Checker.inv_action_interruptScoped _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  rw [fiberTy_eq_some hfib] at hty
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  obtain ⟨index, rfl, fty, hdecl, -⟩ := fiber_of_fits hfit
  have hact : actionAt root.program p = some (WithFiberAction.interruptScoped ⟨index⟩) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv]
    rfl
  rw [denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () (show (w.Γ ⟨index⟩).isSome = true by rw [hdecl]; rfl)
    (fun w' _ ans post => unitAnswer_typed root post)

/-- Fiber handles that fit are declared. -/
theorem fibersDeclared_of_fits {ids : List FiberId} {a e : Ty}
    (hdecl : ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e)) :
    ∀ t ∈ ids, (w.Γ t).isSome = true := by
  intro t ht
  obtain ⟨fty, hΓ, -, -⟩ : ∃ fty, w.Γ t = some fty ∧ Ty.subN fty.answer a = true ∧
      Ty.subN fty.error e = true := hdecl t ht
  rw [hΓ]
  rfl

/-- **`interruptAll`**: the targets a list of declared fiber handles (`fibers_of_fits`, the row's
pre), the interruptor a number; the row answers `unit`. -/
theorem interruptAll_arm {targets : Term} {who : Option Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.interruptAll targets who))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hc := Checker.inv_withFiber _ _ _ _ _ hcheck
  cases who with
  | none =>
    obtain ⟨inner, pair, hts, hfib, rfl⟩ := Checker.inv_action_interruptAll_self _ _ _ _ _ hc
    rw [fiberTy_eq_some hfib] at hts
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
    obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
        some (WithFiberAction.interruptAll ids none) ∧
          ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
      unfold actionAt
      rw [hat]
      simp only []
      rw [hv, Option.bind_some]
      rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
      · simp only [Val.tuple?, Option.bind_some]
        split
        · next ids heq =>
          obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          cases hids'
          exact ⟨ids, rfl, hfits⟩
        · next heq =>
          obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          exact nomatch hids
      · simp only [hofv]
        exact ⟨ids, rfl, hall⟩
    rw [denoteAction_of _ _ hact]
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () (fibersDeclared_of_fits hdecl)
      (fun w' _ ans post => unitAnswer_typed root post)
  | some who =>
    obtain ⟨inner, pair, hts, hfib, hwho, rfl⟩ := Checker.inv_action_interruptAll_by _ _ _ _ _ _ hc
    rw [fiberTy_eq_some hfib] at hts
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
    obtain ⟨n, hn, hnfit⟩ := evalTerm_progress_env henv hwho
    obtain ⟨m, rfl⟩ := fits_nat_inv hnfit
    obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
        some (WithFiberAction.interruptAll ids (some ⟨m⟩)) ∧
          ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
      unfold actionAt
      rw [hat]
      simp only []
      rw [hv, Option.bind_some, hn]
      rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
      · simp only [Val.tuple?, Option.bind_some]
        split
        · next ids heq =>
          obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          cases hids'
          exact ⟨ids, rfl, hfits⟩
        · next heq =>
          obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          exact nomatch hids
      · simp only [hofv]
        exact ⟨ids, rfl, hall⟩
    rw [denoteAction_of _ _ hact]
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () (fibersDeclared_of_fits hdecl)
      (fun w' _ ans post => unitAnswer_typed root post)

/-- **`awaitAll`**: the targets a list of declared fibers (`fibers_of_fits`); the row is met at the
raw unions of their declared columns (`awaitAllCert`), whose answer is below the checked list of
exits. -/
theorem awaitAll_arm {targets : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.awaitAll targets))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨inner, pair, hts, hfib, rfl⟩ :=
    Checker.inv_action_awaitAll _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  rw [fiberTy_eq_some hfib] at hts
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
  obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
      some (WithFiberAction.awaitAll ids) ∧
        ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some]
    rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
    · simp only [Val.tuple?, Option.bind_some]
      split
      · next ids heq =>
        obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        cases hids'
        exact ⟨ids, rfl, hfits⟩
      · next heq =>
        obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        exact nomatch hids
    · simp only [hofv]
      exact ⟨ids, rfl, hall⟩
  rw [denoteAction_of _ _ hact]
  obtain ⟨A, E, hpre, hA, hE⟩ := awaitAllCert hdecl
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.list (.exitOf A E)) ⟨A, E, rfl, hpre⟩
    (fun w' _ ans post =>
      .pure (strongExit_success w' _ ans (fits_subN w' (subN_listExitOf hA hE) ans post)))

/-- **`awaitAllFailFast`**: as `awaitAll`. -/
theorem awaitAllFailFast_arm {targets : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.awaitAllFailFast targets))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨inner, pair, hts, hfib, rfl⟩ :=
    Checker.inv_action_awaitAllFailFast _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  rw [fiberTy_eq_some hfib] at hts
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
  obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
      some (WithFiberAction.awaitAllFailFast ids) ∧
        ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some]
    rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
    · simp only [Val.tuple?, Option.bind_some]
      split
      · next ids heq =>
        obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        cases hids'
        exact ⟨ids, rfl, hfits⟩
      · next heq =>
        obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        exact nomatch hids
    · simp only [hofv]
      exact ⟨ids, rfl, hall⟩
  rw [denoteAction_of _ _ hact]
  obtain ⟨A, E, hpre, hA, hE⟩ := awaitAllCert hdecl
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.list (.exitOf A E)) ⟨A, E, rfl, hpre⟩
    (fun w' _ ans post =>
      .pure (strongExit_success w' _ ans (fits_subN w' (subN_listExitOf hA hE) ans post)))

/-- **`snapshotChildren`**: the row answers at its certificate, the checked type. -/
theorem snapshotChildren_arm
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber .snapshotChildren)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_action_snapshotChildren _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  subst hty
  have hact : actionAt root.program p = some WithFiberAction.snapshotChildren := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.list (.fiberOf .unknown .unknown)) rfl
    (fun w' _ ans post => .pure (strongExit_success w' _ ans post))

/-- **`awaitNewChildren`**: the snapshot a list of fiber handles (below the snapshot type in raw
`sub`, `fits_sub`); the row answers `unit`. -/
theorem awaitNewChildren_arm {snapshot : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.awaitNewChildren snapshot))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨s, hs, hsub, rfl⟩ :=
    Checker.inv_action_awaitNewChildren _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hs
  have hfit' : Fits w v (.list (.fiberOf .unknown .unknown)) :=
    fits_sub w hsub v ((fits_normalize w s v).mpr hfit)
  obtain ⟨ids, hact⟩ : ∃ ids, actionAt root.program p =
      some (WithFiberAction.awaitNewChildren ids) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some]
    rcases fibers_of_fits hfit' with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, -⟩
    · simp only [Val.tuple?, Option.bind_some]
      split
      · next ids _ => exact ⟨ids, rfl⟩
      · next heq =>
        obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        exact nomatch hids
    · simp only [hofv]
      exact ⟨ids, rfl⟩
  rw [denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => unitAnswer_typed root post)

/-- **`raceAll`**: every entrant's point is typed (the row's pre, `raceEntrants_typed`), at the raw
unions of the entrants' columns; the race's exit fits them, so the checked join. -/
theorem raceAll_arm {es : Effs NativeOp}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.raceAll es))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_raceAll] at hcheck
  have hc := Checker.inv_action_raceAll _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨A, E, hpre, hA, hE⟩ := raceEntrants_typed es ((p.child 0).child 0) ty
    (node_at_child (node_at_child hat rfl) rfl) hc henv hview
  obtain ⟨ents, hact⟩ : ∃ ents, actionAt root.program p =
      some (WithFiberAction.raceAll ents (some ((p.child 0).child 0).path)) := by
    unfold actionAt
    rw [hat]
    exact ⟨_, rfl⟩
  rw [denoteAction_of _ _ hact]
  have hrace : racePoints root.program p = entrantPoints es ((p.child 0).child 0) := by
    unfold racePoints
    rw [hat]
  show TypedProg root w ty (.vis (.inr (.raceAll (racePoints root.program p)
    (some ((p.child 0).child 0).path))) Effects.Program.pure)
  rw [hrace]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ⟨A, E, ty.requires⟩ hpre
    (fun w' _ ans post => .pure (exitOk_widen hA hE post))

/-- **`setContext`**: the context term a context whose services fit (`fits_context_inv`), the
row's pre; it answers `unit`. -/
theorem setContext_arm {context : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.setContext context))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨hc, rfl⟩ :=
    Checker.inv_action_setContext _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hc
  obtain ⟨ctx, hctx, hsvc⟩ := fits_context_inv hfit
  have hact : actionAt root.program p = some (WithFiberAction.setContext ctx) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some, hctx]
  rw [denoteAction_of _ _ hact]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () hsvc (fun w' _ ans post => unitAnswer_typed root post)

/-- **`getContext`**: the context read at the context type (`getContext_typed`). -/
theorem getContext_arm
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber .getContext)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_action_getContext _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  subst hty
  have hact : actionAt root.program p = some WithFiberAction.getContext := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  exact getContext_typed root w

/-- **`getId`**: the fiber's id, a number. -/
theorem getId_arm
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber .getId)))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_action_getId _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  subst hty
  have hact : actionAt root.program p = some WithFiberAction.getId := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_)
  obtain ⟨id, rfl⟩ := post
  exact .pure (strongExit_success w' _ _ trivial)

/-- **`closeScope`**: a present scope and an exit value that decodes (`exitOfVal_of_fits`) and fits
`Exit<unknown, unknown>` (the row's pre, F-CLOSE); the close answers an exit at `pure unit`. -/
theorem closeScope_arm {scope exit : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.closeScope scope exit))))
    (hpt : PointTyped root w p ty) : TypedProg root w ty (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨pair, hs, hex, rfl⟩ :=
    Checker.inv_action_closeScope _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨u, hu, hufit⟩ := evalTerm_progress_env henv hs
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv hufit
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hex
  obtain ⟨ex, hexv⟩ := exitOfVal_of_fits hvfit
  have hact : actionAt root.program p = some (WithFiberAction.closeScope sc ex) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hu, hv, Option.bind_some, hexv]
    rfl
  rw [denoteAction_of _ _ hact]
  -- the closing exit fits `Exit<unknown, unknown>` (F-CLOSE): the value is the exit's image, at
  -- its checked exit type, widened
  have himage : v = reifyExitVal ex := by
    rw [reifyExitVal_eq_exitImage]
    exact exitImage.ofVal_exact hexv
  have hfits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex := by
    show Fits w (reifyExitVal ex) (.exitOf .unknown .unknown)
    rw [← himage]
    refine fits_subN w (subN_exitOf ?_ ?_) v hvfit
    · exact Ty.sub_unknown _
    · exact Ty.sub_unknown _
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () ⟨hlive, hfits⟩ (fun _ _ _ post => .pure post)

/-- **`withFiber`**: the sixteen actions, each by its arm. -/
theorem withFiber_arm {a : ActionTerm NativeOp} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber a)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.withFiber a) p) := by
  rw [denoteR_withFiber _ _ _ hfuel]
  cases a with
  | fork b options => exact fork_arm hat hpt
  | forkIn b options scope => exact forkIn_arm hat hpt
  | forkScoped b options => exact forkScoped_arm hat hpt
  | runIn target scope => exact runIn_arm hat hpt
  | interrupt target => exact interrupt_arm hat hpt
  | interruptScoped target => exact interruptScoped_arm hat hpt
  | interruptAll targets who => exact interruptAll_arm hat hpt
  | awaitAll targets => exact awaitAll_arm hat hpt
  | awaitAllFailFast targets => exact awaitAllFailFast_arm hat hpt
  | snapshotChildren => exact snapshotChildren_arm hat hpt
  | awaitNewChildren snapshot => exact awaitNewChildren_arm hat hpt
  | raceAll es => exact raceAll_arm hat hpt
  | setContext context => exact setContext_arm hat hpt
  | getContext => exact getContext_arm hat hpt
  | getId => exact getId_arm hat hpt
  | closeScope scope exit => exact closeScope_arm hat hpt

end FiberArms

/-! ## Arms: the store rows, the services and `exit`

A `perform` at a built-in row is the row's store operation (`syncRow_typed`), its asynchronous
registration (`deferredAwait`, `sleep`) or, at a host row, the host registration whose certificate
`bitEntry` (`Typed/Residual.lean`) holds raw-above the row's template columns. The checker types
the node at the row's instance at the request (`rowTy`); a template's post has no member at a
parameter, so the continuation is typed at the instance by `fits_instantiate`
(`Typed/Membership.lean`), not because a host answer can meet the template there (decisions
row 183). `service` reads the context's binding at the key's declared carrier (`ServicesFit`, the
world's table tied to the source's); `provideService` sets a context whose new binding fits that
carrier (`fits_flatFits`, a lawful signature's carriers being flat) and restores the previous
one. `exit` reifies its body's exit, an inline exit typed by `inlineYield_typed`. -/

/-! ### Built-in rows -/

/-- A member of the native cell type is a cell declared at a type equivalent to `nat` in the
checker's order (`RefDeclared`: both `subN` directions, not syntactic equality). -/
theorem fits_refTy_inv {w : World} {v : Val} (h : Fits w v NativeOp.refTy) :
    ∃ k, v = Val.cell k ∧ RefDeclared w k .nat := by
  simp only [Fits, NativeOp.refTy] at h
  split at h
  · rename_i kind index
    simp only [HandleFits] at h
    split at h
    · rename_i hk
      have hk_byte : kind = HandleKind.cell.byte := HandleKind.ofByte?_exact hk
      subst hk_byte
      exact ⟨⟨index⟩, rfl, h.2⟩
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact nomatch h
    · exact nomatch h
  · exact absurd h.1 (by decide)

/-- A member of the native deferred type is a deferred declared at columns equivalent to
`(nat, nat)` in the checker's order. -/
theorem fits_deferredTy_inv {w : World} {v : Val} (h : Fits w v NativeOp.deferredTy) :
    ∃ k, v = Val.promise k ∧ PromiseDeclared w k .nat .nat := by
  simp only [Fits, NativeOp.deferredTy] at h
  split at h
  · rename_i kind index
    simp only [HandleFits] at h
    split at h
    · exact absurd h.1 (by decide)
    · rename_i hk
      have hk_byte : kind = HandleKind.promise.byte := HandleKind.ofByte?_exact hk
      subst hk_byte
      exact ⟨⟨index⟩, rfl, h.2⟩
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact nomatch h
    · exact nomatch h
  · exact absurd h.1 (by decide)

/-- A cell's declaration survives compatible world extension (`leHost` extends the reference
table). -/
theorem refDeclared_mono {w w' : World} (ord : w.leHost w') {key : RefKey} {t : Ty}
    (h : RefDeclared w key t) : RefDeclared w' key t := by
  obtain ⟨t', hlookup, hequiv⟩ := h
  exact ⟨t', ord.1.2.2.2.1 _ _ hlookup, hequiv⟩

/-- A deferred's declaration survives compatible world extension. -/
theorem promiseDeclared_mono {w w' : World} (ord : w.leHost w') {key : DeferredKey} {a e : Ty}
    (h : PromiseDeclared w key a e) : PromiseDeclared w' key a e := by
  obtain ⟨a', e', hlookup, ha, he⟩ := h
  exact ⟨a', e', ord.1.2.2.1 _ _ hlookup, ha, he⟩

/-- **Reference read** (the TYPES 2003 card's first step): a reply fitting the cell's declared
type at the reply's world fits `nat` when the cell is declared equivalent to `nat`; the lookup's
equality identifies the reply's declaration, and normalized subtyping transports the reply. -/
theorem refRead_nat {w : World} {key : RefKey} {ty : Ty} {ans : Val}
    (hdecl : RefDeclared w key .nat) (hlookup : w.Ρ key = some ty) (hfit : Fits w ans ty) :
    Fits w ans .nat := by
  obtain ⟨t', hlookup', hequiv⟩ := hdecl
  rw [hlookup] at hlookup'
  cases hlookup'
  exact fits_subN w hequiv.1 ans hfit

/-- **The store rows**: a request fitting a `sync` row's request column decodes to the row's
store operation (`NativeOp.syncOpOf`), whose pre it meets at a certificate the row fixes, and
whose post answers at the row's answer column at every later world. -/
theorem syncRow_typed (root : ProgramSource) {w : World} {req : Env.Requirement}
    (op : NativeOp) (hk : NativeOp.kind op = .sync) (v : Val)
    (hfit : Fits w v (NativeOp.row op).request) :
    ∃ o, NativeOp.syncOpOf op v = some o ∧
      TypedProg root w ⟨(NativeOp.row op).answer, (NativeOp.row op).error, req⟩
        (.vis (.inl o) fun ans => .pure (.success ans)) := by
  cases op with
  | refMake =>
    change Fits w v .nat at hfit
    cases v with
    | nat n =>
      refine ⟨SyncOp.refMake (Val.nat n), rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refMake (Val.nat n)) (cert := .nat) hfit ?_
      intro w' ord ans post
      obtain ⟨key, rfl, hlookup⟩ := post
      refine TypedProg.pure ?_
      refine strongExit_success w' _ (Val.cell key) ?_
      change Fits w' (Val.cell key) NativeOp.refTy
      show HandleFits w' HandleKind.cell.byte key.index NativeOp.refTarget
      change NativeOp.refTarget = NativeOp.refTarget ∧ RefDeclared w' key .nat
      exact ⟨rfl, ⟨.nat, hlookup, ⟨Ty.subN_refl .nat, Ty.subN_refl .nat⟩⟩⟩
    | _ => exact hfit.elim
  | refGet =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refGet k, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refGet k) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refSet =>
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v NativeOp.refTy .nat).mp hfit
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hp
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refSet k q, rfl, ?_⟩
    have hq' : Fits w q t' := fits_subN w hequiv.2 q hq
    refine TypedProg.store (op := SyncOp.refSet k q) (cert := ()) ⟨t', hlookup, hq'⟩ ?_
    intro w' ord ans post
    subst post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.cell k) ?_
    change Fits w' (Val.cell k) NativeOp.refTy
    show HandleFits w' HandleKind.cell.byte k.index NativeOp.refTarget
    change NativeOp.refTarget = NativeOp.refTarget ∧ RefDeclared w' k .nat
    exact ⟨rfl, refDeclared_mono ord ⟨t', hlookup, hequiv⟩⟩
  | refGetAndSet =>
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v NativeOp.refTy .nat).mp hfit
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hp
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refGetAndSet k q, rfl, ?_⟩
    have hq' : Fits w q t' := fits_subN w hequiv.2 q hq
    refine TypedProg.store (op := SyncOp.refGetAndSet k q) (cert := ()) ⟨t', hlookup, hq'⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refSetAndGet =>
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v NativeOp.refTy .nat).mp hfit
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hp
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refSetAndGet k q, rfl, ?_⟩
    have hq' : Fits w q t' := fits_subN w hequiv.2 q hq
    refine TypedProg.store (op := SyncOp.refSetAndGet k q) (cert := ()) ⟨t', hlookup, hq'⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refUpdate f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, _⟩ := hdecl
    refine ⟨SyncOp.refUpdate k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refUpdate k f) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    subst post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ Val.unit trivial
  | refGetAndUpdate f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refGetAndUpdate k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refGetAndUpdate k f) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refUpdateAndGet f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refUpdateAndGet k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refUpdateAndGet k f) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refUpdateSome f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, _⟩ := hdecl
    refine ⟨SyncOp.refUpdateSome k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refUpdateSome k f) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    subst post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ Val.unit trivial
  | refGetAndUpdateSome f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refGetAndUpdateSome k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refGetAndUpdateSome k f) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refUpdateSomeAndGet f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refUpdateSomeAndGet k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refUpdateSomeAndGet k f) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ?_
    exact refRead_nat (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refModify f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    refine ⟨SyncOp.refModify k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refModify k f) (cert := ()) hdecl ?_
    intro w' ord ans post
    obtain ⟨n, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.nat n) trivial
  | refModifySome f =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refTy_inv hfit
    refine ⟨SyncOp.refModifySome k f, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refModifySome k f) (cert := ()) hdecl ?_
    intro w' ord ans post
    obtain ⟨n, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.nat n) trivial
  | deferredMake =>
    have hv : v = Val.unit := fits_unit_inv hfit
    subst hv
    refine ⟨SyncOp.deferredMake, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.deferredMake) (cert := (.nat, .nat)) trivial ?_
    intro w' ord ans post
    obtain ⟨key, rfl, hlookup⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.promise key) ?_
    change Fits w' (Val.promise key) NativeOp.deferredTy
    show HandleFits w' HandleKind.promise.byte key.index NativeOp.deferredTarget
    change NativeOp.deferredTarget = NativeOp.deferredTarget ∧ PromiseDeclared w' key .nat .nat
    exact ⟨rfl, ⟨.nat, .nat, hlookup, ⟨Ty.subN_refl .nat, Ty.subN_refl .nat⟩,
      ⟨Ty.subN_refl .nat, Ty.subN_refl .nat⟩⟩⟩
  | deferredIsDone =>
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredTy_inv hfit
    obtain ⟨a', e', hlookup, _, _⟩ := hdecl
    refine ⟨SyncOp.deferredIsDone k, rfl, ?_⟩
    have hisSome : (w.«Π» k).isSome = true := by rw [hlookup]; rfl
    refine TypedProg.store (op := SyncOp.deferredIsDone k) (cert := ()) hisSome ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.bool b) trivial
  | deferredPoll =>
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredTy_inv hfit
    obtain ⟨a', e', hlookup, _, _⟩ := hdecl
    refine ⟨SyncOp.deferredPoll k, rfl, ?_⟩
    have hisSome : (w.«Π» k).isSome = true := by rw [hlookup]; rfl
    refine TypedProg.store (op := SyncOp.deferredPoll k) (cert := ()) hisSome ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.bool b) trivial
  | deferredSucceed =>
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v NativeOp.deferredTy .nat).mp hfit
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredTy_inv hp
    obtain ⟨n, rfl⟩ := fits_nat_inv hq
    obtain ⟨a', e', hlookup, ha, _⟩ := hdecl
    refine ⟨SyncOp.deferredCompleteWith k (.ofExit (.success (Val.nat n))), rfl, ?_⟩
    have hexit : ExitOk w ⟨a', e', Env.Requirement.empty⟩ (.success (Val.nat n)) := by
      refine strongExit_success w _ (Val.nat n) ?_
      exact fits_subN w ha.2 (Val.nat n) trivial
    refine TypedProg.store (op := SyncOp.deferredCompleteWith k (.ofExit (.success (Val.nat n))))
      (cert := ()) ⟨a', e', hlookup, hexit⟩ ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.bool b) trivial
  | deferredFail =>
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v NativeOp.deferredTy .nat).mp hfit
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredTy_inv hp
    obtain ⟨n, rfl⟩ := fits_nat_inv hq
    obtain ⟨a', e', hlookup, _, he⟩ := hdecl
    refine ⟨SyncOp.deferredCompleteWith k (.ofExit (.failure (.fail (.tag n)))), rfl, ?_⟩
    have hexit : ExitOk w ⟨a', e', Env.Requirement.empty⟩ (.failure (.fail (.tag n))) := by
      refine ⟨(fitsExit_failure_iff _ _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
      all_goals
        simp only [Cause.fail, List.mem_singleton] at hr
        subst hr
      · exact ⟨Val.nat n, rfl, fits_subN w he.2 (Val.nat n) trivial⟩
      · trivial
      · trivial
    refine TypedProg.store
      (op := SyncOp.deferredCompleteWith k (.ofExit (.failure (.fail (.tag n)))))
      (cert := ()) ⟨a', e', hlookup, hexit⟩ ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.bool b) trivial
  | scopeMake strategy =>
    cases strategy with
    | sequential =>
      have hv : v = Val.unit := fits_unit_inv hfit
      subst hv
      refine ⟨SyncOp.scopeMake .sequential, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.scopeMake .sequential) (cert := ()) trivial ?_
      intro w' ord ans post
      exact TypedProg.pure (strongExit_success w' _ ans post)
    | parallel =>
      have hv : v = Val.unit := fits_unit_inv hfit
      subst hv
      refine ⟨SyncOp.scopeMake .parallel, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.scopeMake .parallel) (cert := ()) trivial ?_
      intro w' ord ans post
      exact TypedProg.pure (strongExit_success w' _ ans post)
  | clockNow =>
    have hv : v = Val.unit := fits_unit_inv hfit
    subst hv
    refine ⟨SyncOp.clockNow, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.clockNow) (cert := ()) trivial ?_
    intro w' ord ans post
    obtain ⟨n, rfl⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.nat n) trivial
  | deferredAwait => cases hk
  | sleep => cases hk
  | external _ => cases hk

/-- A built-in operation reads its own row; only a host operation reads the table. -/
theorem nativeRowOf_builtin (table : RowTable) {op : NativeOp}
    (hk : NativeOp.kind op ≠ .program) : nativeRowOf table op = op.row := by
  cases op with
  | external i => exact absurd rfl hk
  | _ => rfl

/-- A store row is not a host row. -/
theorem kind_ne_program_of_sync {op : NativeOp} (h : NativeOp.kind op = .sync) :
    NativeOp.kind op ≠ .program := by
  rw [h]
  decide

/-- The checker's order places a type below its double normal form. -/
theorem subN_normalize₂ {a b : Ty} (h : Ty.subN a b = true) :
    Ty.subN a b.normalize.normalize = true := by
  rw [Ty.subN_normalize_right, Ty.subN_normalize_right]
  exact h

section PerformArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy}

/-- **A checked built-in `perform`**: its request evaluates to a value fitting the row's request
column (`evalTerm_progress_env`), and its type is the row's normalized columns
(`rowTy_closed_some`; every built-in row is closed, `NativeOp.row_closed`). -/
theorem builtinPerform_inv {op : NativeOp} {r : Term} {q : Point} {t : EffTy}
    (hk : NativeOp.kind op ≠ .program)
    (hat : Node.at_ (.eff root.program) q.path = some (.eff (.perform op r)))
    (hpt : PointTyped root w q t) :
    ∃ v, evalTerm q.env r = some v ∧ Fits w v (NativeOp.row op).request ∧
      t = ⟨(NativeOp.row op).answer.normalize.normalize,
        (NativeOp.row op).error.normalize.normalize,
        Env.Requirement.ofList (NativeOp.row op).requires⟩ := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨reqTy, -, hreq, hrow⟩ := Checker.inv_perform _ _ _ _ _ _ hcheck
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hreq
  have hrowOf : root.signature.rowOf op = (NativeOp.row op).normalizeTypes := by
    show (nativeRowOf root.table op).normalizeTypes = _
    rw [nativeRowOf_builtin root.table hk]
  rw [hrowOf] at hrow
  obtain ⟨hsub, rfl⟩ := rowTy_closed_some (Ty.closed_normalize _ (NativeOp.row_closed op).1)
    (Ty.closed_normalize _ (NativeOp.row_closed op).2.1)
    (Ty.closed_normalize _ (NativeOp.row_closed op).2.2) hrow
  have hnorm : Fits w v (NativeOp.row op).request.normalize := fits_subN w hsub v hvfit
  exact ⟨v, hv, (fits_normalize w _ v).mp hnorm, rfl⟩

/-- **A `perform` at a `sync` built-in row**: the store operation (`syncRow_typed`), widened to
the row's normalized columns. The consumer of the reference-read card. -/
theorem syncPerform_arm {op : NativeOp} {r : Term} (hk : NativeOp.kind op = .sync)
    (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform op r)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.perform op r) p) := by
  obtain ⟨v, hv, hfit, rfl⟩ := builtinPerform_inv (by rw [hk]; exact nofun) hat hpt
  obtain ⟨o, ho, htyped⟩ :=
    syncRow_typed root (req := Env.Requirement.ofList (NativeOp.row op).requires) op hk v hfit
  rw [denoteR_perform_sync _ _ _ hfuel ((NativeOp.row_kind op).trans hk), hv, Option.bind_some, ho]
  exact typedProg_widen root (subN_normalize₂ (Ty.subN_refl _)) (subN_normalize₂ (Ty.subN_refl _))
    htyped

/-- **`Deferred.await`**: the registration on the request's deferred, met at the deferred's
declared columns (`asyncPre`), which are below the row's `(nat, nat)` in the checker's order. -/
theorem deferredAwait_arm {r : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform .deferredAwait r)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.perform .deferredAwait r) p) := by
  obtain ⟨v, hv, hfit, rfl⟩ := builtinPerform_inv (by decide) hat hpt
  obtain ⟨k, rfl, a', e', hPi, ⟨ha, -⟩, ⟨he, -⟩⟩ := fits_deferredTy_inv hfit
  rw [denoteR_perform _ _ _ hfuel]
  show TypedProg root w _ (denoteAsync r p)
  unfold denoteAsync
  rw [hv]
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ⟨a', e', Env.Requirement.empty⟩
    ⟨a', e', hPi, Ty.sub_refl _, Ty.sub_refl _⟩
    (fun w' _ ans post => .pure (exitOk_widen (subN_normalize₂ ha) (subN_normalize₂ he) post))

/-- **`Effect.sleep`**: no time is the counted yield, answering `unit`; a positive time the
timer's registration, met at `(unit, never)`. -/
theorem sleep_arm {r : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform .sleep r)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.perform .sleep r) p) := by
  obtain ⟨v, hv, hfit, rfl⟩ := builtinPerform_inv (by decide) hat hpt
  obtain ⟨n, rfl⟩ := fits_nat_inv hfit
  rw [denoteR_perform _ _ _ hfuel]
  show TypedProg root w _ (denoteSleep r p)
  unfold denoteSleep
  rw [hv, Option.bind_some]
  cases n with
  | zero =>
    show TypedProg root w _ (.vis (.inr (.yieldNow 0)) fun v => .pure (.success v))
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_)
    have hans : ans = Val.unit := post
    subst hans
    exact .pure (strongExit_success w' _ _ trivial)
  | succ n =>
    show TypedProg root w _ (.vis (.inr (.async (.store (.registerSleep (ClockMillis.ofNat (n + 1))))
      (Val.nat (n + 1)))) Effects.Program.pure)
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (EffTy.pure .unit) (Ty.sub_refl _)
      (fun w' _ ans post => .pure (exitOk_widen (Ty.subN_refl _) (Ty.subN_refl _) post))

/-- A host row's exit, typed at the row's template columns, is typed at the row's instance at a
request (`rowTy`) when the columns keep their parameters under value formers: a parameter has no
member (`fits_instantiate`). -/
theorem exitOk_instantiate (σ : Ty.Subst) (w : World) (ty : EffTy) (ex : ExitV)
    (hans : Ty.valueVars ty.answer = true) (herr : Ty.valueVars ty.error = true)
    (hex : ExitOk w ty ex) {req : Env.Requirement} :
    ExitOk w ⟨(Ty.instantiate σ ty.answer).normalize, (Ty.instantiate σ ty.error).normalize, req⟩
      ex := by
  have hex' : ExitOk w ⟨Ty.instantiate σ ty.answer, Ty.instantiate σ ty.error, req⟩ ex := by
    cases ex with
    | success v => exact strongExit_success w _ v (fits_instantiate σ w ty.answer hans v hex.1)
    | failure cause =>
      have hfit := (fitsExit_failure_iff w ty cause).mp hex.1
      refine ⟨(fitsExit_failure_iff w _ cause).mpr ⟨fun r hr => ?_, hex.2⟩, hex.2⟩
      have hr_fit := hfit.1 r hr
      cases r with
      | fail e ann =>
        obtain ⟨v, he, hv⟩ := hr_fit
        exact ⟨v, he, fits_instantiate σ w ty.error herr v hv⟩
      | die defect ann => trivial
      | interrupt who ann => trivial
  refine exitOk_widen ?_ ?_ hex'
  · rw [Ty.subN_normalize_right]
    exact Ty.subN_refl _
  · rw [Ty.subN_normalize_right]
    exact Ty.subN_refl _

/-- **A lawful host row's columns keep their parameters under value formers**: the row passes
`rowChecks`' internal-handle scan at its answer and error (`LawfulSig.rows`), so
`valueVars_of_noInternalHandle`, and the signature's row is its normalization
(`valueVars_normalize`). -/
theorem hostRow_valueVars (root : ProgramSource) (i : Nat) (hi : i < root.table.length) :
    Ty.valueVars (root.signature.rowOf (.external i)).answer = true ∧
    Ty.valueVars (root.signature.rowOf (.external i)).error = true := by
  have hmem : root.table[i] ∈ root.table := List.get_mem _ ⟨i, hi⟩
  have hchecks := root.lawful.rows (root.table[i]) hmem
  have hrow : root.signature.rowOf (.external i) = (root.table[i]).normalizeTypes := by
    show ((nativeRowOf root.table (.external i)).normalizeTypes) = _
    unfold nativeRowOf
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hrow]
  show Ty.valueVars (root.table[i]).answer.normalize = true ∧
    Ty.valueVars (root.table[i]).error.normalize = true
  have hc7 : ((findInternalHandle [] (root.table[i]).answer).isNone,
      RowReason.internalHandle "answer") ∈ rowChecks (root.table[i]) := by
    simp only [rowChecks, List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))))
  have hc8 : ((findInternalHandle [] (root.table[i]).error).isNone,
      RowReason.internalHandle "error") ∈ rowChecks (root.table[i]) := by
    simp only [rowChecks, List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))
  have h7 := hchecks _ hc7
  have h8 := hchecks _ hc8
  simp only [Option.isNone_iff_eq_none] at h7 h8
  exact ⟨(valueVars_normalize _).2 (valueVars_of_noInternalHandle (root.table[i]).answer [] h7),
    (valueVars_normalize _).2 (valueVars_of_noInternalHandle (root.table[i]).error [] h8)⟩

/-- **A host row** (`perform (.external i)`): the host registration, its certificate the row's
template columns (`bitEntry` by reflexivity); the continuation is typed at the checked instance
because the template's post has no member at a parameter (`exitOk_instantiate`), not because a
host answer can meet it there (decisions row 183). -/
theorem external_arm {i : Nat} {request : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform (.external i) request)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.perform (.external i) request) p) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨requestTy, hdom, hreq, hrow⟩ :=
    Checker.inv_perform root.signature env p.path (.external i) request ty hcheck
  have hdom_lt : i < root.table.length := by
    change decide (i < root.table.length) = true at hdom
    exact of_decide_eq_true hdom
  obtain ⟨v, hv, -⟩ := evalTerm_progress_env henv hreq
  rw [denoteR_perform _ _ _ hfuel]
  show TypedProg root w ty (denoteForeign (.external i) request p)
  unfold denoteForeign
  rw [hv]
  let row := root.signature.rowOf (.external i)
  have hrow' : rowTy row requestTy = some ty := hrow
  obtain ⟨subst, hmatch, hformed⟩ := rowTy_instantiated_formed hrow'
  have hformed := (Formation.check_eq_none_iff _).mpr hformed
  simp only [rowTy, checkRow, hmatch, hformed, Except.toOption, Option.some.injEq] at hrow'
  cases hrow'
  have hvv := hostRow_valueVars root i hdom_lt
  let cert : EffTy := ⟨row.answer, row.error, Env.Requirement.ofList row.requires⟩
  have hbit : bitEntry root (.external i) cert := ⟨hdom, Ty.sub_refl row.answer, Ty.sub_refl row.error⟩
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbit ?_
  intro w' ord ans post
  exact .pure (exitOk_instantiate subst w' cert ans hvv.1 hvv.2 post)

/-- **`perform`**: a host row, the two asynchronous built-in rows, or a store row. -/
theorem perform_arm {op : NativeOp} {r : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform op r)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.perform op r) p) := by
  cases op with
  | external i => exact external_arm hfuel hat hpt
  | deferredAwait => exact deferredAwait_arm hfuel hat hpt
  | sleep => exact sleep_arm hfuel hat hpt
  | _ => exact syncPerform_arm rfl hfuel hat hpt

end PerformArms

/-! ### Services -/

/-- **A lawful source's service carriers are flat**: the reserved `Scope` key's carrier, a
declaration's (`serviceChecks`' flatness check, `LawfulSig.services`), or a built-in code's. -/
theorem serviceTy_flat (root : ProgramSource) (key : ServiceKey) (sty : Ty)
    (hsty : root.signature.serviceTy key = some sty) :
    flatCarrier sty = true := by
  have hsig : root.signature.serviceTy = root.sig.serviceTy := rfl
  rw [hsig] at hsty
  unfold SigApp.serviceTy at hsty
  split at hsty
  · rename_i entry hentry
    have hmem := List.mem_of_find?_eq_some hentry
    simp only [nativeReservedServiceTypes, List.mem_singleton] at hmem
    injection hmem with _ henty
    subst henty
    injection hsty with hsty'
    subst hsty'
    decide
  · split at hsty
    · exact nomatch hsty
    · split at hsty
      · rename_i ty hcode
        unfold SigApp.codeTy at hcode
        cases hfind : root.sig.services.find? (fun entry => entry.1.service == key.service) with
        | none =>
          rw [hfind] at hcode
          exact nomatch hcode
        | some entry =>
          rw [hfind] at hcode
          simp only [Option.map_some] at hcode
          injection hcode with hcode'
          subst hcode'
          injection hsty with hsty'
          subst hsty'
          have hmem := List.mem_of_find?_eq_some hfind
          have hsvc := root.lawful.services entry hmem
          have hc1 : (flatCarrier entry.2, ServiceReason.nonFlatCarrier) ∈ serviceChecks entry := by
            simp only [serviceChecks, List.mem_cons]
            exact Or.inr (Or.inl trivial)
          exact hsvc _ hc1
      · unfold SigApp.builtinCodeTy at hsty
        cases hfind : nativeServiceTypes.find? (fun entry => entry.1 == key.service.value) with
        | none =>
          rw [hfind] at hsty
          exact nomatch hsty
        | some entry =>
          rw [hfind] at hsty
          simp only [Option.map_some] at hsty
          injection hsty with hsty'
          subst hsty'
          have hmem := List.mem_of_find?_eq_some hfind
          have hall : ∀ e ∈ nativeServiceTypes, flatCarrier e.2 = true := by decide
          exact hall entry hmem

/-- A context's services fit at every later world. -/
theorem servicesFit_mono {w w' : World} (ord : w.leHost w') {ctx : Env.Ctx}
    (h : ServicesFit w ctx) : ServicesFit w' ctx :=
  servicesFit_map ord.1.2.1 ord.1.2.2.1 ord.1.2.2.2.1 ord.2 ord.1.1.2
    (serviceTy_of_le ord.1) h

/-- The context set, at a context whose services fit, answers `unit`. -/
theorem setContext_typed (root : ProgramSource) {w : World} {ctx : Ctx}
    (h : ServicesFit w ctx.services) :
    TypedProg root w (EffTy.pure .unit) (fiberValR (.setContext ctx) rfl) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () h (fun _ _ _ post => unitAnswer_typed root post)

section ServiceArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`service`**: the context read, then the binding at the key, which fits the key's carrier
(`ServicesFit`, the world's table being the source's), or the missing-service defect, which the
part-one exclusion admits; the defect is not a successful service value. -/
theorem service_arm {key : ServiceKey} (hfuel : p.fuel ≠ 0)
    (htie : w.serviceTy = root.sig.serviceTy)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.service key)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.service key) p) := by
  obtain ⟨env, hcheck, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨sty, hsty, rfl⟩ := Checker.inv_service root.signature env p.path key ty hcheck
  rw [denoteR_service _ _ hfuel]
  refine seqGuard_typed root (getContext_typed root w) (subN_never _) (fun w' ord v hv => ?_)
  obtain ⟨ctx, hctx, hsvc⟩ := fits_context_inv hv
  simp only [seqR]
  unfold serviceLookupR
  rw [hctx]
  dsimp only
  cases hget : ctx.services.getV key with
  | some val =>
    have hsty' : w'.serviceTy key = some sty := by
      rw [serviceTy_leHost ord htie]
      exact hsty
    exact .pure (strongExit_success w' _ val (flatFits_fits (hsvc.1 key val sty hget hsty')))
  | none =>
    refine .pure ⟨?_, ?_⟩
    · rw [fitsExit_failure_iff]
      refine ⟨fun r hr => ?_, ?_⟩
      · simp only [Cause.die, List.mem_singleton] at hr
        subst hr
        trivial
      · intro r hr
        simp only [Cause.die, List.mem_singleton] at hr
        subst hr
        decide
    · intro r hr
      simp only [Cause.die, List.mem_singleton] at hr
      subst hr
      decide

/-- **`provideService`**: the value term at the key's carrier, then the context update: the
context read; when the update keeps the context's identity the body runs as is, else the set
context binding the value (its services fit: `fits_flatFits`, the carrier flat by
`serviceTy_flat`) and the body at the child under the finalizer restoring the previous context
(`onExit_typed`). -/
theorem provideService_arm {key : ServiceKey} {value : Term} {b : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.provideService key value b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) :
    TypedProg root w ty (denoteR root.program (.provideService key value b) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_provideService] at hcheck
  obtain ⟨sty, vty, tb, hsty, hvty, hsub, hcb, rfl⟩ :=
    Checker.inv_provideService _ _ _ _ _ _ _ hcheck
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hvty
  have hflat : flatCarrier sty = true := serviceTy_flat root key sty hsty
  have hfit : Fits w v sty := fits_subN w hsub v hvfit
  have hchild : ∀ w'', w.leHost w'' →
      TypedProg root w'' ⟨tb.answer, tb.error, Row.diff tb.requires (Env.Requirement.single key)⟩
        (denoteR root.program b (p.child 0)) := fun w'' o'' =>
    typedProg_widen root (T := tb) (Ty.subN_refl _) (Ty.subN_refl _)
      (hb w'' (serviceTy_leHost o'' htie) (p.child 0) tb (child_fuel_eq hfuel 0) rfl
        (pointTyped_child hat rfl rfl hcb (envTyped_mono o'' henv) (completed_mono o'' hview)))
  rw [denoteR_provideService _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), hv]
  unfold updateContextR
  refine seqGuard_typed root (getContext_typed root w) (subN_never _) (fun w' o u hu => ?_)
  obtain ⟨prev, hprev, hsvc⟩ := fits_context_inv hu
  simp only [seqR]
  rw [hprev]
  dsimp only
  split
  · exact hchild w' o
  · have hsvc' : ServicesFit w' (Ctx.withServices
        ((Env.ContextUpdate.provideService key v).apply prev.services)).services := by
      refine ⟨fun key' sv sty' hget hty' => ?_,
        entriesLive_addV (fits_live _ _ _ (fits_mono o hfit)) hsvc.2⟩
      change (prev.services.addV key v).getV key' = some sv at hget
      by_cases hk : key' = key
      · subst hk
        rw [Env.Context.getV_addV_same] at hget
        cases hget
        rw [serviceTy_leHost o htie] at hty'
        have hsame : root.sig.serviceTy key' = some sty := hsty
        rw [hsame] at hty'
        cases hty'
        exact fits_flatFits hflat (fits_mono o hfit)
      · rw [Env.Context.getV_addV_other _ _ _ _ hk] at hget
        exact hsvc.1 key' sv sty' hget hty'
    refine seqGuard_typed root (setContext_typed root hsvc') (subN_never _) (fun w'' o' x _ => ?_)
    simp only [seqR]
    exact onExit_typed root (b := ⟨tb.answer, tb.error, _⟩) (f := EffTy.pure .unit)
      (Ty.subN_refl _) (Ty.subN_refl _) (subN_never _)
      (hchild w'' (leHost_trans _ _ _ o o'))
      (fun w3 o3 _ _ => setContext_typed root (servicesFit_mono (leHost_trans _ _ _ o' o3) hsvc))

end ServiceArms

/-! ### `exit` -/

/-- **An immediate exit is admitted** (the `exit` arm's inline branch): at a checked point, an
exit `inlineYield` reads off the source is admitted at the point's type. The wrong-shape branches
never fire at a typed point: every request, value and target the checker types evaluates and
decodes (term progress, `syncRow_typed`, the handle inversions); a completed target answers from
the view (row 175); `exit` of an immediate exit is that exit's success, by induction on fuel. -/
theorem inlineYield_typed {root : ProgramSource} {w : World} (f : Nat) :
    ∀ (p : Point) {e : NativeEff} {ty : EffTy} {ex : ExitV}, p.fuel = f →
      Node.at_ (.eff root.program) p.path = some (.eff e) → PointTyped root w p ty →
      inlineYield e p = some ex → ExitOk w ty ex := by
  induction f with
  | zero =>
    intro p e ty ex hfuel _ _ hinline
    unfold inlineYield at hinline
    rw [if_pos hfuel] at hinline
    exact nomatch hinline
  | succ f ih =>
    intro p e ty ex hfuel hat hpt hinline
    have hpos : p.fuel ≠ 0 := by rw [hfuel]; exact Nat.succ_ne_zero f
    unfold inlineYield at hinline
    rw [if_neg hpos] at hinline
    cases e with
    | succeed t =>
      obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      obtain ⟨t', hty, rfl⟩ := Checker.inv_succeed _ _ _ _ _ hcheck
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
      simp only [hv, Option.some.injEq] at hinline
      subst hinline
      exact strongExit_success w _ v hfit
    | fail t =>
      obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      obtain ⟨e, hty, hadm, rfl⟩ := Checker.inv_fail _ _ _ _ _ hcheck
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
      simp only [hv, Option.some.injEq] at hinline
      subst hinline
      refine ⟨(fitsExit_failure_iff _ _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
      all_goals
        simp only [Cause.fail, List.mem_singleton] at hr
        subst hr
      · exact ⟨v, valOfErr_errOf_fits hadm hfit, hfit⟩
      · trivial
      · trivial
    | failCause c =>
      obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      obtain ⟨e, hty, rfl⟩ := Checker.inv_failCause _ _ _ _ _ hcheck
      obtain ⟨cause, hc, hfits, hshape⟩ := causeOf_progress henv c e hty
      simp only [hc, Option.some.injEq] at hinline
      subst hinline
      exact ⟨(fitsExit_failure_iff _ _ _).mpr ⟨hfits, hshape⟩, hshape⟩
    | perform op r =>
      cases op with
      | external i =>
        obtain ⟨env, hcheck, henv, _⟩ := hpt.at_node hat
        rw [Eff.expandIn_of_round _ _ rfl] at hcheck
        obtain ⟨reqTy, -, hreq, -⟩ := Checker.inv_perform _ _ _ _ _ _ hcheck
        obtain ⟨v, hv, -⟩ := evalTerm_progress_env henv hreq
        simp only [inlineAsyncYield, hv] at hinline
        exact nomatch hinline
      | sleep =>
        obtain ⟨v, hv, hfit, -⟩ := builtinPerform_inv (by decide) hat hpt
        obtain ⟨n, rfl⟩ := fits_nat_inv hfit
        simp only [NativeOp.row_kind, NativeOp.kind, inlineAsyncYield, hv, Option.bind_some,
          NativeOp.sleepMillisOf] at hinline
        exact nomatch hinline
      | deferredAwait =>
        obtain ⟨v, hv, hfit, -⟩ := builtinPerform_inv (by decide) hat hpt
        obtain ⟨k, rfl, -⟩ := fits_deferredTy_inv hfit
        simp only [NativeOp.row_kind, NativeOp.kind, inlineAsyncYield, hv, Option.bind_some,
          NativeOp.awaitCellOf] at hinline
        exact nomatch hinline
      | _ =>
        obtain ⟨v, hv, hfit, -⟩ := builtinPerform_inv (kind_ne_program_of_sync rfl) hat hpt
        obtain ⟨o, ho, -⟩ := syncRow_typed root (req := Env.Requirement.empty) _ rfl v hfit
        simp only [NativeOp.row_kind, NativeOp.kind, hv, Option.bind_some, ho] at hinline
        exact nomatch hinline
    | awaitFiber target mode =>
      obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      cases mode with
      | joinEffect =>
        obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_join _ _ _ _ _ hcheck
        rw [fiberTy_eq_some hfib] at hty
        obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
        obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
        simp only [hv] at hinline
        obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_join hinline
        exact view_exitOk hview hmem hid hdecl _
      | awaitValue =>
        obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_await _ _ _ _ _ hcheck
        rw [fiberTy_eq_some hfib] at hty
        obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
        obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
        simp only [hv] at hinline
        obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_value hinline
        exact strongExit_success w _ _ (view_exitOk hview hmem hid hdecl .empty).1
    | exit b =>
      obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
      rw [Eff.expandIn_exit] at hcheck
      obtain ⟨tb, hcb, rfl⟩ := Checker.inv_exit _ _ _ _ _ hcheck
      dsimp only at hinline
      cases hsub : inlineYield b (p.child 0) with
      | none =>
        rw [hsub] at hinline
        exact nomatch hinline
      | some ex' =>
        rw [hsub, Option.map_some, Option.some.injEq] at hinline
        subst hinline
        have hex' := ih (p.child 0) (child_fuel_eq hfuel 0) (node_at_child hat rfl)
          (pointTyped_child hat rfl rfl hcb henv hview) hsub
        exact strongExit_success w _ (reifyExitVal ex') hex'.1
    | provideService key value b =>
      obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
      rw [Eff.expandIn_provideService] at hcheck
      obtain ⟨sty, vty, tb, -, hvty, -, -, -⟩ := Checker.inv_provideService _ _ _ _ _ _ _ hcheck
      obtain ⟨v, hv, -⟩ := evalTerm_progress_env henv hvty
      simp only [hv] at hinline
      exact nomatch hinline
    | _ => exact nomatch hinline

section ExitArm

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`exit`**: the body's exit reified as a successful exit value at `Exit<A, E>`; an immediate
exit by `inlineYield_typed`, otherwise the body at the child under the both-arm boundary
(`allGuard_typed`). -/
theorem exit_arm {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.exit b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) :
    TypedProg root w ty (denoteR root.program (.exit b) p) := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_exit] at hcheck
  obtain ⟨tb, hcb, rfl⟩ := Checker.inv_exit _ _ _ _ _ hcheck
  have hchild : PointTyped root w (p.child 0) tb := pointTyped_child hat rfl rfl hcb henv hview
  rw [denoteR_exit _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  cases hsub : inlineYield b (p.child 0) with
  | some ex' =>
    exact .pure (strongExit_success w _ _ (inlineYield_typed f (p.child 0) (child_fuel_eq hfuel 0)
      (node_at_child hat rfl) hchild hsub).1)
  | none =>
    exact allGuard_typed root (fun ex => by cases ex <;> rfl)
      (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl hchild)
      (fun w' _ ex hex => .pure (strongExit_success w' _ (reifyExitVal ex) hex.1))

end ExitArm

/-! ## The assembly: the arms by induction on fuel

At no fuel every point is the frontier (`denoteR_zero_typed`); at positive fuel each constructor's
arm applies, every child's hypothesis (`ChildDenotes`) being the induction's at the child's node
and the lower fuel. The layer family (`provideLayer`, decisions row 176 (b)) is proved in
`Typed/LayerArm.lean`: its arm enters here as the hypothesis `ProvideLayerArm`, which that module
discharges (`provideLayerArm`). -/

/-- **The layer family's arm, as a hypothesis** (decisions row 176 (b): built layers answer the
fiber-context image; proved at every source by `provideLayerArm`, `Typed/LayerArm.lean`, which the
import direction places after this module): at a well-formed program, given that
every node at every fuel up to `f` denotes typed programs at its typed points, a typed
`provideLayer` point with fuel `f + 1` denotes a typed program. -/
def ProvideLayerArm (root : ProgramSource) : Prop :=
  root.program.layerRefsWF = true → ∀ (f : Nat),
    (∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path) →
    ∀ (w : World), w.serviceTy = root.sig.serviceTy → ∀ (p : Point) (ty : EffTy)
      (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff), p.fuel = f + 1 →
      Node.at_ (.eff root.program) p.path = some (.eff (.provideLayer l i b)) →
      PointTyped root w p ty → TypedProg root w ty (denoteR root.program (.provideLayer l i b) p)

/-- **The arms assembled** (by induction on fuel, given the layer family's arm): every node of a
well-formed program, at every fuel up to `f`, denotes typed programs at its typed points. -/
theorem childDenotes_upto (root : ProgramSource) (hlayer : ProvideLayerArm root)
    (hwf : root.program.layerRefsWF = true) :
    ∀ (f : Nat), ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path := by
  intro f
  induction f with
  | zero =>
    intro f' hf' c path _ w _ q ty hq _ _
    exact denoteR_zero_typed c (by omega)
  | succ f ih =>
    intro f' hf' c path hc w htie q ty hq hqpath hqt
    rcases Nat.lt_or_eq_of_le hf' with hlt | heq
    · exact ih f' (Nat.lt_succ_iff.mp hlt) c path hc w htie q ty hq hqpath hqt
    · subst heq
      have hat : Node.at_ (.eff root.program) q.path = some (.eff c) := hqpath ▸ hc
      have hpos : q.fuel ≠ 0 := by rw [hq]; exact Nat.succ_ne_zero f
      have hch : ∀ (c' : NativeEff) (i : Nat), (Node.eff c).child i = some (.eff c') →
          ChildDenotes root f c' (q.path ++ [i]) :=
        fun c' i hci => ih f (Nat.le_refl f) c' (q.path ++ [i]) (node_at_child hat hci)
      cases c with
      | succeed t => exact succeed_arm hpos hat hqt
      | fail t => exact fail_arm hpos hat hqt
      | failCause c => exact failCause_arm hpos hat hqt
      | sync t => exact sync_arm hpos hat hqt
      | suspend b => exact suspend_arm hq hat hqt htie (hch b 0 rfl)
      | perform op r => exact perform_arm hpos hat hqt
      | bind a b => exact bind_arm hq hat hqt htie (hch a 0 rfl) (hch b 1 rfl)
      | gen body => exact gen_arm hq hat hqt
      | catchCause b h => exact catchCause_arm hq hat hqt htie (hch b 0 rfl) (hch h 1 rfl)
      | matchCause b v c =>
        exact matchCause_arm hq hat hqt htie (hch b 0 rfl) (hch v 1 rfl) (hch c 2 rfl)
      | onExit b fin => exact onExit_arm hq hat hqt htie (hch b 0 rfl) (hch fin 1 rfl)
      | exit b => exact exit_arm hq hat hqt htie (hch b 0 rfl)
      | uninterruptible b => exact uninterruptible_arm hq hat hqt
      | interruptible b => exact interruptible_arm hq hat hqt
      | yieldNow priority => exact yieldNow_arm hpos hat hqt
      | awaitFiber t mode => exact awaitFiber_arm hpos hat hqt
      | withFiber a => exact withFiber_arm hpos hat hqt
      | «scoped» b => exact scoped_arm hq hat hqt
      | acquireRelease a r => exact acquireRelease_arm hq hat hqt
      | provideLayer l i b => exact hlayer hwf f ih w htie q ty l i b hq hat hqt
      | service key => exact service_arm hpos htie hat hqt
      | provideService key value b => exact provideService_arm hq hat hqt htie (hch b 0 rfl)
      | catchIf test b h => exact catchIf_arm hq hat hqt htie (hch b 0 rfl) (hch h 1 rfl)
      | select s d a0 a1 => exact select_arm hq hat hqt htie (hch a0 0 rfl) (hch a1 1 rfl)
      | iterate cursorTy initial test step result body => exact iterate_arm hq hat hqt

/-- **No node of the program is a `provideLayer`**: the fragment on which the layer family's arm
cannot be reached. -/
def LayerFree (root : NativeEff) : Prop :=
  ∀ (path : List Nat) (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff),
    Node.at_ (.eff root) path ≠ some (.eff (.provideLayer l i b))

/-- On the layer-free fragment the layer family's arm holds: no point reaches it. -/
theorem provideLayerArm_of_layerFree {root : ProgramSource} (h : LayerFree root.program) :
    ProvideLayerArm root :=
  fun _ _ _ _ _ p _ l i b _ hat _ => absurd hat (h p.path l i b)

end Effect4.Program.Typed
