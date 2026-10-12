import Effect4.Laws.Program.Typed.Context
import Effect4.Laws.Program.Typed.StackCertificates
import Effect4.Laws.Program.Typed.Seq
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Eliminators
import Effect4.Laws.Program.Decision
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.ExpandFix

/-!
# M5's source term and bind producers (decisions rows 117, 349)

The existing source declarations retain their names in this dependency module.
The context-aware leaves and bind use the same program arrow with actual entry coverage.
The remaining source arms and the closed load consumer belong to `Typed/Denotation.lean`.
This dependency checkpoint does not complete the source denotation migration.

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
abbrev effsRounds (xs : List Nat) (es : Effs NativeOp) : Effs NativeOp :=
  xs.foldl (fun acc _ => Effs.expandRound orig acc) es

/-- The rounds on a block's module layers (decisions row 341), layer by layer. -/
private abbrev layersRounds (xs : List Nat) (ls : LayerTerms NativeOp) : LayerTerms NativeOp :=
  xs.foldl (fun acc _ => LayerTerms.expandRound orig acc) ls

private theorem rounds_raceAll : ∀ (xs : List Nat) (es : Effs NativeOp),
    rounds orig xs (.withFiber (.raceAll es)) = .withFiber (.raceAll (effsRounds orig xs es))
  | [], _ => rfl
  | _ :: xs, es => rounds_raceAll xs (Effs.expandRound orig es)

private theorem rounds_raceAllFirst : ∀ (xs : List Nat) (es : Effs NativeOp),
    rounds orig xs (.withFiber (.raceAllFirst es)) = .withFiber (.raceAllFirst (effsRounds orig xs es))
  | [], _ => rfl
  | _ :: xs, es => rounds_raceAllFirst xs (Effs.expandRound orig es)

/-- The rounds on an invocation's spine (decisions row 340), as on a race's. A step of
`Eff.expandIn_invoke`. -/
private theorem rounds_invoke (k : Nat) (r : Term) : ∀ (xs : List Nat) (es : Effs NativeOp),
    rounds orig xs (.invoke k r es) = .invoke k r (effsRounds orig xs es)
  | [], _ => rfl
  | _ :: xs, es => rounds_invoke k r xs (Effs.expandRound orig es)

theorem effsRounds_nil : ∀ (xs : List Nat), effsRounds orig xs .nil = .nil
  | [] => rfl
  | _ :: xs => effsRounds_nil xs

theorem effsRounds_cons : ∀ (xs : List Nat) (h : NativeEff) (t : Effs NativeOp),
    effsRounds orig xs (.cons h t) = .cons (rounds orig xs h) (effsRounds orig xs t)
  | [], _, _ => rfl
  | _ :: xs, h, t => effsRounds_cons xs (Eff.expandRound orig h) (Effs.expandRound orig t)

/-- A block's rounds keep the block: its spine's rounds and its main program's (decisions row 328;
private like `rounds_raceAll`). A step of `Eff.expandIn_defs`. -/
private theorem rounds_defs : ∀ (xs : List Nat) (decls : List DefDecl) (bodies : Effs NativeOp)
    (main : NativeEff) (layers : LayerTerms NativeOp),
    rounds orig xs (.defs decls bodies main layers) =
      .defs decls (effsRounds orig xs bodies) (rounds orig xs main) (layersRounds orig xs layers)
  | [], _, _, _, _ => rfl
  | _ :: xs, decls, bodies, main, layers =>
    rounds_defs xs decls (Effs.expandRound orig bodies) (Eff.expandRound orig main)
      (LayerTerms.expandRound orig layers)

/-- One round keeps a node that is no block a node that is no block: the round is the identity
fold but at a layer reference. A step of `Eff.expandIn_ne_defs`. -/
private theorem expandRound_ne_defs (e : NativeEff) (he : ∀ d b m layers, e ≠ .defs d b m layers) :
    ∀ d b m layers, Eff.expandRound orig e ≠ .defs d b m layers := by
  intro d b m l h
  cases e with
  | defs d' b' m' l' => exact he d' b' m' l' rfl
  | _ => cases h

private theorem rounds_ne_defs : ∀ (xs : List Nat) (e : NativeEff), (∀ d b m layers, e ≠ .defs d b m layers) →
    ∀ d b m layers, rounds orig xs e ≠ .defs d b m layers
  | [], _, he => he
  | _ :: xs, e, he => rounds_ne_defs xs _ (expandRound_ne_defs orig e he)

/-- The spine's rounds, entry by entry. A step of `Eff.expandIn_defs`. -/
private theorem effsRounds_getElem? (xs : List Nat) : ∀ (es : Effs NativeOp) (k : Nat),
    (effsRounds orig xs es).toList[k]? = (es.toList[k]?).map (rounds orig xs)
  | .nil, k => by
    rw [effsRounds_nil]
    simp only [Effs.toList, List.getElem?_nil, Option.map_none]
  | .cons h t, 0 => by
    rw [effsRounds_cons]
    simp only [Effs.toList, List.getElem?_cons_zero, Option.map_some]
  | .cons h t, k + 1 => by
    rw [effsRounds_cons]
    simp only [Effs.toList, List.getElem?_cons_succ]
    exact effsRounds_getElem? xs t k

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

/-- A definition block keeps its head and its declarations through the expansion's rounds
(decisions row 328): each round folds the block into a block. A step of `defs_not_typed`. -/
theorem Eff.expandIn_defs_head (decls : List DefDecl) (bodies : Effs NativeOp) (main : NativeEff)
    (layers : LayerTerms NativeOp) :
    ∃ bodies' main' layers', Eff.expandIn root (.defs decls bodies main layers) =
      .defs decls bodies' main' layers' := by
  unfold Eff.expandIn
  generalize List.range ((root.refSites []).length + 1) = rounds
  induction rounds generalizing bodies main layers with
  | nil => exact ⟨bodies, main, layers, rfl⟩
  | cons _ rest ih =>
    exact ih (Effs.expandRound (Node.eff root) bodies) (Eff.expandRound (Node.eff root) main)
      (LayerTerms.expandRound (Node.eff root) layers)

/-- **A block's expansion** (decisions row 328): the rounds keep the block and its declarations;
each body and the main program is expanded in place, entry by entry. A step of
`bodiesTyped_of_typeOf` and `mainChecked_of_typeOf`. -/
theorem Eff.expandIn_defs (decls : List DefDecl) (bodies : Effs NativeOp) (main : NativeEff)
    (layers : LayerTerms NativeOp) :
    ∃ bodies' : Effs NativeOp, Eff.expandIn root (.defs decls bodies main layers) =
        .defs decls bodies' (Eff.expandIn root main) (LayerTerms.expandIn root layers) ∧
      ∀ k : Nat, bodies'.toList[k]? = (bodies.toList[k]?).map (Eff.expandIn root) :=
  ⟨_, rounds_defs _ _ decls bodies main layers, effsRounds_getElem? _ _ bodies⟩

/-- The expansion keeps a program that is no block a program that is no block. A step of
`rootCode_typed` (`Typed/Assembly.lean`). -/
theorem Eff.expandIn_ne_defs {e : NativeEff} (he : ∀ d b m layers, e ≠ .defs d b m layers) :
    ∀ d b m layers, Eff.expandIn root e ≠ .defs d b m layers :=
  rounds_ne_defs _ _ e he

theorem Eff.expandIn_restore (saved : Term) (b : NativeEff) :
    Eff.expandIn root (.restore saved b) = .restore saved (Eff.expandIn root b) :=
  rounds_one _ (Eff.restore saved) (fun _ => rfl) _ b

theorem Eff.expandIn_provideContext (context : Term) (body : NativeEff) :
    Eff.expandIn root (.provideContext context body) =
      .provideContext context (Eff.expandIn root body) :=
  rounds_one _ (Eff.provideContext context) (fun _ => rfl) _ body

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
theorem Eff.expandIn_raceAll (es : Effs NativeOp) :
    Eff.expandIn root (.withFiber (.raceAll es)) =
      .withFiber (.raceAll
        (effsRounds (Node.eff root) (List.range ((root.refSites []).length + 1)) es)) :=
  rounds_raceAll _ _ es

/-- The first-exit expansion serves `raceAllFirst_arm`. -/
theorem Eff.expandIn_raceAllFirst (es : Effs NativeOp) :
    Eff.expandIn root (.withFiber (.raceAllFirst es)) =
      .withFiber (.raceAllFirst
        (effsRounds (Node.eff root) (List.range ((root.refSites []).length + 1)) es)) :=
  rounds_raceAllFirst _ _ es

/-- An invocation's expansion is the invocation of its spine's rounds (decisions row 340; private
like `Eff.expandIn_raceAll`). A step of `invoke_arm`. -/
theorem Eff.expandIn_invoke (k : Nat) (r : Term) (args : Effs NativeOp) :
    Eff.expandIn root (.invoke k r args) =
      .invoke k r (effsRounds (Node.eff root) (List.range ((root.refSites []).length + 1)) args) :=
  rounds_invoke _ k r _ args

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

/-- The node at a child's path is the node's child there: the address law
(`Effect4.Program.Node.at_child`, `Laws/Program/Address.lean`) at a program's root. -/
theorem node_at_child {root : NativeEff} {path : List Nat} {n : Node NativeOp} {i : Nat}
    {c : Node NativeOp} (hat : Node.at_ (.eff root) path = some n)
    (hc : n.child i = some c) : Node.at_ (.eff root) (path ++ [i]) = some c :=
  Effect4.Program.Node.at_child hat hc

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
environment and at the node's signature, at a point whose path is the child's, whose view is
typed, and whose stack is typed at the node's scope. A child has its node's scope
(`ProgramSource.scopeSig_child`, `scopeParams_child`). -/
theorem pointTyped_child {src : ProgramSource} {w : World} {path : List Nat} {e c : NativeEff}
    {i : Nat} {env : List Ty} {q : Point} {ty : EffTy}
    (hat : Node.at_ (.eff src.program) path = some (.eff e))
    (hc : (Node.eff e).child i = some (.eff c)) (hpath : q.path = path ++ [i])
    (hcheck : Checker.check (src.scopeSig path) env (path ++ [i]) (Eff.expandIn src.program c) =
      .ok ty)
    (henv : EnvTyped w env q.env)
    (hview : ∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2)
    (hstack : StackTyped src w (scopeParams src.program path) q.params) :
    PointTyped src w q ty := by
  rw [← src.scopeSig_child hat i] at hcheck
  rw [← scopeParams_child hat i] at hstack
  exact ⟨c, env, hpath ▸ node_at_child hat hc, hpath ▸ hcheck, henv, hview, hpath ▸ hstack⟩

/-- A point typed at the scope of a path that has its parameters: its node checked at that path's
signature, and its stack typed at that path's scope. A grandchild of a program node is one
(`scopeParams_prefix`). -/
theorem pointTyped_scope {src : ProgramSource} {w : World} {path : List Nat} {c : NativeEff}
    {env : List Ty} {q : Point} {ty : EffTy}
    (hscope : scopeParams src.program q.path = scopeParams src.program path)
    (hat : Node.at_ (.eff src.program) q.path = some (.eff c))
    (hcheck : Checker.check (src.scopeSig path) env q.path (Eff.expandIn src.program c) = .ok ty)
    (henv : EnvTyped w env q.env)
    (hview : ∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2)
    (hstack : StackTyped src w (scopeParams src.program path) q.params) :
    PointTyped src w q ty := by
  have hsig : src.scopeSig q.path = src.scopeSig path := by
    unfold ProgramSource.scopeSig
    rw [hscope]
  rw [← hsig] at hcheck
  rw [← hscope] at hstack
  exact ⟨c, env, hat, hcheck, henv, hview, hstack⟩

/-- The actual child keeps the same captured parameter stack and its ambient annotation.
Consumer: recursive source arms in the original closed M5 proof. -/
theorem ambientPointTyped_child {src : ProgramSource} {w : World} {available : Env.Requirement}
    {parent q : Point} {e c : NativeEff} {parentTy ty : EffTy} {i : Nat} {env : List Ty}
    (typed : AmbientPointTyped src w available parent parentTy)
    (hat : Node.at_ (.eff src.program) parent.path = some (.eff e))
    (hc : (Node.eff e).child i = some (.eff c)) (hpath : q.path = parent.path ++ [i])
    (sameParams : q.params = parent.params)
    (checked : Checker.check (src.scopeSig parent.path) env (parent.path ++ [i])
      (Eff.expandIn src.program c) = .ok ty)
    (values : EnvTyped w env q.env)
    (view : ∀ entry ∈ q.completed, ∃ declared, w.Γ entry.1 = some declared ∧ ExitOk w declared entry.2) :
    AmbientPointTyped src w available q ty := by
  obtain ⟨_, _, _, _, _, _, stack⟩ := typed.1
  have stackAt : StackTyped src w (scopeParams src.program parent.path) q.params :=
    sameParams.symm ▸ stack
  refine ⟨pointTyped_child hat hc hpath checked values view stackAt, ?_⟩
  have scope : scopeParams src.program q.path = scopeParams src.program parent.path :=
    hpath ▸ scopeParams_child hat i
  exact (congrArg (fun declarations => AmbientStackTyped src w available declarations q.params)
    scope).mpr (sameParams.symm ▸ typed.2)

/-- The actual child retains its parameter frame and the existing certificate policy.
Consumer: recursive ambient source arms in the closed M5 proof. -/
theorem ambientStackTyped_child {src : ProgramSource} {w : World} {available : Env.Requirement}
    {parent q : Point} {e : NativeEff} {i : Nat}
    (node : Node.at_ (.eff src.program) parent.path = some (.eff e))
    (path : q.path = parent.path ++ [i]) (params : q.params = parent.params)
    (saved : AmbientStackTyped src w available (scopeParams src.program parent.path) parent.params) :
    AmbientStackTyped src w available (scopeParams src.program q.path) q.params := by
  have scope : scopeParams src.program q.path = scopeParams src.program parent.path :=
    path ▸ scopeParams_child node i
  exact (congrArg (fun declarations => AmbientStackTyped src w available declarations q.params)
    scope).mpr (params.symm ▸ saved)

/-- A checked descendant uses the same source-scope certificate fold.
Consumer: actual fork entrants and callback source points in ambient M5. -/
theorem ambientPointTyped_scope {src : ProgramSource} {w : World} {available : Env.Requirement}
    {path : List Nat} {c : NativeEff} {env : List Ty} {q : Point} {ty : EffTy}
    (scope : scopeParams src.program q.path = scopeParams src.program path)
    (node : Node.at_ (.eff src.program) q.path = some (.eff c))
    (checked : Checker.check (src.scopeSig path) env q.path (Eff.expandIn src.program c) = .ok ty)
    (values : EnvTyped w env q.env)
    (view : ∀ entry ∈ q.completed, ∃ declared, w.Γ entry.1 = some declared ∧ ExitOk w declared entry.2)
    (stack : AmbientStackTyped src w available (scopeParams src.program path) q.params) :
    AmbientPointTyped src w available q ty :=
  ⟨pointTyped_scope scope node checked values view (ambientStackTyped_erases stack),
    (congrArg (fun declarations => AmbientStackTyped src w available declarations q.params) scope).mpr stack⟩

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

private theorem progress_of_poly {a : NativeAtom} {params : List Ty} {answer : Ty}
    (hs : (NativeAtom.spec a).scheme = .poly params answer)
    (_hvv : ∀ p ∈ params, Ty.valueVars p = true)
    (hev : ∀ (w : World) (σ : Ty.Subst) (vs : List Val),
      FitsAll w vs (params.map (Ty.instantiate σ)) → (NativeAtom.eval a vs).isSome = true)
    (w : World) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : a.typeOf tys = some ty) (hfit : FitsAll w vs tys) :
    (NativeAtom.eval a vs).isSome = true := by
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply] at hty
  obtain ⟨σ, hmatch, _⟩ := Option.map_eq_some_iff.mp hty
  exact hev w σ vs (FitsAll.instantiateB hmatch hfit)

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
  | int2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨_, he, _⟩ := hev x y hx hy
    rw [he]
    rfl
  | intRel =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨_, he⟩ := hev x y hx hy
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
  | tuple => rfl
  | succ => exact progress_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | pred => exact progress_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | isZero => exact progress_of_shape .natTest rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | boolNot => exact progress_of_shape .bool1 rfl (fun _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | add => exact progress_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩) w tys ty vs hty hfit
  | lt =>
    refine progress_of_shape .intRel rfl (fun x y hx hy => ?_) w tys ty vs hty hfit
    obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := intImage_inv hx <;>
      obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := intImage_inv hy <;> exact ⟨_, rfl⟩
  | intAdd =>
    exact progress_of_shape (a := .intAdd) .int2 rfl (fun _ _ hx hy => intAdd_closed hx hy) w tys ty vs
      hty hfit
  | intSub =>
    exact progress_of_shape (a := .intSub) .int2 rfl (fun _ _ hx hy => intSub_closed hx hy) w tys ty vs
      hty hfit
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
        obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := intImage_inv hx <;>
          obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := intImage_inv hy <;> rfl
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

  | mapEmpty =>
    refine progress_of_mono rfl (fun w vs hfit => ?_) w tys ty vs hty hfit
    cases hfit.nil_inv
    rfl
  | mapGet =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨value, key, rfl, hf, hk⟩ := hfit.pair_inv
    obtain ⟨name, rfl⟩ := fits_string_inv hk
    obtain ⟨out, he, _⟩ := MapFits.get hf name
    exact Option.isSome_iff_exists.mpr ⟨out, he⟩
  | mapSet =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨value, key, replacement, rfl, hf, hk, hr⟩ := hfit.triple_inv
    obtain ⟨name, rfl⟩ := fits_string_inv hk
    obtain ⟨out, he, _⟩ := MapFits.set hf name hr
    exact Option.isSome_iff_exists.mpr ⟨out, he⟩
  | mapKeys =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨value, rfl, hf⟩ := hfit.singleton_inv
    obtain ⟨out, he, _⟩ := MapFits.keys hf
    exact Option.isSome_iff_exists.mpr ⟨out, he⟩
  | mapEntries =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨value, rfl, hf⟩ := hfit.singleton_inv
    obtain ⟨out, he, _⟩ := MapFits.entries hf
    exact Option.isSome_iff_exists.mpr ⟨out, he⟩
  | mapFromEntries =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨value, rfl, hf⟩ := hfit.singleton_inv
    obtain ⟨out, he, _⟩ := MapFits.fromEntries hf
    exact Option.isSome_iff_exists.mpr ⟨out, he⟩
  -- a prefix and its rest answer on every list and every count (decisions row 228)
  | listTake =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨l, i, rfl, hl, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := fits_nat_inv hi
    obtain ⟨elems, he⟩ := asList_of_fits hl
    simp only [NativeAtom.eval, he, Option.map_some, Option.isSome_some]
  | listDrop =>
    refine progress_of_poly rfl (by decide) (fun w σ vs hfit => ?_) w tys ty vs hty hfit
    obtain ⟨l, i, rfl, hl, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := fits_nat_inv hi
    obtain ⟨elems, he⟩ := asList_of_fits hl
    simp only [NativeAtom.eval, he, Option.map_some, Option.isSome_some]
  -- two members of one admitted handle type carry one kind byte, so the identity test answers
  -- (decisions row 229): the typing excludes the evaluation's two-kinds refusal
  | sameHandle =>
    simp only [NativeAtom.typeOf, NativeAtom.spec, NativeAtom.Scheme.apply,
      NativeAtom.CustomScheme.apply, NativeAtom.sameHandleRule] at hty
    split at hty
    · obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨k, rfl, _⟩ := fits_refOf_inv hx
      obtain ⟨k', rfl, _⟩ := fits_refOf_inv hy
      show (if (2 : UInt8) = 2 then some (Val.bool (decide (k.index = k'.index)))
        else none).isSome = true
      rw [if_pos rfl]
      rfl
    · obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨k, rfl, _⟩ := fits_deferredOf_inv hx
      obtain ⟨k', rfl, _⟩ := fits_deferredOf_inv hy
      show (if (3 : UInt8) = 3 then some (Val.bool (decide (k.index = k'.index)))
        else none).isSome = true
      rw [if_pos rfl]
      rfl
    · exact nomatch hty

section TermProgress

variable {sig : Signature NativeOp} {w : World}

mutual
/-- **Term progress at a world** (proved): a term the checker types, over values that fit their
types at a world, evaluates, and its value fits the term's type (`atomFits`). Under any signature
whose atoms are the native table's; the const-generic flag is the signature's own. The world is
fixed. The environment is the theorem's own binder, since a list fold's body runs at the
environment extended by its accumulator and its element (decisions row 228). -/
theorem evalTerm_progress {vals : List Val} {env : List Ty} (hatom : sig.atomOf = nativeAtomTy)
    (hfit : FitsAll w vals env) :
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
  | .tupleAt target index, ty, hty => by
    have ht : (termTy sig env target).bind (fun targetType => Tuple.typeAt targetType index) = some ty := hty
    obtain ⟨targetType, ht, hp⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨value, he, hm⟩ := evalTerm_progress hatom hfit target targetType ht
    obtain ⟨out, hout, hfitout⟩ := tuple_typeAt_fits hp hm
    refine ⟨out, ?_, hfitout⟩
    show (evalTerm vals target).bind (fun value => Val.tupleAt? value index) = some out
    rw [he, Option.bind_some, hout]
  -- the term typer's rule discharges the premises of the fold's semantic rule (`fold_fits`):
  -- the list and the initial value evaluate into their types, the initial value's type is
  -- below the fold's, and each step runs at the environment extended by a member of the
  -- fold's type and an element, so it answers a member of the body's type, which is below it
  | .fold accTy list init body, ty, hty => by
    obtain ⟨listType, item, initType, bodyType, hlist, hitem, hinit, _, hsubInit, hbody, hsubBody⟩ :=
      termTy_fold_inv hty
    obtain ⟨value, hlv, hfitList⟩ := evalTerm_progress hatom hfit list listType hlist
    replace hfitList := fits_subN w (listOf_upper hitem) value hfitList
    obtain ⟨start, hstart, hfitStart⟩ := evalTerm_progress hatom hfit init initType hinit
    refine fold_fits hlv hfitList hstart (fits_subN w hsubInit start hfitStart) ?_
    intro acc x hacc hx
    obtain ⟨next, hnext, hfitNext⟩ :=
      evalTerm_progress hatom (hfit.append_pair hacc hx) body bodyType hbody
    exact ⟨next, hnext, fits_subN w hsubBody next hfitNext⟩
termination_by t => sizeOf t

/-- The argument list's form. -/
theorem evalTerms_progress {vals : List Val} {env : List Ty}
    (hatom : sig.atomOf = nativeAtomTy) (hfit : FitsAll w vals env) :
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

/-- Term progress in the environment judgment `PointTyped` reads, under the signature of a
scope (`ProgramSource.scopeSig`; the source's own at `path := []`). A term types alike in every
scope (`ProgramSource.scopeSig_extends`). -/
theorem evalTerm_progress_env {src : ProgramSource} {path : List Nat} {w : World} {env : List Ty}
    {vals : List Val} (henv : EnvTyped w env vals) {t : Term} {ty : Ty}
    (hty : termTy (src.scopeSig path) env t = some ty) :
    ∃ v, evalTerm vals t = some v ∧ Fits w v ty :=
  evalTerm_progress rfl (fitsAll_of_pointwise henv.1 henv.2) t ty
    (((src.scopeSig_extends path).termTy env t).symm.trans hty)

/-- **A typed binder term maps its parameter into its type**, at every later world (the claim
`term-typed-maps`): a term the checker types at `tys ++ [A]` with type `R`, over an environment
that fits `tys`, runs at `env ++ [a]` for every member `a` of `A` to a member of `R`. It is the
term relation's fundamental property for the term typer (`TermMaps`, `Typed/Residual.lean`):
the environment stays typed at every later world (`envTyped_mono`), the current value extends it
(`envTyped_append`), and a typed term over fitting values evaluates into its type
(`evalTerm_progress`). Under any signature whose atoms are the native table's. Its consumer is
`syncRow_typed`, which discharges a read-modify-write row's pre from the term's typing. It says
nothing of a term the checker refuses. -/
@[semantics "store-typing" (requirement := R4)]
theorem termMaps_of_typed {sig : Signature NativeOp} (hatom : sig.atomOf = nativeAtomTy)
    {w : World} {tys : TyEnv} {env : List Val} (henv : EnvTyped w tys env)
    {f : Term} {A R : Ty} (hty : termTy sig (tys ++ [A]) f = some R) :
    TermMaps w f env A R := by
  intro w' ord a ha
  have henv' := envTyped_append (envTyped_mono ord henv) ha
  exact evalTerm_progress hatom (fitsAll_of_pointwise henv'.1 henv'.2) f R hty

/-- An admitted error value is represented: its error image reads back (`valOfErr_errOf_supported`
at the world's allocation table), so it is not the payload-discarding `boom`. -/
theorem valOfErr_errOf_fits {w : World} {e : Ty} {v : Val} (hs : admittedErrTy e = true)
    (hv : Fits w v e) : valOfErr (errOf v) = some v :=
  valOfErr_errOf_supported e v _ hs (fits_hasTy w e v hv)

/-- A defect made from an admitted error value is not a shape defect. -/
theorem shapeFree_die_of_fits {w : World} {e : Ty} {v : Val} (hs : admittedErrTy e = true)
    (hv : Fits w v e) : ShapeFree (Cause.die (Defect.ofError (errOf v)) : CauseV) := by
  intro r hr
  simp only [Cause.die, List.mem_singleton] at hr
  subst hr
  exact Defect.ofError_shapeFree (valOfErr_errOf_fits hs hv)

/-- **Cause progress at a world** (proved): a cause term the checker types at an error column
evaluates, in a typed environment, to a cause whose typed failures fit the column and which no
shape defect enters. -/
theorem causeOf_progress {src : ProgramSource} {path : List Nat} {w : World} {env : List Ty}
    {vals : List Val} (henv : EnvTyped w env vals) :
    ∀ (c : CauseTerm) (e : Ty), causeTy (src.scopeSig path) env c = some e →
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
    have h' : ((termTy (src.scopeSig path) env who).bind fun t =>
        if Ty.sub t.normalize .nat then some Ty.never else none) = some e := h
    obtain ⟨t, ht, hnat⟩ := Option.bind_eq_some_iff.mp h'
    split at hnat
    · next htn =>
      cases hnat
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv ht
      obtain ⟨n, rfl⟩ := fits_nat_inv (fits_subN w (b := .nat) htn v hfit)
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
    have h' : ((causeTy (src.scopeSig path) env left).bind fun l =>
        (causeTy (src.scopeSig path) env right).bind fun r => some (l.join r)) = some e := h
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

/-- A checked point's node: the checker's verdict on its expansion at its scope's signature in a
typed environment, the typed completed view, and the typed stack. -/
theorem PointTyped.at_node {src : ProgramSource} {w : World} {p : Point} {ty : EffTy}
    {e : NativeEff} (hpt : PointTyped src w p ty)
    (hat : Node.at_ (.eff src.program) p.path = some (.eff e)) :
    ∃ env, Checker.check (src.scopeSig p.path) env p.path (Eff.expandIn src.program e) = .ok ty ∧
      EnvTyped w env p.env ∧ (∀ q ∈ p.completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) ∧
      StackTyped src w (scopeParams src.program p.path) p.params := by
  obtain ⟨e', env, hat', hcheck, henv, hview, hstack⟩ := hpt
  rw [hat] at hat'
  cases hat'
  exact ⟨env, hcheck, henv, hview, hstack⟩

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
  {available : Env.Requirement}

/-- **No fuel**: the frontier at the point. -/
theorem denoteR_zero_typed (e : NativeEff) (hzero : p.fuel = 0) :
    AmbientProg root w available (ty, available, available) (denoteR root.program e p) := by
  rw [denoteR_zero _ _ _ hzero]
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () True.intro ?_ (Row.subset_refl _)
  intro _ _ _ impossible
  exact impossible.elim

/-- **`succeed`**: the term's value, which fits the term's type (`evalTerm_progress_env`). -/
theorem succeed_arm {t : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.succeed t)))
    (hpt : PointTyped root w p ty) : AmbientProg root w available (ty, available, available) (denoteR root.program (.succeed t) p) := by
  obtain ⟨env, hcheck, henv, _, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨t', hty, rfl⟩ := Checker.inv_succeed _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  rw [denoteR_succeed _ _ hfuel, hv]
  exact .pure ⟨strongExit_success w _ v hfit, Row.subset_refl _⟩ (Row.subset_refl _)

/-- **`fail`**: the failure of the term's value, an admitted error that reads back
(`valOfErr_errOf_fits`). -/
theorem fail_arm {t : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.fail t)))
    (hpt : PointTyped root w p ty) : AmbientProg root w available (ty, available, available) (denoteR root.program (.fail t) p) := by
  obtain ⟨env, hcheck, henv, _, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨e, hty, hadm, rfl⟩ := Checker.inv_fail _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  rw [denoteR_fail _ _ hfuel, hv]
  refine .pure ⟨?_, Row.subset_refl _⟩ (Row.subset_refl _)
  refine ⟨(fitsExit_failure_iff _ _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
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
    (hpt : PointTyped root w p ty) : AmbientProg root w available (ty, available, available) (denoteR root.program (.failCause c) p) := by
  obtain ⟨env, hcheck, henv, _, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨e, hty, rfl⟩ := Checker.inv_failCause _ _ _ _ _ hcheck
  obtain ⟨cause, hc, hfits, hshape⟩ := causeOf_progress henv c e hty
  rw [denoteR_failCause _ _ hfuel, hc]
  exact .pure ⟨⟨(fitsExit_failure_iff _ _ _).mpr ⟨hfits, hshape⟩, hshape⟩,
    Row.subset_refl _⟩ (Row.subset_refl _)

/-- **`sync`**: the counted step answering the term's value, which fits the term's type. -/
theorem sync_arm {t : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.sync t)))
    (hpt : PointTyped root w p ty) : AmbientProg root w available (ty, available, available) (denoteR root.program (.sync t) p) := by
  obtain ⟨env, hcheck, henv, _, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨t', hty, rfl⟩ := Checker.inv_sync _ _ _ _ _ hcheck
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  rw [denoteR_sync _ _ hfuel, hv]
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' o ans post => ?_) (Row.subset_refl _)
  have hans : ans = v := post
  exact .pure ⟨strongExit_success w' _ ans (by rw [hans]; exact fits_mono o hfit),
    Row.subset_refl _⟩ (Row.subset_refl _)

/-- **`yieldNow`**: the park answers `unit` (`fiberPost`'s `yieldNow` arm). -/
theorem yieldNow_arm {priority : Nat} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.yieldNow priority)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.yieldNow priority) p) := by
  obtain ⟨env, hcheck, _, _, _⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_yieldNow _ _ _ _ _ hcheck
  subst hty
  rw [denoteR_yieldNow _ _ hfuel]
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_) (Row.subset_refl _)
  have hans : ans = Val.unit := post
  subst hans
  exact .pure ⟨strongExit_success w' _ _ trivial, Row.subset_refl _⟩ (Row.subset_refl _)

end TermArms


/-- The existing M5 child judgment retains its actual entry and common completion row. -/
def ChildDenotes (root : ProgramSource) (f : Nat) (c : NativeEff) (path : List Nat) : Prop :=
  ∀ (w : World), w.serviceTy = root.sig.serviceTy → ∀ (q : Point) (ty : EffTy),
    q.fuel = f → q.path = path → PointTyped root w q ty →
    ∀ available : Env.Requirement, Row.Subset ty.requires available →
      AmbientStackTyped root w available (scopeParams root.program q.path) q.params →
      AmbientProg root w available (ty, available, available) (denoteR root.program c q)

theorem child_fuel_eq {p : Point} {f : Nat} (hfuel : p.fuel = f + 1) (i : Nat) :
    (p.child i).fuel = f := by
  rw [Point.child_fuel, hfuel, Nat.add_sub_cancel]

theorem childWith_fuel_eq {p : Point} {f : Nat} (hfuel : p.fuel = f + 1) (i : Nat) (v : Val) :
    (p.childWith i v).fuel = f := by
  rw [Point.childWith_fuel, hfuel, Nat.add_sub_cancel]

section AmbientBindArm
variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}
  {available : Env.Requirement}
/-- The actual source bind uses the same shared guard arrow with both checked child requirements. -/
theorem bind_arm {a b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.bind a b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (ha : ChildDenotes root f a (p.path ++ [0])) (hb : ChildDenotes root f b (p.path ++ [1]))
    (coverage : Row.Subset ty.requires available)
    (saved : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.bind a b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_bind] at hcheck
  obtain ⟨tf, tr, hcf, hcr, rfl⟩ := Checker.inv_bind _ _ _ _ _ _ hcheck
  have requiredFirst : Row.Subset tf.requires available :=
    Row.subset_trans (Row.subset_union_left _ _) coverage
  have requiredNext : Row.Subset tr.requires available :=
    Row.subset_trans (Row.subset_union_right _ _) coverage
  rw [denoteR_bind _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_guardBind root
    (ha w htie (p.child 0) tf (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcf henv hview hstack) available requiredFirst
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl saved))
    (fun later ordered exit present payload => ?_) (fun later ordered exit payload absent => ?_)
    (Row.subset_refl _)
  · cases exit with
    | failure cause => exact Bool.noConfusion present
    | success value =>
      simp only [seqR]
      have member : Fits later value tf.answer := payload.1.1
      unfold constructR
      refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () trivial (fun after grew completed completedTyped => ?_)
        (Row.subset_refl _)
      have future := leHost_trans _ _ _ ordered grew
      have completedView : ∀ r ∈ completed, ∃ fty, after.Γ r.1 = some fty ∧
          ExitOk after fty r.2 := completedTyped
      refine ambientProg_widen root (before := (tr, available, available))
        (after := ((⟨tr.answer, tf.error.join tr.error, Row.union tf.requires tr.requires⟩ : EffTy),
          available, available))
        (Ty.subN_refl _) (Ty.subN_join_right _ _) (Row.subset_refl _) (Row.subset_refl _) ?_
      exact hb after (serviceTy_leHost future htie) ({ p with completed }.childWith 1 value) tr
        (childWith_fuel_eq (p := { p with completed }) hfuel 1 value) rfl
        (pointTyped_child (w := after) (q := { p with completed := completed }.childWith 1 value) hat rfl rfl hcr
          (envTyped_append (envTyped_mono future henv) (fits_mono grew member)) completedView
          (stackTyped_mono future hstack)) available requiredNext
        (ambientStackTyped_child (q := { p with completed }.childWith 1 value) hat rfl rfl
          (ambientStackTyped_mono future saved))
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Ty.subN_join_left _ _) payload.1, payload.2⟩
end AmbientBindArm
end Effect4.Program.Typed
