import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Typed.Adequacy
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Codegen.ReadLeaf

/-!
# Laws.Program.Typed.ListFold — the list fold's rules, and the identity of a handle

Concept: Store Typing (`store-typing`). Requirement: R4. Two registry claims
(`tools/Tools/SemanticsRegistry.lean`) have their statements here.

* **`fold-typed-atomic-update`** (decisions row 228) is `fold_typed_atomic_update`, a
  `ListFoldRules`: the fold's scope, evaluation, failure, weakening and typing rules, its typed
  evaluation over `Fits` in a fixed world, the printed and read equations of the leaf, and the
  store step of one `Ref.modify` whose term the checker types.
* **`handle-identity-laws`** (decisions row 229) is `handle_identity_laws`, a
  `HandleIdentityLaws`: the identity test's evaluation, its totality on two members of one
  handle type, its three order laws, a fresh handle's absence from every value that fits the
  earlier world, a later world's membership, and the containment of a term's handles.

Each top node is a decomposition: its proof cites one theorem for each field, so its status is
derived from theirs (`#plan_status`). No field rests on a planned goal.

Reach. The world is fixed in the fold's typed evaluation, and only `later` moves it. The
signature's atoms are the native table's (`sig.atomOf = nativeAtomTy`) where a field types a
term. The store step is `SyncOp.refModify`'s, at a cell that holds a member of the cell's type.
Freshness reads the world's declaration tables, and the allocation supplies the undeclared key
at typed cell columns (`CellsTyped`).

What they do not establish. Nothing about a module that uses the fold. No agreement with a
target: that a printed fold computes the model's answer on a host is a finite check
(`harness/truth`), and the correspondence of a handle's key with a host object is each target's
relation. No statement about a body that the checker refuses. No fairness and no progress of a
scheduler. The faces of a fold inside an operation's binder term are the state plan's T5.

Consumers. The Queue's service pass reads `ListFoldRules.step` through `syncRow_typed`
(`Typed/Denotation.lean`), and its withdrawal by identity reads `HandleIdentityLaws`.
-/

set_option autoImplicit false

/-! ## Evaluation under an inserted slot, and a refusing step -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- A lookup after one inserted slot: positions at or above the cut move up by one. The typing
weakening reads the same fact of type environments (`argTy_weaken`,
`src/Effect4/Program/Typing/Rules.lean`). -/
theorem getElem?_weaken {α : Type} (pre post : List α) (inserted : α) (index : Nat) :
    (pre ++ inserted :: post)[Var.weaken pre.length index]? = (pre ++ post)[index]? := by
  unfold Var.weaken
  split
  · next h => rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · next h =>
    have hge : pre.length ≤ index := Nat.le_of_not_lt h
    have hsucc : index + 1 - pre.length = index - pre.length + 1 := by omega
    rw [List.getElem?_append_right (Nat.le_succ_of_le hge), List.getElem?_append_right hge,
      hsucc, List.getElem?_cons_succ]

mutual
  /-- **Weakening of evaluation**: inserting one slot at a cut, with every variable at or above
  the cut moved up, keeps the whole result of a term's evaluation, refusal included. A fold
  needs no case of its own beyond its body's: the body's environment gains the two binders
  after the inserted slot, and the cut stays the prefix's length, so the same statement holds
  under them. A step of `fold-typed-atomic-update` (R4), beside the typing's `argTy_weaken`. -/
  theorem evalTerm_weaken (pre post : List Val) (inserted : Val) (term : Term) :
      evalTerm (pre ++ inserted :: post) (Term.weaken pre.length term) =
        evalTerm (pre ++ post) term :=
    match term with
    | .var index => getElem?_weaken pre post inserted index
    | .lit _ => rfl
    | .app atom args => by
      simp only [Term.weaken, evalTerm, evalTerms_weaken pre post inserted args]
    | .record fields names values => by
      simp only [Term.weaken, evalTerm, evalTerms_weaken pre post inserted values]
    | .field mode target name => by
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted target]
    | .recordSet target name value => by
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted target,
        evalTerm_weaken pre post inserted value]
    | .tupleAt target index => by
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted target]
    | .fold accTy list init body => by
      have hbody : ∀ acc item : Val,
          evalTerm ((pre ++ inserted :: post) ++ [acc, item]) (Term.weaken pre.length body) =
            evalTerm ((pre ++ post) ++ [acc, item]) body := fun acc item => by
        rw [List.append_assoc, List.cons_append, List.append_assoc]
        exact evalTerm_weaken pre (post ++ [acc, item]) inserted body
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted list,
        evalTerm_weaken pre post inserted init, hbody]

  theorem evalTerms_weaken (pre post : List Val) (inserted : Val) (terms : Terms) :
      evalTerms (pre ++ inserted :: post) (Terms.weaken pre.length terms) =
        evalTerms (pre ++ post) terms :=
    match terms with
    | .nil => rfl
    | .cons head tail => by
      simp only [Terms.weaken, evalTerms, evalTerm_weaken pre post inserted head,
        evalTerms_weaken pre post inserted tail]
end

/-- **A refusing step refuses the fold**: where the steps before an element answer and the
element's step refuses, the fold over the whole list refuses. No partial answer exists. -/
theorem foldlM_refuses {α β : Type} (step : β → α → Option β) :
    ∀ (xs ys : List α) (x : α) (acc a : β), xs.foldlM step acc = some a → step a x = none →
      (xs ++ x :: ys).foldlM step acc = none
  | [], ys, x, acc, a, h, hx => by
    have h' : some acc = some a := h
    cases h'
    show (step acc x).bind (fun next => ys.foldlM step next) = none
    rw [hx]
    rfl
  | y :: xs, ys, x, acc, a, h, hx => by
    have h' : (step acc y).bind (fun next => xs.foldlM step next) = some a := h
    obtain ⟨next, hnext, hrest⟩ := Option.bind_eq_some_iff.mp h'
    show (step acc y).bind (fun next => (xs ++ x :: ys).foldlM step next) = none
    rw [hnext]
    exact foldlM_refuses step xs ys x next a hrest hx

end Effect4.Program

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Codegen.Classes (Classes)

/-! ## The fold: one atomic step, and the rules as one statement -/

/-- **One atomic step.** A `Ref.modify` whose term the checker types at the node's environment
extended by the cell's type `A`, with the pair type of `B` and `A`, is one store step. At a
store whose cell holds a member `a` of `A`, the step reads the cell once and evaluates the term
once, at `env ++ [a]`. It answers the pair's first component, a member of `B`, and leaves the
second, a member of `A`, in the cell. The term may hold a fold: the whole fold is inside the
one evaluation. The term's map is `termMaps_of_typed`, and the step is the census clause
`refStep_modify`. It reads the fixed world `w` and no later one. -/
theorem refModify_typed_step {sig : Signature NativeOp} (hatom : sig.atomOf = nativeAtomTy)
    {w : World} {tys : TyEnv} {env : List Val} (henv : EnvTyped w tys env) {f : Term}
    {A B : Ty} (hty : termTy sig (tys ++ [A]) f = some (.prod B A)) {s : Stores}
    {cell : RefKey} {a : Val} (hcell : refPeek s.refs cell = some a) (ha : Fits w a A) :
    ∃ b a', evalTerm (env ++ [a]) f = some (Val.tuple [b, a']) ∧
      syncOpStep (.refModify cell f env) s =
        some ({ s with refs := refPoke s.refs cell a' }, b) ∧
      Fits w b B ∧ Fits w a' A := by
  obtain ⟨r, hr, hfit⟩ := termMaps_of_typed hatom henv hty w (leHost_refl w) a ha
  obtain ⟨b, a', rfl, hb, ha'⟩ := (fits_prod_iff w r B A).mp hfit
  refine ⟨b, a', hr, ?_, hb, ha'⟩
  show (refStep (.refModify cell f env) s.refs).map
    (fun step => ({ s with refs := step.2 }, step.1)) = _
  rw [refStep_modify s.refs cell f env a b a' hcell hr]
  rfl

/-- The rules of the list fold (decisions row 228; the design's F1), each over the tree's
definitions. `sig` is the signature that types a term. -/
structure ListFoldRules (sig : Signature NativeOp) : Prop where
  /-- **Scope.** The list and the initial value are scoped at the fold's level, and the body two
  levels up: it reads the accumulator at the level and the element one above it. -/
  scope : ∀ (n : Nat) (accTy : Option Ty) (list init body : Term),
    Term.scoped n (.fold accTy list init body) =
      (Term.scoped n list && Term.scoped n init && Term.scoped (n + 2) body)
  /-- **Scope, as an author writes it.** The builder keeps the authoring scope judgment. -/
  authored : ∀ (acc item : String) (accTy : Option Ty) (list init body : Authoring.TermSrc),
    list.Scoped → init.Scoped → body.Scoped →
      (Authoring.fold acc item accTy list init body).Scoped
  /-- **Evaluation and capture.** The list and the initial value are evaluated once. The body
  runs once for each element, from the head, at the environment extended by the accumulator
  and the element, so it reads every outer variable unchanged. The empty list answers the
  initial value. -/
  eval : ∀ (env : List Val) (accTy : Option Ty) (list init body : Term),
    evalTerm env (.fold accTy list init body) =
      (evalTerm env list).bind fun value => (Val.asList? value).bind fun items =>
        (evalTerm env init).bind fun start =>
          items.foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start
  /-- **Failure.** A step that refuses on one element refuses the whole fold. -/
  failure : ∀ (env : List Val) (body : Term) (xs ys : List Val) (x start acc : Val),
    xs.foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start = some acc →
      evalTerm (env ++ [acc, x]) body = none →
        (xs ++ x :: ys).foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start = none
  /-- **Weakening of evaluation**, for every term: a fold's binders move with the free
  variables. -/
  weakenEval : ∀ (pre post : List Val) (inserted : Val) (term : Term),
    evalTerm (pre ++ inserted :: post) (Term.weaken pre.length term) =
      evalTerm (pre ++ post) term
  /-- **Weakening of typing**, for every term. -/
  weakenTy : ∀ (pre post : TyEnv) (inserted : Ty) (term : Term),
    termTy sig (pre ++ inserted :: post) (Term.weaken pre.length term) =
      termTy sig (pre ++ post) term
  /-- **Typing.** The list has a list type at the element's type `A`. The fold's type `B` is
  the stated type, or the initial value's type `B0` where none is stated. `B0` is below `B` in
  the checker's order. Under `B` at the fold's level and `A` one above it, the body's type is
  below `B`. -/
  typing : ∀ (env : TyEnv) (accTy : Option Ty) (list init body : Term) (B : Ty),
    termTy sig env (.fold accTy list init body) = some B →
      ∃ A B0 C, termTy sig env list = some (.list A) ∧ termTy sig env init = some B0 ∧
        B = accTy.getD B0 ∧ Ty.subN B0 B = true ∧
        termTy sig (env ++ [B, A]) body = some C ∧ Ty.subN C B = true
  /-- **The semantic rule**, in a fixed world, with no rule of the checker. -/
  semantic : ∀ (w : World) (vals : List Val) (accTy : Option Ty) (list init body : Term)
    (A B : Ty) (value start : Val),
    evalTerm vals list = some value → Fits w value (.list A) →
    evalTerm vals init = some start → Fits w start B →
    (∀ acc x, Fits w acc B → Fits w x A →
      ∃ next, evalTerm (vals ++ [acc, x]) body = some next ∧ Fits w next B) →
    ∃ v, evalTerm vals (.fold accTy list init body) = some v ∧ Fits w v B
  /-- **Typed evaluation: progress.** A fold that the checker types, over values that fit
  their types at a world, answers, and its answer is a member of its type at that world. -/
  typed : sig.atomOf = nativeAtomTy → ∀ (w : World) (vals : List Val) (env : List Ty),
    FitsAll w vals env → ∀ (accTy : Option Ty) (list init body : Term) (B : Ty),
      termTy sig env (.fold accTy list init body) = some B →
        ∃ v, evalTerm vals (.fold accTy list init body) = some v ∧ Fits w v B
  /-- **Typed evaluation: preservation.** A fold that the checker types and that answers, over
  values that fit, answers a member of its type. It takes the answer as a premise and proves
  no answer: its premises differ from `typed`'s, and it is a separate theorem. -/
  preserved : sig.atomOf = nativeAtomTy → sig.constAtom = nativeConstAtom →
    ∀ (w : World) (vals : List Val) (env : List Ty), FitsAll w vals env →
      ∀ (accTy : Option Ty) (list init body : Term) (B : Ty) (v : Val),
        termTy sig env (.fold accTy list init body) = some B →
          evalTerm vals (.fold accTy list init body) = some v → Fits w v B
  /-- **One atomic step** (`refModify_typed_step`): the term may hold a fold. -/
  step : sig.atomOf = nativeAtomTy → ∀ (w : World) (tys : TyEnv) (env : List Val),
    EnvTyped w tys env → ∀ (f : Term) (A B : Ty),
      termTy sig (tys ++ [A]) f = some (.prod B A) →
        ∀ (s : Stores) (cell : RefKey) (a : Val), refPeek s.refs cell = some a → Fits w a A →
          ∃ b a', evalTerm (env ++ [a]) f = some (Val.tuple [b, a']) ∧
            syncOpStep (.refModify cell f env) s =
              some ({ s with refs := refPoke s.refs cell a' }, b) ∧
            Fits w b B ∧ Fits w a' A
  /-- **The printed equation of the leaf.** A scoped term whose class constructions are
  declared and whose folds state no accumulator type reads back from its image. -/
  readPrint : ∀ (classes : Classes) (n : Nat) (term : Term), Term.scoped n term = true →
    term.covers classes = true → term.unannotated = true →
      readTerm classes n (printTerm n term) = .ok term
  /-- **The read equation of the leaf.** What reads as a term is that term's image. -/
  readExact : ∀ (classes : Classes) (n : Nat) (x : TypeScript.Expr) (term : Term),
    readTerm classes n x = .ok term → printTerm n term = x

/-- **The list fold's rules hold** (the claim `fold-typed-atomic-update`), at every signature.
Each field is one theorem: the two definitional equations, the builder's scope law
(`Authoring.fold_scoped`), `foldlM_refuses`, `evalTerm_weaken`, `termTy_weaken`,
`termTy_fold_inv`, `fold_fits`, the fold's cases of `evalTerm_progress` and of
`evalTerm_fitsAll`, `refModify_typed_step`, and the fold's cases of `readTerm_printTerm` and
`readTerm_exact`.

It establishes nothing about a module that uses the fold and no agreement with a target. Its
consumer is the Queue's service pass (decisions row 228), on the M5 and M6 path through
`syncRow_typed`. -/
@[semantics "store-typing" (requirement := R4)]
theorem fold_typed_atomic_update (sig : Signature NativeOp) : ListFoldRules sig where
  scope := fun _ _ _ _ _ => rfl
  authored := fun acc item accTy _ _ _ hl hi hb => Authoring.fold_scoped acc item accTy hl hi hb
  eval := evalTerm_fold
  failure := fun env body xs ys x start acc hpre hx =>
    foldlM_refuses (fun acc item => evalTerm (env ++ [acc, item]) body) xs ys x start acc hpre hx
  weakenEval := evalTerm_weaken
  weakenTy := termTy_weaken sig
  typing := fun _ _ _ _ _ _ h => termTy_fold_inv h
  semantic := fun _ _ _ _ _ _ _ _ _ _ hlist hvalue hinit hstart hbody =>
    fold_fits hlist hvalue hinit hstart hbody
  typed := fun hatom _ _ _ hfit accTy list init body B hty =>
    evalTerm_progress hatom hfit (.fold accTy list init body) B hty
  preserved := fun hatom hconst w vals env hfit accTy list init body B v hty hev =>
    evalTerm_fitsAll sig hatom hconst w (.fold accTy list init body) vals env B v hfit hty hev
  step := fun hatom _ _ _ henv _ _ _ hty _ _ _ hcell ha =>
    refModify_typed_step hatom henv hty hcell ha
  readPrint := fun _ _ term hs hc hu => readTerm_printTerm term hs hc hu
  readExact := fun _ _ x _ h => readTerm_exact x h

/-! ## The identity of a handle -/

/-- The identity test on two handle frames: one kind byte compares the two keys, and two kinds
refuse. It reads no payload, no cell and no world. -/
theorem sameHandle_eval (kind kind' : UInt8) (index index' : Nat) :
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      if kind = kind' then some (Val.bool (decide (index = index'))) else none := rfl

/-- On two cells the test decides the equality of the two keys. -/
theorem sameHandle_cells (k k' : RefKey) :
    NativeAtom.eval .sameHandle [Val.cell k, Val.cell k'] = some (Val.bool (decide (k = k'))) := by
  have hdec : decide (k.index = k'.index) = decide (k = k') :=
    decide_eq_decide.mpr
      ⟨fun h => by cases k; cases k'; exact congrArg RefKey.mk h, fun h => congrArg RefKey.index h⟩
  show (if (2 : UInt8) = 2 then some (Val.bool (decide (k.index = k'.index))) else none) = _
  rw [if_pos rfl, hdec]

/-- On two Deferred cells the test decides the equality of the two keys. -/
theorem sameHandle_promises (k k' : DeferredKey) :
    NativeAtom.eval .sameHandle [Val.promise k, Val.promise k'] =
      some (Val.bool (decide (k = k'))) := by
  have hdec : decide (k.index = k'.index) = decide (k = k') :=
    decide_eq_decide.mpr
      ⟨fun h => by cases k; cases k'; exact congrArg DeferredKey.mk h,
        fun h => congrArg DeferredKey.index h⟩
  show (if (3 : UInt8) = 3 then some (Val.bool (decide (k.index = k'.index))) else none) = _
  rw [if_pos rfl, hdec]

/-- **Total on two members of `refOf`**, at any two payload types: the test answers, and its
answer decides the equality of the two keys. -/
theorem sameHandle_total_ref {w : World} {a b : Val} {A B : Ty} (ha : Fits w a (.refOf A))
    (hb : Fits w b (.refOf B)) :
    ∃ k k', a = Val.cell k ∧ b = Val.cell k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k'))) := by
  obtain ⟨k, rfl, _⟩ := fits_refOf_inv ha
  obtain ⟨k', rfl, _⟩ := fits_refOf_inv hb
  exact ⟨k, k', rfl, rfl, sameHandle_cells k k'⟩

/-- **Total on two members of `deferredOf`**, at any payload and error types. -/
theorem sameHandle_total_deferred {w : World} {a b : Val} {A E B F : Ty}
    (ha : Fits w a (.deferredOf A E)) (hb : Fits w b (.deferredOf B F)) :
    ∃ k k', a = Val.promise k ∧ b = Val.promise k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k'))) := by
  obtain ⟨k, rfl, _⟩ := fits_deferredOf_inv ha
  obtain ⟨k', rfl, _⟩ := fits_deferredOf_inv hb
  exact ⟨k, k', rfl, rfl, sameHandle_promises k k'⟩

/-- **Reflexive**: a handle is the same handle as itself. -/
theorem sameHandle_refl (kind : UInt8) (index : Nat) :
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind index] =
      some (Val.bool true) := by
  rw [sameHandle_eval, if_pos rfl, decide_eq_true rfl]

/-- **Symmetric**: the answer, a refusal of two kinds included, does not read the order. -/
theorem sameHandle_symm (kind kind' : UInt8) (index index' : Nat) :
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      NativeAtom.eval .sameHandle [.handle kind' index', .handle kind index] := by
  rw [sameHandle_eval, sameHandle_eval]
  by_cases hkind : kind = kind'
  · rw [if_pos hkind, if_pos hkind.symm,
      (decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩ : decide (index = index') = decide (index' = index))]
  · rw [if_neg hkind, if_neg (fun h => hkind h.symm)]

/-- **The allocation supplies a fresh cell**: at typed cell columns, the cell that `refMake`
answers is undeclared before the step. The key comes from the allocation itself, not from the
world's order. -/
theorem refMake_fresh {w : World} (cells : CellsTyped w) {value : Val} {state : Stores}
    {key : RefKey} (step : syncOpStep (.refMake value) w.state = some (state, Val.cell key)) :
    w.Ρ key = none := by
  rw [syncOpStep_refMake, Option.some.injEq, Prod.mk.injEq] at step
  obtain rfl := cell_inj step.2
  cases h : w.Ρ ⟨w.state.refs.length⟩ with
  | none => rfl
  | some t =>
    have hlt := (cells.heap ⟨w.state.refs.length⟩).mp (by rw [h]; rfl)
    exact absurd hlt (Nat.lt_irrefl _)

/-- **The allocation supplies a fresh Deferred cell**, as `refMake_fresh`. -/
theorem deferredMake_fresh {w : World} (cells : CellsTyped w) {state : Stores}
    {key : DeferredKey} (step : syncOpStep .deferredMake w.state = some (state, Val.promise key)) :
    w.«Π» key = none := by
  rw [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at step
  obtain rfl := promise_inj step.2
  exact cells.promise_fresh

/-- **A fresh cell is the same handle as no handle of a value that fits the earlier world**, at
any type and any depth of nesting: every raw handle frame of a member is live in its kind's
column (`fits_live`), and the fresh cell is declared in none. -/
theorem sameHandle_fresh_cell {w : World} {key : RefKey} (fresh : w.Ρ key = none) {v : Val}
    {ty : Ty} (hv : Fits w v ty) (kind : UInt8) (index : Nat)
    (hmem : (kind, index) ∈ Store.Val.handles v) :
    NativeAtom.eval .sameHandle [Val.cell key, .handle kind index] ≠ some (Val.bool true) := by
  intro heq
  have heq' : (if (2 : UInt8) = kind then some (Val.bool (decide (key.index = index)))
      else none) = some (Val.bool true) := heq
  split at heq'
  · next hkind =>
    by_cases hidx : key.index = index
    · have hlive : KindLive w index (HandleKind.ofByte? kind) :=
        fits_live w ty v hv (kind, index) hmem
      have hcellKind : HandleKind.ofByte? 2 = some .cell := HandleKind.ofByte?_byte .cell
      rw [← hkind, hcellKind] at hlive
      have hdecl : (w.Ρ ⟨index⟩).isSome = true := hlive
      have hkey : (⟨index⟩ : RefKey) = key := by
        cases key
        exact congrArg RefKey.mk hidx.symm
      rw [hkey, fresh] at hdecl
      cases hdecl
    · rw [decide_eq_false hidx] at heq'
      cases heq'
  · cases heq'

/-- **A fresh Deferred cell is the same handle as no handle of a value that fits the earlier
world**, as `sameHandle_fresh_cell`. -/
theorem sameHandle_fresh_promise {w : World} {key : DeferredKey} (fresh : w.«Π» key = none)
    {v : Val} {ty : Ty} (hv : Fits w v ty) (kind : UInt8) (index : Nat)
    (hmem : (kind, index) ∈ Store.Val.handles v) :
    NativeAtom.eval .sameHandle [Val.promise key, .handle kind index] ≠ some (Val.bool true) := by
  intro heq
  have heq' : (if (3 : UInt8) = kind then some (Val.bool (decide (key.index = index)))
      else none) = some (Val.bool true) := heq
  split at heq'
  · next hkind =>
    by_cases hidx : key.index = index
    · have hlive : KindLive w index (HandleKind.ofByte? kind) :=
        fits_live w ty v hv (kind, index) hmem
      have hpromiseKind : HandleKind.ofByte? 3 = some .promise := HandleKind.ofByte?_byte .promise
      rw [← hkind, hpromiseKind] at hlive
      have hdecl : (w.«Π» ⟨index⟩).isSome = true := hlive
      have hkey : (⟨index⟩ : DeferredKey) = key := by
        cases key
        exact congrArg DeferredKey.mk hidx.symm
      rw [hkey, fresh] at hdecl
      cases hdecl
    · rw [decide_eq_false hidx] at heq'
      cases heq'
  · cases heq'

/-- **A fresh cell is a member of no stored list of cells**: on every element of a list that
fits the earlier world, the test answers `false`. -/
theorem fresh_cell_not_member {w : World} {key : RefKey} (fresh : w.Ρ key = none) {v : Val}
    {A : Ty} (hv : Fits w v (.list (.refOf A))) :
    ∃ xs, Val.asList? v = some xs ∧
      ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.cell key, x] = some (Val.bool false) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp hv
  refine ⟨xs, hxs, fun x hx => ?_⟩
  obtain ⟨k', rfl, t', hdecl, _⟩ := fits_refOf_inv (hall x hx)
  have hne : ¬ key = k' := fun e => by
    rw [e, hdecl] at fresh
    cases fresh
  rw [sameHandle_cells, decide_eq_false hne]

/-- **A fresh Deferred cell is a member of no stored list of Deferred cells.** -/
theorem fresh_promise_not_member {w : World} {key : DeferredKey} (fresh : w.«Π» key = none)
    {v : Val} {A E : Ty} (hv : Fits w v (.list (.deferredOf A E))) :
    ∃ xs, Val.asList? v = some xs ∧
      ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.promise key, x] = some (Val.bool false) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp hv
  refine ⟨xs, hxs, fun x hx => ?_⟩
  obtain ⟨k', rfl, a', e', hdecl, _⟩ := fits_deferredOf_inv (hall x hx)
  have hne : ¬ key = k' := fun e => by
    rw [e, hdecl] at fresh
    cases fresh
  rw [sameHandle_promises, decide_eq_false hne]

/-- **A later world keeps a list's membership and each element's**: the decoded elements are the
value's own, read with no world, and each fits at the later world (`fits_mono`). The identity
test reads no world, so every answer it gave is its answer there. -/
theorem list_later {w w' : World} (ord : w.leHost w') {v : Val} {H : Ty}
    (hv : Fits w v (.list H)) :
    Fits w' v (.list H) ∧ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w' x H := by
  have hv' := fits_mono ord hv
  exact ⟨hv', (fits_list_iff w' v H).mp hv'⟩

/-- The laws of a handle's identity in a term (decisions row 229; the design's F4), over `Fits`
and the world's order. -/
structure HandleIdentityLaws : Prop where
  /-- **The test.** One kind byte compares the two keys, and two kinds refuse. It reads no
  payload, no cell and no world. -/
  eval : ∀ (kind kind' : UInt8) (index index' : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      if kind = kind' then some (Val.bool (decide (index = index'))) else none
  /-- **Law 1 and the decision of law 2**, at `refOf`: total at any two payload types, and the
  answer decides the equality of the two keys. -/
  totalRef : ∀ (w : World) (a b : Val) (A B : Ty), Fits w a (.refOf A) → Fits w b (.refOf B) →
    ∃ k k', a = Val.cell k ∧ b = Val.cell k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k')))
  /-- The same at `deferredOf`. -/
  totalDeferred : ∀ (w : World) (a b : Val) (A E B F : Ty), Fits w a (.deferredOf A E) →
    Fits w b (.deferredOf B F) →
      ∃ k k', a = Val.promise k ∧ b = Val.promise k' ∧
        NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k')))
  /-- **Law 2, reflexive.** -/
  refl : ∀ (kind : UInt8) (index : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind index] = some (Val.bool true)
  /-- **Law 2, symmetric.** -/
  symm : ∀ (kind kind' : UInt8) (index index' : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      NativeAtom.eval .sameHandle [.handle kind' index', .handle kind index]
  /-- **Law 3, the allocation.** The cell that `refMake` answers is undeclared before it. -/
  allocRef : ∀ (w : World), CellsTyped w → ∀ (value : Val) (state : Stores) (key : RefKey),
    syncOpStep (.refMake value) w.state = some (state, Val.cell key) → w.Ρ key = none
  /-- The same for `deferredMake`. -/
  allocDeferred : ∀ (w : World), CellsTyped w → ∀ (state : Stores) (key : DeferredKey),
    syncOpStep .deferredMake w.state = some (state, Val.promise key) → w.«Π» key = none
  /-- **Law 3, a fresh cell.** It is the same handle as no handle of a value that fits the
  earlier world. -/
  freshRef : ∀ (w : World) (key : RefKey), w.Ρ key = none → ∀ (v : Val) (ty : Ty),
    Fits w v ty → ∀ (kind : UInt8) (index : Nat), (kind, index) ∈ Store.Val.handles v →
      NativeAtom.eval .sameHandle [Val.cell key, .handle kind index] ≠ some (Val.bool true)
  /-- The same for a fresh Deferred cell. -/
  freshDeferred : ∀ (w : World) (key : DeferredKey), w.«Π» key = none → ∀ (v : Val) (ty : Ty),
    Fits w v ty → ∀ (kind : UInt8) (index : Nat), (kind, index) ∈ Store.Val.handles v →
      NativeAtom.eval .sameHandle [Val.promise key, .handle kind index] ≠ some (Val.bool true)
  /-- **Law 3, a stored list.** A fresh cell is a member of no stored list of cells. -/
  notMemberRef : ∀ (w : World) (key : RefKey), w.Ρ key = none → ∀ (v : Val) (A : Ty),
    Fits w v (.list (.refOf A)) →
      ∃ xs, Val.asList? v = some xs ∧
        ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.cell key, x] = some (Val.bool false)
  /-- The same for a fresh Deferred cell. -/
  notMemberDeferred : ∀ (w : World) (key : DeferredKey), w.«Π» key = none →
    ∀ (v : Val) (A E : Ty), Fits w v (.list (.deferredOf A E)) →
      ∃ xs, Val.asList? v = some xs ∧
        ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.promise key, x] = some (Val.bool false)
  /-- **Law 4.** A later world keeps a list's membership and each element's. The test reads no
  world (`eval`), so a later world keeps every answer. -/
  later : ∀ (w w' : World), w.leHost w' → ∀ (v : Val) (H : Ty), Fits w v (.list H) →
    Fits w' v (.list H) ∧ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w' x H
  /-- **Law 5.** The handles of a term's answer are handles of its environment, a fold's
  answer included. It needs successful evaluation and no typing. -/
  contained : ∀ (term : Term) (env : List Val) (v : Val), evalTerm env term = some v →
    Store.Val.handles v ⊆ env.flatMap Store.Val.handles

/-- **The laws of a handle's identity hold** (the claim `handle-identity-laws`). Each field is
one theorem: `sameHandle_eval`, the two totality theorems, `sameHandle_refl`,
`sameHandle_symm`, the two allocation facts, the two freshness theorems and their two list
forms, `list_later`, and `RawHandles.evalTerm_handles` with its fold case.

It establishes no correspondence in a target: that two handles have equal keys exactly when
their host objects are one object is each target's relation. Its consumer is the Queue's
withdrawal by identity (decisions row 229). -/
@[semantics "store-typing" (requirement := R4)]
theorem handle_identity_laws : HandleIdentityLaws where
  eval := sameHandle_eval
  totalRef := fun _ _ _ _ _ ha hb => sameHandle_total_ref ha hb
  totalDeferred := fun _ _ _ _ _ _ _ ha hb => sameHandle_total_deferred ha hb
  refl := sameHandle_refl
  symm := sameHandle_symm
  allocRef := fun _ cells _ _ _ step => refMake_fresh cells step
  allocDeferred := fun _ cells _ _ step => deferredMake_fresh cells step
  freshRef := fun _ _ fresh _ _ hv kind index hmem => sameHandle_fresh_cell fresh hv kind index hmem
  freshDeferred := fun _ _ fresh _ _ hv kind index hmem =>
    sameHandle_fresh_promise fresh hv kind index hmem
  notMemberRef := fun _ _ fresh _ _ hv => fresh_cell_not_member fresh hv
  notMemberDeferred := fun _ _ fresh _ _ _ hv => fresh_promise_not_member fresh hv
  later := fun _ _ ord _ _ hv => list_later ord hv
  contained := RawHandles.evalTerm_handles

end Effect4.Program.Typed
