import Effect4.Laws.Program.Typed.FoldEval
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Codegen.ReadLeaf

/-!
# Laws.Program.Typed.ListFold — the list fold's rules as one statement

Concept: Store Typing (`store-typing`). Requirement: R4. The registry claim
`fold-typed-atomic-update` (decisions row 228) is `fold_typed_atomic_update`, a
`ListFoldRules`: the fold's scope, evaluation, failure, weakening and typing rules, its typed
evaluation over `Fits` in a fixed world, the printed and read equations of the leaf, and the
store step of one `Ref.modify` whose term the checker types.

The top node is a decomposition: its proof cites one theorem for each field, so its status is
derived from theirs (`#plan_status`). No field rests on a planned goal.

The statement holds the printed and read equations of the leaf (`readTerm_printTerm` and
`readTerm_exact`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`), so this module imports the
codegen's laws. The fields that read no printer are theorems of
`src/Effect4/Laws/Program/Typed/FoldEval.lean`. A consumer that needs one of them imports that
module, and no codegen module comes with it. The identity of a handle, which landed beside the
fold (decisions row 229), is `src/Effect4/Laws/Program/Typed/HandleIdentity.lean`.

Reach. The world is fixed in the fold's typed evaluation, and only `later` moves it. The
signature's atoms are the native table's (`sig.atomOf = nativeAtomTy`) where a field types a
term, and its declaration table is within the world's where a field reads membership: the empty
table at every world, or the source's at a world tied to it (`TyDecls.Within`). The store step is
`SyncOp.refModify`'s, at a cell that holds a member of the cell's type.

What it does not establish. Nothing about a module that uses the fold. No agreement with a
target: that a printed fold computes the model's answer on a host is a finite check
(`harness/truth`). No statement about a body that the checker refuses. No fairness and no
progress of a scheduler. The faces of a fold inside an operation's binder term are the state
plan's T5.

Consumers. The Queue's service pass reads the claim's `step` field through `syncRow_typed`
(`Typed/Denotation.lean`), and the store law of a step reads that field's theorem,
`refModify_typed_step`.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Codegen.Classes (Classes)

/-! ## The rules as one statement -/

/-- The rules of the list fold (decisions row 228; the design's F1), each over the tree's
definitions. `sig` is the signature that types a term, under its declaration table; the fields
that read membership at a world take the table within the world's (`TyDecls.Within`). -/
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
  /-- **Typing.** The list has a list type at the element's type `A`, read under the signature's
  table (`Checker.listOfIn`). The fold's type `B` is the stated type, or the initial value's type
  `B0` where none is stated. `B0` is below `B` in the checker's order. Under `B` at the fold's
  level and `A` one above it, the body's type is below `B`. -/
  typing : ∀ (env : TyEnv) (accTy : Option Ty) (list init body : Term) (B : Ty),
    termTy sig env (.fold accTy list init body) = some B →
      ∃ listType A B0 C, termTy sig env list = some listType ∧
        Checker.listOfIn sig.types listType = some A ∧
        termTy sig env init = some B0 ∧
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
  their types at a world whose table holds the signature's, answers, and its answer is a member
  of its type at that world. -/
  typed : sig.atomOf = nativeAtomTy → ∀ (w : World) (vals : List Val) (env : List Ty),
    TyDecls.Within sig.types w.types → FitsAll w vals env →
      ∀ (accTy : Option Ty) (list init body : Term) (B : Ty),
      termTy sig env (.fold accTy list init body) = some B →
        ∃ v, evalTerm vals (.fold accTy list init body) = some v ∧ Fits w v B
  /-- **Typed evaluation: preservation.** A fold that the checker types and that answers, over
  values that fit, answers a member of its type. It takes the answer as a premise and proves
  no answer: its premises differ from `typed`'s, and it is a separate theorem. -/
  preserved : sig.atomOf = nativeAtomTy → sig.constAtom = nativeConstAtom →
    ∀ (w : World) (vals : List Val) (env : List Ty), TyDecls.Within sig.types w.types →
      FitsAll w vals env →
      ∀ (accTy : Option Ty) (list init body : Term) (B : Ty) (v : Val),
        termTy sig env (.fold accTy list init body) = some B →
          evalTerm vals (.fold accTy list init body) = some v → Fits w v B
  /-- **One atomic step** (`refModify_typed_step`): the term may hold a fold. -/
  step : sig.atomOf = nativeAtomTy → ∀ (w : World) (tys : TyEnv) (env : List Val),
    TyDecls.Within sig.types w.types → EnvTyped w tys env → ∀ (f : Term) (A B : Ty),
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
`termTy_fold_invIn`, `fold_fits`, the fold's cases of `evalTerm_progress` and of
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
  typing := fun _ _ _ _ _ _ h => termTy_fold_invIn h
  semantic := fun _ _ _ _ _ _ _ _ _ _ hlist hvalue hinit hstart hbody =>
    fold_fits hlist hvalue hinit hstart hbody
  typed := fun hatom _ _ _ htypes hfit accTy list init body B hty =>
    evalTerm_progress hatom htypes hfit (.fold accTy list init body) B hty
  preserved := fun hatom hconst w vals env htypes hfit accTy list init body B v hty hev =>
    evalTerm_fitsAll sig hatom hconst w htypes (.fold accTy list init body) vals env B v hfit hty
      hev
  step := fun hatom _ _ _ htypes henv _ _ _ hty _ _ _ hcell ha =>
    refModify_typed_step hatom htypes henv hty hcell ha
  readPrint := fun _ _ term hs hc hu => readTerm_printTerm term hs hc hu
  readExact := fun _ _ x _ h => readTerm_exact x h

end Effect4.Program.Typed
