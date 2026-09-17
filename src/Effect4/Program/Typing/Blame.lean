import Effect4.Program.Typing

/-!
# Program.Typing.Blame — the one checker's refusal, located (DI-86)

`effTy` answers `Option EffTy`: a refusal is `none`, with no position and no reason. This
module is a projection over that checker, not a second one. `explainEff` follows every arm
of `effTy` in the same order, asking `effTy` itself about each child at the environment the
arm gives it: the first child the checker refuses is where the refusal is (the projection
descends into it, so the located node is the deepest refused one whose children all type),
and a node whose children type but whose own rule refuses names its reason in the rule's
own terms (a term with no type, a request outside the row's request, a predicate that is
not `bool`, a bare layer reference, a `return` that is not last, …). Paths are `Node.child`
indices, the same addressing the authoring refusals and the layer references use.

The law is `explain_none_iff`: `explain` answers `none` exactly when `effTy` answers, so
the projection cannot drift from the checker without the proof breaking. The checker's
statement and its two agreement theorems do not move.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)

/-- Why the checker refused at a node, in the node's own rule's terms. -/
inductive TypeReason
  /-- A term with no type in this environment: an unbound level, an atom the signature
  refuses at these argument types, a literal outside the value alphabet. -/
  | term (t : Term)
  | cause (c : CauseTerm)
  /-- `fail` or `yieldError` at a type the error alphabet does not admit. -/
  | errorNotAdmitted (error : Ty)
  /-- The row is outside the signature's domain (DI-54). -/
  | outsideDomain (row : String)
  /-- A `callback` on a row that is not `async`. -/
  | notAsync (row : String)
  /-- The request is not a subtype of the row's request (DI-15). -/
  | requestNotSubtype (row : String) (request expected : Ty)
  | predicateNotBool (t : Ty)
  /-- A `select` whose decision cannot select on the scrutinee's type (`Decision.arms`
  answers `none`): a non-option under `.option`, a column that is not tagged or carries no
  member of the tag under `.tag`. Under `.bool` the refusal is `predicateNotBool`, the
  conditional's own reason (`selectRefusal`). -/
  | notSelectable (decision : Decision) (scrutinee : Ty)
  /-- A loop's step does not have the cursor's type. -/
  | stepNotCursor (step cursor : Ty)
  /-- An `iterate`'s initial cursor is not under the cursor's annotation. -/
  | initialNotCursor (initial cursor : Ty)
  | notFiber (t : Ty)
  | scopeExpected (t : Ty)
  | natExpected (t : Ty)
  | listOfFibersExpected (t : Ty)
  | contextExpected (t : Ty)
  | snapshotExpected (t : Ty)
  | exitExpected (t : Ty)
  /-- The signature types no service under this key. -/
  | serviceUnknown (key : ServiceKey)
  /-- The provided value is not a subtype of the key's carrier (DI-15). -/
  | valueNotSubtype (key : ServiceKey) (value carrier : Ty)
  /-- A bare reference is typed by the whole program after expansion, never structurally. -/
  | layerReference (target : List Nat)
  /-- A reference of the whole program is ill formed (`Eff.layerRefsWF`): its target is not a
  preceding non-reference layer. Reported at the root by the facade. -/
  | referencesIllFormed
  | mergeAllEmpty
  | returnNotLast
  | breakOutsideLoop
  | literalOutsideAlphabet (value : Lit)
deriving DecidableEq

/-- The constructor's name: the reason as one word, for tables and reports. -/
def TypeReason.head : TypeReason → String
  | .term _ => "term"
  | .cause _ => "cause"
  | .errorNotAdmitted _ => "errorNotAdmitted"
  | .outsideDomain _ => "outsideDomain"
  | .notAsync _ => "notAsync"
  | .requestNotSubtype _ _ _ => "requestNotSubtype"
  | .predicateNotBool _ => "predicateNotBool"
  | .notSelectable _ _ => "notSelectable"
  | .stepNotCursor _ _ => "stepNotCursor"
  | .initialNotCursor _ _ => "initialNotCursor"
  | .notFiber _ => "notFiber"
  | .scopeExpected _ => "scopeExpected"
  | .natExpected _ => "natExpected"
  | .listOfFibersExpected _ => "listOfFibersExpected"
  | .contextExpected _ => "contextExpected"
  | .snapshotExpected _ => "snapshotExpected"
  | .exitExpected _ => "exitExpected"
  | .serviceUnknown _ => "serviceUnknown"
  | .valueNotSubtype _ _ _ => "valueNotSubtype"
  | .layerReference _ => "layerReference"
  | .referencesIllFormed => "referencesIllFormed"
  | .mergeAllEmpty => "mergeAllEmpty"
  | .returnNotLast => "returnNotLast"
  | .breakOutsideLoop => "breakOutsideLoop"
  | .literalOutsideAlphabet _ => "literalOutsideAlphabet"

/-- A refusal at a path of the tree. -/
structure TypeRefusal where
  path : List Nat
  reason : TypeReason
deriving DecidableEq

variable {Op : Type}

/-- A term's refusal at a node, when it has no type. -/
def termRefusal (sig : Signature Op) (env : TyEnv) (p : List Nat) (t : Term) : Option TypeRefusal :=
  if (termTy sig env t).isSome then none else some ⟨p, .term t⟩

/-- Why a `select` refuses its scrutinee's type: under `.bool` it is the conditional on a
non-Boolean, which TypeScript accepts (no diagnostic); under the other two decisions the
argument is not assignable. -/
def selectRefusal : Decision → Ty → TypeReason
  | .bool, t => .predicateNotBool t
  | .option, t => .notSelectable .option t
  | .tag name, t => .notSelectable (.tag name) t

mutual
  /-- The checker's refusal under a program, located; `none` exactly when `effTy` answers. -/
  def explainEff (sig : Signature Op) (env : TyEnv) (p : List Nat) : Eff Op → Option TypeRefusal
    | .succeed value => termRefusal sig env p value
    | .fail error =>
      match termTy sig env error with
      | none => some ⟨p, .term error⟩
      | some e => if admittedErrTy e then none else some ⟨p, .errorNotAdmitted e⟩
    | .failCause cause => if (causeTy sig env cause).isSome then none else some ⟨p, .cause cause⟩
    | .yieldError error =>
      match termTy sig env error with
      | none => some ⟨p, .term error⟩
      | some e => if admittedErrTy e then none else some ⟨p, .errorNotAdmitted e⟩
    | .sync thunk => termRefusal sig env p thunk
    | .suspend body => explainEff sig env (p ++ [0]) body
    | .perform op request =>
      match termTy sig env request with
      | none => some ⟨p, .term request⟩
      | some r =>
        let row := sig.rowOf op
        if sig.dom op = false then some ⟨p, .outsideDomain row.name⟩
        else if Ty.sub r.normalize row.request.normalize then none
        else some ⟨p, .requestNotSubtype row.name r row.request⟩
    | .bind first rest =>
      match effTy sig env first with
      | none => explainEff sig env (p ++ [0]) first
      | some f => explainEff sig (env ++ [f.answer]) (p ++ [1]) rest
    | .gen body => explainStmts sig env false (p ++ [0]) body
    | .catchCause body handler =>
      match effTy sig env body with
      | none => explainEff sig env (p ++ [0]) body
      | some b => explainEff sig (env ++ [.causeOf b.error]) (p ++ [1]) handler
    | .catchIf test body handler =>
      match effTy sig env body with
      | none => explainEff sig env (p ++ [0]) body
      | some b =>
        match termTy sig (env ++ [b.error]) test with
        | none => some ⟨p, .term test⟩
        | some predicate =>
          if predicate = .bool then explainEff sig (env ++ [b.error]) (p ++ [1]) handler
          else some ⟨p, .predicateNotBool predicate⟩
    | .matchCause body onValue onCause =>
      match effTy sig env body with
      | none => explainEff sig env (p ++ [0]) body
      | some b =>
        match effTy sig (env ++ [b.answer]) onValue with
        | none => explainEff sig (env ++ [b.answer]) (p ++ [1]) onValue
        | some _ => explainEff sig (env ++ [.causeOf b.error]) (p ++ [2]) onCause
    | .onExit body finalizer =>
      match effTy sig env body with
      | none => explainEff sig env (p ++ [0]) body
      | some b => explainEff sig (env ++ [.exitOf b.answer b.error]) (p ++ [1]) finalizer
    | .exit body => explainEff sig env (p ++ [0]) body
    | .uninterruptible body => explainEff sig env (p ++ [0]) body
    | .interruptible body => explainEff sig env (p ++ [0]) body
    | .select s d a0 a1 =>
      match termTy sig env s with
      | none => some ⟨p, .term s⟩
      | some t =>
        match d.arms t with
        | none => some ⟨p, selectRefusal d t⟩
        | some (e0, e1) =>
          match effTy sig (env ++ e0) a0 with
          | none => explainEff sig (env ++ e0) (p ++ [0]) a0
          | some _ => explainEff sig (env ++ e1) (p ++ [1]) a1
    | .whileLoop initial test step body =>
      match termTy sig env initial with
      | none => some ⟨p, .term initial⟩
      | some cursor =>
        match termTy sig (env ++ [cursor]) test with
        | none => some ⟨p, .term test⟩
        | some t =>
          match effTy sig (env ++ [cursor]) body with
          | none => explainEff sig (env ++ [cursor]) (p ++ [0]) body
          | some b =>
            match termTy sig (env ++ [cursor, b.answer]) step with
            | none => some ⟨p, .term step⟩
            | some s =>
              if t = .bool ∧ s = cursor then none
              else if t = .bool then some ⟨p, .stepNotCursor s cursor⟩
              else some ⟨p, .predicateNotBool t⟩
    | .iterate cursor initial test step result body =>
      match termTy sig env initial with
      | none => some ⟨p, .term initial⟩
      | some c0 =>
        match termTy sig (env ++ [cursor]) test with
        | none => some ⟨p, .term test⟩
        | some t =>
          match effTy sig (env ++ [cursor]) body with
          | none => explainEff sig (env ++ [cursor]) (p ++ [0]) body
          | some b =>
            match termTy sig (env ++ [cursor, b.answer]) step with
            | none => some ⟨p, .term step⟩
            | some c1 =>
              match termTy sig (env ++ [cursor]) result with
              | none => some ⟨p, .term result⟩
              | some _ =>
                if t = .bool ∧ Ty.sub c0.normalize cursor.normalize = true
                    ∧ Ty.sub c1.normalize cursor.normalize = true then none
                else if ¬ t = .bool then some ⟨p, .predicateNotBool t⟩
                else if Ty.sub c0.normalize cursor.normalize = true then
                  some ⟨p, .stepNotCursor c1 cursor⟩
                else some ⟨p, .initialNotCursor c0 cursor⟩
    | .yieldNow _ => none
    | .callback register request =>
      match termTy sig env request with
      | none => some ⟨p, .term request⟩
      | some r =>
        let row := sig.rowOf register
        if sig.dom register = false then some ⟨p, .outsideDomain row.name⟩
        else if row.kind ≠ .async then some ⟨p, .notAsync row.name⟩
        else if Ty.sub r.normalize row.request.normalize then none
        else some ⟨p, .requestNotSubtype row.name r row.request⟩
    | .awaitFiber fiber _ =>
      match termTy sig env fiber with
      | none => some ⟨p, .term fiber⟩
      | some t => if (fiberTy t).isSome then none else some ⟨p, .notFiber t⟩
    | .withFiber action => explainAction sig env (p ++ [0]) action
    | .scoped body => explainEff sig env (p ++ [0]) body
    | .acquireRelease acquire release =>
      match effTy sig env acquire with
      | none => explainEff sig env (p ++ [0]) acquire
      | some a => explainEff sig (env ++ [a.answer, .exitOf a.answer a.error]) (p ++ [1]) release
    | .provideLayer layer _ body =>
      match layerTy sig layer with
      | none => explainLayer sig (p ++ [0]) layer
      | some _ => explainEff sig env (p ++ [1]) body
    | .service key => if (sig.serviceTy key).isSome then none else some ⟨p, .serviceUnknown key⟩
    | .provideService key value body =>
      match sig.serviceTy key with
      | none => some ⟨p, .serviceUnknown key⟩
      | some ty =>
        match termTy sig env value with
        | none => some ⟨p, .term value⟩
        | some v =>
          match effTy sig env body with
          | none => explainEff sig env (p ++ [0]) body
          | some _ =>
            if Ty.sub v.normalize ty.normalize then none
            else some ⟨p, .valueNotSubtype key v ty⟩

  def explainLayer (sig : Signature Op) (p : List Nat) : LayerTerm Op → Option TypeRefusal
    | .succeed _ value =>
      if (litVal value).isSome then none else some ⟨p, .literalOutsideAlphabet value⟩
    | .effect _ body => explainEff sig [] (p ++ [0]) body
    | .effectDiscard body => explainEff sig [] (p ++ [0]) body
    | .provide self that =>
      match layerTy sig self with
      | none => explainLayer sig (p ++ [0]) self
      | some _ => explainLayer sig (p ++ [1]) that
    | .provideMerge self that =>
      match layerTy sig self with
      | none => explainLayer sig (p ++ [0]) self
      | some _ => explainLayer sig (p ++ [1]) that
    | .merge left right =>
      match layerTy sig left with
      | none => explainLayer sig (p ++ [0]) left
      | some _ => explainLayer sig (p ++ [1]) right
    | .fresh inner => explainLayer sig (p ++ [0]) inner
    | .orDie inner => explainLayer sig (p ++ [0]) inner
    | .ref target => some ⟨p, .layerReference target⟩
    | .mergeAll layers => explainLayers sig (p ++ [0]) layers

  def explainLayers (sig : Signature Op) (p : List Nat) : LayerTerms Op → Option TypeRefusal
    | .nil => some ⟨p, .mergeAllEmpty⟩
    | .cons head .nil => explainLayer sig (p ++ [0]) head
    | .cons head tail =>
      match layerTy sig head with
      | none => explainLayer sig (p ++ [0]) head
      | some _ => explainLayers sig (p ++ [1]) tail

  def explainStmts (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat) :
      Stmts Op → Option TypeRefusal
    | .nil => none
    | .cons (.bindYield effect) rest =>
      match effTy sig env effect with
      | none => explainEff sig env (p ++ [0, 0]) effect
      | some t => explainStmts sig (env ++ [t.answer]) inLoop (p ++ [1]) rest
    | .cons (.yieldDiscard effect) rest =>
      match effTy sig env effect with
      | none => explainEff sig env (p ++ [0, 0]) effect
      | some _ => explainStmts sig env inLoop (p ++ [1]) rest
    | .cons (.ret value) rest =>
      match rest with
      | .nil => termRefusal sig env (p ++ [0]) value
      | .cons _ _ => some ⟨p ++ [0], .returnNotLast⟩
    | .cons (.ifElse test thenB elseB) rest =>
      match termTy sig env test with
      | none => some ⟨p ++ [0], .term test⟩
      | some t =>
        if t = .bool then
          match stmtsTy sig env inLoop thenB with
          | none => explainStmts sig env inLoop (p ++ [0, 0]) thenB
          | some _ =>
            match stmtsTy sig env inLoop elseB with
            | none => explainStmts sig env inLoop (p ++ [0, 1]) elseB
            | some _ => explainStmts sig env inLoop (p ++ [1]) rest
        else some ⟨p ++ [0], .predicateNotBool t⟩
    | .cons (.whileTrue body) rest =>
      match stmtsTy sig env true body with
      | none => explainStmts sig env true (p ++ [0, 0]) body
      | some _ => explainStmts sig env inLoop (p ++ [1]) rest
    | .cons .breakLoop rest =>
      if inLoop then explainStmts sig env inLoop (p ++ [1]) rest
      else some ⟨p ++ [0], .breakOutsideLoop⟩

  def explainEffs (sig : Signature Op) (env : TyEnv) (p : List Nat) : Effs Op → Option TypeRefusal
    | .nil => none
    | .cons head tail =>
      match effTy sig env head with
      | none => explainEff sig env (p ++ [0]) head
      | some _ => explainEffs sig env (p ++ [1]) tail

  def explainAction (sig : Signature Op) (env : TyEnv) (p : List Nat) :
      ActionTerm Op → Option TypeRefusal
    | .fork program _ => explainEff sig env (p ++ [0]) program
    | .forkIn program _ scope =>
      match effTy sig env program with
      | none => explainEff sig env (p ++ [0]) program
      | some _ =>
        match termTy sig env scope with
        | none => some ⟨p, .term scope⟩
        | some s => if s = Ty.scope then none else some ⟨p, .scopeExpected s⟩
    | .forkScoped program _ => explainEff sig env (p ++ [0]) program
    | .runIn target scope =>
      match termTy sig env target with
      | none => some ⟨p, .term target⟩
      | some t =>
        if (fiberTy t).isNone then some ⟨p, .notFiber t⟩
        else
          match termTy sig env scope with
          | none => some ⟨p, .term scope⟩
          | some s => if s = Ty.scope then none else some ⟨p, .scopeExpected s⟩
    | .interrupt target =>
      match termTy sig env target with
      | none => some ⟨p, .term target⟩
      | some t => if (fiberTy t).isSome then none else some ⟨p, .notFiber t⟩
    | .interruptScoped target =>
      match termTy sig env target with
      | none => some ⟨p, .term target⟩
      | some t => if (fiberTy t).isSome then none else some ⟨p, .notFiber t⟩
    | .interruptAll targets interruptor =>
      match termTy sig env targets with
      | none => some ⟨p, .term targets⟩
      | some ts =>
        match ts with
        | .list inner =>
          if (fiberTy inner).isNone then some ⟨p, .notFiber inner⟩
          else
            match interruptor with
            | none => none
            | some who =>
              match termTy sig env who with
              | none => some ⟨p, .term who⟩
              | some w => if w = .nat then none else some ⟨p, .natExpected w⟩
        | _ => some ⟨p, .listOfFibersExpected ts⟩
    | .awaitAll targets =>
      match termTy sig env targets with
      | none => some ⟨p, .term targets⟩
      | some ts =>
        match ts with
        | .list inner => if (fiberTy inner).isSome then none else some ⟨p, .notFiber inner⟩
        | _ => some ⟨p, .listOfFibersExpected ts⟩
    | .awaitAllFailFast targets =>
      match termTy sig env targets with
      | none => some ⟨p, .term targets⟩
      | some ts =>
        match ts with
        | .list inner => if (fiberTy inner).isSome then none else some ⟨p, .notFiber inner⟩
        | _ => some ⟨p, .listOfFibersExpected ts⟩
    | .snapshotChildren => none
    | .awaitNewChildren snapshot =>
      match termTy sig env snapshot with
      | none => some ⟨p, .term snapshot⟩
      | some s =>
        if s = .list (.fiberOf (.handle "unknown") (.handle "unknown")) then none
        else some ⟨p, .snapshotExpected s⟩
    | .raceAll entrants => explainEffs sig env (p ++ [0]) entrants
    | .setContext context =>
      match termTy sig env context with
      | none => some ⟨p, .term context⟩
      | some c => if c = Ty.context then none else some ⟨p, .contextExpected c⟩
    | .getContext => none
    | .getId => none
    | .closeScope scope exit =>
      match termTy sig env scope with
      | none => some ⟨p, .term scope⟩
      | some s =>
        match termTy sig env exit with
        | none => some ⟨p, .term exit⟩
        | some e =>
          match e with
          | .exitOf _ _ => if s = Ty.scope then none else some ⟨p, .scopeExpected s⟩
          | _ => some ⟨p, .exitExpected e⟩
end

/-- The checker's refusal of a program at an environment, located from the root; `none`
exactly when `effTy` answers. -/
def explain (sig : Signature Op) (env : TyEnv) (e : Eff Op) : Option TypeRefusal :=
  explainEff sig env [] e

/-- The path of the node the checker refuses: the deepest refused node whose children type. -/
def blame (sig : Signature Op) (env : TyEnv) (e : Eff Op) : Option (List Nat) :=
  (explain sig env e).map (·.path)

/-! ## The law of the projection (DI-86)

`explain` answers `none` exactly when `effTy` answers, at every sort and every environment:
the located refusal is a projection of the one checker, and this law is what keeps it one.
It lives beside the definition because the facade's `Api.check` needs it to be total (the
application root never reaches `Effect4.Laws`). Each arm unfolds both sides, splits every
match on the same discriminants the checker matches on, and closes with the children's laws.
-/

/-- The checker's `do` chains end in `some`: their success is the last bound option's. -/
@[simp] private theorem isSome_bind_some {α β : Type} (x : Option α) (f : α → β) :
    (x.bind fun r => some (f r)).isSome = x.isSome := by
  cases x <;> rfl

@[simp] private theorem isSome_ite_some_none {α : Type} (c : Prop) [Decidable c] (x : α) :
    (if c then some x else none).isSome = decide c := by
  split <;> simp_all

/-- A bound option whose continuation always succeeds succeeds exactly when it does. -/
@[simp] private theorem isSome_bind_of_forall {α β : Type} (x : Option α) (f : α → Option β)
    (h : ∀ a, (f a).isSome = true) : (x.bind f).isSome = x.isSome := by
  cases x <;> simp_all

@[simp] private theorem isSome_of_not_none {α : Type} (x : Option α) (h : ¬ x = none) :
    x.isSome = true := by
  cases x <;> simp_all

/-- The generator answer join never refuses (part 4: the least upper bound). -/
@[simp] theorem GenTy.joinAnswer_isSome (a b : Option Ty) : (GenTy.joinAnswer a b).isSome = true := by
  unfold GenTy.joinAnswer
  split <;> simp [EffTy.joinAnswer]

@[simp] theorem GenTy.merge_isSome (a b : GenTy) : (GenTy.merge a b).isSome = true := by
  simp [GenTy.merge]

set_option maxHeartbeats 1600000 in
mutual
  theorem explainEff_none_iff (sig : Signature Op) (e : Eff Op) :
      ∀ env p, explainEff sig env p e = none ↔ (effTy sig env e).isSome := by
    match e with
  | .succeed v =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .fail e =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .failCause c =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .yieldError e =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .sync t =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .suspend b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .perform op r =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .bind a b =>
    intro env pth
    have ih_a := explainEff_none_iff sig a
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .gen ss =>
    intro env pth
    have ih_ss := explainStmts_none_iff sig ss
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .catchCause b h =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_h := explainEff_none_iff sig h
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .catchIf t b h =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_h := explainEff_none_iff sig h
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .matchCause b v c =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_v := explainEff_none_iff sig v
    have ih_c := explainEff_none_iff sig c
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .onExit b f =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_f := explainEff_none_iff sig f
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .exit b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .uninterruptible b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interruptible b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .select s d a b =>
    intro env pth
    have ih_a := explainEff_none_iff sig a
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .iterate c i t s r b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .whileLoop i t s b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .yieldNow n =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .callback op r =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitFiber f m =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .withFiber a =>
    intro env pth
    have ih_a := explainAction_none_iff sig a
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .scoped b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .acquireRelease a r =>
    intro env pth
    have ih_a := explainEff_none_iff sig a
    have ih_r := explainEff_none_iff sig r
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provideLayer l i b =>
    intro env pth
    have ih_l := explainLayer_none_iff sig l
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .service k =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provideService k v b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural e

  theorem explainStmts_none_iff (sig : Signature Op) (ss : Stmts Op) :
      ∀ env inLoop p, explainStmts sig env inLoop p ss = none ↔ (stmtsTy sig env inLoop ss).isSome := by
    match ss with
    | .nil =>
      intro env inLoop pth
      simp [explainStmts, stmtsTy]
    | .cons (.bindYield effect) rest =>
      intro env inLoop pth
      have ih_effect := explainEff_none_iff sig effect
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons (.yieldDiscard effect) rest =>
      intro env inLoop pth
      have ih_effect := explainEff_none_iff sig effect
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons (.ret value) rest =>
      intro env inLoop pth
      cases rest <;> simp only [explainStmts, stmtsTy, termRefusal] <;> (repeat' split) <;> (try simp_all)
    | .cons (.ifElse test thenB elseB) rest =>
      intro env inLoop pth
      have ih_thenB := fun env => explainStmts_none_iff sig thenB env inLoop
      have ih_elseB := fun env => explainStmts_none_iff sig elseB env inLoop
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons (.whileTrue body) rest =>
      intro env inLoop pth
      have ih_body := fun env => explainStmts_none_iff sig body env true
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons .breakLoop rest =>
      intro env inLoop pth
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural ss

  theorem explainEffs_none_iff (sig : Signature Op) (es : Effs Op) :
      ∀ env p, explainEffs sig env p es = none ↔ (effsTy sig env es).isSome := by
    match es with
    | .nil =>
      intro env pth
      simp [explainEffs, effsTy]
    | .cons head tail =>
      intro env pth
      have ih_head := explainEff_none_iff sig head
      have ih_tail := explainEffs_none_iff sig tail
      simp only [explainEffs, effsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural es

  theorem explainAction_none_iff (sig : Signature Op) (a : ActionTerm Op) :
      ∀ env p, explainAction sig env p a = none ↔ (actionTy sig env a).isSome := by
    match a with
  | .fork p o =>
    intro env pth
    have ih_p := explainEff_none_iff sig p
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .forkIn p o s =>
    intro env pth
    have ih_p := explainEff_none_iff sig p
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .forkScoped p o =>
    intro env pth
    have ih_p := explainEff_none_iff sig p
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .runIn t s =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interrupt t =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interruptScoped t =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interruptAll ts who =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitAll ts =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitAllFailFast ts =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .snapshotChildren =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitNewChildren s =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .raceAll es =>
    intro env pth
    have ih_es := explainEffs_none_iff sig es
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .setContext c =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .getContext =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .getId =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .closeScope s e =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural a

  theorem explainLayer_none_iff (sig : Signature Op) (l : LayerTerm Op) :
      ∀ p, explainLayer sig p l = none ↔ (layerTy sig l).isSome := by
    match l with
  | .succeed k v =>
    intro pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .effect k b =>
    intro pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .effectDiscard b =>
    intro pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provide s t =>
    intro pth
    have ih_s := explainLayer_none_iff sig s
    have ih_t := explainLayer_none_iff sig t
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provideMerge s t =>
    intro pth
    have ih_s := explainLayer_none_iff sig s
    have ih_t := explainLayer_none_iff sig t
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .merge s t =>
    intro pth
    have ih_s := explainLayer_none_iff sig s
    have ih_t := explainLayer_none_iff sig t
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .fresh i =>
    intro pth
    have ih_i := explainLayer_none_iff sig i
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .orDie i =>
    intro pth
    have ih_i := explainLayer_none_iff sig i
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .ref t =>
    intro pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .mergeAll ls =>
    intro pth
    have ih_ls := explainLayers_none_iff sig ls
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural l

  theorem explainLayers_none_iff (sig : Signature Op) (ls : LayerTerms Op) :
      ∀ p, explainLayers sig p ls = none ↔ (layersTy sig ls).isSome := by
    match ls with
    | .nil =>
      intro pth
      simp [explainLayers, layersTy]
    | .cons head .nil =>
      intro pth
      have ih_head := explainLayer_none_iff sig head
      simp only [explainLayers, layersTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons head (.cons h2 t2) =>
      intro pth
      have ih_head := explainLayer_none_iff sig head
      have ih_tail := explainLayers_none_iff sig (.cons h2 t2)
      simp only [explainLayers, layersTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural ls
end

/-- The law of the projection: `explain` refuses exactly when the checker does. -/
theorem explain_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    explain sig env e = none ↔ (effTy sig env e).isSome :=
  explainEff_none_iff sig e env []

/-- A refusal is where a program fails to type, and a typed program has no refusal. -/
theorem blame_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    blame sig env e = none ↔ (effTy sig env e).isSome := by
  simp [blame, ← explain_none_iff]

end Effect4.Program
