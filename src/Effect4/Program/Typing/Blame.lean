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

The law is `explain_none_iff` (`Typing/Agreement.lean`): `explain` answers `none` exactly
when `effTy` answers, so the projection cannot drift from the checker without the proof
breaking. Since 2026-09-18 both blocks are the two projections of one `Except`-valued fold
(`Program/Checker.lean`), and the law is the shape of `Except` through the agreement; the
mutual induction that proved it here is gone.
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
  /-- `fail` at a type the error alphabet does not admit. -/
  | errorNotAdmitted (error : Ty)
  /-- The row is outside the signature's domain (DI-54). -/
  | outsideDomain (row : String)
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
    | .iterate cursorTy initial test step result body =>
      match termTy sig env initial with
      | none => some ⟨p, .term initial⟩
      | some c0 =>
        let cursor := cursorTy.getD c0
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

/-- The generator answer join never refuses (part 4: the least upper bound). -/
@[simp] theorem GenTy.joinAnswer_isSome (a b : Option Ty) : (GenTy.joinAnswer a b).isSome = true := by
  unfold GenTy.joinAnswer
  split <;> simp [EffTy.joinAnswer]

@[simp] theorem GenTy.merge_isSome (a b : GenTy) : (GenTy.merge a b).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (GenTy.joinAnswer_isSome a.answer b.answer)
  simp [GenTy.merge, hx]

end Effect4.Program
