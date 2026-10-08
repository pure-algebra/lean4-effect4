module

public import Effect4.Program.Typing.Table

/-!
# Program.Typing.Annotate — the address table in one pass

**The question.** The address table (`table`, `Program/Typing/Table.lean`) gives the
environment and the checker's answer at every address of a program. It is a specification:
each entry asks `Node.envAt` from the root and the checker at the address. The typed print
(slice PRINT, steps P2 and after) reads an answer at every node, so it needs the table at the
cost of one check. This module computes it in one pass, `annotate`, and
`annotate_eq_table` (`Laws/Program/Typing/Annotate.lean`) proves it equal to the table.

## The pass

`Annotate.check` and its six siblings are the checker's seven functions (`Checker.check`,
`Program/Checker.lean`) with a record at each node. Each takes the environment and the path
that its checker function takes, and it answers two things: the entries of the node's subtree,
in the order of `Node.addresses`, and the checker's answer at the node.

- **A node is checked once.** Its answer comes from its children's answers by its checker
  arm. A leaf has no child, so its answer is the checker's own at it.
- **A child's environment comes from the answers before it.** The eleven reads of the step
  function (`Node.childEnv`, `Program/Typing/Focus.lean`) take the answer that the pass has
  already computed: the answer of an earlier sibling, or the type of a term of the node, read
  once.
- **A refused read leaves a subtree not reached.** Where a child reads a refused sibling, each
  address of the child's subtree gets an entry with no environment and no answer, in address
  order (`Annotate.unreached`). A later child that reads nothing refused is still visited: the
  second arm of `select`, the failure branch of `matchCause`, the rest of a race's entrants.
- **The statements after a head** are visited where the checker checks them: at the head's
  environment, extended by what the head binds. After a refused `bindYield`, whose answer they
  read, they are not reached. After any other refused head they are visited at the head's
  environment, which the checker never reaches.

## The cost

Each node's checker arm runs once, and each term that a rule reads is typed once. A subtree
that is not reached costs its address list. The entries of a node's children are joined by
`List.append`, which copies the left list: a deep left spine of two-child nodes pays that copy
at each node on it.

## What this module is not

- It is not a second checker. Its answers are `Checker.check`'s, and the law says so.
- It marks nothing past a refusal: a subtree after a refused read is not reached.
- It is not the typed tree of the design note, which keeps a call's bindings. The entries are
  `Table.Entry`, and slice P2 decides what the printer reads from them.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)

variable {Op : Type}

namespace Annotate

/-- What the pass answers at a node: the entries of its subtree, in address order, and the
checker's answer at it. -/
abbrev Out (α : Type) : Type := List Table.Entry × Except TypeRefusal α

/-- **The entries of a subtree that is not reached**: one for each address of the node `n`,
standing at the address `a`, with no environment and no answer. -/
def unreached (a : List Nat) (n : Node Op) : List Table.Entry :=
  (Node.addresses n).map fun b => ⟨a ++ b, none, none⟩

/-- The record at a program: its entry holds its environment and the checker's answer `r`, and
its children's entries follow. -/
def atProgram (a : List Nat) (env : TyEnv) (r : Except TypeRefusal EffTy)
    (children : List Table.Entry) : Out EffTy :=
  (⟨a, some (.env env), some r⟩ :: children, r)

/-- The record at a node of another sort: its entry holds its environment and no answer, since
the checker answers at those sorts through the program above them. -/
def atNode {α : Type} (a : List Nat) (ctx : NodeEnv) (r : Except TypeRefusal α)
    (children : List Table.Entry) : Out α :=
  (⟨a, some ctx, none⟩ :: children, r)

mutual
  /-- `Checker.check` with a record at each node. -/
  def check (s : Signature Op) (env : TyEnv) (p : List Nat) : Eff Op → Out EffTy
    | .succeed value => atProgram p env (Checker.check s env p (.succeed value)) []
    | .fail error => atProgram p env (Checker.check s env p (.fail error)) []
    | .failCause cause => atProgram p env (Checker.check s env p (.failCause cause)) []
    | .sync thunk => atProgram p env (Checker.check s env p (.sync thunk)) []
    | .suspend body =>
      let b := check s env (p ++ [0]) body
      atProgram p env b.2 b.1
    | .perform op request => atProgram p env (Checker.check s env p (.perform op request)) []
    | .bind first rest =>
      let f := check s env (p ++ [0]) first
      match f.2 with
      | .ok ft =>
        let r := check s (env ++ [ft.answer]) (p ++ [1]) rest
        atProgram p env (do
          let rt ← r.2
          pure ⟨rt.answer, ft.error.join rt.error, ft.requires.union rt.requires⟩) (f.1 ++ r.1)
      | .error e => atProgram p env (.error e) (f.1 ++ unreached (p ++ [1]) (.eff rest))
    | .gen body =>
      let b := checkStmts s env false none (p ++ [0]) body
      atProgram p env (do
        let g ← b.2
        pure ⟨g.genAnswer, g.error, g.requires⟩) b.1
    | .catchCause body handler =>
      let b := check s env (p ++ [0]) body
      match b.2 with
      | .ok bt =>
        let h := check s (env ++ [.causeOf bt.error]) (p ++ [1]) handler
        atProgram p env (do
          let ht ← h.2
          pure ⟨Ty.join bt.answer ht.answer, ht.error, bt.requires.union ht.requires⟩)
          (b.1 ++ h.1)
      | .error e => atProgram p env (.error e) (b.1 ++ unreached (p ++ [1]) (.eff handler))
    | .catchIf test body handler =>
      let b := check s env (p ++ [0]) body
      match b.2 with
      | .ok bt =>
        let h := check s (env ++ [bt.error]) (p ++ [1]) handler
        atProgram p env (do
          let predicate ← Checker.term? s (env ++ [bt.error]) p test
          if Ty.sub predicate.normalize .bool then
            let ht ← h.2
            pure ⟨Ty.join bt.answer ht.answer, catchIfError test env.length bt.error ht.error,
              bt.requires.union ht.requires⟩
          else throw ⟨p, .predicateNotBool predicate⟩) (b.1 ++ h.1)
      | .error e => atProgram p env (.error e) (b.1 ++ unreached (p ++ [1]) (.eff handler))
    | .select scrutinee d a0 a1 =>
      -- the scrutinee is typed once; both arms read what the decision binds from its type
      let unreachedArms := unreached (p ++ [0]) (.eff a0) ++ unreached (p ++ [1]) (.eff a1)
      match Checker.term? s env p scrutinee with
      | .ok t =>
        match d.arms t with
        | some arms =>
          let c0 := check s (env ++ arms.1) (p ++ [0]) a0
          let c1 := check s (env ++ arms.2) (p ++ [1]) a1
          atProgram p env (do
            let t0 ← c0.2
            let t1 ← c1.2
            pure ⟨Ty.join t0.answer t1.answer, t0.error.join t1.error,
              t0.requires.union t1.requires⟩) (c0.1 ++ c1.1)
        | none => atProgram p env (.error ⟨p, selectRefusal d t⟩) unreachedArms
      | .error e => atProgram p env (.error e) unreachedArms
    | .matchCause body onValue onCause =>
      let b := check s env (p ++ [0]) body
      match b.2 with
      | .ok bt =>
        let v := check s (env ++ [bt.answer]) (p ++ [1]) onValue
        let c := check s (env ++ [.causeOf bt.error]) (p ++ [2]) onCause
        atProgram p env (do
          let vt ← v.2
          let ct ← c.2
          pure ⟨Ty.join vt.answer ct.answer, vt.error.join ct.error,
            (bt.requires.union vt.requires).union ct.requires⟩) (b.1 ++ (v.1 ++ c.1))
      | .error e =>
        atProgram p env (.error e)
          (b.1 ++ (unreached (p ++ [1]) (.eff onValue) ++ unreached (p ++ [2]) (.eff onCause)))
    | .onExit body finalizer =>
      let b := check s env (p ++ [0]) body
      match b.2 with
      | .ok bt =>
        let f := check s (env ++ [.exitOf bt.answer bt.error]) (p ++ [1]) finalizer
        atProgram p env (do
          let ft ← f.2
          pure ⟨bt.answer, bt.error.join ft.error, bt.requires.union ft.requires⟩) (b.1 ++ f.1)
      | .error e => atProgram p env (.error e) (b.1 ++ unreached (p ++ [1]) (.eff finalizer))
    | .exit body =>
      let b := check s env (p ++ [0]) body
      atProgram p env (do
        let bt ← b.2
        pure ⟨.exitOf bt.answer bt.error, .never, bt.requires⟩) b.1
    | .uninterruptible body =>
      let b := check s env (p ++ [0]) body
      atProgram p env b.2 b.1
    | .interruptible body =>
      let b := check s env (p ++ [0]) body
      atProgram p env b.2 b.1
    | .iterate cursorTy initial test step result body =>
      -- the initial term is typed once; the body reads the cursor
      match Checker.term? s env p initial with
      | .ok c0 =>
        let cursor := cursorTy.getD c0
        let b := check s (env ++ [cursor]) (p ++ [0]) body
        atProgram p env (do
          let t ← Checker.term? s (env ++ [cursor]) p test
          let bt ← b.2
          let c1 ← Checker.term? s (env ++ [cursor, bt.answer]) p step
          let d ← Checker.term? s (env ++ [cursor]) p result
          if Ty.sub t.normalize .bool ∧ Ty.sub c0.normalize cursor.normalize = true
              ∧ Ty.sub c1.normalize cursor.normalize = true then pure ⟨d, bt.error, bt.requires⟩
          else if ¬ Ty.sub t.normalize .bool then throw ⟨p, .predicateNotBool t⟩
          else if Ty.sub c0.normalize cursor.normalize = true then
            throw ⟨p, .stepNotCursor c1 cursor⟩
          else throw ⟨p, .initialNotCursor c0 cursor⟩) b.1
      | .error e => atProgram p env (.error e) (unreached (p ++ [0]) (.eff body))
    | .yieldNow priority => atProgram p env (Checker.check s env p (.yieldNow priority)) []
    | .awaitFiber fiber mode => atProgram p env (Checker.check s env p (.awaitFiber fiber mode)) []
    | .withFiber action =>
      let a := checkAction s env (p ++ [0]) action
      atProgram p env a.2 a.1
    | .scoped body =>
      let b := check s env (p ++ [0]) body
      atProgram p env (do
        let t ← b.2
        pure { t with requires := bodyRequires s t }) b.1
    | .acquireRelease acquire release =>
      let a := check s env (p ++ [0]) acquire
      match a.2 with
      | .ok at_ =>
        let r := check s (env ++ [at_.answer, .exitOf .unknown .unknown]) (p ++ [1]) release
        atProgram p env (do
          let rt ← r.2
          if rt.error.normalize = .never then
            pure ⟨at_.answer, at_.error,
              (at_.requires.union rt.requires).union (Requirement.single s.scopeKey)⟩
          else throw ⟨p, .releaseFails rt.error⟩) (a.1 ++ r.1)
      | .error e => atProgram p env (.error e) (a.1 ++ unreached (p ++ [1]) (.eff release))
    | .provideLayer layer _ body =>
      let l := checkLayer s (p ++ [0]) layer
      let b := check s env (p ++ [1]) body
      atProgram p env (do
        let lt ← l.2
        let bt ← b.2
        pure ⟨bt.answer, bt.error.join lt.error, Row.union lt.requires (Row.diff bt.requires lt.out)⟩)
        (l.1 ++ b.1)
    | .service key => atProgram p env (Checker.check s env p (.service key)) []
    | .provideService key value body =>
      let b := check s env (p ++ [0]) body
      atProgram p env (do
        let ty ← Checker.expect ⟨p, .serviceUnknown key⟩ (s.serviceTy key)
        let v ← Checker.term? s env p value
        let bt ← b.2
        if Ty.sub v.normalize ty.normalize then
          pure ⟨bt.answer, bt.error, Row.diff bt.requires (Requirement.single key)⟩
        else throw ⟨p, .valueNotSubtype key v ty⟩) b.1
    | .restore saved body =>
      let b := check s env (p ++ [0]) body
      atProgram p env (do
        let st ← Checker.term? s env p saved
        if Ty.sub st.normalize Ty.maskRestore then b.2
        else throw ⟨p, .maskRestoreExpected st⟩) b.1

  /-- `Checker.checkLayer` with a record at each node. -/
  def checkLayer (s : Signature Op) (p : List Nat) : LayerTerm Op → Out LayerTy
    | .succeed key value => atNode p .closed (Checker.checkLayer s p (.succeed key value)) []
    | .effect key body =>
      let b := check s [] (p ++ [0]) body
      atNode p .closed (do
        let t ← b.2
        let ty ← Checker.expect ⟨p, .serviceUnknown key⟩ (s.serviceTy key)
        if Ty.sub t.answer.normalize ty.normalize then
          pure ⟨Requirement.single key, t.error, bodyRequires s t⟩
        else throw ⟨p, .valueNotSubtype key t.answer ty⟩) b.1
    | .effectDiscard body =>
      let b := check s [] (p ++ [0]) body
      atNode p .closed (do
        let t ← b.2
        pure ⟨Requirement.empty, t.error, bodyRequires s t⟩) b.1
    | .provide self that =>
      let a := checkLayer s (p ++ [0]) self
      let b := checkLayer s (p ++ [1]) that
      atNode p .closed (do
        let st ← a.2
        let tt ← b.2
        pure (st.provide tt)) (a.1 ++ b.1)
    | .provideMerge self that =>
      let a := checkLayer s (p ++ [0]) self
      let b := checkLayer s (p ++ [1]) that
      atNode p .closed (do
        let st ← a.2
        let tt ← b.2
        pure (st.provideMerge tt)) (a.1 ++ b.1)
    | .merge left right =>
      let a := checkLayer s (p ++ [0]) left
      let b := checkLayer s (p ++ [1]) right
      atNode p .closed (do
        let at_ ← a.2
        let bt ← b.2
        pure (at_.merge bt)) (a.1 ++ b.1)
    | .fresh inner =>
      let i := checkLayer s (p ++ [0]) inner
      atNode p .closed i.2 i.1
    | .orDie inner =>
      let i := checkLayer s (p ++ [0]) inner
      atNode p .closed (do
        let l ← i.2
        pure l.orDie) i.1
    | .ref target => atNode p .closed (Checker.checkLayer s p (.ref target)) []
    | .mergeAll layers =>
      let ls := checkLayers s (p ++ [0]) layers
      atNode p .closed (do
        let lts ← ls.2
        Checker.expect ⟨p ++ [0], .mergeAllEmpty⟩ (LayerTy.mergeNonempty lts)) ls.1

  /-- `Checker.checkLayers` with a record at each node. -/
  def checkLayers (s : Signature Op) (p : List Nat) : LayerTerms Op → Out (List LayerTy)
    | .nil => atNode p .closed (Checker.checkLayers s p .nil) []
    | .cons head tail =>
      let h := checkLayer s (p ++ [0]) head
      let t := checkLayers s (p ++ [1]) tail
      atNode p .closed (do
        let ht ← h.2
        let tt ← t.2
        pure (ht :: tt)) (h.1 ++ t.1)

  /-- `Checker.checkStmt` with a record at each node. -/
  def checkStmt (s : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat) :
      Stmt Op → Out StmtTy
    | .bindYield effect =>
      let e := check s env (p ++ [0]) effect
      atNode p (.body env inLoop) (do
        let t ← e.2
        pure (.step ⟨none, t.error, t.requires, true, false⟩ [t.answer])) e.1
    | .yieldDiscard effect =>
      let e := check s env (p ++ [0]) effect
      atNode p (.body env inLoop) (do
        let t ← e.2
        pure (.step ⟨none, t.error, t.requires, true, false⟩ [])) e.1
    | .ret value => atNode p (.body env inLoop) (Checker.checkStmt s env inLoop p (.ret value)) []
    | .ifElse test thenB elseB =>
      let a := checkStmts s env inLoop none (p ++ [0]) thenB
      let b := checkStmts s env inLoop none (p ++ [1]) elseB
      atNode p (.body env inLoop) (do
        let t ← Checker.term? s env p test
        if Ty.sub t.normalize .bool then
          let at_ ← a.2
          let bt ← b.2
          pure (.step (at_.mergeT bt) [])
        else throw ⟨p, .predicateNotBool t⟩) (a.1 ++ b.1)
    | .whileTrue body =>
      let b := checkStmts s env true none (p ++ [0]) body
      atNode p (.body env inLoop) (do
        let bt ← b.2
        pure (.step bt.loop [])) b.1
    | .breakLoop => atNode p (.body env inLoop) (Checker.checkStmt s env inLoop p .breakLoop) []

  /-- `Checker.checkStmts` with a record at each node. The entries do not read `afterRet`. -/
  def checkStmts (s : Signature Op) (env : TyEnv) (inLoop : Bool) (afterRet : Option (List Nat))
      (p : List Nat) : Stmts Op → Out GenTy
    | .nil => atNode p (.body env inLoop) (Checker.checkStmts s env inLoop afterRet p .nil) []
    | .cons head rest =>
      let h := checkStmt s env inLoop (p ++ [0]) head
      -- the rest where the checker checks it, after the head's type; after a refused head, not
      -- reached when the head is a `bindYield`, whose answer it reads, and else visited at the
      -- head's environment
      let r : Out GenTy :=
        match h.2 with
        | .ok st => st.fold
            (fun _ binds => checkStmts s (env ++ binds) inLoop none (p ++ [1]) rest)
            (fun _ => checkStmts s env inLoop (some (p ++ [0])) (p ++ [1]) rest)
            (checkStmts s env inLoop none (p ++ [1]) rest)
        | .error e =>
          match head with
          | .bindYield _ => (unreached (p ++ [1]) (.stmts rest), .error e)
          | _ => checkStmts s env inLoop none (p ++ [1]) rest
      atNode p (.body env inLoop)
        (match afterRet with
          | some ret => throw ⟨ret, .returnNotLast⟩
          | none => do
            let st ← h.2
            st.fold
              (fun g _ => do
                let rt ← r.2
                pure (g.seqT rt))
              (fun answer => do
                let _ ← r.2
                let t ← answer
                pure ⟨some t, .never, Requirement.empty, false, false⟩)
              (do
                let rt ← r.2
                pure rt.broken))
        (h.1 ++ r.1)

  /-- `Checker.checkEffs` with a record at each node. -/
  def checkEffs (s : Signature Op) (env : TyEnv) (p : List Nat) : Effs Op → Out EffTy
    | .nil => atNode p (.env env) (Checker.checkEffs s env p .nil) []
    | .cons head tail =>
      let h := check s env (p ++ [0]) head
      let t := checkEffs s env (p ++ [1]) tail
      atNode p (.env env) (do
        let ht ← h.2
        let tt ← t.2
        pure ⟨Ty.join ht.answer tt.answer, ht.error.join tt.error, ht.requires.union tt.requires⟩)
        (h.1 ++ t.1)

  /-- `Checker.checkAction` with a record at each node. -/
  def checkAction (s : Signature Op) (env : TyEnv) (p : List Nat) : ActionTerm Op → Out EffTy
    | .fork program _ =>
      let c := check s env (p ++ [0]) program
      atNode p (.env env) (do
        let t ← c.2
        pure ⟨.fiberOf t.answer t.error, .never, t.requires⟩) c.1
    | .forkIn program _ scope =>
      let c := check s env (p ++ [0]) program
      atNode p (.env env) (do
        let t ← c.2
        let st ← Checker.term? s env p scope
        if Ty.sub st.normalize Ty.scope then pure ⟨.fiberOf t.answer t.error, .never, t.requires⟩
        else throw ⟨p, .scopeExpected st⟩) c.1
    | .forkScoped program _ =>
      let c := check s env (p ++ [0]) program
      atNode p (.env env) (do
        let t ← c.2
        pure ⟨.fiberOf t.answer t.error, .never,
          t.requires.union (Requirement.single s.scopeKey)⟩) c.1
    | .runIn target scope => atNode p (.env env) (Checker.checkAction s env p (.runIn target scope)) []
    | .interrupt target => atNode p (.env env) (Checker.checkAction s env p (.interrupt target)) []
    | .interruptScoped target =>
      atNode p (.env env) (Checker.checkAction s env p (.interruptScoped target)) []
    | .interruptAll targets interruptor =>
      atNode p (.env env) (Checker.checkAction s env p (.interruptAll targets interruptor)) []
    | .awaitAll targets => atNode p (.env env) (Checker.checkAction s env p (.awaitAll targets)) []
    | .awaitAllFailFast targets =>
      atNode p (.env env) (Checker.checkAction s env p (.awaitAllFailFast targets)) []
    | .snapshotChildren => atNode p (.env env) (Checker.checkAction s env p .snapshotChildren) []
    | .awaitNewChildren snapshot =>
      atNode p (.env env) (Checker.checkAction s env p (.awaitNewChildren snapshot)) []
    | .raceAll entrants =>
      let c := checkEffs s env (p ++ [0]) entrants
      atNode p (.env env) c.2 c.1
    | .setContext context =>
      atNode p (.env env) (Checker.checkAction s env p (.setContext context)) []
    | .getContext => atNode p (.env env) (Checker.checkAction s env p .getContext) []
    | .getId => atNode p (.env env) (Checker.checkAction s env p .getId) []
    | .closeScope scope exit =>
      atNode p (.env env) (Checker.checkAction s env p (.closeScope scope exit)) []
    | .getInterruptible => atNode p (.env env) (Checker.checkAction s env p .getInterruptible) []
end

end Annotate

/-- **The address table of a program, in one pass.** It equals `table s env0 p`
(`annotate_eq_table`, `Laws/Program/Typing/Annotate.lean`), and it checks each node once. -/
def annotate (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : List Table.Entry :=
  (Annotate.check s env0 [] p).1

end Effect4.Program
