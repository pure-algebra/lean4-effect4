import OCaml5.Eff.Emit
import Effect4.Store.Canonical

/-!
# OCaml5.Eff.Goldens

**What it is.** The goldens: `V`, a generic value tree serialised by the wire rule (`V.bytes`) and
by the JSON rule (`V.json`); one total conversion per family (`effV`, `termV`, …); and `Corpus`,
the program corpus every constructor of the closed world is reached by.

**Depends on.** `OCaml5.Eff.Emit` (`jsonStr`, and through it `World`), `Effect4.Store.Canonical` (`Bytes`).

**Properties.**
* **Total by pattern matching**: every conversion covers every constructor — *by construction*.
* **Coverage.** The corpus reaches every constructor of the program families; a family it misses
  fails the run — *tested* (the driver's coverage check).
-/

open Lean Meta
open Effect4.Program
open Effect4.Supervision (MaskMode ForkOptions ObserverMode)
open Effect4 (FinalizerStrategy ServiceKey)
open Effect4.Machine (FnName)

namespace OCaml5.Eff

/-! ## Goldens: a generic value tree, serialised by the wire rule and by the JSON rule -/

/-- A Lean value as the wire sees it. `ctor` carries the constructor's full name; its index
is looked up in the environment when the bytes are written. -/
inductive V
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | list (xs : List V)
  | none
  | some (x : V)
  | pair (a b : V)
  | ctor (name : Name) (args : List V)
  | struct (name : Name) (fields : List (String × V))

instance : Inhabited V := ⟨.unit⟩

/-- The constructor tag: `Tag.ctor` in the PC's pending edit of `Canonical.lean`; the value
is the wire's, restated here so the tool builds at HEAD. -/
def ctorTag : UInt8 := 10

/-- The byte rule of `src/Effect4/Store/Canonical.lean` (`framed`, `natBytes`, `Tag.*` are the
library's own), with `ctorTag` for a constructor application. -/
partial def V.bytes (idx : Name → Nat) : V → Effect4.Store.Bytes
  | .unit => Effect4.Store.framed Effect4.Store.Tag.unit []
  | .bool b => Effect4.Store.framed Effect4.Store.Tag.bool [if b then 1 else 0]
  | .nat n => Effect4.Store.framed Effect4.Store.Tag.nat (Effect4.Store.natBytes n)
  | .str s => Effect4.Store.framed Effect4.Store.Tag.string s.toUTF8.data.toList
  | .list xs => Effect4.Store.framed Effect4.Store.Tag.list (xs.map (bytes idx)).flatten
  | .none => Effect4.Store.framed Effect4.Store.Tag.none []
  | .some x => Effect4.Store.framed Effect4.Store.Tag.some (bytes idx x)
  | .pair a b => Effect4.Store.framed Effect4.Store.Tag.pair (bytes idx a ++ bytes idx b)
  | .ctor n args =>
    Effect4.Store.framed ctorTag (bytes idx (.nat (idx n)) ++ (args.map (bytes idx)).flatten)
  | .struct _ fields =>
    Effect4.Store.framed ctorTag (bytes idx (.nat 0) ++ (fields.map fun (_, v) => bytes idx v).flatten)

partial def V.json : V → String
  | .unit => "[]"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .str s => jsonStr s
  | .list xs => "[" ++ ",".intercalate (xs.map json) ++ "]"
  | .none => "null"
  | .some x => json x
  | .pair a b => "[" ++ json a ++ "," ++ json b ++ "]"
  | .ctor n args => "[" ++ ",".intercalate (jsonStr (shortName n) :: args.map json) ++ "]"
  | .struct _ fields => "{" ++ ",".intercalate (fields.map fun (k, v) => jsonStr k ++ ":" ++ json v) ++ "}"

/-- Every constructor name a tree uses (validated against the environment before writing). -/
partial def V.names : V → List Name
  | .list xs => (xs.map names).flatten
  | .some x => names x
  | .pair a b => names a ++ names b
  | .ctor n args => n :: (args.map names).flatten
  | .struct n fields => n :: (fields.map fun (_, v) => names v).flatten
  | _ => []

/-! ### The conversions, one per family, total by pattern matching -/

def tyV : Ty → V
  | .never => .ctor ``Ty.never []
  | .unit => .ctor ``Ty.unit []
  | .nat => .ctor ``Ty.nat []
  | .int => .ctor ``Ty.int []
  | .string => .ctor ``Ty.string []
  | .bool => .ctor ``Ty.bool []
  | .handle target => .ctor ``Ty.handle [.str target]
  | .option inner => .ctor ``Ty.option [tyV inner]
  | .list inner => .ctor ``Ty.list [tyV inner]
  | .prod l r => .ctor ``Ty.prod [tyV l, tyV r]
  | .except e v => .ctor ``Ty.except [tyV e, tyV v]
  | .exitOf v e => .ctor ``Ty.exitOf [tyV v, tyV e]
  | .causeOf e => .ctor ``Ty.causeOf [tyV e]
  | .fiberOf v e => .ctor ``Ty.fiberOf [tyV v, tyV e]
  | .union l r => .ctor ``Ty.union [tyV l, tyV r]

def litV : Lit → V
  | .unit => .ctor ``Lit.unit []
  | .nat n => .ctor ``Lit.nat [.nat n]
  | .bool b => .ctor ``Lit.bool [.bool b]
  | .str s => .ctor ``Lit.str [.str s]

mutual
partial def termV : PTerm → V
  | .var i => .ctor ``Term.var [.nat i]
  | .lit l => .ctor ``Term.lit [litV l]
  | .app atom args => .ctor ``Term.app [.str atom, termsV args]
partial def termsV : Terms → V
  | .nil => .ctor ``Terms.nil []
  | .cons h t => .ctor ``Terms.cons [termV h, termsV t]
end

partial def causeV : CauseTerm → V
  | .fail e => .ctor ``CauseTerm.fail [termV e]
  | .die d => .ctor ``CauseTerm.die [termV d]
  | .interrupt none => .ctor ``CauseTerm.interrupt [.none]
  | .interrupt (some who) => .ctor ``CauseTerm.interrupt [.some (termV who)]
  | .both l r => .ctor ``CauseTerm.both [causeV l, causeV r]

def maskV : MaskMode → V
  | .interruptible => .ctor ``Effect4.Supervision.MaskMode.interruptible []
  | .uninterruptible => .ctor ``Effect4.Supervision.MaskMode.uninterruptible []
  | .inherit => .ctor ``Effect4.Supervision.MaskMode.inherit []

def optionsV (o : ForkOptions) : V :=
  .struct ``Effect4.Supervision.ForkOptions
    [("startImmediately", .bool o.startImmediately), ("daemon", .bool o.daemon), ("maskMode", maskV o.maskMode)]

def modeV : ObserverMode → V
  | .awaitValue => .ctor ``Effect4.Supervision.ObserverMode.awaitValue []
  | .joinEffect => .ctor ``Effect4.Supervision.ObserverMode.joinEffect []

def stratV : FinalizerStrategy → V
  | .sequential => .ctor ``Effect4.FinalizerStrategy.sequential []
  | .parallel => .ctor ``Effect4.FinalizerStrategy.parallel []

def fnV : FnName → V
  | .incr => .ctor ``Effect4.Machine.FnName.incr []
  | .double => .ctor ``Effect4.Machine.FnName.double []
  | .zeroWhenPositive => .ctor ``Effect4.Machine.FnName.zeroWhenPositive []
  | .noChange => .ctor ``Effect4.Machine.FnName.noChange []
  | .takeAndBump => .ctor ``Effect4.Machine.FnName.takeAndBump []

def opV : NativeOp → V
  | .refMake => .ctor ``NativeOp.refMake []
  | .refGet => .ctor ``NativeOp.refGet []
  | .refSet => .ctor ``NativeOp.refSet []
  | .refGetAndSet => .ctor ``NativeOp.refGetAndSet []
  | .refSetAndGet => .ctor ``NativeOp.refSetAndGet []
  | .refUpdate f => .ctor ``NativeOp.refUpdate [fnV f]
  | .refGetAndUpdate f => .ctor ``NativeOp.refGetAndUpdate [fnV f]
  | .refUpdateAndGet f => .ctor ``NativeOp.refUpdateAndGet [fnV f]
  | .refUpdateSome f => .ctor ``NativeOp.refUpdateSome [fnV f]
  | .refGetAndUpdateSome f => .ctor ``NativeOp.refGetAndUpdateSome [fnV f]
  | .refUpdateSomeAndGet f => .ctor ``NativeOp.refUpdateSomeAndGet [fnV f]
  | .refModify f => .ctor ``NativeOp.refModify [fnV f]
  | .refModifySome f => .ctor ``NativeOp.refModifySome [fnV f]
  | .deferredMake => .ctor ``NativeOp.deferredMake []
  | .deferredIsDone => .ctor ``NativeOp.deferredIsDone []
  | .deferredPoll => .ctor ``NativeOp.deferredPoll []
  | .deferredSucceed => .ctor ``NativeOp.deferredSucceed []
  | .deferredFail => .ctor ``NativeOp.deferredFail []
  | .deferredAwait => .ctor ``NativeOp.deferredAwait []
  | .scopeMake s => .ctor ``NativeOp.scopeMake [stratV s]

mutual
partial def effV : Eff NativeOp → V
  | .succeed v => .ctor ``Eff.succeed [termV v]
  | .fail e => .ctor ``Eff.fail [termV e]
  | .failCause c => .ctor ``Eff.failCause [causeV c]
  | .yieldError e => .ctor ``Eff.yieldError [termV e]
  | .sync t => .ctor ``Eff.sync [termV t]
  | .suspend b => .ctor ``Eff.suspend [effV b]
  | .perform op r => .ctor ``Eff.perform [opV op, termV r]
  | .bind f r => .ctor ``Eff.bind [effV f, effV r]
  | .gen body => .ctor ``Eff.gen [stmtsV body]
  | .catchCause b h => .ctor ``Eff.catchCause [effV b, effV h]
  | .matchCause b v c => .ctor ``Eff.matchCause [effV b, effV v, effV c]
  | .onExit b f => .ctor ``Eff.onExit [effV b, effV f]
  | .exit b => .ctor ``Eff.exit [effV b]
  | .uninterruptible b => .ctor ``Eff.uninterruptible [effV b]
  | .interruptible b => .ctor ``Eff.interruptible [effV b]
  | .branch t a b => .ctor ``Eff.branch [termV t, effV a, effV b]
  | .whileLoop i t s b => .ctor ``Eff.whileLoop [termV i, termV t, termV s, effV b]
  | .yieldNow p => .ctor ``Eff.yieldNow [.nat p]
  | .callback op r => .ctor ``Eff.callback [opV op, termV r]
  | .awaitFiber f m => .ctor ``Eff.awaitFiber [termV f, modeV m]
  | .withFiber a => .ctor ``Eff.withFiber [actionV a]
  | .scoped b => .ctor ``Eff.scoped [effV b]
  | .acquireRelease a r => .ctor ``Eff.acquireRelease [effV a, effV r]
  | .choose site l r => .ctor ``Eff.choose [.nat site, effV l, effV r]
partial def stmtV : Stmt NativeOp → V
  | .bindYield e => .ctor ``Stmt.bindYield [effV e]
  | .yieldDiscard e => .ctor ``Stmt.yieldDiscard [effV e]
  | .ret v => .ctor ``Stmt.ret [termV v]
  | .ifElse t a b => .ctor ``Stmt.ifElse [termV t, stmtsV a, stmtsV b]
  | .whileTrue b => .ctor ``Stmt.whileTrue [stmtsV b]
  | .breakLoop => .ctor ``Stmt.breakLoop []
partial def stmtsV : Stmts NativeOp → V
  | .nil => .ctor ``Stmts.nil []
  | .cons h t => .ctor ``Stmts.cons [stmtV h, stmtsV t]
partial def effsV : Effs NativeOp → V
  | .nil => .ctor ``Effs.nil []
  | .cons h t => .ctor ``Effs.cons [effV h, effsV t]
partial def actionV : ActionTerm NativeOp → V
  | .fork p o => .ctor ``ActionTerm.fork [effV p, optionsV o]
  | .forkIn p o s => .ctor ``ActionTerm.forkIn [effV p, optionsV o, termV s]
  | .forkScoped p o => .ctor ``ActionTerm.forkScoped [effV p, optionsV o]
  | .runIn t s => .ctor ``ActionTerm.runIn [termV t, termV s]
  | .interrupt t => .ctor ``ActionTerm.interrupt [termV t]
  | .interruptScoped t => .ctor ``ActionTerm.interruptScoped [termV t]
  | .interruptAll ts none => .ctor ``ActionTerm.interruptAll [termV ts, .none]
  | .interruptAll ts (some who) => .ctor ``ActionTerm.interruptAll [termV ts, .some (termV who)]
  | .awaitAll ts => .ctor ``ActionTerm.awaitAll [termV ts]
  | .awaitAllFailFast ts => .ctor ``ActionTerm.awaitAllFailFast [termV ts]
  | .snapshotChildren => .ctor ``ActionTerm.snapshotChildren []
  | .awaitNewChildren s => .ctor ``ActionTerm.awaitNewChildren [termV s]
  | .raceAll es => .ctor ``ActionTerm.raceAll [effsV es]
  | .setContext c => .ctor ``ActionTerm.setContext [termV c]
  | .getContext => .ctor ``ActionTerm.getContext []
  | .getId => .ctor ``ActionTerm.getId []
  | .closeScope s e => .ctor ``ActionTerm.closeScope [termV s, termV e]
end

def keyV (k : ServiceKey) : V :=
  .struct ``Effect4.ServiceKey
    [ ("name", .struct ``Effect4.ServiceName [("value", .nat k.name.value)])
    , ("service", .struct ``Effect4.ServiceTypeCode [("value", .nat k.service.value)]) ]

def effTyV (t : EffTy) : V :=
  .struct ``EffTy [("answer", tyV t.answer), ("error", tyV t.error), ("requires", .list (t.requires.elems.map keyV))]

/-! ## The corpus -/

namespace Corpus

abbrev P := Eff NativeOp

def ts (xs : List PTerm) : Terms := xs.foldr .cons .nil
def n (k : Nat) : PTerm := .lit (.nat k)
def v (i : Nat) : PTerm := .var i
def u : PTerm := .lit .unit
def opts : ForkOptions := ⟨false, false, .inherit⟩
def st (xs : List (Stmt NativeOp)) : Stmts NativeOp := xs.foldr .cons .nil
def es (xs : List P) : Effs NativeOp := xs.foldr .cons .nil
def binds (steps : List P) (last : P) : P := steps.foldr .bind last

/-- `yieldNow 0` then `7`. -/
def child : P := .bind (.yieldNow 0) (.succeed (n 7))

def p42 : P := .succeed (n 42)
def pBind : P := .bind (.succeed (n 1)) (.succeed (.app "succ" (ts [v 0])))
def pFork : P := .bind (.withFiber (.fork child opts)) (.awaitFiber (v 0) .awaitValue)
def pTwo : P :=
  binds [.withFiber (.fork child opts), .withFiber (.fork child ⟨true, false, .interruptible⟩),
         .awaitFiber (v 0) .awaitValue] (.awaitFiber (v 1) .awaitValue)
def pAwait : P := .bind (.perform .deferredMake u) (.perform .deferredAwait (v 0))
def pGen : P := .gen (st [.bindYield (.succeed (n 1)), .ret (.app "succ" (ts [v 0]))])
def pWhile : P := .whileLoop (n 0) (.app "lt" (ts [v 0, n 3])) (.app "succ" (ts [v 0])) (.yieldNow 0)
def pCatch : P := .catchCause (.fail (n 1)) (.succeed (n 0))
def pStr : P := .succeed (.lit (.str "hi \"there\"\n"))
def pFailCause : P :=
  .failCause (.both (.fail (n 1)) (.both (.die (n 2)) (.both (.interrupt (some (n 3))) (.interrupt none))))
def pYieldError : P := .yieldError (.lit (.bool true))
def pSync : P := .sync (.app "add" (ts [n 2, n 3]))
def pSuspend : P := .suspend (.succeed u)
def pMatch : P := .matchCause (.succeed (n 1)) (.succeed (.app "isZero" (ts [v 0]))) (.succeed (.lit (.bool false)))
def pOnExit : P := .onExit (.succeed (n 1)) (.yieldNow 1)
def pExit : P := .exit (.fail (n 9))
def pMasks : P := .uninterruptible (.interruptible (.succeed (n 1)))
def pBranch : P := .branch (.lit (.bool true)) (.succeed (n 1)) (.fail (n 2))
def pCallback : P := .bind (.perform .deferredMake u) (.callback .deferredAwait (v 0))
def pJoin : P := .bind (.withFiber (.fork child ⟨false, true, .uninterruptible⟩)) (.awaitFiber (v 0) .joinEffect)
def pScoped : P :=
  .scoped (.bind (.perform (.scopeMake .parallel) u)
    (.withFiber (.forkIn (.succeed (n 1)) ⟨true, true, .uninterruptible⟩ (v 0))))
def pAcquire : P := .acquireRelease (.perform .refMake (n 0)) (.perform .refGet (v 0))
def pChoose : P := .choose 3 (.succeed (n 1)) (.succeed (n 2))
def pPair : P := .succeed (.app "fst" (ts [.app "pair" (ts [n 1, .lit (.bool true)])]))
def pStmts : P :=
  .gen (st [ .bindYield (.succeed (n 0))
           , .whileTrue (st [.ifElse (.app "lt" (ts [v 0, n 3])) (st [.yieldDiscard (.yieldNow 0)]) (st [.breakLoop])])
           , .ret (v 0) ])
/-- Every fiber action, one after another; `raceAll` last. -/
def pActions : P :=
  binds
    [ .withFiber (.forkScoped child opts)                                  -- v0 : fiberOf nat never
    , .perform (.scopeMake .sequential) u                                 -- v1 : scope
    , .withFiber (.runIn (v 0) (v 1))                                     -- v2
    , .withFiber (.interrupt (v 0))                                       -- v3
    , .withFiber (.interruptScoped (v 0))                                 -- v4
    , .withFiber .snapshotChildren                                        -- v5 : list (fiberOf unknown unknown)
    , .withFiber (.awaitNewChildren (v 5))                                -- v6
    , .withFiber .getContext                                              -- v7 : context
    , .withFiber (.setContext (v 7))                                      -- v8
    , .withFiber .getId                                                   -- v9 : nat
    , .withFiber (.interruptAll (v 5) (some (v 9)))                       -- v10
    , .withFiber (.interruptAll (v 5) none)                               -- v11
    , .withFiber (.awaitAll (v 5))                                        -- v12
    , .withFiber (.awaitAllFailFast (v 5))                                -- v13
    , .exit (.succeed (n 1))                                              -- v14 : exitOf nat never
    , .withFiber (.closeScope (v 1) (v 14)) ]                             -- v15
    (.withFiber (.raceAll (es [child, .succeed (n 3)])))
/-- Every native operation, one after another; the async row through `callback` last. -/
def pOps : P :=
  binds
    [ .perform .refMake (n 1)                                             -- v0 : ref
    , .perform .refGet (v 0)                                              -- v1
    , .perform .refSet (.app "pair" (ts [v 0, n 2]))                      -- v2 : ref
    , .perform .refGetAndSet (.app "pair" (ts [v 0, n 3]))                -- v3
    , .perform .refSetAndGet (.app "pair" (ts [v 0, n 4]))                -- v4
    , .perform (.refUpdate .incr) (v 0)                                   -- v5
    , .perform (.refGetAndUpdate .double) (v 0)                           -- v6
    , .perform (.refUpdateAndGet .zeroWhenPositive) (v 0)                 -- v7
    , .perform (.refUpdateSome .noChange) (v 0)                           -- v8
    , .perform (.refGetAndUpdateSome .takeAndBump) (v 0)                  -- v9
    , .perform (.refUpdateSomeAndGet .incr) (v 0)                         -- v10
    , .perform (.refModify .double) (v 0)                                 -- v11
    , .perform (.refModifySome .noChange) (v 0)                           -- v12
    , .perform .deferredMake u                                            -- v13 : deferred
    , .perform .deferredIsDone (v 13)                                     -- v14
    , .perform .deferredPoll (v 13)                                       -- v15
    , .perform .deferredSucceed (.app "pair" (ts [v 13, n 1]))            -- v16
    , .perform .deferredFail (.app "pair" (ts [v 13, n 2]))               -- v17
    , .perform (.scopeMake .sequential) u                                 -- v18
    , .perform (.scopeMake .parallel) u ]                                 -- v19
    (.callback .deferredAwait (v 13))

-- ill-typed
def pIll : P := .succeed (.app "succ" (ts [.lit (.bool true)]))
def pIllRet : P := .gen (st [.ret (n 1), .ret (n 2)])
def pIllReq : P := .perform .refGet (n 1)
def pIllBreak : P := .gen (st [.breakLoop])
def pIllBranch : P := .branch (n 1) (.succeed (n 1)) (.succeed (n 2))
def pIllJoin : P := .branch (.lit (.bool true)) (.succeed (n 1)) (.succeed (.lit (.bool true)))
def pIllVar : P := .succeed (v 0)
def pIllCallback : P := .bind (.perform .refMake (n 0)) (.callback .refGet (v 0))
def pIllStep : P := .whileLoop (n 0) (.app "lt" (ts [v 0, n 3])) (.lit (.bool true)) (.yieldNow 0)
def pIllInterruptor : P := .failCause (.interrupt (some (.lit (.bool true))))

def corpus : List (String × P) :=
  [ ("p42", p42), ("pBind", pBind), ("pFork", pFork), ("pTwo", pTwo), ("pAwait", pAwait)
  , ("pGen", pGen), ("pWhile", pWhile), ("pCatch", pCatch), ("pStr", pStr), ("pFailCause", pFailCause)
  , ("pYieldError", pYieldError), ("pSync", pSync), ("pSuspend", pSuspend), ("pMatch", pMatch)
  , ("pOnExit", pOnExit), ("pExit", pExit), ("pMasks", pMasks), ("pBranch", pBranch)
  , ("pCallback", pCallback), ("pJoin", pJoin), ("pScoped", pScoped), ("pAcquire", pAcquire)
  , ("pChoose", pChoose), ("pPair", pPair), ("pStmts", pStmts), ("pActions", pActions), ("pOps", pOps)
  , ("pIll", pIll), ("pIllRet", pIllRet), ("pIllReq", pIllReq), ("pIllBreak", pIllBreak)
  , ("pIllBranch", pIllBranch), ("pIllJoin", pIllJoin), ("pIllVar", pIllVar)
  , ("pIllCallback", pIllCallback), ("pIllStep", pIllStep), ("pIllInterruptor", pIllInterruptor) ]

end Corpus

end OCaml5.Eff
