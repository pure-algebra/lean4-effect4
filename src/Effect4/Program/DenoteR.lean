import Effect4.Program.Sched
import Effect4.Program.Agreement

/-!
# Bounded denotation over stores and fibers (R2)

Contract: `Test/contracts/program-denote-r.contract.md`. Design and authorized
corrections: `docs/research/2026-09-06-w3-r2-continuation.md` and
`docs/research/2026-09-06-r3-r4-implementation.md`.

`denoteR` unfolds the existing `Eff` at a `Point`. Its leading structural budget
bounds this unfolding; `Point.fuel` separately retains the compile's fuel. A
frontier carries the residual address, never a failed exit. The generator uses
the compile's program-counter navigation and environment truncation, but does
not run compiled code to obtain a meaning. `inlineYield` records exactly which
yielded source forms expose an immediate exit before the iterator resumes.

After explicit control erasure the straight fragment restricts to `Denote.denote`
when both budgets cover its depth. The raw terms retain handler and cleanup
boundaries (`E4-SCHED-CE-004`). Fiber nodes are the term scheduler's interface, not a handler
semantics or a simulation theorem. In particular the placeholder `rHandler`
must not be used to interpret a frontier as a finished result (`RDEN-FB-HANDLER`).
Scope and mask nodes carry addressed or synthesized bodies; their execution and
interruption rules live in R3/R4 (`RDEN-FB-SCHEDULER`). Program rows and acquisition/release
remain unsupported frontiers, as in `compileEff` (`RDEN-FB-UNSUPPORTED`).
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- A live frontier, including the control state needed by a later unfolding. -/
def pending (reason : FrontierReason) (at_ : ResumePoint) : RProgram :=
  .vis (.inr (.frontier reason at_)) Effects.Program.pure

/-- Value continuations short-circuit on a failed exit. -/
def seqR (k : Val → RProgram) : ExitV → RProgram
  | .success v => k v
  | .failure c => .pure (.failure c)

/-- Retain a continuation boundary. The normal branch closes it explicitly;
an interrupted body resumes through the saved exit branch instead. -/
def guardR (kind : GuardKind) (body : RProgram) : RProgram :=
  .vis (.inr (.guard_ kind)) fun
    | none => body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure
    | some ex => .pure ex

/-- An exit finalizer has its own boundary, then restores the body's exit and mask.
The runtime implements the mask; erasure below removes only these control markers. -/
def onExitR (body : RProgram) (fin : ExitV → RProgram)
    (interruptible : Bool := false) : RProgram :=
  (guardR (.onExit interruptible) body).bind fun ex =>
    (guardR .all (fin ex)).bind fun fex =>
      .vis (.inr (.finishFinalizer (Exit.restoreAfterFinalizer ex (finVoid fex))))
        Effects.Program.pure

/-- Forget control boundaries for the store meaning, retaining every other operation.
This is an erasure, not a scheduler or a handler for interruption. -/
def controlErasure : Effects.Handler RSig (Effects.Program RSig) where
  handle
    | .inr (.guard_ _) => .pure none
    | .inr (.unguard ex) | .inr (.finishFinalizer ex) => .pure ex
    | op => .vis op Effects.Program.pure

def eraseControl {A : Type} (program : Effects.Program RSig A) : Effects.Program RSig A :=
  Effects.interpret controlErasure program

theorem eraseControl_pure {A : Type} (a : A) :
    eraseControl (Effects.Program.pure a) = .pure a := rfl

theorem eraseControl_bind {A B : Type} (p : Effects.Program RSig A)
    (k : A → Effects.Program RSig B) :
    eraseControl (p.bind k) = (eraseControl p).bind (fun a => eraseControl (k a)) :=
  Effects.interpret_bind controlErasure p k

theorem eraseControl_guardR (kind : GuardKind) (body : RProgram) :
    eraseControl (guardR kind body) = eraseControl body := by
  change eraseControl (body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure) = _
  rw [eraseControl_bind]
  exact Effects.Program.bind_pure_right _

theorem eraseControl_onExitR (body : RProgram) (fin : ExitV → RProgram) (flag : Bool) :
    eraseControl (onExitR body fin flag) =
      (eraseControl body).bind fun ex => (eraseControl (fin ex)).bind fun fex =>
        .pure (Exit.restoreAfterFinalizer ex (finVoid fex)) := by
  simp only [onExitR, eraseControl_bind, eraseControl_guardR]
  rfl

/-- Race entrants use the same list-node addresses as `actionAt.entrants`. -/
def entrantPoints : Effs NativeOp → Point → List Point
  | .nil, _ => []
  | .cons _ rest, p => p.child 0 :: entrantPoints rest (p.child 1)

def racePoints (root : NativeEff) (p : Point) : List Point :=
  match Node.at_ (.eff root) p.path with
  | some (.eff (.withFiber (.raceAll es))) => entrantPoints es ((p.child 0).child 0)
  | _ => []

/-- The fiber action selected by the actual point lookup. Program-valued fields of
`actionAt` are represented by their source addresses, never stored as `Prim`. -/
def denoteAction (root : NativeEff) (p : Point) : RProgram :=
  match actionAt root p with
  | none => .pure outsideExit
  | some action =>
    match action with
    | .fork _ options =>
      .vis (.inr (.fork (.at_ ((p.child 0).child 0)) options)) fun v => .pure (.success v)
    | .forkIn _ options scope key =>
      .vis (.inr (.forkIn ((p.child 0).child 0) options scope key)) fun v => .pure (.success v)
    | .forkScoped _ options key =>
      .vis (.inr (.forkScoped ((p.child 0).child 0) options key)) Effects.Program.pure
    | .runIn target scope key =>
      .vis (.inr (.runIn target scope key)) fun v => .pure (.success v)
    | .interrupt target => .vis (.inr (.interrupt target)) fun v => .pure (.success v)
    | .interruptScoped target =>
      .vis (.inr (.interruptScoped target)) fun v => .pure (.success v)
    | .interruptAll targets who =>
      .vis (.inr (.interruptAll targets who)) fun v => .pure (.success v)
    | .awaitAll targets => .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)
    | .awaitAllFailFast targets =>
      .vis (.inr (.awaitAllFailFast targets)) fun v => .pure (.success v)
    | .snapshotChildren => .vis (.inr .snapshotChildren) fun v => .pure (.success v)
    | .awaitNewChildren snapshot =>
      .vis (.inr (.awaitNewChildren snapshot)) fun v => .pure (.success v)
    | .raceAll _ => .vis (.inr (.raceAll (racePoints root p))) Effects.Program.pure
    | .setInterruptible _ flag =>
      .vis (.inr (.mask flag (.at_ (p.child 0)))) Effects.Program.pure
    | .setContext ctx => .vis (.inr (.setContext ctx)) fun v => .pure (.success v)
    | .getContext => .vis (.inr .getContext) fun v => .pure (.success v)
    | .getId => .vis (.inr .getId) fun v => .pure (.success v)
    | .closeScope scope ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure
    | .refuse cause => .pure (.failure cause)
    | .dropObservers token => .vis (.inr (.dropObservers token)) fun v => .pure (.success v)
    | .cancelRace race => .vis (.inr (.cancelRace race)) fun v => .pure (.success v)

/-- Async registration answers with an exit; failure is not a successful error value.
The request and registration name retain the exact `Deferred.await` decoding. -/
def denoteAsync (request : Term) (p : Point) : RProgram :=
  match evalTerm p.env request with
  | none => .pure badShapeExit
  | some value =>
    match NativeOp.awaitCellOf value with
    | none => .pure badShapeExit
    | some cell => .vis (.inr (.async (.registerAwait cell) value)) Effects.Program.pure

/-- A yielded source form with an immediate `Prim.success` or `Prim.failure` head.
`sync`, `yieldError` with a valid argument, and compound frames are not inline exits.
The definition inspects source data only; its compiler-head equation is checked below. -/
def inlineYield : NativeEff → Point → Option ExitV
  | e, p =>
    if p.fuel = 0 then none else
    match e with
    | .succeed t => some (match evalTerm p.env t with
      | some v => .success v | none => badShapeExit)
    | .fail t => some (match evalTerm p.env t with
      | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
    | .failCause t => some (match causeOf p.env t with
      | some c => .failure c | none => badShapeExit)
    | .yieldError t => match evalTerm p.env t with
      | some _ => none | none => some badShapeExit
    | .perform op request =>
      match (NativeOp.row op).kind with
      | .sync => match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
        | some _ => none | none => some badShapeExit
      | .async => match (evalTerm p.env request).bind NativeOp.awaitCellOf with
        | some _ => none | none => some badShapeExit
      | .program => none
    | .callback op request =>
      match (NativeOp.row op).kind with
      | .async => match (evalTerm p.env request).bind NativeOp.awaitCellOf with
        | some _ => none | none => some badShapeExit
      | _ => some badShapeExit
    | .awaitFiber target _ => match evalTerm p.env target with
      | some (.fiber _) => none | _ => some badShapeExit
    | .whileLoop initial _ _ _ => match evalTerm p.env initial with
      | some _ => none | none => some badShapeExit
    | .choose _ left right => match p.tape with
      | true :: rest => inlineYield left { p with path := p.path ++ [0], tape := rest }
      | false :: rest => inlineYield right { p with path := p.path ++ [1], tape := rest }
      | [] => none
    | _ => none

mutual
  /-- Bounded unfolding at an address. Compile fuel and unfolding fuel are distinct. -/
  def denoteR (root : NativeEff) : Nat → NativeEff → Point → RProgram
    | 0, _, p => pending (if p.fuel = 0 then .compileFuel else .unfoldingFuel) (.effect p)
    | n + 1, e, p =>
      match p.fuel with
      | 0 => pending .compileFuel (.effect p)
      | _ + 1 =>
        match e with
        | .succeed t => .pure (match evalTerm p.env t with
          | some v => .success v | none => badShapeExit)
        | .fail t => .pure (match evalTerm p.env t with
          | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
        | .failCause t => .pure (match causeOf p.env t with
          | some c => .failure c | none => badShapeExit)
        | .yieldError t => .pure (match evalTerm p.env t with
          | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
        | .sync t => .pure (.success ((evalTerm p.env t).getD Val.unit))
        | .suspend b => denoteR root n b (p.child 0)
        | .perform op request =>
          match (NativeOp.row op).kind with
          | .sync =>
            match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
            | some operation => .vis (.inl operation) fun v => .pure (.success v)
            | none => .pure badShapeExit
          | .async => denoteAsync request p
          | .program => pending .unsupported (.effect p)
        | .bind a b => (guardR .onSuccess (denoteR root n a (p.child 0))).bind
          (seqR fun v => denoteR root n b (p.childWith 1 v))
        | .branch test a b =>
          match evalTerm p.env test with
          | some (.bool true) => denoteR root n a (p.child 0)
          | some (.bool false) => denoteR root n b (p.child 1)
          | _ => .pure badShapeExit
        | .exit b => (guardR .all (denoteR root n b (p.child 0))).bind fun ex =>
          .pure (.success (reifyExitVal ex))
        | .catchCause b h => (guardR .onFailure (denoteR root n b (p.child 0))).bind fun
          | .success v => .pure (.success v)
          | .failure c => denoteR root n h (p.childWith 1 (.exitErr c))
        | .matchCause b v c => (guardR .all (denoteR root n b (p.child 0))).bind fun
          | .success x => denoteR root n v (p.childWith 1 x)
          | .failure cause => denoteR root n c (p.childWith 2 (.exitErr cause))
        | .onExit b f => onExitR (denoteR root n b (p.child 0)) fun ex =>
          denoteR root n f (p.childWith 1 (reifyExitVal ex))
        | .gen _ => denoteGen root n p p.fuel [] p.env
        | .whileLoop initial _ _ _ =>
          match evalTerm p.env initial with
          | some cursor => denoteLoop root n p cursor
          | none => .pure badShapeExit
        | .yieldNow priority => .vis (.inr (.yieldNow priority)) fun _ => .pure (.success .unit)
        | .callback op request =>
          match (NativeOp.row op).kind with
          | .async => denoteAsync request p
          | _ => .pure badShapeExit
        | .awaitFiber target mode =>
          match evalTerm p.env target with
          | some (.fiber id) => match mode with
            | .joinEffect => .vis (.inr (.await id .joinEffect)) Effects.Program.pure
            | .awaitValue => .vis (.inr (.await id .awaitValue)) fun v => .pure (.success v)
          | _ => .pure badShapeExit
        | .uninterruptible _ | .interruptible _ | .withFiber _ => denoteAction root p
        | .scoped _ => .vis (.inl (.scopeMake .sequential)) fun
          | .scopeHandle scope => .vis (.inr (.scoped (p.child 0) scope)) Effects.Program.pure
          | _ => .pure badShapeExit
        | .acquireRelease _ _ => pending .unsupported (.effect p)
        | .choose _ left right =>
          match p.tape with
          | true :: rest => denoteR root n left { p with path := p.path ++ [0], tape := rest }
          | false :: rest => denoteR root n right { p with path := p.path ++ [1], tape := rest }
          | [] => pending .unansweredChoice (.effect p)

  /-- The generator walker. Its scan budget resets from the saved point after a
  resumed yield, exactly as `iterNext`; inline exits continue with the remaining scan. -/
  def denoteGen (root : NativeEff) : Nat → Point → Nat → List Nat → List Val → RProgram
    | 0, p, scan, pc, env =>
      pending (if scan = 0 then .compileFuel else .unfoldingFuel) (.generator p pc env scan)
    | n + 1, p, scan, pc, env =>
      match scan with
      | 0 => pending .compileFuel (.generator p pc env 0)
      | fuel + 1 =>
        match blockAt root p pc with
        | none => .pure badShapeExit
        | some .nil => match blockExit root p pc env with
          | none => .pure (.success .unit)
          | some (pc', env') => denoteGen root n p fuel pc' env'
        | some (.cons stmt _) =>
          match stmt with
          | .bindYield e => denoteYield root n p fuel pc env e true
          | .yieldDiscard e => denoteYield root n p fuel pc env e false
          | .ret value => .pure (match evalTerm env value with
            | some v => .success v | none => badShapeExit)
          | .ifElse test _ _ => match evalTerm env test with
            | some (.bool true) => denoteGen root n p fuel (pc ++ [0, 0]) env
            | some (.bool false) => denoteGen root n p fuel (pc ++ [0, 1]) env
            | _ => .pure badShapeExit
          | .whileTrue _ => denoteGen root n p fuel (pc ++ [0, 0]) env
          | .breakLoop => match loopExit root (pc.length + 1) p pc env with
            | some (pc', env') => denoteGen root n p fuel pc' env'
            | none => .pure badShapeExit

  /-- A yield's child point and advanced continuation. Kept separate to preserve the
  distinction between inline source exits and resumed computations. -/
  def denoteYield (root : NativeEff) :
      Nat → Point → Nat → List Nat → List Val → NativeEff → Bool → RProgram
    | 0, p, fuel, pc, env, _, _ =>
      pending .unfoldingFuel (.generator p pc env (fuel + 1))
    | n + 1, p, fuel, pc, env, e, bind =>
      let q : Point := { p with path := p.path ++ [0] ++ pc ++ [0, 0], env, fuel := fuel + 1 }
      match inlineYield e q with
      | some (.success value) =>
        denoteGen root n p fuel (pc ++ [1]) (if bind then env ++ [value] else env)
      | some (.failure cause) => .pure (.failure cause)
      | none => (guardR .onSuccess (denoteR root n e q)).bind (seqR fun value =>
        denoteGen root n { p with env } p.fuel (pc ++ [1])
          (if bind then env ++ [value] else env))

  /-- Cursor loops retain their compile point across iterations. Only the unfolding
  budget decreases; the step's fallback is the previous cursor, as in `interpOf`. -/
  def denoteLoop (root : NativeEff) : Nat → Point → Val → RProgram
    | 0, p, cursor => pending .unfoldingFuel (.loop p cursor)
    | n + 1, p, cursor =>
      match loopAt root p with
      | none => .pure (.success .unit)
      | some (test, step, body) =>
        if evalTerm (p.env ++ [cursor]) test = some (.bool true) then
          (guardR .onSuccess (denoteR root n body (p.childWith 0 cursor))).bind (seqR fun value =>
            denoteLoop root n p ((evalTerm (p.env ++ [cursor, value]) step).getD cursor))
        else .pure (.success .unit)
end

/-! ## The address and frontier equations -/

theorem denoteR_zero (root e : NativeEff) (p : Point) :
    denoteR root 0 e p =
      pending (if p.fuel = 0 then .compileFuel else .unfoldingFuel) (.effect p) := rfl

theorem denoteR_compile_zero (root e : NativeEff) (n : Nat) (p : Point) (h : p.fuel = 0) :
    denoteR root n e p = pending .compileFuel (.effect p) := by
  cases n <;> simp only [denoteR, h, ↓reduceIte]

theorem denoteR_bind (root : NativeEff) (n : Nat) (a b : NativeEff) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (n + 1) (.bind a b) p =
      (guardR .onSuccess (denoteR root n a (p.child 0))).bind
        (seqR fun v => denoteR root n b (p.childWith 1 v)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_branch (root : NativeEff) (n : Nat) (t : Term) (a b : NativeEff) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (n + 1) (.branch t a b) p =
      match evalTerm p.env t with
      | some (.bool true) => denoteR root n a (p.child 0)
      | some (.bool false) => denoteR root n b (p.child 1)
      | _ => .pure badShapeExit := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_choose (root : NativeEff) (n site : Nat) (a b : NativeEff) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (n + 1) (.choose site a b) p =
      match p.tape with
      | true :: rest => denoteR root n a { p with path := p.path ++ [0], tape := rest }
      | false :: rest => denoteR root n b { p with path := p.path ++ [1], tape := rest }
      | [] => pending .unansweredChoice (.effect p) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_withFiber (root : NativeEff) (n : Nat) (action : ActionTerm NativeOp)
    (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (n + 1) (.withFiber action) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_gen (root : NativeEff) (n : Nat) (body : Stmts NativeOp)
    (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (n + 1) (.gen body) p = denoteGen root n p p.fuel [] p.env := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_whileLoop (root : NativeEff) (n : Nat) (initial test step : Term)
    (body : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (n + 1) (.whileLoop initial test step body) p =
      match evalTerm p.env initial with
      | some cursor => denoteLoop root n p cursor
      | none => .pure badShapeExit := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

/-- Only the two immediate exit constructors; all other heads require a machine step. -/
def headExit : NCode → Option ExitV
  | .success v => some (.success v)
  | .failure c => some (.failure c)
  | _ => none

theorem inlineYield_eq_headExit (e : NativeEff) (p : Point) :
    inlineYield e p = headExit (compileEff e p) := by
  cases hf : p.fuel with
  | zero =>
    cases e <;> simp only [inlineYield, compileEff, hf, ↓reduceIte, frontier, headExit]
  | succ f =>
    cases e with
    | choose site a b =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases ht : p.tape with
      | nil => rfl
      | cons choice rest =>
        cases choice <;> dsimp only
        · exact inlineYield_eq_headExit b _
        · exact inlineYield_eq_headExit a _
    | perform op request =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases hk : (NativeOp.row op).kind with
      | sync =>
        cases hv : evalTerm p.env request with
        | none => rfl
        | some value =>
          dsimp only [Option.bind]
          cases NativeOp.syncOpOf op value <;> rfl
      | async => cases (evalTerm p.env request).bind NativeOp.awaitCellOf <;> rfl
      | program => rfl
    | callback op request =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases hk : (NativeOp.row op).kind with
      | sync | program => rfl
      | async => cases (evalTerm p.env request).bind NativeOp.awaitCellOf <;> rfl
    | succeed t | fail t | yieldError t | whileLoop t _ _ _ =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env t <;> rfl
    | failCause c =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases causeOf p.env c <;> rfl
    | awaitFiber target mode =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env target with
      | none => rfl
      | some v => cases v <;> rfl
    | sync _ | suspend _ | bind _ _ | gen _ | catchCause _ _ | matchCause _ _ _
    | onExit _ _ | exit _ | uninterruptible _ | interruptible _ | branch _ _ _
    | yieldNow _ | withFiber _ | «scoped» _ | acquireRelease _ _ =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte, headExit, frontier]
termination_by structural e

/-! ## Restriction to the existing straight denotation -/

theorem denoteR_straight (root : NativeEff) (n : Nat) (e : NativeEff) (p : Point)
    (hs : Straight e = true) (hn : Agreement.depth e ≤ n) (hp : Agreement.depth e ≤ p.fuel) :
    eraseControl (denoteR root n e p) = Effects.Program.inl (denote e p.env) := by
  induction n generalizing e p with
  | zero =>
    have impossible : False := by have := Agreement.depth_pos e; omega
    exact impossible.elim
  | succ n ih =>
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos e; omega
    cases hf : p.fuel with
    | zero => exact (hpos hf).elim
    | succ f =>
      cases e with
      | succeed t | fail t | failCause t | yieldError t | sync t =>
        rw [denoteR, hf, denote]
        rfl
      | perform op request =>
        have hk := Straight.perform_sync hs
        simp only [denoteR, hf, denote, hk]
        cases (evalTerm p.env request).bind (NativeOp.syncOpOf op) <;> rfl
      | suspend b =>
        rw [denoteR, hf, denote]
        exact ih b (p.child 0) hs (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      | bind a b =>
        have hab := Straight.bind hs
        have ha := ih a (p.child 0) hab.1
          (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        rw [denoteR_bind root n a b p hpos, eraseControl_bind, eraseControl_guardR,
          ha, denote, Effects.Program.inl_bind]
        congr 1
        funext ex
        cases ex with
        | failure c => rfl
        | success v =>
          exact ih b (p.childWith 1 v) hab.2
            (by simp only [Agreement.depth] at hn; omega)
            (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
      | branch test a b =>
        have hab := Straight.branch hs
        rw [denoteR_branch root n test a b p hpos, denote]
        split
        · rename_i ht
          rw [ht]
          exact ih a (p.child 0) hab.1
            (by simp only [Agreement.depth] at hn; omega)
            (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        · rename_i ht
          rw [ht]
          exact ih b (p.child 1) hab.2
            (by simp only [Agreement.depth] at hn; omega)
            (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        · split
          · contradiction
          · contradiction
          · rfl
      | exit b =>
        have hb := ih b (p.child 0) hs
          (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        rw [denoteR, hf, eraseControl_bind, eraseControl_guardR,
          hb, denote, Effects.Program.inl_bind]
        rfl
      | catchCause b h =>
        have hbh := Straight.catchCause hs
        have hb := ih b (p.child 0) hbh.1
          (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        rw [denoteR, hf, eraseControl_bind, eraseControl_guardR,
          hb, denote, Effects.Program.inl_bind]
        congr 1
        funext ex
        cases ex with
        | success v => rfl
        | failure c =>
          exact ih h (p.childWith 1 (.exitErr c)) hbh.2
            (by simp only [Agreement.depth] at hn; omega)
            (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
      | matchCause b v c =>
        have hparts := Straight.matchCause hs
        have hb := ih b (p.child 0) hparts.1
          (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        rw [denoteR, hf, eraseControl_bind, eraseControl_guardR,
          hb, denote, Effects.Program.inl_bind]
        congr 1
        funext ex
        cases ex with
        | success value =>
          exact ih v (p.childWith 1 value) hparts.2.1
            (by simp only [Agreement.depth] at hn; omega)
            (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
        | failure cause =>
          exact ih c (p.childWith 2 (.exitErr cause)) hparts.2.2
            (by simp only [Agreement.depth] at hn; omega)
            (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
      | onExit b fin =>
        have hparts := Straight.onExit hs
        have hb := ih b (p.child 0) hparts.1
          (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
        rw [denoteR, hf, eraseControl_onExitR, hb, denote, Effects.Program.inl_bind]
        congr 1
        funext ex
        have hfin := ih fin (p.childWith 1 (reifyExitVal ex)) hparts.2
          (by simp only [Agreement.depth] at hn; omega)
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
        rw [hfin, Effects.Program.inl_bind]
        rfl
      | gen _ | uninterruptible _ | interruptible _ | whileLoop _ _ _ _ | yieldNow _
      | callback _ _ | awaitFiber _ _ | withFiber _ | «scoped» _ | acquireRelease _ _
      | choose _ _ _ => simp only [Straight, Bool.false_eq_true] at hs

theorem meaning_denoteR_straight (root : NativeEff) (n : Nat) (e : NativeEff) (p : Point)
    (hs : Straight e = true) (hn : Agreement.depth e ≤ n) (hp : Agreement.depth e ≤ p.fuel)
    (stores : Stores) :
    (Effects.interpret rHandler (eraseControl (denoteR root n e p))).run stores =
      meaning e p.env stores := by
  rw [denoteR_straight root n e p hs hn hp]
  exact meaning_via_rsig e p.env stores

end Effect4.Program.Sched
