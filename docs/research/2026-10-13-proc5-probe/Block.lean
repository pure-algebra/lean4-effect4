import Effects.Algebra.Laws
import Effect4.Laws.Program.DenoteRows
import Effect4.Api

set_option autoImplicit false
namespace ProcProbe

open Effects

variable {S D : Signature.{0, 0}} {A : Type}

/-- One layer of the knot: the program's own operations pass, and an invocation is handed to
`rec`, applied to the body bound to the invocation's continuation. Structural in the program. -/
def mrecStep (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    (rec : Program (S ⊕ₛ D) A → Program S (Option A)) :
    Program (S ⊕ₛ D) A → Program S (Option A)
  | .pure a => .pure (some a)
  | .vis (.inl s) next => .vis s (fun x => mrecStep rh rec (next x))
  | .vis (.inr d) next => rec ((rh d).bind next)

/-- The budgeted knot: at budget `0` every invocation is the frontier `none`; at `k + 1` an
invocation unfolds its body and continues at budget `k`. -/
def mrecB (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) :
    Nat → Program (S ⊕ₛ D) A → Program S (Option A)
  | 0 => mrecStep rh (fun _ => .pure none)
  | k + 1 => mrecStep rh (mrecB rh k)

/-- The approximation order on budgeted results: a frontier leaf is below everything, a
finished leaf only below itself, and an operation node below the same operation whose answers
are each above. -/
inductive Approx : Program S (Option A) → Program S (Option A) → Prop
  | frontier (q : Program S (Option A)) : Approx (.pure none) q
  | done (a : A) : Approx (.pure (some a)) (.pure (some a))
  | vis (s : S.Op) {k k' : S.Answer s → Program S (Option A)} :
      (∀ x, Approx (k x) (k' x)) → Approx (.vis s k) (.vis s k')

theorem Approx.refl : ∀ (p : Program S (Option A)), Approx p p
  | .pure none => .frontier _
  | .pure (some a) => .done a
  | .vis s k => .vis s (fun x => Approx.refl (k x))

/-- The unfolding at one budget is definitional: an invocation at `k + 1` is its body at `k`. -/
theorem mrecB_invoke (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) (k : Nat) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) :
    mrecB rh (k + 1) (.vis (.inr d) next) = mrecB rh k ((rh d).bind next) := rfl

/-- The step is monotone in its recursive argument. -/
theorem mrecStep_mono (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    {r r' : Program (S ⊕ₛ D) A → Program S (Option A)} (h : ∀ q, Approx (r q) (r' q)) :
    ∀ p, Approx (mrecStep rh r p) (mrecStep rh r' p)
  | .pure a => .done a
  | .vis (.inl s) next => .vis s (fun x => mrecStep_mono rh h (next x))
  | .vis (.inr _) _ => h _

/-- **The budget chain is monotone**: one more budget refines every frontier and keeps every
finished leaf. -/
theorem mrecB_refines (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) :
    ∀ (k : Nat) (p : Program (S ⊕ₛ D) A), Approx (mrecB rh k p) (mrecB rh (k + 1) p)
  | 0, p => mrecStep_mono rh (fun _ => .frontier _) p
  | k + 1, p => mrecStep_mono rh (fun q => mrecB_refines rh k q) p

set_option linter.unusedVariables false in
/-- The chain at an invocation is below the chain at its unfolding, budget for budget. -/
theorem invoke_cofinal_left (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) :
    ∀ k, Approx (mrecB rh k (.vis (.inr d) next)) (mrecB rh k ((rh d).bind next))
  | 0 => .frontier _
  | k + 1 => mrecB_refines rh k _

/-- The chain at the unfolding is below the chain at the invocation, one budget later. -/
theorem invoke_cofinal_right (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) (k : Nat) :
    Approx (mrecB rh k ((rh d).bind next)) (mrecB rh (k + 1) (.vis (.inr d) next)) :=
  Approx.refl _

/-! ## The red control: no single budget solves the unfolding equation -/

/-- A signature with no operation of the program's own. -/
abbrev Empty : Signature.{0, 0} := ⟨PEmpty, fun _ => PUnit⟩

/-- One definition, answering a natural number. -/
abbrev One : Signature.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- The definition's body answers `7` and invokes nothing. -/
def seven : (d : One.Op) → Program (Empty ⊕ₛ One) (One.Answer d) := fun _ => .pure (7 : Nat)

/-- At budget `0` the invocation is the frontier, while its unfolding finishes with `7`. -/
theorem budget_not_unfolding :
    ¬ ∀ k, mrecB seven k (.vis (.inr ()) (fun n => .pure n) : Program (Empty ⊕ₛ One) Nat) =
      mrecB seven k ((seven ()).bind (fun n => .pure n)) := by
  intro h
  have h0 := h 0
  simp only [mrecB, mrecStep, seven, Program.bind] at h0
  cases h0



end ProcProbe

/-! # Probe PROC-5: `denoteRows` reads a definition block -/

namespace Proc5Probe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote ProcProbe

/-- The block's signature: definition `k`'s row, answered by an exit (`RowSig` of the block's rows). -/
abbrev BlockSig (table block : RowTable) : Effects.Signature.{0, 0} :=
  Effects.Signature.sum (RowsSig table) (RowSig block)

/-- `denoteRows` over the stores, the host rows and the block: each arm is `denoteRows`'s, and an
invocation `perform (call k) r` is one node of the block's signature. -/
def denoteBlock (table block : RowTable) : NativeEff → List Val → Effects.Program (BlockSig table block) ExitV
  | .succeed v, env =>
    pure (match evalTerm env v with | some x => Exit.success x | none => badShapeExit)
  | .fail e, env =>
    pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => badShapeExit)
  | .failCause c, env =>
    pure (match causeOf env c with | some cause => Exit.failure cause | none => badShapeExit)
  | .sync t, env => pure (Exit.success ((evalTerm env t).getD Val.unit))
  | .suspend b, env => denoteBlock table block b env
  | .perform op r, env =>
    match op with
    | .external i =>
      match evalTerm env r with
      | some v => if h : i < table.length then
          Effects.Program.vis (.inl (.inr ⟨⟨i, h⟩, v⟩)) Effects.Program.pure else pure outsideExit
      | none => pure badShapeExit
    | .call k =>
      match evalTerm env r with
      | some v => if h : k < block.length then
          Effects.Program.vis (.inr ⟨⟨k, h⟩, v⟩) Effects.Program.pure else pure outsideExit
      | none => pure badShapeExit
    | _ =>
      match (NativeOp.row op).kind with
      | .sync =>
        match (evalTerm env r).bind (NativeOp.syncOpOf op env) with
        | some o => Effects.Program.vis (.inl (.inl o)) fun v => pure (Exit.success v)
        | none => pure badShapeExit
      | _ => pure outsideExit
  | .bind a b, env =>
    Effects.Program.bind (denoteBlock table block a env) (seqRows fun v => denoteBlock table block b (env ++ [v]))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteBlock table block a (env ++ bound.toList)
    | some (false, bound) => denoteBlock table block b (env ++ bound.toList)
    | none => pure badShapeExit
  | .exit b, env =>
    Effects.Program.bind (denoteBlock table block b env) fun ex => pure (Exit.success (reifyExitVal ex))
  | .catchCause b h, env => Effects.Program.bind (denoteBlock table block b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure c => denoteBlock table block h (env ++ [Val.exitErr c])
  | .catchIf test b h, env => Effects.Program.bind (denoteBlock table block b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure cause =>
      match caughtErrorValue? env test cause with
      | some value => denoteBlock table block h (env ++ [value])
      | none => pure (Exit.failure cause)
  | .matchCause b v c, env => Effects.Program.bind (denoteBlock table block b env) fun
    | Exit.success x => denoteBlock table block v (env ++ [x])
    | Exit.failure cause => denoteBlock table block c (env ++ [Val.exitErr cause])
  | .onExit b f, env => Effects.Program.bind (denoteBlock table block b env) fun ex =>
    Effects.Program.bind (denoteBlock table block f (env ++ [reifyExitVal ex])) fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex))
  | _, _ => pure outsideExit

/-- **The meaning of a program with a block, at a budget**: the block's handler (`mrecB`) unfolds
at most `k` nested invocations; a deeper one is the frontier `none`. A program with no block is
`denoteRows`, every leaf finished. A body reads one variable, its request. -/
def denoteDefs (table : RowTable) (k : Nat) : NativeEff → List Val → Effects.Program (RowsSig table) (Option ExitV)
  | .defs decls bodies main _, env =>
    let block := decls.map DefDecl.row
    mrecB (S := RowsSig table) (D := RowSig block)
      (fun d => denoteBlock table block ((bodies.toList.getD d.1.1 (.succeed (.lit .unit)))) [d.2]) k
      (denoteBlock table block main env)
  | e, env => Effects.Program.bind (denoteRows table e env) fun ex => pure (some ex)

/-- The meaning under a reply tape, as `meaningRows`. -/
def meaningDefs (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val) (s : Stores)
    (tape : ReplyTape) : Option ((Option ExitV × Stores) × ReplyTape) :=
  ((Effects.interpret (rowsHandler (tapeHandler table)) (denoteDefs table k e env)).run s).run tape

def exitAt (e : NativeEff) (k : Nat) : Option (Option ExitV) :=
  (meaningDefs [] k e [] Stores.empty []).map (·.1.1)

def ap (name : String) (args : List Term) : Term := .app name (args.foldr (fun a acc => .cons a acc) .nil)
def twiceDecl : DefDecl := { name := "twice", request := .nat, answer := .prod .nat .nat }
def twiceProg : NativeEff :=
  .defs [twiceDecl] (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil) (.perform (.call 0) (.lit (.nat 21))) .nil
def evenOdd (k : Nat) : NativeEff :=
  .defs [{ name := "isEven", request := .nat, answer := .bool }, { name := "isOdd", request := .nat, answer := .bool }]
    (.cons (.select (ap "isZero" [.var 0]) .bool (.succeed (.lit (.bool true))) (.perform (.call 1) (ap "pred" [.var 0])))
      (.cons (.select (ap "isZero" [.var 0]) .bool (.succeed (.lit (.bool false))) (.perform (.call 0) (ap "pred" [.var 0]))) .nil))
    (.perform (.call 0) (.lit (.nat k))) .nil
def spinProg : NativeEff :=
  .defs [{ name := "spin", request := .nat, answer := .nat }] (.cons (.perform (.call 0) (.var 0)) .nil) (.perform (.call 0) (.lit (.nat 1))) .nil

def tag : Option (Option ExitV) → String
  | none => "no answer"
  | some none => "frontier"
  | some (some (.success _)) => "success"
  | some (some (.failure _)) => "failure"

#eval (List.range 3).map fun k => tag (exitAt twiceProg k)
#eval (List.range 10).map fun k => tag (exitAt (evenOdd 7) k)
#eval (List.range 5).map fun k => tag (exitAt spinProg k)
-- the meaning at a budget past the depth agrees with the machine's run
#guard (exitAt twiceProg 1).join == (Api.run twiceProg 200).exit
#guard (exitAt (evenOdd 7) 8).join == (Api.run (evenOdd 7) 400).exit
#guard (exitAt (evenOdd 6) 7).join == (Api.run (evenOdd 6) 400).exit
-- below the depth, the frontier; the spin never finishes and never fails
#guard exitAt (evenOdd 7) 7 == some none
#guard (List.range 20).all fun k => exitAt spinProg k == some none
#guard (Api.run spinProg 60).outcome == .frontier
-- a program with no block: denoteRows, finished at every budget
#guard (List.range 3).all fun k => exitAt (.succeed (.lit (.nat 3))) k == some (some (.success (.nat 3)))
end Proc5Probe
