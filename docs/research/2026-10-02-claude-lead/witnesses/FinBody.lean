import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# `E4-TYPED-CE-036` — the `fin` body's admission types an exit the finalizer never answers

Historical refutation, compiled once at `f4d8be8f` against the pre-change `BodyTyped.fin`
(`Typed/Admission.lean`: `fin name ex ty (hex : ExitOk w ty ex)`), with its log beside it.

`fiberPre` admits `mask false (.fin name ex)` at any `ty` the exit `ex` fits. The evaluator's mask
arm installs `bodyR interp (.fin name ex) = denoteFin name ex` as current code
(`Laws/Program/EvaluateR.lean`, the `mask` arm): the finalizer's own program, not `.pure ex`. For
`name = .interruptFiber ⟨0⟩ true` that program is `fiberValR (.interruptScoped ⟨0⟩) rfl`, which
answers `unit`, so at `ty = ⟨string, never⟩` with `ex = .success (.str "x")` the pre holds and the
installed code is not `TypedProg` at `ty`. The body bridge (`BodyTyped → TypedProg (bodyR …)`),
which the `mask` and `fork` clauses need, is false on the pre-change judgment; a `ConfigTyped`
state with this code current is a refutation of `M6Ledger.step_deliver`'s shape (not built: the
bridge's refutation is the smaller, exact statement).

Repair in the same slice: `BodyTyped.fin` reads `FinalizerAdmitted` and types at rc.112's
finalizer type `⟨unknown, never⟩` (`finalizerTyped_of_admitted`). No producer of `Body.fin`
exists in the tree (the close walk passes `denoteFin` programs directly), so no producer changes.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed.FinBodyWitness

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

def finBody : Body := .fin (.interruptFiber ⟨0⟩ true) (.success (Val.str "x"))

def strTy : EffTy := ⟨.string, .never, Env.Requirement.empty⟩

/-- The pre-change admission: the exit fits, so the mask's pre holds at `strTy`. -/
theorem admitted (root : ProgramSource) (w : World) :
    fiberPre root w (.mask false finBody) strTy :=
  BodyTyped.fin _ _ _ ⟨trivial, trivial⟩

/-- The installed code answers `unit`, which `string` refuses. -/
theorem body_untyped (root : ProgramSource) (w : World) (completed : List (FiberId × ExitV)) :
    ¬ TypedProg root w strTy (bodyR (interpRAt root.program completed) finBody) := by
  intro h
  obtain ⟨_, _, next⟩ := TypedProg.fiber_inv (op := .interruptScoped ⟨0⟩) h
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have ok := TypedProg.pure_inv (next w (leHost_refl w) Val.unit rfl)
  have fits : Fits w Val.unit Ty.string := ok.1
  exact fits

/-- The bridge is false on the pre-change judgment, at every source and world. -/
theorem bridge_refuted (root : ProgramSource) (w : World) (completed : List (FiberId × ExitV)) :
    BodyTyped root w finBody strTy ∧
      ¬ TypedProg root w strTy (bodyR (interpRAt root.program completed) finBody) :=
  ⟨admitted root w, body_untyped root w completed⟩

#print axioms admitted
#print axioms body_untyped
#print axioms bridge_refuted

end Effect4.Program.Typed.FinBodyWitness
