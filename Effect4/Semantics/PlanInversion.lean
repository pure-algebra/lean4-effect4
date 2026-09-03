import Effect4.Semantics.Runs

/-!
# Semantics.PlanInversion

Owner: reading a `plan` backwards. `Effect4/Semantics/Runs.lean` defines
`plan`, the pure control decision of one block; this module says what each of
its shapes can have come from.

Seven inversion lemmas -- one per shape `plan` can take other than `stuck` --
and the two readings of a `branch`'s test operand they need. Every one is
stated over an arbitrary `FlowAlphabet` so that the alphabet's `lookup` stays
opaque: a lowering's alphabet is a table, and unfolding it turns `lookup` into
a `dite` no equation can be rewritten into.

They lived in `Effect4/Target/TypeScript/SkeletonSemantics.lean` until
2026-09-03 (survey finding L7), which meant nothing outside the TypeScript
target could invert a plan without importing the skeleton IR. They are facts
about `Effect4.Flow.plan` and belong beside it.
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val)

section Inversion

variable {Ty : Type} {alphabet : FlowAlphabet Ty} {block : RawBlock Ty} {env : Env} {tape : Tape}

/-- The boolean reading of a test operand is a `Val.bool` in the environment. -/
theorem testValue_some {test : Var} {value : Bool} (h : testValue env test = some value) :
    env[test.index]? = some (.bool value) := by
  unfold testValue at h
  split at h
  · rename_i b read
    simp only [Option.some.injEq] at h
    subst h
    exact read
  · cases h

/-- A test operand whose boolean reading is not the tape's answer does not hold
that answer's `Val.bool` either — the machine's own form of the disagreement
(`E4-FLOW-CE-029`). -/
theorem testValue_ne {test : Var} {answer : Bool} {value : Val}
    (at_ : env[test.index]? = some value) (ne : testValue env test ≠ some answer) :
    value ≠ .bool answer := by
  intro eq
  exact ne (by simp [testValue, at_, eq])

theorem plan_ret_inv {value : Val} (planned : plan alphabet block env tape = .ret value) :
    ∃ v : Var, block.term = .ret v ∧ env[v.index]? = some value := by
  cases hterm : block.term with
  | ret v =>
      cases read : env[v.index]? with
      | none => simp [plan, hterm, read] at planned
      | some w =>
          simp only [plan, hterm, read, Plan.ret.injEq] at planned
          exact ⟨v, rfl, by rw [read, planned]⟩
  | jump target args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation request target args =>
      cases known : alphabet.lookup operation <;> cases got : env[request.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned
  | performCatch operation request target args onError errorArgs =>
      cases known : alphabet.lookup operation <;> cases got : env[request.index]? <;>
        cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
        simp [plan, hterm, known, got, read, readE] at planned
  | branch test site onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read site with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              cases tv : testValue env test with
              | none => simp [plan, hterm, read, answered, tv] at planned
              | some value =>
                  simp only [plan, hterm, read, answered, tv] at planned
                  split at planned <;> simp at planned

theorem plan_jump_inv {target : BlockId} {env' : Env}
    (planned : plan alphabet block env tape = .jump target env') :
    ∃ args, block.term = .jump target args ∧ readArgs env args = some env' := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          simp only [plan, hterm, read, Plan.jump.injEq] at planned
          obtain ⟨rfl, rfl⟩ := planned
          exact ⟨args, rfl, read⟩
  | perform operation request target args =>
      cases known : alphabet.lookup operation <;> cases got : env[request.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned
  | performCatch operation request tgt args onError errorArgs =>
      cases known : alphabet.lookup operation <;> cases got : env[request.index]? <;>
        cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
        simp [plan, hterm, known, got, read, readE] at planned
  | branch test site onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read site with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              cases tv : testValue env test with
              | none => simp [plan, hterm, read, answered, tv] at planned
              | some value =>
                  simp only [plan, hterm, read, answered, tv] at planned
                  split at planned <;> simp at planned

theorem plan_perform_inv {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
    (planned : plan alphabet block env tape = .perform op request target env') :
    ∃ (operation : OperationId) (requestVar : Var) (args : List Var),
      block.term = .perform operation requestVar target args
        ∧ alphabet.lookup operation = some op
        ∧ env[requestVar.index]? = some request
        ∧ readArgs env args = some env' := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation with
      | none =>
          cases got : env[requestVar.index]? <;> cases read : readArgs env args <;>
            simp [plan, hterm, known, got, read] at planned
      | some found =>
          cases got : env[requestVar.index]? with
          | none =>
              cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
          | some requested =>
              cases read : readArgs env args with
              | none => simp [plan, hterm, known, got, read] at planned
              | some values =>
                  simp only [plan, hterm, known, got, read, Plan.perform.injEq] at planned
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := planned
                  exact ⟨operation, requestVar, args, rfl, known, got, read⟩
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned
  | performCatch operation requestVar tgt args onError errorArgs =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
        simp [plan, hterm, known, got, read, readE] at planned
  | branch test site onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read site with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              cases tv : testValue env test with
              | none => simp [plan, hterm, read, answered, tv] at planned
              | some value =>
                  simp only [plan, hterm, read, answered, tv] at planned
                  split at planned <;> simp at planned

/-- Flow v3: a caught perform plans exactly from a `performCatch` block. -/
theorem plan_performCatch_inv {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
    {onError : BlockId} {errorEnv : Env}
    (planned : plan alphabet block env tape = .performCatch op request target env' onError errorEnv) :
    ∃ (operation : OperationId) (requestVar : Var) (args errorArgs : List Var),
      block.term = .performCatch operation requestVar target args onError errorArgs
        ∧ alphabet.lookup operation = some op
        ∧ env[requestVar.index]? = some request
        ∧ readArgs env args = some env'
        ∧ readArgs env errorArgs = some errorEnv := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args <;> cases answered : tape.read decision <;>
        simp [plan, hterm, read, answered] at planned
  | performCatch operation requestVar tgt args onErr errorArgs =>
      cases known : alphabet.lookup operation with
      | none =>
          cases got : env[requestVar.index]? <;> cases read : readArgs env args <;>
            cases readE : readArgs env errorArgs <;>
            simp [plan, hterm, known, got, read, readE] at planned
      | some found =>
          cases got : env[requestVar.index]? with
          | none =>
              cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
                simp [plan, hterm, known, got, read, readE] at planned
          | some requested =>
              cases read : readArgs env args with
              | none =>
                  cases readE : readArgs env errorArgs <;>
                    simp [plan, hterm, known, got, read, readE] at planned
              | some values =>
                  cases readE : readArgs env errorArgs with
                  | none => simp [plan, hterm, known, got, read, readE] at planned
                  | some errorValues =>
                      simp only [plan, hterm, known, got, read, readE,
                        Plan.performCatch.injEq] at planned
                      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := planned
                      exact ⟨operation, requestVar, args, errorArgs, rfl, known, got, read, readE⟩
  | branch test site onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read site with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              cases tv : testValue env test with
              | none => simp [plan, hterm, read, answered, tv] at planned
              | some value =>
                  simp only [plan, hterm, read, answered, tv] at planned
                  split at planned <;> simp at planned

/-- A planned decision comes from a `choose`, or (Flow v3) from a `branch` whose
value, when it has one, agrees with the tape. -/
theorem plan_choose_inv {site : DecisionId} {branch : Bool} {target : BlockId} {env' : Env}
    {rest : Tape}
    (planned : plan alphabet block env tape = .choose site branch target env' rest) :
    (∃ (left right : BlockId) (args : List Var),
      block.term = .choose site left right args
        ∧ readArgs env args = some env'
        ∧ tape.read site = .answered branch rest
        ∧ target = (if branch then left else right))
    ∨ (∃ (test : Var) (onTrue onFalse : BlockId) (args : List Var),
      block.term = .branch test site onTrue onFalse args
        ∧ readArgs env args = some env'
        ∧ tape.read site = .answered branch rest
        ∧ target = (if branch then onTrue else onFalse)
        ∧ testValue env test = some branch) := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              simp only [plan, hterm, read, answered, Plan.choose.injEq] at planned
              obtain ⟨rfl, rfl, eqTarget, rfl, rfl⟩ := planned
              exact Or.inl ⟨left, right, args, rfl, read, answered, eqTarget.symm⟩
  | performCatch operation requestVar tgt args onError errorArgs =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
        simp [plan, hterm, known, got, read, readE] at planned
  | branch test decision onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              simp only [plan, hterm, read, answered] at planned
              split at planned
              · rename_i agreed
                simp only [Plan.choose.injEq] at planned
                obtain ⟨rfl, rfl, eqTarget, rfl, rfl⟩ := planned
                exact Or.inr ⟨test, onTrue, onFalse, args, rfl, read, answered, eqTarget.symm,
                  agreed⟩
              · simp at planned

/-- An unanswered decision comes from a `choose` or a `branch` at an exhausted tape. -/
theorem plan_exhausted_inv {site : DecisionId}
    (planned : plan alphabet block env tape = .exhausted site) :
    (∃ (left right : BlockId) (args : List Var),
      block.term = .choose site left right args ∧ tape.read site = .exhausted)
    ∨ (∃ (test : Var) (onTrue onFalse : BlockId) (args : List Var),
      block.term = .branch test site onTrue onFalse args ∧ tape.read site = .exhausted) := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted =>
              simp only [plan, hterm, read, answered, Plan.exhausted.injEq] at planned
              subst planned
              exact Or.inl ⟨left, right, args, rfl, answered⟩
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more => simp [plan, hterm, read, answered] at planned
  | performCatch operation requestVar tgt args onError errorArgs =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
        simp [plan, hterm, known, got, read, readE] at planned
  | branch test decision onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted =>
              simp only [plan, hterm, read, answered, Plan.exhausted.injEq] at planned
              subst planned
              exact Or.inr ⟨test, onTrue, onFalse, args, rfl, answered⟩
          | mismatch expected actual => simp [plan, hterm, read, answered] at planned
          | answered chosen more =>
              cases tv : testValue env test with
              | none => simp [plan, hterm, read, answered, tv] at planned
              | some value =>
                  simp only [plan, hterm, read, answered, tv] at planned
                  split at planned <;> simp at planned

/-- A refusal comes from a `choose` or a `branch` at a tape naming another site,
or (Flow v3) from a `branch` whose value disagrees with the tape's answer. -/
theorem plan_mismatch_inv {expected actual : DecisionId}
    (planned : plan alphabet block env tape = .mismatch expected actual) :
    (∃ (site : DecisionId) (left right : BlockId) (args : List Var),
      block.term = .choose site left right args
        ∧ tape.read site = .mismatch expected actual)
    ∨ (∃ (test : Var) (site : DecisionId) (onTrue onFalse : BlockId) (args : List Var),
      block.term = .branch test site onTrue onFalse args
        ∧ tape.read site = .mismatch expected actual)
    ∨ (∃ (test : Var) (onTrue onFalse : BlockId) (args : List Var) (chosen : Bool) (more : Tape),
      block.term = .branch test expected onTrue onFalse args
        ∧ actual = expected
        ∧ tape.read expected = .answered chosen more
        ∧ testValue env test ≠ some chosen) := by
  cases hterm : block.term with
  | ret v => cases read : env[v.index]? <;> simp [plan, hterm, read] at planned
  | jump tgt args => cases read : readArgs env args <;> simp [plan, hterm, read] at planned
  | perform operation requestVar tgt args =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> simp [plan, hterm, known, got, read] at planned
  | choose decision left right args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch e a =>
              simp only [plan, hterm, read, answered, Plan.mismatch.injEq] at planned
              obtain ⟨rfl, rfl⟩ := planned
              exact Or.inl ⟨decision, left, right, args, rfl, answered⟩
          | answered chosen more => simp [plan, hterm, read, answered] at planned
  | performCatch operation requestVar tgt args onError errorArgs =>
      cases known : alphabet.lookup operation <;> cases got : env[requestVar.index]? <;>
        cases read : readArgs env args <;> cases readE : readArgs env errorArgs <;>
        simp [plan, hterm, known, got, read, readE] at planned
  | branch test decision onTrue onFalse args =>
      cases read : readArgs env args with
      | none => simp [plan, hterm, read] at planned
      | some values =>
          cases answered : tape.read decision with
          | exhausted => simp [plan, hterm, read, answered] at planned
          | mismatch e a =>
              simp only [plan, hterm, read, answered, Plan.mismatch.injEq] at planned
              obtain ⟨rfl, rfl⟩ := planned
              exact Or.inr (Or.inl ⟨test, decision, onTrue, onFalse, args, rfl, answered⟩)
          | answered chosen more =>
              simp only [plan, hterm, read, answered] at planned
              split at planned
              · simp at planned
              · rename_i disagreed
                simp only [Plan.mismatch.injEq] at planned
                obtain ⟨rfl, rfl⟩ := planned
                exact Or.inr (Or.inr ⟨test, onTrue, onFalse, args, chosen, more, rfl, rfl,
                  answered, disagreed⟩)

end Inversion

end Effect4.Flow
