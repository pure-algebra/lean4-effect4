import Effect4.Laws.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

namespace CritiqueStaging

-- Kernel-checked equations over the actual repository definitions; see evidence.json.
theorem absolute_zero_reads_context : evalTerm [Val.bool true, Val.nat 7] (.var 0) = some (Val.bool true) := rfl
theorem input_reads_context_length : evalTerm [Val.bool true, Val.nat 7] (.var 1) = some (Val.nat 7) := rfl
theorem wrong_identity_type : effTy (nativeSignature []) [.bool, .nat] (.succeed (.var 0)) =
    some (EffTy.pure .bool) := rfl
theorem correct_identity_type : effTy (nativeSignature []) [.bool, .nat] (.succeed (.var 1)) =
    some (EffTy.pure .nat) := rfl

-- Under Γ=[] and input 4, p returns 7 and q is the identity on its sole input.
-- Raw bind leaves input 4 in position zero, so q still returns 4.
def p : NativeEff := .succeed (.lit (.nat 7))
def q : NativeEff := .succeed (.var 0)
theorem raw_composition_reads_old_input (s : Stores) : Denote.meaning (.bind p q) [.nat 4] s = (.success (.nat 4), s) := rfl
theorem weakened_composition_reads_answer (s : Stores) : Denote.meaning (.bind p (q.weaken 0)) [.nat 4] s =
    (.success (.nat 7), s) := rfl

-- Raw reassociation also shifts the scope of the final continuation.
def a : NativeEff := .succeed (.lit (.nat 1))
def b : NativeEff := .succeed (.lit (.nat 2))
def c : NativeEff := .succeed (.var 0)
theorem left_associated_result (s : Stores) : Denote.meaning (.bind (.bind a b) c) [] s = (.success (.nat 2), s) := rfl
theorem raw_right_associated_result (s : Stores) : Denote.meaning (.bind a (.bind b c)) [] s = (.success (.nat 1), s) := rfl
theorem weakened_right_associated_result (s : Stores) : Denote.meaning (.bind a (.bind b (c.weaken 0))) [] s =
    (.success (.nat 2), s) := rfl

-- Scoping is not intrinsic in the raw Term type.
theorem raw_term_can_be_unscoped : Term.scoped 0 (.var 0) = false := rfl
theorem unscoped_term_refuses : evalTerm [] (.var 0) = none := rfl

-- compileEff partially evaluates actual values. It does not call effTy and reject first.
theorem compile_evaluates_env_three : compileEff (.succeed (.var 0)) { path := [], env := [.nat 3], fuel := 1, tape := [] } = Prim.success (.nat 3) := rfl
theorem compile_evaluates_env_five : compileEff (.succeed (.var 0)) { path := [], env := [.nat 5], fuel := 1, tape := [] } = Prim.success (.nat 5) := rfl

#print axioms absolute_zero_reads_context
#print axioms input_reads_context_length
#print axioms wrong_identity_type
#print axioms correct_identity_type
#print axioms raw_composition_reads_old_input
#print axioms weakened_composition_reads_answer
#print axioms left_associated_result
#print axioms raw_right_associated_result
#print axioms weakened_right_associated_result
#print axioms raw_term_can_be_unscoped
#print axioms unscoped_term_refuses
#print axioms compile_evaluates_env_three
#print axioms compile_evaluates_env_five

end CritiqueStaging
