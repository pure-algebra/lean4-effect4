import Effect4.Laws.Program.Typed.Membership

/-!
# Named record value helpers

Concept: Store Typing & Value Membership (`docs/core/semantics.md`).
Role: helpers for registry claim `denote-typed`, through `evalTerm_progress`
(`Laws/Program/Typed/Denotation.lean`). Slice 2's required read and overwrite consume these facts.

Reach: the existing `NamedFit` judgment over the names and values of row 165's record frame.
No world premise is needed because the field predicates retain their own membership premises.
Rows 178 and 195 do not change the meaning of `NamedFit`.

Limits: column length equality does not imply unique or sorted names. A required field's fitting
pair does not identify a first-match lookup without the declaration's unique-name premise.
These helpers establish no program termination, scheduling service, or host execution fact.

Consumer: typed record reads and overwrite on the M5 path. Requirement: R3 (data).
The full operation contract is `docs/research/2026-10-03-data-language/record-contract.md`.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine

/-- The two columns of a fitting record have equal lengths. The record lookup and overwrite
proofs use this before reading or rebuilding paired columns (claim `denote-typed`, R3). -/
theorem namedFit_lengths :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      NamedFit ps ns xs → ns.length = xs.length
  | [], [], [], _ => rfl
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | (_n, _o, _P) :: _ps, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, v :: _, [], h => by cases v <;> exact h.elim
  | (n, o, P) :: ps, v :: ns, x :: xs, h => by
    cases v with
    | str m =>
      simp only [NamedFit] at h
      by_cases hm : m = n
      · rw [if_pos hm] at h
        exact congrArg Nat.succ (namedFit_lengths ps ns xs h.2)
      · rw [if_neg hm] at h
        exact namedFit_lengths ps (.str m :: ns) (x :: xs) h.2
    | _ => exact h.elim

/-- A required declaration has a fitting value at its own name in the paired columns.
Required-read progress consumes this witness with canonical unique names
(claim `denote-typed`, rows 165, 178 and 195, R3). -/
theorem namedFit_required_pair :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      NamedFit ps ns xs → ∀ q ∈ ps, q.2.1 = false →
        ∃ x, (Val.str q.1, x) ∈ ns.zip xs ∧ q.2.2 x
  | [], _, _, _ => fun _ hq => absurd hq List.not_mem_nil
  | (n, o, P) :: ps, ns, xs, h => by
    intro q hq hrequired
    match ns, xs, h with
    | [], [], h =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Bool.noConfusion (hrequired.symm.trans h.1)
      · exact namedFit_required_pair ps [] [] h.2 q hq hrequired
    | [], _ :: _, h => exact h.elim
    | v :: _, [], h => cases v <;> exact h.elim
    | v :: ns, x :: xs, h =>
      cases v with
      | str m =>
        simp only [NamedFit] at h
        by_cases hm : m = n
        · rw [if_pos hm] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · refine ⟨x, ?_, h.1⟩
            rw [hm]
            exact List.mem_cons_self
          · obtain ⟨y, hy, hfit⟩ := namedFit_required_pair ps ns xs h.2 q hq hrequired
            exact ⟨y, List.mem_cons_of_mem _ hy, hfit⟩
        · rw [if_neg hm] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Bool.noConfusion (hrequired.symm.trans h.1)
          · exact namedFit_required_pair ps (.str m :: ns) (x :: xs) h.2 q hq hrequired
      | _ => exact h.elim

end Effect4.Program.Typed
