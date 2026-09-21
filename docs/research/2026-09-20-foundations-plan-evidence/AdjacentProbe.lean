import Effect4.Laws.Program.Intro.Weight
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

macro "finish_probe" : tactic => `(tactic|
  first
  | cases ‹_ = some _›
  | (simp only [Option.some.injEq, WithFiberAction.fork.injEq, WithFiberAction.forkIn.injEq] at *;
     first | (rename_i hh; exact hh.1.symm) | (rename_i hh; exact hh.2.1.symm) | assumption | simp_all))

theorem fork_without_h (root : NativeEff) (p : Point) (site : List Nat) (program : NCode)
    (options : Supervision.ForkOptions)
    (hact : actionAt root p = some (.fork program options site)) :
    program = resolve root ((p.child 0).child 0) := by
  unfold actionAt at hact
  rcases hn : Node.at_ (Node.eff root) p.path with _ | n
  · rw [hn] at hact; cases hact
  · rw [hn] at hact
    cases n with
    | eff e =>
      cases e <;> simp only [Option.some.injEq] at hact <;> (repeat' split at hact) <;>
        first | cases hact | (simp only [WithFiberAction.fork.injEq] at hact; exact hact.1.symm) | rfl
    | _ => cases hact
  all_goals rfl

theorem forkIn_without_h (root : NativeEff) (p : Point) (site : List Nat) (program : NCode)
    (options : Supervision.ForkOptions) (scope : Nat)
    (hact : actionAt root p = some (.forkIn program options scope site)) :
    program = resolve root ((p.child 0).child 0) := by
  unfold actionAt at hact
  rcases hn : Node.at_ (Node.eff root) p.path with _ | n
  · rw [hn] at hact; cases hact
  · rw [hn] at hact
    cases n with
    | eff e =>
      cases e <;> simp only [Option.some.injEq] at hact <;> (repeat' split at hact) <;>
        first | cases hact | (simp only [WithFiberAction.forkIn.injEq] at hact; exact hact.1.symm) | rfl
    | _ => cases hact
  all_goals rfl

theorem not_forkScoped_without_h (root : NativeEff) (p : Point) (site : List Nat) (program : NCode)
    (options : Supervision.ForkOptions)
    (hact : actionAt root p = some (.forkScoped program options site)) : False := by
  unfold actionAt at hact
  rcases hn : Node.at_ (Node.eff root) p.path with _ | n
  · rw [hn] at hact; cases hact
  · rw [hn] at hact
    cases n with
    | eff e =>
      cases e <;> simp only [Option.some.injEq] at hact <;> (repeat' split at hact) <;> cases hact
    | _ => cases hact

#print axioms fork_without_h
#print axioms forkIn_without_h
#print axioms not_forkScoped_without_h
