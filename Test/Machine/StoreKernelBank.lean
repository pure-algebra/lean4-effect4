import Effect4.Laws.Machine.Arena

/-!
# The `Effect4.StoreKernel` bank's controls (decisions row 65)

The bank carries the list arena's definitions (`instArenaList`, `Arena.size`, `Arena.alloc`, …)
for unfolding inside the store-kernel modules. Its controls, which the bank census found missing
(`make bank-census`, 2026-10-04): a fact about the list arena that `aesop` closes with the clause,
and the same goal with **no clause at all**, which fails, so the bank is what closed it. The
clause is omitted rather than negated, as in `Test/Program/AtomRulesRed.lean`.
-/

namespace Test.Machine.StoreKernelBank

open Effect4.Machine

/-- The positive control: allocating into a list arena grows its size by one. -/
theorem alloc_size_closes (xs : List Nat) (v : Nat) :
    Arena.size (Arena.alloc xs v).2 = xs.length + 1 := by
  aesop (rule_sets := [Effect4.StoreKernel])

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  xs : List Nat
  v : Nat
  ⊢ Arena.size (Arena.alloc xs v).snd = xs.length + 1
-/
#guard_msgs (error) in
example (xs : List Nat) (v : Nat) : Arena.size (Arena.alloc xs v).2 = xs.length + 1 := by
  aesop

end Test.Machine.StoreKernelBank
