import Effect4.Laws.Program.CompileInduction
import Effect4.Laws.Program.SourceScope

/-!
# Compiled operation source ownership

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
Every direct compiler operation retains its source request and exact lexical level.
The statement permits every source constructor and compile budget.
It does not establish ownership after callback invocation or machine history closure.
-/

set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The source request that produces a native operation. Consumer: `origin_keeps`. -/
def OpOrigin (root : NativeEff) (op : SyncOp) : Prop :=
  ∃ (p : Point) (row : NativeOp) (request : Term) (value : Val),
    Node.at_ (.eff root) p.path = some (.eff (.perform row request)) ∧ At root p ∧
      evalTerm p.env request = some value ∧ row.syncOpOf p.env value = some op

/-- A direct compilation retains an operation's actual source and lexical environment.
Consumer: `resolve_op_origin` and the heap writer command clause. -/
theorem compile_op_origin (root : NativeEff) (e : NativeEff) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (hs : At root p)
    (op : SyncOp) (code : compileEff e p = .sync (.op op)) : OpOrigin root op := by
  revert found hs op
  fun_induction compileEff e p
  case case13 p n hf row request kind value hval operation hop nex ncall nparam =>
    intro found hs op code
    simp only [kind, hval, hop] at code
    cases code
    exact ⟨p, row, request, value, found, hs, hval, hop⟩
  case case43 p n hf saved body mask ih =>
    intro found hs op code
    apply ih (Agreement.at_child found 0) _ op code
    unfold At at hs ⊢
    change levelAt (.eff root) 0 (p.path ++ [0]) = some p.env.length
    rw [levelAt_suffix _ _ p.path [0] 0 found, hs]
    rfl
  case case45 p n hf decls bodies main layers ih =>
    intro found hs op code
    apply ih (Agreement.at_child found 1) _ op code
    unfold At at hs ⊢
    change levelAt (.eff root) 0 (p.path ++ [1]) = some p.env.length
    rw [levelAt_suffix _ _ p.path [1] 0 found, hs]
    rfl
  all_goals intro found hs op code
  all_goals aesop (add norm unfold [frontier, badShape, asyncRoute, Prim.ofExit, updateContextAt])
/-- Resolving a source point retains the actual operation witness.
Consumer: the heap writer command clause. -/
theorem resolve_op_origin (root : NativeEff) (p : Point) (hs : At root p)
    (op : SyncOp) (code : resolve root p = .sync (.op op)) : OpOrigin root op := by
  unfold resolve at code
  split at code
  · rename_i e found
    exact compile_op_origin root e p found hs op code
  · cases code

end Effect4.Program.SourceScope
