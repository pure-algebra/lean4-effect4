import Effect4.Machine.LiveStack

/-!
# Live-stack kernel dependency report

The two executable entries and all six promised public theorems are inspected
in contract order. The permitted public theorem ceiling is `propext` and
`Quot.sound`; no classical choice, project axiom or unchecked implementation
is admitted. Counterexample receipts are printed by their own green module.
-/

#print axioms Effect4.FrameFiber.popLive
#print axioms Effect4.FrameFiber.getContLive
#print axioms Effect4.FrameFiber.popLive_eq_popFrom
#print axioms Effect4.FrameFiber.getContLive_eq_getCont
#print axioms Effect4.FrameFiber.getContLive_false_eq_getCont
#print axioms Effect4.FrameFiber.getContLive_deferred_kept
#print axioms Effect4.FrameFiber.getContLive_deferred_discarded
#print axioms Effect4.FrameFiber.getContLive_while
