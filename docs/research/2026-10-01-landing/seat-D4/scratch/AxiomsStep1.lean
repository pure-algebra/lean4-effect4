import Effect4.Laws
open Effect4 Effect4.Machine Effect4.Program
#print axioms Effect4.Machine.storesCloseScope_unsafe
#print axioms Effect4.Machine.storesCloseScope_state_first
#print axioms Effect4.Machine.storesCloseScope_unknown
#print axioms Effect4.Machine.programKeys_voided
#print axioms Effect4.Machine.storesCloseScope_keys
#print axioms Effect4.Machine.storesCloseScopeUnsafe_keys
#print axioms Effect4.Machine.stores_keyBounded
#print axioms Effect4.Program.Sched.closeWalk_means
#print axioms Effect4.Program.Sched.closeScopeUnsafe_means
#print axioms Effect4.Program.Sched.voidedFin_means
#print axioms Effect4.Program.Sched.closeScope_means
#print axioms Effect4.Program.Sched.storesOk_closeScope
#print axioms Effect4.Program.Guard.FrameOwned.raceSites_closeScopeUnsafe
#print axioms Effect4.Program.Guard.FrameOwned.raceSites_closeScope
#print axioms Effect4.Program.Guard.FrameOwned.closeScope_hook_sites
#print axioms Effect4.Program.Typed.voidedClose_typed
#print axioms Effect4.Program.Typed.closeScope_installs
#print axioms Effect4.Program.Guard.NativeState.closeScope_state
#print axioms Effect4.Program.Guard.MemoIds.closeScope
