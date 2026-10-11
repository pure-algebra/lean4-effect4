import Effect4.Laws.Machine.PopTrace

/-!
Readers for the shared actual continuation-pop specification.
The control retains the hook-injected mask that prevents a naive original-prefix equation.
These readers establish no reached scenario history or host agreement.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.MachinePopTrace
open Effect4 Effect4.Machine

private def hooked : FrameFiber Nat Nat Nat Nat Nat Nat Nat :=
  ⟨.success 0, [.asyncFinalizer 1, .onSuccess (.success 0) 2], true,
    some (.interrupt (some 0)), false⟩

-- Control: the real hook drain pops a mask absent from the original stack.
#guard (hooked.getCont .contA false).popped = [.asyncFinalizer 1, .setInterruptible true]
#guard (hooked.getCont .contA false).fiber.stack = [.onSuccess (.success 0) 2]
#guard hooked.stack ≠ (hooked.getCont .contA false).popped ++ (hooked.getCont .contA false).fiber.stack

-- Reader: the shared specification accounts for this real injected-mask pop.
example : ∃ (parts : List (Prim Nat Nat Nat Nat Nat Nat Nat × List (Prim Nat Nat Nat Nat Nat Nat Nat))) (suffix : List (Prim Nat Nat Nat Nat Nat Nat Nat)),
    hooked.stack = parts.map Prod.fst ++ suffix ∧
    (hooked.getCont .contA false).popped = parts.flatMap (fun part => part.1 :: part.2) ∧
    FrameEvent.poppedFrames (hooked.getCont .contA false).events = parts.flatMap (fun part => part.1 :: part.2) ∧
    ∃ scratch, (hooked.getCont .contA false).fiber.stack = scratch ++ suffix := by
  rcases PopTrace.getCont_spec hooked .contA false none with ⟨deferred, _⟩ | ⟨_, parts, suffix, trace, _⟩
  · cases deferred
  · exact ⟨parts, suffix, trace.original, trace.popped, trace.events, trace.stack⟩

-- Reader: an ordinary selected callback belongs to the consumed original prefix.
example : ∃ (parts : List (Prim Nat Nat Nat Nat Nat Nat Nat × List (Prim Nat Nat Nat Nat Nat Nat Nat))),
    (.onSuccess (.success 0) 2 : Prim Nat Nat Nat Nat Nat Nat Nat) ∈ parts.map Prod.fst := by
  let ordinary : FrameFiber Nat Nat Nat Nat Nat Nat Nat :=
    ⟨.success 0, [.onFailure (.success 0) 1, .onSuccess (.success 0) 2], true, none, false⟩
  rcases PopTrace.getCont_spec ordinary .contA false none with ⟨deferred, _⟩ | ⟨_, parts, _, _, source⟩
  · cases deferred
  · exact ⟨parts, source (.onSuccess (.success 0) 2) (.inl rfl) rfl⟩

end Test.Dogfood.Proofs.MachinePopTrace
