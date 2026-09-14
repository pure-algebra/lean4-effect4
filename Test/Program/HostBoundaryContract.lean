import Effect4.Laws.Program.HostBoundary

/-! S6b-0 independent boundary and state-observation controls. These classify the small
Lean models; they are not evidence that a real adapter implements their transitions. -/

set_option autoImplicit false

namespace Test.Program.HostBoundaryContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Profile

#guard Scalar.poll Scalar.waitRow (.nat 3) () true = .completed (.ofExit (.success (.nat 3))) ()
-- The valid answer exists in the semantic model, but has not been supplied at this observation.
#guard Scalar.poll Scalar.waitRow (.nat 3) () false = .pending ()
example : Scalar.spec.RowStep Scalar.waitRow (.nat 3) () (.ofExit (.success (.nat 3))) () :=
  Scalar.in_profile 3 (by decide)
#guard Scalar.poll Scalar.waitRow (.nat 9) () true = .outsideProfile "nat outside the profile" ()
#guard Scalar.poll Scalar.waitRow (.nat 9) () false = .outsideProfile "nat outside the profile" ()
#guard Scalar.poll Scalar.waitRow (.str "3") () true = .malformed "expected a natural request" ()
#guard Scalar.poll { Scalar.waitRow with answer := .bool } (.nat 3) () true =
  .malformed "unknown scalar row" ()

#guard Resource.poll Resource.acquireRow .unit Resource.State.empty false = .pending Resource.State.empty
#guard Resource.poll Resource.acquireRow .unit Resource.State.empty true =
  .completed (.ofExit (.success (Value.external 0))) ⟨[true], 0⟩
#guard Resource.poll Resource.useRow (Value.external 0) Resource.spentState true =
  .completed (.ofExit (.failure (Cause.fail Resource.spent))) ⟨[true], 3⟩
#guard Resource.poll Resource.releaseRow (Value.external 0) ⟨[true], 3⟩ true =
  .completed (.ofExit (.success .unit)) ⟨[false], 3⟩
#guard Resource.poll Resource.useRow (Value.external 0) ⟨[false], 3⟩ true =
  .completed (.ofExit (.failure (Cause.die Resource.closedUse))) ⟨[false], 3⟩
#guard Resource.poll Resource.releaseRow (Value.external 0) ⟨[false], 3⟩ true =
  .completed (.ofExit (.failure (Cause.die Resource.doubleRelease))) ⟨[false], 3⟩
#guard Resource.poll Resource.useRow (Value.external 2) ⟨[true], 0⟩ true =
  .malformed "resource was never acquired" ⟨[true], 0⟩
#guard Resource.poll Resource.useRow (.nat 0) ⟨[true], 0⟩ true =
  .malformed "expected an external resource handle" ⟨[true], 0⟩
#guard Resource.poll { Resource.useRow with request := .nat } (Value.external 0) ⟨[true], 0⟩ true =
  .malformed "unknown resource row" ⟨[true], 0⟩

-- Completing cleanup for one resource does not make another open slot disappear.
example : Resource.CleanupComplete ⟨[false, true], 4⟩ [0] := by
  intro index hindex
  have h : index = 0 := List.mem_singleton.mp hindex
  subst index
  rfl

example : ¬ Resource.OwnsAll ⟨[false, true], 4⟩ [0] := by
  intro h
  have hbad := h 1 (by decide)
  have heq : 1 = 0 := List.mem_singleton.mp hbad
  cases heq

#guard ¬ Resource.observe
  { Stores.empty with externals := { ExternalStore.empty with allocated := [Resource.target, Resource.target] } }
  ⟨[false, true], 4⟩

example : ¬ Resource.CleanupComplete ⟨[true], 4⟩ [0] := by
  intro h
  have hbad := h 0 (by simp)
  cases hbad

end Test.Program.HostBoundaryContract
