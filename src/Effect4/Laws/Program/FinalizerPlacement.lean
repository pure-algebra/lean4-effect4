import Effect4.Laws.Program.SourceOpportunityCallbacks

/-!
Concept: scope-lifetime-finalization, R11.
Question: the definition-call step of `FinalizerRun.once_placed_outside_census`.
Consumer: the selected-source opportunity bound at native invocation redirects.
Reach: every native definition block and selected once-placed source.
These source facts establish no history bound, finalizer start or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerPlacement
open Effect4 Effect4.Machine Effect4.Program
open SourceScope.Opportunities

/-- A once-placed path retains the placement test at each reached suffix.
Consumer: repeated-body exclusion in the once-placed finalizer source ledger. -/
theorem suffix_placed (root target : Node NativeOp) (path suffix : List Nat)
    (found : Node.at_ root path = some target)
    (placed : OncePlaced root (path ++ suffix) = true) : OncePlaced target suffix = true := by
  induction path generalizing root with
  | nil =>
    cases Option.some.inj found
    exact placed
  | cons index path ih =>
    simp only [Node.at_] at found
    cases child : root.child index with
    | none => rw [child] at found; cases found
    | some next =>
      rw [child] at found
      simp only [Option.bind_some] at found
      simp only [List.cons_append, OncePlaced, child, Bool.and_eq_true] at placed
      exact ih next found placed.2

/-- An excluded syntax edge carries no selected once-placed source.
Consumer: loop bodies, definition bodies and invocation program-argument sites.
This is the static exclusion needed by their selective source ledger. -/
theorem forbidden_child_zero (root target : Node NativeOp) (q path : List Nat)
    (index : Nat) (found : Node.at_ root path = some target)
    (forbidden : onceChild target index = false) (placed : OncePlaced root q = true) :
    below q (path ++ [index]) = 0 := by
  cases prefixed : (path ++ [index]).isPrefixOf q with
  | false => simp only [below, prefixed, Bool.false_eq_true, ↓reduceIte]
  | true =>
    obtain ⟨suffix, equal⟩ := List.isPrefixOf_iff_prefix.mp prefixed
    have tailPlaced := suffix_placed root target path ([index] ++ suffix) found
      (by rw [← List.append_assoc, equal]; exact placed)
    change OncePlaced target (index :: suffix) = true at tailPlaced
    simp only [OncePlaced, forbidden, Bool.false_and, Bool.false_eq_true] at tailPlaced

/-- A once-placed source lies outside every iterate body.
Consumer: loop-entry zero opportunities in the outside-census finalizer proof.
This removes the loop restriction from the statement's independent assumptions. -/
theorem clear_loops (root : NativeEff) (q : List Nat)
    (placed : OncePlaced (.eff root) q = true) : ClearLoops root q := by
  apply List.all_eq_true.mpr
  intro path _
  cases found : Node.at_ (.eff root) path with
  | none => rfl
  | some node =>
    simp only [Option.all_some]
    split
    · rename_i cursor initial test step result body
      have zero := forbidden_child_zero (.eff root)
        (.eff (.iterate cursor initial test step result body)) q path 0 found rfl placed
      cases prefixed : (path ++ [0]).isPrefixOf q with
      | false => rfl
      | true =>
        change (if (path ++ [0]).isPrefixOf q then 1 else 0) = 0 at zero
        rw [prefixed] at zero
        cases zero
    · rfl

/-- A once-placed source cannot lie in any definition body of its root block.
Consumer: `definition_resolve_zero`, a step of the once-placed finalizer claim. -/
theorem definition_body_zero (decls : List DefDecl) (bodies : Effs NativeOp)
    (main : NativeEff) (layers : LayerTerms NativeOp) (q tail : List Nat)
    (placed : OncePlaced (.eff (.defs decls bodies main layers)) q = true) :
    below q (0 :: tail) = 0 := by
  cases q with
  | nil => rfl
  | cons index rest =>
    cases index with
    | zero => cases placed
    | succ index =>
      cases index with
      | zero => rfl
      | succ index => cases placed

/-- Resolving any root definition body cannot supply a selected once-placed opportunity.
Placement: scope-lifetime-finalization R11, a step of the outside-census finalizer claim.
Consumer: the invocation and direct-call suspension cases of its source ledger.
The point's environment, tape, call stack and compilation fuel remain arbitrary. -/
theorem definition_resolve_zero (decls : List DefDecl) (bodies : Effs NativeOp)
    (main : NativeEff) (layers : LayerTerms NativeOp) (q : List Nat)
    (placed : OncePlaced (.eff (.defs decls bodies main layers)) q = true)
    (point : Point) (tail : List Nat) (path : point.path = 0 :: tail) :
    current (.defs decls bodies main layers) q
      (resolve (.defs decls bodies main layers) point) = 0 := by
  have bounded := resolve_le (.defs decls bodies main layers) q point
  rw [path, definition_body_zero decls bodies main layers q tail placed] at bounded
  exact Nat.eq_zero_of_le_zero bounded

end Effect4.Program.FinalizerPlacement
