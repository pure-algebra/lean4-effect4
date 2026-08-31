import Effects.Replay.Interp
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.CMP001ForkNestedCursor

open Effects.Replay

abbrev St := ReplayState String String String String

/-- The model's interpretation with one change: a substituted leaf's
continuation continues from the PRE-step state — the cursor forks. -/
def interpForked {α : Type} :
    Prog String String String String α → St →
      EStateM.Result (Halt String) St α
  | .pure a, s => .ok a s
  | .fail e, s => .error (.failed e) s
  | .invoke inv k, s =>
    have hm : (reduce s.val (.invoke inv)).state.mode = .replay :=
      (reduce_preserves_mode s.val (.invoke inv)).trans s.property
    match (reduce s.val (.invoke inv)).result with
    | .substituted out => interpForked (k out) s
    | .rejected c pos =>
        .error (.rejected c pos) ⟨(reduce s.val (.invoke inv)).state, hm⟩
    | _ => .error .absorbed ⟨(reduce s.val (.invoke inv)).state, hm⟩

/-- The mutation task's comparison unit for CMP-001: the interpretation
at the witness program's value type. -/
abbrev CmpInterp :=
  Prog String String String String String → St →
    EStateM.Result (Halt String) St String

def mutant : Effects.Conformance.Mutant CmpInterp where
  id := "CMP001_ForkNestedCursor"
  attacks := "CMP-001"
  represents := "Killing this mutant demonstrates the witness run notices a nested call that forks the cursor — a continuation interpreted from the pre-step state re-reads a consumed occurrence instead of continuing from the state its prefix reached."
  mutant := interpForked

end Effects.Mutants.CMP001ForkNestedCursor
