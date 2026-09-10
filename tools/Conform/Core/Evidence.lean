/-!
# Conform.Core.Evidence — the evidence vocabulary

**What it is.** The five words a conformance check may use for how a claim is supported, as separate methods, and the four outcomes a check can report on one subject. Every row of
every report (`Conform.Core.Report`) carries one of each, so a reader never has to infer from
prose whether "the check passed" means a theorem or a finite run.

**Depends on.** Nothing in this repository. `Lean.Json` for the encodings.

**Properties.**
* Evidence belongs to each claim. No total order combines unrelated claims into a certificate.
* A lower grade never wears a higher word: `Evidence.ofString?` is the inverse of `toString`
  on exactly the five spellings and refuses everything else — *proved* (`ofString?_toString`,
  `toString_injective`).
* Absence, refusal and frontier are three things (the common brief). `Outcome.unresolved` is
  "the check could not run" — a missing input, an unsupported form — and is **never** a pass;
  `refused` is "the check ran and the input failed it"; `counterexample` is a refusal that
  carries a concrete witness. Nothing here encodes a machine frontier: that is the machine's
  own vocabulary and does not belong in a report.
-/

namespace Conform

/-- How a claim is supported. `proved` is a kernel-checked theorem whose axioms were printed;
`reproduced` is a regenerated artefact equal byte for byte; `tested` is a finite run of a
named tool on named inputs with its command and exit code recorded; `stamped` is a cut-from
stamp whose inputs digest matches; `assumed` is named and unproved. -/
inductive Evidence
  | assumed
  | stamped
  | tested
  | reproduced
  | proved
deriving DecidableEq, Repr, Inhabited

namespace Evidence

/-- The one spelling of each grade, the word the design documents use. -/
protected def toString : Evidence → String
  | .assumed => "assumed"
  | .stamped => "stamped"
  | .tested => "tested"
  | .reproduced => "reproduced"
  | .proved => "proved"

instance : ToString Evidence := ⟨Evidence.toString⟩

/-- The inverse of `toString` on the five spellings; anything else is refused. -/
def ofString? : String → Option Evidence
  | "assumed" => some .assumed
  | "stamped" => some .stamped
  | "tested" => some .tested
  | "reproduced" => some .reproduced
  | "proved" => some .proved
  | _ => none

theorem ofString?_toString (e : Evidence) : ofString? (toString e) = some e := by
  cases e <;> rfl

theorem toString_injective {a b : Evidence} (h : toString a = toString b) : a = b := by
  have := congrArg ofString? h
  rw [ofString?_toString, ofString?_toString] at this
  exact Option.some.inj this

end Evidence

/-- The outcome of one check on one subject. -/
inductive Outcome
  /-- The check ran and the subject satisfied it. -/
  | pass
  /-- The check ran and the subject failed it; the row's message names why. -/
  | refused
  /-- The check ran, the subject failed it, and the row's detail carries a concrete witness. -/
  | counterexample
  /-- The check could not run: a missing input, an unsupported form, an unresolved name. This is
  never a pass and never silently dropped from a denominator. -/
  | unresolved
deriving DecidableEq, Repr, Inhabited

namespace Outcome

protected def toString : Outcome → String
  | .pass => "pass"
  | .refused => "refused"
  | .counterexample => "counterexample"
  | .unresolved => "unresolved"

instance : ToString Outcome := ⟨Outcome.toString⟩

def ofString? : String → Option Outcome
  | "pass" => some .pass
  | "refused" => some .refused
  | "counterexample" => some .counterexample
  | "unresolved" => some .unresolved
  | _ => none

/-- Whether a row with this outcome contributes to a nonzero exit. -/
def isFailure : Outcome → Bool
  | .pass => false
  | _ => true

theorem ofString?_toString (o : Outcome) : ofString? (toString o) = some o := by
  cases o <;> rfl

end Outcome

end Conform
