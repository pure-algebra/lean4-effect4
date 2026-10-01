import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Forms

/-! Seat J, step 2: the axioms of every theorem added or restated (`minting_scoped`,
`bindWith_scoped`, `andThen_scoped`, `iterateWith_scoped`), of the sugar lemmas that read them,
and of the 19 regenerated form lemmas. -/

open Effect4.Program.Authoring in
#print axioms minting_scoped
open Effect4.Program.Authoring in
#print axioms bindWith_scoped
open Effect4.Program.Authoring in
#print axioms andThen_scoped
open Effect4.Program.Authoring in
#print axioms iterateWith_scoped
open Effect4.Program.Authoring in
#print axioms map_scoped
open Effect4.Program.Authoring in
#print axioms forRange_scoped
open Effect4.Program.Authoring in
#print axioms foldRange_scoped
open Effect4.Program.Authoring in
#print axioms repeatWhile_scoped
open Effect4.Program.Authoring in
#print axioms elaborate_scoped
#print axioms Effect4.Program.Authoring.Forms.void_scoped
#print axioms Effect4.Program.Authoring.Forms.die_scoped
#print axioms Effect4.Program.Authoring.Forms.yieldKey_scoped
#print axioms Effect4.Program.Authoring.Forms.andThenEffect_scoped
#print axioms Effect4.Program.Authoring.Forms.andThenContinuation_scoped
#print axioms Effect4.Program.Authoring.Forms.andThenThunk_scoped
#print axioms Effect4.Program.Authoring.Forms.as_scoped
#print axioms Effect4.Program.Authoring.Forms.asVoid_scoped
#print axioms Effect4.Program.Authoring.Forms.tapContinuation_scoped
#print axioms Effect4.Program.Authoring.Forms.tapEffect_scoped
#print axioms Effect4.Program.Authoring.Forms.ensuring_scoped
#print axioms Effect4.Program.Authoring.Forms.matchCause_scoped
#print axioms Effect4.Program.Authoring.Forms.matchCauseEffect_scoped
#print axioms Effect4.Program.Authoring.Forms.yieldNow_scoped
#print axioms Effect4.Program.Authoring.Forms.forkChildDefault_scoped
#print axioms Effect4.Program.Authoring.Forms.forkDetachDefault_scoped
#print axioms Effect4.Program.Authoring.Forms.forkInDefault_scoped
#print axioms Effect4.Program.Authoring.Forms.forkScopedDefault_scoped
#print axioms Effect4.Program.Authoring.Forms.releaseOne_scoped
