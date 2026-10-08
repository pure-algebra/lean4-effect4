# Named module input authoring receipt

The declaration and both input macros share one name/type list.
Reordering same-typed inputs therefore retains named source application order.
The step remains existing positional data.

The base is `4a247d70`, including the checked structural rename checkpoint.
The changed files are `src/Effect4/Modules/Step/Inputs.lean`, `src/Effect4/Modules/Step/Elab/Inputs.lean`, and `Test/Program/StepInputs.lean`.

## Interface

```lean
step_context% TakeInputs (need : .nat, id : idTy, hint : idTy, cell : cellTy)
step_context% OfferInputs (A : Ty) where (value : A, count : .nat)

def take := step_inputs% TakeInputs => body

def takeTerm (need id hint cell : TermSrc) :=
  take.term (input_sources% (TakeInputs) {cell := cell, hint := hint, id := id, need := need})
```

An ordinary definition of `InputContext` also serves both macros.
Metadata names and its list spine must reduce to literals.
Types may contain declaration parameters.

```lean
fold_step% xs from acc := initial with item => body
```

A fold lifts every visible local step in the outer input context through `Step.rename`.
This includes derived local steps and the binders of enclosing folds.
The Lean elaborator records local aliases for editor information and unused-variable checking.
It refuses repeated binders and shadowing of existing locals.

## Placement and boundary

This interface elaborates existing Step and Input data.
The shared `Step.sound`, `Step.typed`, and `Step.scoped` statements own its semantics.
No new interpreter or theorem statement lands here.
The kernel checks generated data against its indexed type.
Metadata checks establish neither type formation nor carrier inhabitance.
No result crosses the host boundary.

The metadata reader has a finite budget of 4096 list cells.
A declaration outside its literal profile refuses before body elaboration.
Named source application refuses missing, repeated, and unknown names.
The macros store no metadata name, expression, or function inside a step.
Structural renaming computes ordinary positional data.

## Checks

`LEAN_NUM_THREADS=3 lake build Test.Program.StepInputs` passes with 735 jobs.
The battery reads a same-typed input before and after declaration reorder.
Both named source applications answer the intended literal.
A parameterized payload declaration and its application pass.
Nested folds capture outer inputs and a derived local step; their observed natural-number answer is 24.
The nested step applies the shared scope theorem at concrete caller sources.
Nine refusal controls check declaration repetition, source repetition, missing and unknown sources, unknown body names, binder repetition, and local shadowing.
Structural equality controls inspect generated positional constructors.
`git diff --check` passes.

Root imports and module consumer migrations remain coordinator work.
These checks are source elaboration and finite value evidence, without native execution.
