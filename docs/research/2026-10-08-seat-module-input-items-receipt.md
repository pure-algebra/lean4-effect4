# Named list item and input reference receipt

`item_step% xs with item => body` shares the fold macro's lexical capture implementation.
The shared list builders receive its body at `item :: outerInputs`.
Derived local steps retain their outer values through structural renaming.

The base is `cce86f14`, including the shared list builders.
The changed source is `src/Effect4/Modules/Step/Elab/Inputs.lean`.
The changed battery is `Test/Program/StepInputs.lean`.

`input_ref% (Inputs) id` reads the same declaration metadata and emits the positional `Input` witness.
Its consumers are existing generic helper and proof statements that take `Input`.
Live operation bodies use named step locals as their primary interface.
This bridge adds no program constructor or runtime name lookup.

This is an elaboration-only interface.
The shared Step reading, typing, and scope laws retain semantic ownership.

`LEAN_NUM_THREADS=3 lake build Test.Program.StepInputs` passes with 736 jobs.
The concrete named map reads `[4, 5]` after capturing a derived outer step.
Structural controls inspect references before and after a same-typed declaration reorder.
The two new refusal controls reject item shadowing and an unknown input reference.
The earlier named-input and nested-fold controls continue to pass.
No native host executes.
