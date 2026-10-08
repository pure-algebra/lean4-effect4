import Effect4.Api.Author
import Effect4.Program.Authoring
import Effect4.Program.Authoring.Ascribe
import Effect4.Program.Authoring.Atoms
import Effect4.Program.Authoring.Declare
import Effect4.Program.Authoring.Defs
import Effect4.Program.Authoring.Folds
import Effect4.Program.Authoring.Lifts
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Maps
import Effect4.Program.Authoring.Mask
import Effect4.Program.Authoring.Module
import Effect4.Program.Authoring.Records
import Effect4.Program.Authoring.Rows
import Effect4.Program.Authoring.Services
import Effect4.Program.Authoring.Sugar
import Effect4.Program.Authoring.Tuples
import Effect4.Codegen.Forms
import Effect4.Schema.Modeled.Derive
import Effect4.Schema.FieldRef.Elab
import Effect4.Modules.Words
import Effect4.Modules.Step
import Effect4.Modules.Step.Elab
import Effect4.Modules.Step.Elab.Inputs
import Effect4.Modules.Step.Inputs
import Effect4.Modules.Step.Lists
import Effect4.Modules.Step.Rename
import Effect4.Modules.Waiting

/-!
# Effect4.Author — the entry module for writing a program or a module (decisions row 332)

An agent or a person who writes a program imports this module. It re-exports:

- program authoring: the builders, lifts, rows, loops, records, tuples, folds, masks,
  ascriptions and definition blocks (`Program.Authoring.*`), and authoring against a table
  (`Api.Author`, `Codegen.Forms`);
- `deriving Modeled` and `field_ref%` (`Schema.Modeled.Derive`, `Schema.FieldRef.Elab`);
- the step language with its named inputs, lists and renaming, and the words of a step term;
- the wrappers of a module that waits.

It declares nothing. The prebuilt composed modules are `Effect4.Library`, and their laws and the
shared step laws are `Effect4.Laws.Author`.
-/
