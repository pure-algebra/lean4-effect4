import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Program.Author
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Rows
import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.MeaningEq
import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Run
import Effect4.Laws.Run.Rows
import Effect4.Laws.Run.Tape
import Effect4.Laws.Step
import Effect4.Laws.Step.Annotations
import Effect4.Laws.Step.ErasedCompiler
import Effect4.Laws.Step.Lists
import Effect4.Laws.Step.Rename
import Effect4.Laws.Step.Requirements
import Effect4.Laws.Step.Scope
import Effect4.Laws.Step.Ascribe
import Effect4.Laws.Step.Checking
import Effect4.Laws.Step.Cons
import Effect4.Laws.Step.Construction
import Effect4.Laws.Step.Option
import Effect4.Laws.Step.Reading
import Effect4.Laws.Step.Store
import Effect4.Laws.Step.Table
import Effect4.Laws.Step.Tuples
import Effect4.Laws.Step.Waiting
import Effect4.Laws.Step.Callback
import Effect4.Laws.Author.Explain

/-!
# Effect4.Laws.Author — the entry module of the laws an author reads (decisions row 332)

A module author who proves, and every reader of the proof graph, imports this module. It
re-exports:

- the semantics attribute, which places a theorem under a concept and a requirement;
- the laws of program authoring, and the denotations and observations they are stated in
  (`DenoteB`, `MeaningEq`, `Typed.Denotation`);
- the run API's laws: the journal, its rows and its tape;
- the shared step laws: reading, typing, scope, the store's connectors, the encoding table, the
  lists, renaming and the wrappers' laws.
- `#explain` and `#obligations`: a step's or a theorem's placement, standing and open goals,
  as text or JSON (`src/Effect4/Laws/Author/Explain.lean`).

It declares nothing. A composed module's own laws are in `src/Effect4/Laws/Library/`.
-/
