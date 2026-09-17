import Effect4.Laws.Program.Handles.Alphabet
import Effect4.Laws.Program.Handles.Term
import Effect4.Laws.Program.Handles.Compile
import Effect4.Laws.Program.Handles.Layer
import Effect4.Laws.Program.Handles.Hooks
import Effect4.Laws.Program.Handles.Evaluation

/-!
# The handle invariant at the compiled alphabet

`Effect4.Machine.Handles` proves that replay keeps every collected handle pointing at
something minted, for any name and thunk alphabet whose interpreter is `KeyBounded`. This
module instantiates it at the native alphabet (`EffName`, `EffThunk`, `Point`, `Ctx`) and the
interpreter `interpOf root` of `Effect4.Program.Compile`, and states the result on the public
API:

* `Minted (m : Api.Machine)`: every handle in the declared positions exists (decidable);
* `AnswersValid program fuel tape`: every `answerAsync` of the tape names handles
  that exist in the machine it answers (decidable, the C15 `TapeAddressed` reading);
* `load_minted`: a freshly loaded program holds no handle, so it is `Minted`;
* `handles_minted`: `Minted (Api.load …) ∧ AnswersValid … → Minted (Api.replay …).machine`.

What is proved about the compile: the code a point compiles to names only the handles in
the point's captured exits and environment (`compileEff_keys`, `resolve_keys`), the generator
walker keeps to those captured exits and its environment (`runStmts_keys`), a `withFiber` action names only what its point's terms
evaluate to (`actionAt_keys`), and the embedded stores' programs carry the stores' own keys
(`embed_keys`). The ruling in force is the valid-input premise: `AnswersValid` is a premise of
the theorem, and replay admission is unchanged (`E4-HANDLE-CE-001`).

Excluded, as in the machine module: the cause's interruptor, the race's duplicate winner and
unused bookkeeping, and a Deferred's waiter targets. The exit a scope closed with is
collected since V1 (2026-09-07): `scopeAdd` on a closed scope answers it.
The race's live entrants and accepted exit are collected: both flow into `raceSettle`.

### Sub-module Architecture

The proofs are decomposed into five logical layers under `Effect4.Laws.Program.Handles`:
- `Handles.Alphabet`: The native alphabet and embedding of the stores' programs.
- `Handles.Term`: Evaluation of terms and preservation of handle bounds.
- `Handles.Compile`: Preservation of handle bounds across `compileEff` and `resolve`.
- `Handles.Layer`: Layer builds, region codes, memo map bounds, generator walker, and actions.
- `Handles.Hooks`: Key-boundedness of all interpreter callbacks/hooks for `interpOf root`.
- `Handles.Evaluation`: Handle preservation across evaluation and the public API theorems.
-/
