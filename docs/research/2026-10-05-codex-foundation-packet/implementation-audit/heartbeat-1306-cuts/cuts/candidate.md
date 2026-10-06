# CUTS statement precision

Status: proposed and uncompiled. The four assigned signatures below retain the roadmap packet's statements.
They belong beside `tapeFrom` in `Test/Dogfood/Scenario.lean`.
Use its existing imports and namespace, with `Run` and `Command` in scope.

```lean
-- These declarations are statement sketches, not Lean-checked declarations.
theorem tapeFrom_append (s : Run) (a b : List Command) :
    tapeFrom s (a ++ b) =
      if (tapeFrom s a).2 = [] then
        ((tapeFrom s a).1 ++ (tapeFrom (s.play a) b).1,
          (tapeFrom (s.play a) b).2)
      else ((tapeFrom s a).1, (tapeFrom s a).2 ++ b)

theorem tapeFrom_cut (s : Run) (rows : List Command) :
    ∃ done, rows = done ++ (tapeFrom s rows).2 ∧
      tapeFrom s done = ((tapeFrom s rows).1, [])

theorem tapeFrom_cut_replays (s : Run) (rows : List Command) :
    ∃ done, rows = done ++ (tapeFrom s rows).2 ∧
      tapeFrom s done = ((tapeFrom s rows).1, []) ∧
      (s.play done).machine =
        Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
          ((tapeFrom s rows).1.map (·.decision)) s.machine)

theorem tapeFrom_position_replays (s : Run) (rows : List Command)
    (i : Nat) (position : Position)
    (at : (tapeFrom s rows).1[i]? = some position) :
    position.after.machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
        (((tapeFrom s rows).1.take (i + 1)).map (·.decision)) s.machine)
```

## One helper with an immediate consumer

The position law need not repeat `tape_replays`' semantic induction.
Prove this structural helper using the tape's existing four equations:

```lean
-- PROPOSED, UNCOMPILED.
-- Helper of tapeFrom_position_replays, serving R13 and R8's replay view.
theorem tapeFrom_position_prefix (s : Run) (rows : List Command)
    (i : Nat) (position : Position)
    (at : (tapeFrom s rows).1[i]? = some position) :
    ∃ done tail, rows = done ++ tail ∧
      s.play done = position.after ∧
      tapeFrom s done = ((tapeFrom s rows).1.take (i + 1), [])
```

This preserves the whole stored position and the exact run after its last row.
It does not reconstruct only the decisions or require equality decisions for `Run`.
The following derivation is a proof sketch, not checked code:

```lean
  obtain ⟨done, tail, _, hafter, htape⟩ :=
    tapeFrom_position_prefix s rows i position at
  have complete : (tapeFrom s done).2 = [] := congrArg Prod.snd htape
  have replayed := tape_replays s done complete
  rw [htape, hafter] at replayed
  exact replayed
```

For `tapeFrom_cut_replays`, take `done` from `tapeFrom_cut` and apply `tape_replays` in the same way.
Neither derived theorem needs another machine or reply-application proof.

## Exact first consumer

The following declaration belongs in `Test/Dogfood/Scenario/Tape.lean`.
Its namespace is `Test.Dogfood.Scenario.Lowered`.
It states list equality of the existing views, without asserting agreement of outcome labels.

```lean
-- PROPOSED, UNCOMPILED.
theorem shown_views_opened (name : String) (built : Api.Built) (id : String)
    (budget : Api.Budget) (profile : String) (moves : List Move) :
    let l : Lowered := ⟨name, Run.open built id budget profile, moves⟩
    l.shown.raw.map (·.2) = l.shown.views
```

No empty-remainder premise is needed for this equality.
Both lists contain only the initial view and the positions already read.
A later stopped row contributes no position to either list.

`Shown.agrees` additionally checks `left == 0`.
A theorem about `Shown.agrees = true` must therefore retain the empty-remainder premise.
Keep its Boolean conversion separate from the primary list equality.
