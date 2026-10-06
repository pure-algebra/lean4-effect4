# Proposed theorem shapes

Evidence status: uncompiled proposals. None is a proved declaration.
The existing functions keep their meaning and their owners.

## Reference completeness

The optional helper names the existing repeated fold.

```lean
def expandRounds {Op : Type} (root e : Eff Op) (k : Nat) : Eff Op :=
  (List.range k).foldl (fun acc _ => Eff.expandRound (.eff root) acc) e

-- Intermediate fact: a copied reference still belongs to an earlier original occurrence.
theorem target_refs_prior {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true)
    {site target nested next : List Nat} {layer : LayerTerm Op}
    (caller : (site, target) ∈ root.refSites [])
    (lookup : (Node.eff root).layerAt target = some layer)
    (inside : (nested, next) ∈ layer.refSites target) :
    (nested, next) ∈ root.refSites [] ∧ Path.lt nested site = true

-- Prove this exact bound, rather than only eventual disappearance.
theorem expandRounds_refSites_nil_of_wf {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true) (k : Nat)
    (enough : (root.refSites []).length ≤ k) :
    (expandRounds root root k).refSites [] = []

theorem expanded_refs_nil_of_wf {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true) :
    root.expandRefs.refSites [] = []

theorem typeOfProgram_expandRefs_of_wf {Op : Type}
    (sig : Signature Op) (p : Eff Op) (valid : p.layerRefsWF = true) :
    typeOfProgram sig p.expandRefs = typeOfProgram sig p

theorem typeOfProgram_eq_if_refsWF {Op : Type} (sig : Signature Op) (p : Eff Op) :
    typeOfProgram sig p =
      if p.layerRefsWF then typeOf sig p.expandRefs else none
```

The public completeness law needs only reference well-formedness.
Scope, signature lawfulness, type formation, and runtime agreement are not its conclusions.
A separate constructor theorem can remove `expanded` from `checkTypedProgram_of_hasTy` using this law.
Retain its declarative `HasTy` premise and its exact signature and program.

## Journal cut and positions

These signatures belong beside `tapeFrom` and `tape_replays` in the existing Scenario owner.
No new journal alphabet is needed.

```lean
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

The cut theorem deliberately retains exact positions, not only an empty remainder.
That equation lets `tape_replays` prove the machine clause immediately.
The position theorem does not require the entire journal to be consumed.
The stop conditions come from `tapeFrom`; no extra safety premise is invented.

For `Lowered.shown`, use a fresh `Run.open b id budget profile` in the first consumer.
Its implementation calls `Api.replay` from the loaded machine and uses the whole recorded journal.
An arbitrary progressed `Run` is therefore too broad for that consumer's theorem.
Keep any general arbitrary-Run theorem at `Run.replayFrom s.machine` instead.

The equality covers the machine, then `machineViewOf` by congruence.
It covers neither session ledgers nor a stopped command's partially updated machine.
It proves neither a lowered engine theorem nor resumable ownership.
