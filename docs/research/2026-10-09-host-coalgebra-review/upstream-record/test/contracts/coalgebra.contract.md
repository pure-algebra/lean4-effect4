# Coalgebra contract

Status: FROZEN, builder-authored 2026-10-09 for v0.9.0. The package's development order asks
for a breaker in a separate process; the owner was away, so the builder wrote this packet and its
falsifiers, and an independent review (Codex) is owed before the next release.

Implementation fence: `Effects/Coalgebra/**`, `Effects/Lens.lean`, `Effects/Coalgebra.lean`.

Battery: `EffectsTest/Coalgebra/CoalgebraContract.lean`. Receipt:
`EffectsTest/Coalgebra/AxiomReport.lean`.

Counterexamples: `EF-COALG-CE-001` through `EF-COALG-CE-004` in
`test/counterexamples/REGISTER.md`.

Consumer: lean4-effect4's host session (`docs/research/2026-10-09-host-coalgebra.md` there). The
consumer states one simulation of its session by its meaning and reads agreement against every
host off `Program.run_of_sim_program`.

## Claim boundary

The layer claims, kernel-checked within `propext` and `Quot.sound`:

- **Systems and their unfoldings.** A system is `X → Option (Step S A X)`; `none` is a cut, a live
  frontier, never an error. Unfoldings grow with depth (`System.unfold_succ`, `unfold_mono`), and
  a program's own unfolding approximates it at every depth (`Program.unfold_system`).
- **Bisimulation and simulation.** Bisimilar states have equal unfoldings at every depth
  (`unfold_eq_of_bisim`); a simulated state's unfolding approximates the simulating state's
  (`unfold_approx_of_sim`). Both compose along relational composites (`IsBisim.comp`,
  `IsSim.comp`).
- **Hosts.** A comodel answers each operation from its state or gives no answer. Running a program
  against it is interpreting in `StateT σ Option`. Routing, sharing, renaming along a lens,
  implementation by programs over another signature, admission, reply tapes and recording each
  have one law at `run` (`run_route_inl`, `run_route_inr`, `run_share_inl`, `run_share_inr`,
  `run_rename`, `run_through`, `guard_of_meets`, `run_record_replies`).
- **Protocols of the first order.** A protocol is a predicate on answers per operation; meeting
  is monotone under weakening and is kept by routing, sharing, renaming (pullback), reply tapes
  and recording.
- **Runs.** Where a simulated system finishes against a host, the simulating system finishes the
  same way (`System.run_of_sim`); bisimilar states run alike (`System.run_eq_of_bisim`); where a
  system simulated by a program finishes against a host, the program finishes the same way
  (`Program.run_of_sim_program`). Hiding an inner signature behind a total function of a state
  (`System.peel`) runs as the routed program (`System.run_peel`).

Not claimed:

- no coinductive type, no final coalgebra as a type, no equality of infinite behaviours: every
  statement is at a depth, or about runs that finish;
- no fairness, no liveness, no progress of a host or of a system;
- no host with effects other than `Option` failure; a host into another monad is a `Handler S
  (StateT σ M)`, outside this layer's laws;
- no indexed signature, no promise, no protocol whose answers open operations (planned, v0.10.0);
- no statement about any concrete machine, session or runtime: those are the consumer's.

## Frozen declarations

`Effects.Signature.Hom`, `Hom.id`, `Hom.comp`, `Program.map`, `Handler.pull`, `interpret_map`,
`Program.map_id`, `Program.map_comp` (promoted from `Effects.Experimental.Morphism`, names
unchanged); `Effects.Step` with `map`, `Lift` and its `mono`, `refl`, `eq`, `symm`, `comp`,
`map`; `Effects.System`, `Program.out`, `Program.system`, `Program.uncut`, `Program.Approx`,
`System.unfold`; `OptionLift`, `IsBisim`, `IsSim`; `Effects.Comodel` with `handler`, `ofHandler`, `run`,
`route`, `share`, `rename`, `through`, `guard`, `replies`, `record`, `ofTotal`, `Meets`;
`Effects.Protocol` with `bottom`, `top`, `sum`, `pull`, `Le`; `System.run`, `Program.peel`,
`System.peel`.

## ENSURES

1. `unfold_eq_of_bisim`: `IsBisim c d R → R x y → ∀ n, c.unfold n x = d.unfold n y`.
2. `unfold_approx_of_sim`: `IsSim c d R → R x y → ∀ n, Approx (c.unfold n x) (d.unfold n y)`.
3. `Comodel.run_approx`: an approximant that finishes against a host finishes the same way as what
   it approximates.
4. `Comodel.run_through`: `(host.through impl).run p s = host.run (interpret impl p) s`.
5. `Comodel.run_record_replies`: with `decode o (encode o a) = some a` for every answer, what the
   recording host wrote the reply host replays.
6. `Program.run_of_sim_program`: `IsSim c Program.system R → R x p →
   c.run host n x s = some (some a, s') → host.run p s = some (a, s')`.
7. `System.run_peel`: a finished run of the hiding system is a finished run of the program against
   the inner function routed beside the host.

## Counterexample obligations

| Row | Attack | Witness in the battery |
| --- | --- | --- |
| `EF-COALG-CE-001` | Recording replays without the round-trip premise | `lossy`: the replay of `[0, 0, 0]` gives `0`, not `11` |
| `EF-COALG-CE-002` | A cut is an error | `Program.system.run counter 1 askTwice 5 = some (none, 6)`: a live `none` with the host's state advanced |
| `EF-COALG-CE-003` | A system that ends early is simulated by the program | `early` finishes at depth three where the program's own system is cut |
| `EF-COALG-CE-004` | Admission is the host's business, not the run's | the guarded counter refuses `5`, so the run gives no answer |

## Trust and acceptance

The default `lake build` builds the library, the battery and the gate. The gate reads every
declaration's axioms with the exact walk (`EffectsTest/Audit/Axioms.lean`, v0.9.0), not with
`Lean.collectAxioms`. `./scripts/check-algebra-parity.sh` must pass: the nine `Effects/Algebra`
modules are not touched. `./scripts/test-trust-gate.sh` must pass.
