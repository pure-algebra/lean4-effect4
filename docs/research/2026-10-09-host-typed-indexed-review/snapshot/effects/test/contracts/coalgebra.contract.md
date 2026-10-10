# Coalgebra contract

Status: FROZEN, builder-authored 2026-10-09 for v0.9.0. The package's development order asks
for a breaker in a separate process; the owner was away, so the builder wrote this packet and its
falsifiers, and an independent review (Codex) is owed before the next release.

Implementation fence: `Effects/Coalgebra/**`, `Effects/Lens.lean`, `Effects/Coalgebra.lean`.

Battery: `EffectsTest/Coalgebra/CoalgebraContract.lean`. Receipt:
`EffectsTest/Coalgebra/AxiomReport.lean`.

Counterexamples: `EF-COALG-CE-001` through `EF-COALG-CE-006` in
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
- **Typed programs and handlers (v0.9.1).** A program is typed under a protocol into a
  postcondition (`Program.Sat`), by structure on the tree. The typing is sound for every host that
  meets the protocol (`Program.Sat.sound`), and it composes along `bind` (`Program.Sat.bind`). A
  handler is typed from an upper to a lower protocol when each implementation is typed into the
  upper protocol's admission (`Handler.Typed`). Typed handlers take typed programs to typed
  programs (`Handler.Typed.interpret`), compose (`Handler.Typed.through`), and make a host that
  meets the lower protocol meet the upper one (`Comodel.Meets.through`).
- **Indexed signatures (v0.10.0).** An indexed signature has worlds, the operations each world
  offers, their answers, and the world after each answer (`ISignature`). Its programs end with a
  value whose type depends on the final world (`IProgram`); its hosts answer each world's
  operations from a state, and a run returns the final world, the value and the state
  (`IComodel.run`). Its protocols type its programs (`IProgram.Sat`), soundly for every host that
  meets them (`IProgram.Sat.sound`). A first-order signature is the one-world case
  (`ISignature.const`), and programs and runs embed exactly (`IProgram.toProgram_ofProgram`,
  `IProgram.ofProgram_toProgram`, `IComodel.run_ofProgram`).

Not claimed:

- no coinductive type, no final coalgebra as a type, no equality of infinite behaviours: every
  statement is at a depth, or about runs that finish;
- no fairness, no liveness, no progress of a host or of a system;
- no host with effects other than `Option` failure; a host into another monad is a `Handler S
  (StateT σ M)`, outside this layer's laws;
- no indexed system, bisimulation or handler between indexed signatures, and no host state indexed
  by the world (v0.10.0 holds programs, hosts, runs, protocols and typing only);
- no converse of typing soundness: a postcondition that every host meeting a protocol gives need
  not be stated as a `Program.Sat`, and nothing here builds one from runs;
- no statement about any concrete machine, session or runtime: those are the consumer's.

## Frozen declarations

`Effects.Signature.Hom`, `Hom.id`, `Hom.comp`, `Program.map`, `Handler.pull`, `interpret_map`,
`Program.map_id`, `Program.map_comp` (promoted from `Effects.Experimental.Morphism`, names
unchanged); `Effects.Step` with `map`, `Lift` and its `mono`, `refl`, `eq`, `symm`, `comp`,
`map`; `Effects.System`, `Program.out`, `Program.system`, `Program.uncut`, `Program.Approx`,
`System.unfold`; `OptionLift`, `IsBisim`, `IsSim`; `Effects.Comodel` with `handler`, `ofHandler`, `run`,
`route`, `share`, `rename`, `through`, `guard`, `replies`, `record`, `ofTotal`, `Meets`;
`Effects.Protocol` with `bottom`, `top`, `sum`, `pull`, `Le`; `System.run`, `Program.peel`,
`System.peel`; `Program.Sat`, `Handler.Typed` (v0.9.1); `ISignature`, `ISignature.const`, `IProgram` with `bind`,
`perform`, `ofProgram`, `toProgram`, `Sat`; `IComodel` with `run`, `Meets`; `IProtocol`;
`Comodel.toIndexed` (v0.10.0).

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
8. `Program.Sat.sound`: `host.Meets P → Sat P Q p → host.run p s = some (a, s') → Q a`.
9. `Handler.Typed.interpret`: `impl.Typed PS PT → Sat PS Q p → Sat PT Q (interpret impl p)`.
10. `Comodel.Meets.through`: `impl.Typed PS PT → host.Meets PT → (host.through impl).Meets PS`.
11. `Handler.Typed.through`: `upper.Typed PS PT → lower.Typed PT PU →
    (upper.through lower).Typed PS PU`.
12. `IProgram.Sat.sound`: `host.Meets P → p.Sat P Q → host.run p s = some ⟨w', v, s'⟩ → Q w' v`.
13. `IComodel.run_ofProgram`: `host.toIndexed.run (ofProgram p) s =
    (host.run p s).map fun r => ⟨(), r.1, r.2⟩`.
14. `IProgram.toProgram_ofProgram` and `IProgram.ofProgram_toProgram`: the one-world embedding is
    exact.

## Counterexample obligations

| Row | Attack | Witness in the battery |
| --- | --- | --- |
| `EF-COALG-CE-001` | Recording replays without the round-trip premise | `lossy`: the replay of `[0, 0, 0]` gives `0`, not `11` |
| `EF-COALG-CE-002` | A cut is an error | `Program.system.run counter 1 askTwice 5 = some (none, 6)`: a live `none` with the host's state advanced |
| `EF-COALG-CE-003` | A system that ends early is simulated by the program | `early` finishes at depth three where the program's own system is cut |
| `EF-COALG-CE-004` | Admission is the host's business, not the run's | the guarded counter refuses `5`, so the run gives no answer |
| `EF-COALG-CE-005` | A host behind any implementation meets the upper protocol | `viaRead` is not typed into `evenAsk`, and the counter behind it answers `5` at an `ask` |
| `EF-COALG-CE-006` | A typed program keeps its postcondition under any host | `sevens` answers a number promise with `7`, outside `tens`, and runs `twoJobs` to `7` |

## Trust and acceptance

The default `lake build` builds the library, the battery and the gate. The gate reads every
declaration's axioms with the exact walk (`EffectsTest/Audit/Axioms.lean`, v0.9.0), not with
`Lean.collectAxioms`. `./scripts/check-algebra-parity.sh` must pass: the nine `Effects/Algebra`
modules are not touched. `./scripts/test-trust-gate.sh` must pass.
