# Release merge: receipt (2026-10-12)

**Know this first.** A capture's release now runs under its captured context merged over the
current one, as Effect's `provideContext` does. That one modelling fix proved all four planned goals
that named the restore slot. M6 and M7 now rest on one planned goal,
`Evaluating.countdown_parks_positional`, which changes no run in rc.112 or 4.0.1. The restore slot
is retired (owner, 2026-10-12): no proof needs it.

## Base and head

- Base: `refactor/phase1-phase3` at `10b4b0196` (the typed-context landing).
- Head: `land/release-merge`, the commit that adds this receipt. The base's later commits are merged
  in (`a15a5b56f`).

## What changed

- `releaseContext previous captured` (`src/Effect4/Program/Compile.lean`): the captured services
  merged over the current ones, the captured ones winning on a shared key. Effect runs
  `updateContext(self, Context.merge(context))` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:2197`;
  4.0.1 has the same code). Both machines switch to it: `EffName.releaseUnder`'s continuation and
  `denoteFin`'s `foreign` arm (`src/Effect4/Laws/Program/DenoteR.lean`).
- The simulation, the handle census and the type-only assembly follow the new switch:
  `contAOf_releaseUnder` (`Agreement.lean`), `releaseContext_keys` (`Handles/Layer.lean`), the
  release arm of `Handles/Hooks.lean`, `Intro/AcquireRelease.lean`, `Typed/Assembly.lean`.
- `foreignFin_ambient` and `finalizer_ambient` (`Typed/Body.lean`) lose their `window` premise.

## Planned goals proved in place

| Goal | Path | Proof uses |
| --- | --- | --- |
| `foreignFinalizer_ambient` | `src/Effect4/Laws/Program/Typed/Commands/Clauses/Close.lean` | `foreignFin_ambient` |
| `clause_closeScope` | `src/Effect4/Laws/Program/Typed/Commands/Evaluate.lean` | `closeScope_installs_ambient` (new) |
| `Evaluating.settle_callback` | same | `ambient_finalizerBind`, `closeScopeUnsafe_ambient` (new) |
| `clause_scoped` | same | `ambient_scopedGuardBind` (new) |

Each keeps its placement, `@[semantics "scope-lifetime-finalization" (requirement := R11)]`, and
serves the claims `step-deliver-preserves` and `step-loop-preserves`. The three `Evaluate.lean`
proofs are the proof seat's, from the plan `docs/research/2026-10-12-probe-scope-goals-plan.md`.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4 Effect4.Laws` | 1079 jobs, success |
| `make -k gen` | every group but `semantics` (refused archived counterexample ids, fixed on the base in `c8a2da818`) |
| `make -k check-compiler check-native check-ocaml check-truth check-host-protocol` | pass; truth: 0 divergences |
| `#axiom_audit` over `Evaluate`, `Clauses.Close`, `Typed.Body` (seat) | 402 declarations within `[propext, Quot.sound]`, 0 modulo planned goals |
| `#axiom_audit` over `Clauses.All`, `Clauses.Park` (seat) | 192 declarations within `[propext, Quot.sound]`; 14 modulo the one planned goal |
| `#axiom_audit` over the eleven touched modules (Compile, DenoteR, Agreement, Handles.Layer, Handles.Hooks, Intro.AcquireRelease, Typed.Assembly, Typed.Body, Clauses.Close, Evaluate, Clauses.All) | 4112 declarations within `[propext, Quot.sound]`; 10 modulo planned goals; 0 planned goals |
| `make gen-semantics` | regenerated; next goals: `countdown_parks_positional` and the ten application goals |
| `#plan_status` (seat) | `deliver_preserves`, `loop_preserves`, `reachable_typed` modulo `[Evaluating.countdown_parks_positional]` only |

## What this does not establish

- Preservation only: no progress, and no termination of the close walk.
- The merge changes no read of a well-typed release; the visible difference is the yield budget the
  release runs under, which now matches Effect's.
- Two divergences stay recorded, not fixed: `scoped` entry's one-step interrupt window (as rc.112;
  4.0.1 closes it) and an explicit `Scope.close` running its release unmasked (as rc.112; 4.0.1
  masks it). See `docs/research/2026-10-12-probe-scoped-window.md`.
- `closeScopeUnsafe_installs` (`Typed/Adequacy.lean`) has no proof consumer left.
