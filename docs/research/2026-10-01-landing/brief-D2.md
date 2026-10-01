# Seat D2 brief: M5's denotation lemma (`denoteR_typed`, row 148)

Written 2026-10-01 by the coordinator; dispatched after seat D1 merges (the coordinator names
the base commit at dispatch: main after I2 and D1, so the posts, pres, membership and the frame
contract are in their final shape). Worktree `/Users/pooks/Dev/lean4-effect4-seat-D2`, branch
`seat/D2`; `.lake` cloned from the main checkout, current at the base. Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure), then in full: receipt E
(`seq_typed`, `close_typed`, the owed compatibility lemmas for `onFailure`, `all`, `onExit`, the
`guardR` pass-through reading), receipt I (repair 3: `AwaitLoad.code_typed`, the first positive
instance of M5's route), receipt I2 (row 156; seat A's `evalTerm_fits` in `EnvTyped` form, and
whether the ledger goal `TermFits` closed), receipt D1 (the contract rows as landed), decisions
rows 148, 153, 156 and the formal pass's A3/A4 (`2026-10-01-formal-pass/algebra/note.md`). Seat
D3 may still be running on `Laws/Program/Typed/Commands/*.lean`, `Edits.lean` and the
`M6Ledger`/`M6Edits`/`M7` lines at `Assembly.lean`'s foot: never touch those. You own: a new file
`src/Effect4/Laws/Program/Typed/Denotation.lean` (imported by `Assembly.lean` at the anchor
after `Seq`, or by the Laws root after `Typed.Seq` if `Assembly` must not grow its cone, say
which), `Seq.lean` (the compatibility lemmas beside `seq_typed`), `Assembly.lean` only at the
`#obligation_proved` lines under `M3bAssembly` (`denoteR_typed`, `evalTerm_fits` if still open,
`typedState_load`), a new battery `Test/Program/TypedDenotation.lean` at the `Test/All.lean`
anchor after `Test.Program.H2PartOne`, and your receipt.

**The one thing.** `DenotesTyped root` (`Assembly.lean:826`): a checked point denotes, at the
node its path names, a program typed at the point's certificate, at every world. It is the one
connection from the checker to the machine (plan §5 item 2); `LoadsTyped` (M5) follows by
`loadsTyped_of_denotesTyped` (`:927`, over the expansion since D1's row 153), and M7a–c follow
from M5 and M6 by `m7_of_ledger`. Two checked refutations fixed its shape before you: the
await-by-value post (row 136, `E4-TYPED-CE-010`, now a positive control in `AwaitLoad.lean`) and
the scope-handle posts (row 156, `E4-TYPED-CE-018`, the `forkAfterMake` control in
`ScopePresence.lean`). If an arm needs a post or a pre the contract does not give, that is a
finding of the same kind: a checked refutation, a proposed row, and the arm left open with its
exact obstacle, never a premise added to `DenotesTyped` or a weakening of a post.

## The shape of the proof

`denoteR root e p = denoteRWith root p.fuel e p` (`DenoteR.lean:799`), structural in the fuel
with `rec a (p.child i)` at one less (`Point.child_fuel`); the program's checked type at the
point is `PointTyped` (`TypedSources.lean`/`Sources.lean`: the node, the checker's certificate,
the environment typed at the world by `EnvTyped`). Prove `DenotesTyped` by induction on the
fuel and the node, one lemma per arm of `denoteRWith` and `denoteFiberOp`/`denoteFin`/the layer
builds (`DenoteR.lean:584-640`, `:171-212`, `:248-283`, `:470-481`, the layer arms at `:700-740`),
each lemma a `TypedProg` derivation from the checker's inversion (`Laws/Program/Typing/
CheckInversion.lean`) and the row's pre and post as the tree states them: terms by `TermFits`
(seat A's `evalTerm_fits`); `bind`/`select` and the scoped shapes by `seq_typed` and the
compatibility lemmas you add beside it (`onFailure`: `catchCause`, `catchIf`, `orDie`; `all`:
`exit`, `matchCause`; `onExit`), each resting on `close_typed`'s pattern; `guardR`'s
continuations pass skipped exits through (receipt E's reading, now a theorem); the fiber rows by
`fiberPre`'s `PointTyped root w child cert` for a child body and the row's post for its answer
at every later world (the `fork`/`await` pattern of `AwaitLoad.fork_typed`/`await_typed`); the
store rows by `storePre`/`storePost`; the layer builds by `denoteLayer` with the memo rows'
posts; `construction` by `prepareR`'s typing. `noMarker` (`loadsTyped_of_denotesTyped`'s
premise: the loaded head is not a race marker; only `parkCode` builds one, `InterpR.lean:320`)
as one structural lemma over `denoteR`. Land the arms as separate lemmas and commit per group
(terms and `pure`; `bind`/`select`/the scoped shapes; the fiber rows; the store rows; the layer
rows; the assembly), so a stop leaves a true ledger: declare `DenotesTyped` per arm family only
if the assembly cannot close in this seat, as named goals in `M3bAssembly` with the arms proved
listed, never as a weakened `DenotesTyped`.

## Controls

`Test/Program/TypedDenotation.lean`: the typed corpus (`Test/Program/TypedCorpus.lean`) loaded
at a starting world, each program's root point typed at its certificate by `denoteR_typed`
(`#print axioms`, and a `#guard` that the certificate is the checker's); `AwaitLoad.loadsTyped`
and `ScopePresence`'s controls re-derived from the general theorem as one-line corollaries beside
their hand proofs (which stay as history); the first `LoadsTyped` of a program with a layer
reference through D1's lemma; the eighteen-command ledger untouched.

## Rules

Plan §4 (the list in brief-G's "Rules" applies verbatim). `LEAN_NUM_THREADS=4`, one lake at a
time in this worktree. No generator. Commits by explicit paths on `seat/D2`, one per arm group;
research files force-added; no push; never `git merge`/`checkout`/`reset`; a refused permission
is recorded, not worked around. Evidence words on every claim.

## Receipt

`docs/research/2026-10-01-landing/receipt-D2.md` (force-added, committed last): the one thing
first; base and head; every changed path; per arm the lemma (name, file:line, axioms) and the
contract facts it reads; the ledger before and after (`M3bAssembly`, and `M7` if `m7_of_ledger`
closed its three lines); the arms left open with the exact obstacle and the checked refutation if
one was found; the proposed lines for rows 148, 153 and the register.

## Amendments at dispatch (2026-10-01, base `bd5462df`)

The base is main after seats J and D1 and probe S merged (`bd5462df`); the worktree is at it with
`.lake` cloned. What changed since this brief was written, and the citations as they stand:

- **Citations.** `DenotesTyped` is `Assembly.lean:893`, `TermFits` `:902`, `machineTyped_load`
  `:921`, `loadsTyped_of_denotesTyped` `:1004`, the `M3bAssembly` namespace `:1450-1466`, its three
  open lines `#proof_wanted … typedState_load`, `denoteR_typed`, `evalTerm_fits` at `:1654-1656`
  and `#typed_state_obligations Effect4.Program.Typed.M3bAssembly ceiling 3` at `:1657` (the
  ceiling drops with each line you close; that one line is yours; D3 edits other ceilings).
  `denoteR` is `DenoteR.lean:799` and its arms are equation theorems, not raw `denoteRWith` text:
  `denoteR_zero` … `denoteR_provideService` (`:825-1069`, one per node form), `denoteLayer_succeed`
  … `denoteLayer_ref_redirect` (`:1103-1199`), `denoteR_straight` (`:1433`); `denoteFin` `:247`,
  `prepareR` `:59`, `denoteLayerBody` `:695`, `denoteLayerZero` `:743`. Rewrite with the equations;
  never unfold `denoteRWith` by hand.
- **`evalTerm_fits` exists.** Seat A's lemma is `Typed/Admission.lean:87` (the `EnvTyped` form) with
  `evalTerm_fits_native` (`:94`, a native signature over any row table). The ledger line is still
  open: close it with `#obligation_proved Effect4.Program.Typed.M3bAssembly.evalTerm_fits := @…`
  only if the statement matches `TermFits table` (`:902`) exactly; if it does not, say precisely
  where (the statement is the ledger's, never bent to the lemma).
- **D1's three shape changes** (receipt D1, "The one thing first"): `fitsExit_failure_iff` ends
  `∧ ShapeFree c` and `fitsExit_of_clean` takes a `ShapeFree c` argument (row 152);
  `PointTyped`, `storePre`'s `memoGet` arm and `CaptureTyped` check a node through
  `Eff.expandIn src.program` (row 153; a proof that compares the check with a raw-node lemma needs
  `Eff.expandIn_eq_self`); `IteratorProtocol.step` and `LoopProtocol.step` take a third argument
  `rows` (row 117; `fun _ => rfl` at equal or empty rows).
- **Row 153's owed general fact is your expected obstacle at the `layer.ref` hop.** The expansion
  holds the same term at a reference site and at its target (`expansion_site_is_target` is the
  instance at `layer.ref`); `denoteR_typed` at each hop needs the general version, which needs
  the expansion's rounds to reach a fixed point within `refSites.length + 1` rounds under
  `layerRefsWF`'s program order (a depth bound over the seven mutual sorts of `expandRound`). Land
  every other arm first; prove the bound as its own lemma in `Denotation.lean` if it closes in
  reasonable time, else stop that arm with the exact obstacle and the ledger true.
- **Rows 151 and 117 await the owner.** Never void `denoteFin`'s `acquireRelease` release (row
  151): the arm is typed as the tree states it, and if it cannot close that is row 151's measured
  stop, cited. `LoadsTyped` already carries `ClosedEff rootTy`; `DenotesTyped` is at every world
  with no row premise: add none. If an arm needs the closed row, it is a finding under row 117,
  named by arm.
- **Seat J2 is scoping the authoring syntax in parallel** (`eff …`, `daemon …` become
  `scoped syntax` in `Effect4.Program.Authoring`). Write no new `eff`/`daemon` blocks in
  `Test/Program/TypedDenotation.lean`: its controls are theorems over the programs the typed corpus
  (`Test/Program/TypedCorpus.lean`), `AwaitLoad.lean`, `ScopePresence.lean` and `LayerRefs.lean`
  already hold. If you must author a program, write it as data (`Eff` constructors), not surface
  syntax.
- **The testing rule (ratified, data-wave README "Testing during the wave").** Narrow builds while
  landing (`lake build Effect4.Laws.Program.Typed.Denotation` and the direct dependents; `lake env
  lean Test/Program/TypedDenotation.lean`), the roots once before the receipt
  (`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`), no `make check`, no generator, no
  `check-full`.
