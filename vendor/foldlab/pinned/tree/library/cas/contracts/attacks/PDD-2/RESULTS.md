# PDD-2 — the breaker's results

Independent attack on the PDD-2 contract packet
(`library/cas/contracts/PDD-2.contract.md`) and its castle
(`library/cas/Cas/Lang/Wp.lean`) at commit `539beec8`. The attacker did
not build this and used no channel to the builder. Apparatus:
`Attack.lean` beside this file, elaborated by hand and outside every
Lake target.

## VERDICT — STANDS

Every claim the packet makes was reproduced. No BREAK and no HOLE. The
findings below are all NOTE: seven places where the packet's prose is
looser than its theorems, or where a disclosure sits somewhere other
than the packet. Nothing found is a soundness defect and nothing found
is an overclaim — in four of the seven the theorem is STRONGER than the
sentence describing it.

The decisive result of the attack is in the other direction, and it is
recorded as evidence FOR the packet: **L1 alone pins the transformer.**
`Attack.lean` `anchor_pins_wp` proves that any `wp'` satisfying the
anchor at every table, precondition and postcondition agrees with `wp`
pointwise — instantiate the anchor at the singleton precondition
`(· = w)` and the transformer's value is forced everywhere. The
adequacy class therefore has no room in it: there is no
wrong-but-passing transformer, and the packet's whole adequacy question
reduces to whether `Triple` (`Wp.lean:552`) and `runP`
(`Defun.lean:293`, on main, out of this lane's scope) say what they
should. They do.

## Gates, verbatim

`lake --wfail build` from `library/cas`:

```
info: Cas/Lang/Wp.lean:876:0: PDD-2: computed wp green — chained table
  admits two bindings, refusing table's wp is false
Build completed successfully (93 jobs).
```

`mise run --force check:cas`:

```
ok vectors/value-single.json (378 bytes) — 1 bindings
ok vectors/blob-two-leaves.json (2252 bytes) — 6 bindings
ok vectors/file-readme.json (1557 bytes) — 4 bindings
ok vectors/journal-two-entries.json (4195 bytes) — 11 bindings
ok vectors/shared-chunk.json (1922 bytes) — 5 bindings
ok vectors/git-pin-commit.json (2867 bytes) — 1 bindings
ok vectors/schema-vector-document.json (5480 bytes) — 1 bindings
ok vectors/index.json (2045 bytes) — 7 vectors
ok schemas/*.json (10 canonical payloads), index, addresses
ok conformance/schema-verdicts.json (71998 bytes) — 68 cases
ok conformance/admission-map.json (10414 bytes) — 22 rows
ok ../effects/src/cas/generated/ConformanceVectorSchema.ts (1834 bytes)
ok ../effects/src/cas/generated/SchemaAdmission.ts (13023 bytes)
ok ../effects/test/generated/VectorPrograms.ts (19433 bytes) — 7 programs
ok ../effects/test/generated/VectorProgramAddresses.json (2816 bytes)
ok ../effects/test/generated/VectorProgramLifts.json (11193 bytes)
ok ../effects/test/generated/EmittedLayers.ts (7758 bytes) — 13 layers
ok ../effects/test/generated/materialized/estate/* (10 modules + index)
ok mcp/cas-tools.json (12391 bytes) — 6 tools
ok ../effects/src/cas/generated/McpToolCodes.ts (11330 bytes) — 6 tools
ok ../effects/src/cas/generated/lift/manifest.json (5478 bytes) — 8 rules
ok ../effects/src/cas/generated/lift/manifest.md (4206 bytes) — 8 rules
ok ../effects/src/cas/generated/grammar/manifest.json (21676 bytes) — 11 sorts
ok REGISTRY.md (14529 bytes) — 11 sorts
ok ../effects/src/cas/generated/grammar/kindTags.ts (2869 bytes) — 11 kind tags
ok ../../docs/lab-core/ENVIRONMENT.json (37002 bytes) — 45 tasks, 16 exes, 8 pins
ok surface/cas-surface.json (955041 bytes) — 2026 declarations
ok surface/cas-obligations.json (17363 bytes) — 68 obligations   [10 of 10 controls fire]
ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound, 28 unbound
                                                                 [13 of 13 controls fire]
[exited with code 0]
```

`git status --short` empty afterwards. The packet's claim that a new
theorem file moves no byte is TRUE, and so is the stronger claim the
lakefile makes for the `[[lean_lib]]` addition: the environment ledger
transcribes `[[lean_exe]]` blocks, so a new library does not move it.

## Axiom census, verbatim

Own census over every public declaration of `Wp.lean`, run with
`lake env lean` on a scratch file of `#print axioms`. Abridged to the
distinct verdicts; the pure definitions
(`WPre.meet`, `WPost.meet`, `WPost.join`, `WPost.top`, `WPost.bot`,
`WPre.le_def`, `WPost.le_def`, `Battery.twoBindings`) report
"does not depend on any axioms".

```
propext ONLY (52 declarations), including:
  wpAux, wp, wlp, wpB, Triple, PartialTriple
  wpAux_iff, wpAux_of_done, wpAux_of_refused, wp_iff, wlp_iff
  runPFrom_halted, runP_done_or_refused
  wp_of_done, wp_of_refused, wlp_of_done, wlp_of_refused
  wp_iff_exists, wlp_iff_forall, wp_mono, wlp_mono, wp_and, wp_or
  wp_bot, wlp_top, wp_iff_wlp_and_total
  runPFrom_put_dangling, runPFrom_put_error, runPFrom_put_ok,
  runPFrom_load_dangling, runPFrom_append_refused
  Triple_iff_wp, PartialTriple_iff_wlp, Triple_two_state, Triple_run
  wp_iff_interpretRef, Triple_iff_interpretRef, wpB_iff, wpB_iff_wp
  all seven falsifier_* theorems

propext + Quot.sound (6 declarations):
  'Cas.Lang.wp_meet'             depends on axioms: [propext, Quot.sound]
  'Cas.Lang.wp_forall'           depends on axioms: [propext, Quot.sound]
  'Cas.Lang.wpAux_append'        depends on axioms: [propext, Quot.sound]
  'Cas.Lang.wp_append'           depends on axioms: [propext, Quot.sound]
  'Cas.Lang.wp_append_le_total'  depends on axioms: [propext, Quot.sound]
  'Cas.Lang.Battery.check'       depends on axioms: [propext, Quot.sound]

NO Classical.choice.  NO sorryAx.  NO ofReduceBool.  NO Lean.trustCompiler.
```

`grep` over `Wp.lean` for `sorry`, `native_decide`, `axiom`,
`implemented_by`, `unsafe` and `partial`: zero hits.

The attack module's own census is the same shape — `propext` on 33
theorems, `propext + Quot.sound` on three
(`edge_empty_prefix_nonempty_env`, `candidateA_passes_L5`,
`candidateA_passes_L8`), nothing else.

## Commit order

```
2029a787  PDD-2: the contract packet …          contracts/PDD-2.contract.md  (+260)
fa3b8f8a  PDD-2: wp on the program carrier …    Cas/Lang/Wp.lean (+880), lakefile.toml (+15/-1)
539beec8  PDD-2: the packet's break ledger …    contracts/PDD-2.contract.md  (+57/-5)
```

Packet FIRST, by 12 minutes and by one commit. The history carries the
order the process requires.

`git diff 2029a787 539beec8 -- contracts/PDD-2.contract.md` shows
exactly three changes: the `NOTE L8` block, the `## Breaks` ledger, and
a battery-name correction on `BATT L6` (`wp_join` → `wp_or`). **No law
statement was rewritten.** In particular L5's `NONEMPTY` restriction
was present in the pre-implementation commit — it is not a post-hoc
narrowing, and no ledger entry is owed for it.

## Findings

### NOTE-1 — the Quot.sound census is broader than the summary said

`Wp.lean:333, :341, :501, :528, :538, :866`. `Quot.sound` is carried by
six declarations, not two. `wp_forall` (`:341`) is an INDEPENDENT
carrier — it is not downstream of `wp_meet` or `wpAux_append`; the
other three are downstream of `wpAux_append`. The commit message's own
wording ("axioms `propext` and `Quot.sound` only") is accurate. Not a
soundness issue; recorded so a future census has the full list.

### NOTE-2 — the lakefile device is disclosed everywhere except the packet

`lakefile.toml:7-15` states it plainly ("Being outside `Cas`'s import
closure it is also outside `Walk.libraryImports`, so the surface,
obligation and law ledgers do not move; adding it to that walk is a
promotion"). `Wp.lean:61-65` states it. The commit message states it.
The PACKET does not: its claim-scope has six bullets and none names the
walk invisibility, and a grep of the packet for `lake`, `walk`,
`ledger`, `surface` returns nothing on this point.

Per the dispatch's own rule this is a NOTE and not a claim-scope
finding, because the disclosure exists and is where the lakefile change
lives. But the packet is the pinned artifact the estate reads later,
and one claim-scope line would close it. The invisibility claim itself
was verified TRUE and is recorded above under Gates.

### NOTE-3 — L10 and L2 say "at that fuel"; the theorems carry no fuel

Packet `:210-213` (L10): "The embedding halts at fuel `p.length + 1`
and THE ANCHOR IS STATED AT THAT FUEL." The anchor `Triple_iff_wp`
(`Wp.lean:566`) is stated over `runP`, and `Triple` (`Wp.lean:552`) is
`∀ w, P w → ∃ a w', runP H p w = (.done a, w') ∧ Q a w'` — no fuel
anywhere. The fuel enters only in the derived `Triple_run`
(`Wp.lean:594`) and inside the proof of `wp_iff_interpretRef`.

Same shape at packet `:134-137` (L2): the prose says "at the exact fuel
`p.length + 1`" while `wp_iff_interpretRef` (`Wp.lean:605`) mentions no
fuel. The EQUATION printed under L2 does match the theorem exactly; it
is only the trailing clause that adds a fuel the statement does not
carry.

Direction matters: fuel-free is STRONGER than fuel-indexed, so both are
under-claims in the code and imprecisions in the packet, never
overclaims.

### NOTE-4 — `Triple_two_state` covers only `P = ⊤`

`Wp.lean:583`. CONTRACT.md's debt object asks `σ` for a two-state
postcondition relative to the precondition. The packet's ENSURES
(`:90-95`) names `Triple_two_state` as the mechanism. That theorem
reads

```
(∀ w₀, Triple H p (fun w => w = w₀) (fun a w' => R w₀ a w'))
  ↔ ∀ w₀, ∃ a w', runP H p w₀ = (.done a, w') ∧ R w₀ a w'
```

— universally quantified over `w₀` on both sides, i.e. the two-state
triple at precondition `⊤`. The `P`-relative form is not in the file.
It is derivable in three lines and is proved in `Attack.lean`
(`Triple_two_state_rel`), so the record says DERIVABLE, not MISSING.
A coverage gap in the stated mechanism, not a soundness gap.

### NOTE-5 — the falsifiers' toy address function collides, observably

`Wp.lean:723`. `Falsifier.lenAddr` addresses a node by its ENCODED
LENGTH, so `.put 0 0 [] []` and `.put 0 2 [] []` share an address —
both encode to 10 bytes — and the store then REFUSES the second as the
content collision it is. A witness stated at `lenAddr` can therefore be
an artifact of collision rather than of the law under attack. Recorded
in `Attack.lean` as `toy_hash_collides`; the attack's own corpus needed
a payload byte (`putD`) to get two distinct addresses.

Checked all seven of the castle's falsifiers against this: none depends
on `lenAddr` separating anything. `falsifier_wp_not_faithful` and
`falsifier_empty_prefix` and `falsifier_fuel_bound_is_tight` are
one-address or empty-table; the three `absentLoad` witnesses refuse at
any `H`; `falsifier_append_needs_history` turns on a dangling `.ans 0`
at an empty history, which is hash-independent. The ledger's own
witness was additionally reproduced at the production digest
`sha256Addr` (`Attack.lean` `ledgerWitnessAtDigest`, an `#eval` assert,
green), and the battery's `#guard` at `lenAddr` is corroborated by
`Battery.check`'s `#eval` at `sha256Addr`.

### NOTE-6 — the packet was edited after the implementation commit

CONTRACT.md`:28-29`: "The implementer's commits never edit the packet
or the battery; a packet change is a breaker commit." `539beec8` edits
the packet after `fa3b8f8a`. Under the wave-1 operator ruling — builder
authors packet AND body — this is licensed, and it is exactly the
ledger discipline CONTRACT.md`:31-53` prescribes, since a ledger entry
cannot be written before the break fires. Recorded because the history
shows a post-implementation packet edit and a later auditor should meet
the ruling that licenses it, not the appearance of a process defect.

The same commit also corrected `BATT L6` from `wp_join` to `wp_or` — a
battery-name fix bringing the packet to the code rather than the code
to the packet. The LAW and FALS lines of L6 are byte-identical, so
nothing about the law moved.

### NOTE-7 — global `LE` instances on bare function types

`Wp.lean:83` and `:86`. `WPre` and `WPost` are `abbrev`s, so
`instance : LE WPre` is an instance on `Word → Prop` and
`instance : LE WPost` is one on `Addr32 → Word → Prop`. Harmless today
— nothing imports the module — but a promotion of `Cas.Lang.Wp` into
`Cas`'s import closure would give every `Word → Prop` in the estate
this `≤`. The promotion ruling the lakefile already anticipates should
look at this too.

## Break attempts that FAILED

Fifteen. Each is the packet's earned confidence, and the apparatus for
each is in `Attack.lean`.

1. **A wrong-but-passing `wp` (the adequacy class).** FAILED,
   decisively and formally. `anchor_pins_wp`: any transformer
   satisfying L1 agrees with `wp` at every table, postcondition and
   word. No adversarial transformer can survive the anchor.

2. **`wlp` passed off as `wp`** (BREAKER.md, wp-sp-calculus: "WLP
   passed off as WP — crash-freedom dropped"). FAILED. It genuinely
   passes L3, L4, L5 and L6, and it inherits L8 VERBATIM, because
   `wpAux_append` is stated at an arbitrary `refused` and so does not
   distinguish the two transformers at all. Caught by L7 (the excluded
   miracle: `wlp` of `⊥` is TRUE at a refusing table) and independently
   by L1. Both proved.

3. **The snapshot error** (BREAKER.md, loops §11.0: "wrong-state
   postcondition") — `wpStale`, which reads `Q` at the STARTING word
   instead of the final one. FAILED, and this is the sharpest result
   about the law set: it passes L3, L4, L6 AND L7, and is caught by L1
   alone. Refusal is pinned twice over (L7 and L1); the FINAL WORD is
   pinned by the anchor only. Witness: `onePut` from `[]` establishes
   "the final word holds one binding"; the stale transformer reads it
   at the empty starting word and reports false.

4. **The miracle (`assume false`).** FAILED. Passes L3, L4, L6; caught
   by L7. The cheap candidate, and L7 is the cheap defence.

5. **L5's `Nonempty` being an undisclosed post-hoc narrowing.** FAILED.
   The packet diff shows L5 untouched since `2029a787`; the restriction
   was stated before the body existed.

6. **The L8 weakening being insufficient.** FAILED. A 432-point
   exhaustive grid — 12 nonempty prefixes x 12 suffixes x 3 starting
   words — agrees at every point, at both a trivial and a
   word-discriminating postcondition, kernel-decided. 156 of the 432
   have the LEFT side TRUE, so the grid is not passing by comparing
   `false` to `false`.

7. **The side condition being defensive rather than load-bearing.**
   FAILED — it is load-bearing. The same grid run at `pre = []` fails
   at 12 of its 36 points.

8. **The four named L8 edges** — a nonempty prefix REFUSING MID-TABLE,
   a completing prefix whose suffix indexes an answer OUT OF RANGE, a
   suffix load resolving against the STARTING WORD rather than an
   answer (the same table gets opposite verdicts from two starting
   words), and the `env ≠ [] ∧ pre = []` disjunct. FAILED, all four,
   each a theorem.

9. **`wpB` disagreeing with `wp` on a shape the battery misses.**
   FAILED. `wpB_iff_wp` (`Wp.lean:702`) is universally quantified, so
   the battery's single chained table is not the scope of the claim;
   and on 14 adversarial tables x 3 starting words x 2 postconditions
   the computed transformer equals a reference read straight off
   `runP`. Shapes tried: load-before-put, dangling answer index,
   completing-prefix-then-dangling, load-through-own-answer,
   load-of-absent-literal, duplicate put (the store dedups), a
   three-line table ending in a load, refuses-midway, and the empty
   table.

10. **The battery being a gate that cannot go red.** FAILED. Controls
    run outside the tree: a false `#guard` of the battery's own shape
    errors ("did not evaluate to `true`", exit 1), and a false `#eval`
    IO assert throws into an elaboration error. Both mechanisms bite.

11. **The battery's postcondition being vacuous.** FAILED.
    `twoBindings` separates `chained` (two bindings, TRUE) from
    `dupPut` (one binding after dedup, FALSE).

12. **The fuel bound being tight only at the one witness.** FAILED, and
    the finding is stronger than the packet's: `p.length + 1` is tight
    on every COMPLETING table tried (five still RUNNING at `p.length`)
    and slack on refusing tables (three already halted). No two
    theorems disagree about the fuel discipline — `Triple`,
    `Triple_iff_wp` and `wp_iff_interpretRef` carry no fuel,
    `Triple_run` carries the exact `p.length + 1`, and `Handler.lean`'s
    existential-fuel discipline is never restated here.

13. **The lakefile device hiding a ledger move.** FAILED. `check:cas`
    is byte-identical with `Wp.lean` present, ENVIRONMENT.json
    included.

14. **A fenced file being touched.** FAILED. `fa3b8f8a` touches
    `Cas/Lang/Wp.lean` and `lakefile.toml` only. `lakefile.toml` is not
    in the ticket's fence list and its change moves no gate.

15. **Escape hatches in the castle.** FAILED. No `sorry`, no
    `native_decide`, no `axiom`, no `implemented_by`, no `unsafe`, no
    `partial`.

## What the attacker would ask for, if asked

Nothing blocking. Three one-line packet edits would close every NOTE
that is closable: a claim-scope line naming the Lake-library
invisibility (NOTE-2), a correction to L10 and L2 saying the anchor is
FUEL-FREE and that `Triple_run` is where `p.length + 1` lives (NOTE-3),
and a word in ENSURES saying `Triple_two_state` states the `⊤` case and
the `P`-relative form is a three-line corollary (NOTE-4). NOTE-5 and
NOTE-7 are notes for the promotion ruling the lakefile already
anticipates, not for this packet.
