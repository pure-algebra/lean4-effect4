# Seat brief: the DESIGN-BASIS refresh

Written 2026-10-01 by the coordinator, on the owner's "start the two document pieces now". A
docs-only seat, dispatched when the owner says so, in its own worktree on its own branch from the
base the coordinator names. Nothing in this brief touches `src/`, `Test/`, the registers or the
other authorities.

**The one thing.** `docs/DESIGN-BASIS.md` was last changed on 2026-09-20 (DB-14). Nothing from the
charter, rows 41–118, the typed state, the protocols, the budgeted meaning or `Fits` has reached it,
three of its sections are stale second owners of facts, and sixteen pedigree claims in the research
are wrong or superseded. The refresh makes it one basis with its sources: every row in one shape,
every claim with a source marked tracked or untracked and every paper marked read, by name or
assumed, and status nowhere but as a link to the system map's §8.

## Inputs

Read in this order; where two disagree, the later one wins.
1. The model probe's synthesis, `docs/research/2026-09-30-model-probe/synthesis.md`: §3.1 (the
   pedigree table), §3.2 (the sixteen corrections), §3.3 (the row-by-row verdicts and the row
   shape), §4.1 (one owner per fact), §4.2 (notes that become cited history), §4.3 (the untracked
   notes).
2. Codex's audit, `docs/research/2026-09-30-codex-review-model-probe/audit.md` §6: keep the
   corrections; do not inherit two inaccuracies (the "13 pinned reads" inventory is pre-E, and the
   `ServicesOk` discussion is superseded by `Laws/Program/Typed/Membership.lean`); literature
   claims keep the evidence word of the note that read them, never this seat's "proved"; and the
   two ownership fixes below.
3. The rulings since: decisions rows 111–118 and row 107 (2026-10-01), row 21; brief addenda 4
   and 5; the system map's §1.1 and §8 (2026-10-01).

## The row shape

Every DB row, old or new, ends in this shape:
- **Decision**, in today's names (`Eff`, not `Flow`; `Fits`, not `StrongValue`).
- **Witnesses**: theorem names with `file:line` at a stated commit; a test named as a test; a
  finite probe named as a probe.
- **Refusals**: the register ids (`E4-…-CE-nnn`) and DI numbers that the decision rests on.
- **Sources**: research notes by path and section, each marked *tracked* or *untracked*.
- **Literature**: each paper marked *read* (by which note), *by name*, or *assumed*.
- **Status**: one line, "see system map §8, Rn" or "settled", plus the commit at which the
  witnesses were last re-read. No proof or workstream status is restated here.

## The work, in order

1. **Force-add the eight notes** that hold rulings or literature reads (synthesis §4.3): the
   end-state note, the grill agenda, the provision algebra, the config path, core math, the papers
   review, lit-papers, the dogfood conclusions. Explicit paths; never an evidence folder.
2. **Amend the rows the verdict table names** (synthesis §3.3):
   - **DB-01**: the Σ_core/Σ_app split (system map §1.1) and R2's C1–C8 as conservativity
     *obligations* with the audit's qualifications (C1 binary injections only; C4's iff needs exact
     old protocols; C6 includes every core clause; C7 pins table, profile and session and names
     target admission; C8 per form, tied to R10). Its last paragraph already asks every signature
     map for its own contract and coherence laws: C1 and C2 are those laws. The pin is `v0.8.0`,
     not `v0.1.0`. Add the caveat that sums of theories are Hyland, Plotkin and Power 2006,
     assumed, read by nobody in the tree.
   - **DB-03**: `Beh` and the tape; host answers as decisions (row 95); INV-TAPE-1 and INV-TAPE-2
     only if a row has ruled them by then, else "proposed".
   - **DB-04**: the budgeted meaning (`iter`, `denoteB`, `denoteB_straight`, `meaningB_unique`,
     `loopAgreement`), with its Elgot, Capretta and Jacobs pedigree.
   - **DB-05**: the honest boundary: the fiber layer is algebraic in representation and
     operational in meaning (`E4-SCHED-CE-001`; `Laws/Program/Sched.lean:33-39`).
   - **DB-07**: point to R11 as the theorem its last paragraph asks for; `ExitV` with `StateT`,
     not `EStateM`.
   - **DB-09**: the conflict with system map §1 is resolved toward the system map: it owns the
     route; DB-09 keeps `ProfileData`, `HostSpec`, `Binding` and the evidence classes.
   - **DB-10**: read `Eff` for `Flow`.
   - **DB-11**: admission exists (`admitProgram`, DI-61; reply admission); value typing is rows 44
     and 96, `Fits`.
   - **DB-12**: mark "amend at the landing of rows 104 and 105" and leave the text.
   - **DB-13**: wording only, against DI-11.
   - **DB-15**: untouched; note that the R3 amendment waits on its row.
3. **Add two rows.**
   - **DB-16, typing as a protocol per operation over a world**: the generic `Typed` and the
     concrete `TypedProg` sharing certificates; the world order and antitone typing; coarse values
     with `Fits`. Literature as synthesis §3.1, levels 0–2, with correction 1 (Monotonicity is
     `Typed.widen` plus protocol refinement; `Typed.mono` is Kripke and Iris world weakening).
   - **DB-17, the requirement row calculus**: the provision laws (landed `f182d2b3`), DI-20,
     DI-28, rows 51, 90, 104, 105; `build_total`'s cut (`b08f3b58`) and its restoration owed under
     R5. It owns the row-calculus rationale and links to DB-12 and to the service rulings (rows
     112–114); it does not restate them.
4. **Retire three sections to a dated history appendix** at the end of the file, text kept,
   each with one line saying what superseded it: "Semantic decomposition"; "Native library
   boundaries" (DI-11 and DI-89 own how modules enter; `machine-state.md` §5 restates it);
   "Required proof graph" (status is the system map's; its three stale cells are synthesis §3.2
   item 15).
5. **Replace "Primary sources" with one bibliography** built from §3.1's literature column, each
   entry marked read (by which note), by name, or assumed. Nothing is promoted from by-name to
   read by this seat.
6. **Carry each cited claim into its row** as its decision-relevant conclusion with its source
   line, so the basis stands without the research notes (audit §6: not status, not the host or
   stage contracts wholesale).
7. **Check every citation**: each `file:line` and theorem name exists at the stated commit (a
   small script under the seat's research folder is fine; no generator, no build). A witness that
   cannot be found is marked "witness missing at `<commit>`", never invented.

## The two ownership rules (audit §6)

- A row's status field is a link to system map §8. The basis owns decisions, rationale and dated
  evidence receipts; it does not become a second live ledger of proofs or workstreams.
- DB-01 owns the conservativity obligations; the system map owns the signature's definition and
  the requirement index; `lcnf-route.md` owns the readable-domain stage rules; DB-17 owns the
  row-calculus rationale. Link across them; copy nothing.

## Rules

- Files: `docs/DESIGN-BASIS.md`; the eight force-added notes (unchanged content); the seat's
  folder `docs/research/2026-10-01-design-basis-refresh/` with its receipt and scripts. Nothing
  else. `docs/core/*`, `docs/STATE.md`, `README.md`, `decisions.md` and `DESIGN-ISSUES.md` are the
  coordinator's: propose their lines in the receipt.
- No `lake build`, no `make`, no generator. Reading code is fine; citing it is the point.
- Plain words. Evidence words on every claim: proved, tested, reading, assumed. "Proved" only for
  a theorem this seat re-read at the stated commit.
- One owner per fact. Where a fact would gain a second owner, stop on that item, record it, and go
  on.
- A correction in synthesis §3.2 that turns out wrong is recorded in the receipt and not applied.
- Commits by explicit paths on the seat's branch; the research folder force-added; no push.

## Receipt

`docs/research/2026-10-01-design-basis-refresh/receipt.md`, the one thing first; then base and
head; every changed path; the rows amended, added and retired, each with its witnesses re-read at
the stated commit; the citation check's command and result; the corrections not applied and why;
the lines proposed for the coordinator's files; what remains stale.

## Base

The head of `refactor/phase1-phase3` the coordinator names at dispatch, at or after `56da0e1e`.
