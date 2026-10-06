# Codex's packet on the open questions and on Pool's brief: the coordinator's filing note

Status: history, not authority. Codex wrote this packet at main `2ee2aa91`, and the owner
pasted its relay into the coordinator's session on 2026-10-06 (`relay.txt`). The coordinator
filed the packet's texts here. Its copies of tracked sources, of the seats' logs and of the
coordinator's merge logs are left out.

Do not run a script of this folder in place.

## What the packet says, and what the coordinator did

**1. Two recommendations to the owner. Neither is an approval.** The relay says so itself.

- The census row `interrupt.uninterruptible-mask`: add it with the coverage `partial`. Its
  comment keeps the two missing connections of `questions/review.md`.
- The install made by mistake in seat CONTROLS's scratch folder: delete only that copy.
  Keep the incident's record, the package's identity, the excluded run's log and the
  receipts of the runs that replaced it.

The coordinator applied neither. Each waits for the owner's own word. `docs/STATE.md` lists
both, with these recommendations beside them.

**2. Two corrections of Pool's brief, both made** before any dispatch.

- The brief asked for an invariant: no waiter while an item is idle and the pool is open.
  It is false. A return makes its item idle at once, and its helper selects later. The
  coordinator read the probe's output again. PP4's log holds the line `after H's return and
  before the task: 2 waiting`, on rc.112 and on 4.0.1. The brief now allows that state, and
  it asks for the rule of the step instead. Lease or enrol adds a waiter only when the pool
  is open and no item is idle.
- PP5's schedule starts its borrowers while the acquisition waits
  (`pool-probes/pool-lifecycle.ts`, read again). Decisions row 267 makes `make` acquire every
  item before it answers. So no public run of the first profile reaches PP5. The brief keeps
  PP5 as a control whose state and count are premises, and it adds a public case.

The card has the same two corrections (`docs/research/2026-10-05-claude-lead/module-cards/pool.md`,
sections 3 and 9). No ruling changes, and no statement of the tree changes: Pool has none.

`questions/model-controls.py` is Codex's finite model of the one transition. The coordinator
did not run it. The coordinator's evidence is the retained host output and the probe's source.

**3. The mask's pop discipline has no owner yet.** The coordinator allocated the slice to
Codex first (`../deeper-proof-support/coordinator-filing-note.md`). Codex answers that the
allocation does not lift its own limits: it edits nothing and builds nothing until the owner
says so to Codex directly. So the fallback of that note applies. A seat of the coordinator
takes the slice when one is free, unless the owner lifts Codex's limits first. One owner
holds the slice at a time.

**4. Two reviews of the running seats, with no blocker** (`refs/review.md`, `pub/review.md`).

- Seat REFS: the two consumers lose only the proved premise, and each keeps its formation
  and typing premises. Codex compared seven full statements.
- Seat PUB's attempt laws: no dropped premise. One label is to keep at the merge. The facts
  about names hold for every caller environment. The comparison with the actual operation
  trees is a finite battery. A receipt must not report the second as the first.

Codex ran no Lean, no build and no host program for this packet. Its results on the seats are
readings of the seats' own saved outputs.
