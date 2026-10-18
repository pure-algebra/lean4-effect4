# Codex: implement the authoring system's seams (brief, version 2)

## The one thing to know first

[interfaces.md](interfaces.md) version 2 is the plan. Implement its §6 slices in dependency order,
starting from the declarations in
[interface-probe/SeamsInterfaces.lean](interface-probe/SeamsInterfaces.lean). Each slice lands
green, with its receipt, before a slice that depends on it starts. Where the plan is wrong against
the code, correct it by evidence, record the change in the receipt, and continue. Hand back nothing
that evidence can settle.

This brief also defines the goal's done condition (§6). Version 1 is
[implementation-brief-v1.md](implementation-brief-v1.md).

## 1. Where you work

- Make a worktree on a new branch `codex/seams` from the head that the goal names, on
  `refactor/phase1-phase3`.
- Clone the Lake packages copy-on-write (`cp -c -R .lake/packages <worktree>/.lake/packages`), then
  build.
- Commit each slice on `codex/seams` by explicit paths, with a message that names the slice.
- `docs/research` is ignored by Git, so force-add each receipt (`git add -f`).
- The coordinator merges landed slices into `refactor/phase1-phase3`. Never push.
- Run every `lake` or `lean` command through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`
  with `LEAN_NUM_THREADS=3`, one at a time.
- Run OCaml through `opam exec --switch=effect4 -- dune …`.
- Never run `lake build Test`, `make build` or `make check-full`.

## 2. Read first

1. [interfaces.md](interfaces.md): the plan, its finding tables, the keep and cut divide, the
   loops, the slices, the proof placement and the decisions D1 to D7.
2. [interface-probe/SeamsInterfaces.lean](interface-probe/SeamsInterfaces.lean): the declarations,
   elaborated, with the proved claims and the controls.
3. [README.md](README.md) version 2 and [ledger.md](ledger.md): your amended proposal. Its
   contracts are folded into the plan; §9 of the plan names each choice that differs.
4. [self-review.md](self-review.md) and [codex-review.md](codex-review.md): the two reviews the plan
   answers.
5. [cuts.md](cuts.md): the cut list, slice K0.
6. `AGENTS.md`: the trust rules, proof placement and the landing rules.
7. `ocaml/STANDARDS.md`: the nine rules for every OCaml file you touch.

## 3. What each slice owes

- **Placement before proof.** Each new theorem gets its five placement facts (`AGENTS.md`). Add a
  property to `docs/core/semantics.md` and the registry in the slice that proves it.
- **Registers.** Propose a decisions row in the receipt; never edit `docs/core/decisions.md`.
- **The narrow build** of the touched modules and their direct dependents.
- **`#axiom_audit`** over the touched modules, at `[propext, Quot.sound]`.
- **`make batteries-touched BASE=<slice base>`.**
- **`make check-ocaml`** when the slice touches `ocaml/`, generated OCaml, or a translation root.
- **`python3 scripts/generate.py --only <family>`** after a generator or its input changes.
- **The acceptance rows** of the plan's §6 for that slice, each with its red control.
- **The cuts** that the slice's replacement retires (the plan's §2.2), deleted in the same slice.
- **A receipt** at `docs/research/2026-10-17-seams/receipts/<slice>.md` (§5).

## 4. Order

1. Start K0, S0 and ST1a.
2. Write V1's design beside S0. Land V1 after S0's result.
3. Then S1, then S2 and S4, then S3a, then S3b.
4. ST1b follows ST1a; then ST2 and ST3; ST4 needs ST2, ST3 and S3b.
5. S6 comes last. S5a's receipts run beside every slice.

One `lake` runs at a time, so interleave the protocol and store chains rather than running them at
once.

## 5. The receipt

Each receipt opens with the one thing the coordinator must know before merging. Then it records:

- the base and head commits, and the changed files;
- each command with its exit status and result;
- the `#axiom_audit` output;
- each acceptance row of §6, with the evidence that proves it;
- each placed obligation, proved, or open as a planned goal;
- each departure from the plan, with its evidence;
- whether any evidence is bounded or host-only.

## 6. Done

The goal is achieved when all of the following hold, each shown by a receipt:

1. Every slice of the plan's §6 is committed on `codex/seams`, with its receipt. The slices are K0,
   S0, V1, S1, S2, S4, S3a, S3b, ST1a, ST1b, ST2, ST3, ST4 and S6.
2. Every acceptance row of §6 passes, with its red control.
3. Every "goes" row of the plan's §2.2 is deleted, with its callers moved.
4. The laws the plan marks new are proved, or are planned goals placed by `AGENTS.md`'s rule.
5. The last slice's narrow build, `#axiom_audit`, `batteries-touched` and `check-ocaml` pass.
6. A summary receipt, `receipts/README.md`, maps each slice to its commit and receipt. It also lists
   the plan's departures and the proposed decisions rows.

## 7. Stop rules

- Add no second program representation, run language or edit interpreter.
- Every checker is an `Oracle`. Build no cache that can change an answer.
- Persist no derived state. A session persists as its accepted actions.
- Store no checker result (D1). A result node enters only through the store's node check.
- Leave `lakefile.toml`, `docs/core/decisions.md` and the registers alone outside the slice's
  placement.
- A pattern beside the plan's, or a law weaker than the one placed, stops that slice's line of work.
  Record the counterexample as its control, correct the plan in the receipt, and continue.
