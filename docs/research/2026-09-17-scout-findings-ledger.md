# Scout findings ledger, 2026-09-17

One row per finding that asks for work. The scouts' notes hold the evidence; this file holds the
status, so nothing a scout found is lost between sessions. "Checked" means the coordinator
re-ran or re-read the claim against the tree, and how. Status: **landed** (with the commit),
**queued** (accepted, not started), **ruling** (waits on the owner), **declined** (with the
reason), **open** (not yet assessed).

Notes: A `2026-09-17-scout-reader-as-eff-program.md`; B
`2026-09-17-scout-bidirectional-types-and-iterate-ergonomics.md`; D
`2026-09-17-scout-named-and-exact-service-keys.md`; C (schema and algebra simplification, drift,
tree types), E (cleanup, laws apart from implementation, silent drift), F (coverage and the
foundations close-out): running when this file was opened; their rows are added as they report.
The coordinator's own note: `2026-09-17-loop-sugar-and-list-elimination.md`.

| id | from | finding | checked | status | tracked at |
| --- | --- | --- | --- | --- | --- |
| A-1 | A | One layer of the reader is authorable today as an `Eff` program with the existing sugar; in `Straight`; agrees with a Lean `matchLayer` and the machine; prints with existing prelude names. | probes 1 and 2 re-run, results match | queued: after R5.2, as a worked demonstration, in the scout's three slices | R4-R6 packet §5b |
| A-2 | A | `Val.ctor` is invisible to the language: no atom or decision sees the generated `Image` of an inductive. | read | open: folded into the tree-types question (C) | loop-sugar note §3b |
| A-3 | A | `run_eq_meaning` and the loop agreement are stated at the empty environment; a program with a free variable is not covered. | read | open | none yet |
| B-1 | B | `iterate`'s annotation optional, `none` synthesized and printed unannotated. | compiled (`ofTy` collisions, typing tells them apart) | **landed** `5185a6cd` (DI-91, ruled) | DI-91 |
| B-2 | B | `admitProgram`'s `int` ban missed a `Ty` inside the tree. | compiled (the counterexample was admitted) | **landed** `5185a6cd` (DI-92; `int` stays) | DI-92 |
| B-3 | B | A unit-result loop could print as the bare `Effect.whileLoop`. | n/a | **declined** by the owner: nothing just retired is refurbished | DI-91 |
| B-4 | B | No term constructs an `Option` value, so `select … .option` can only scrutinize a row's answer. | read (`NativeAtom.all`, `Lit`) | ruling: the option and list kit (`none`, `some`, `nil`, `cons`, `uncons`), or the nominal eliminator of §3b | loop-sugar note §3, §4 |
| B-5 | B | Loop sugar as authoring-only definitions (`iterateWith`, counting, folds, an effectful condition). | compiled: four forms typed and correct on the machine, the list fold correct and untyped | ruling: names and home (`Authoring/Loops.lean`) | loop-sugar note §2, §4 |
| B-6 | B | rc.112 has no `Effect.iterate` and no `Effect.loop`. | read (`vendor/…/Effect.ts` exports) | noted; no idiomatic head to print | DI-91 |
| D-1 | D | "Full-key service identity" is one defect: a printed key has no nominal identity on rc.112, so the host's `R` identifies a service by carrier type; the measurement half landed (`38344fcc`), the repair (one nominal class per full key, and spelling `R`) is unstarted. "Named keys" as a change to `ServiceKey`'s data has no written plan; keys stay two numbers. | not yet re-run (the scout reproduced it in Lean and under `tsc`) | ruling: six owner rulings in the note's last section; recommended order R4, R5, then K1 to K4 | scout D's note §6, "What the owner must rule" |
| D-2 | D | `ServiceDef` authoring surface (declare a service once with a shape, then `service`, `provide`, layers), authoring-only (slice K0, no dependency). | read | queued: can land before the reader line; an afternoon | scout D's note §3, §6 |
| D-3 | D | The hand-selection target lane binds no service keys; the corpus lane's adapter branch is dead code. | read, both files | open (defect) | DI-93 |
| D-4 | D | `src/Effect4/Machine/Key.lean` rested the key order's authority on `PORT-MANIFEST.md`, which no longer exists; the citation gate is blind to a bare filename. | read; the file was removed at `1529a1fe` | **landed** with this ledger: the sentence cites `Ascending` in `src/Effect4/Data/Row.lean` and the manifest by revision | this commit |
| D-5 | D | The citation gate does not see bare filenames (`PORT-MANIFEST.md`, the earlier `Codegen/Layer.lean`). | read | open: a second pattern in `scripts/check-source-citations.py` for backticked `*.md`/`*.lean` names with no root | none yet |
| D-6 | D | `declarationTypeRepresentable`'s first disjunct, `printLayer`'s docstring paragraph, DI-24's superseded `R` clause, the scope key named twice with nothing checking agreement, the `nativeServiceTypes` hand list mirrored by hand into the profile. | read | queued with the key slices (K4, K5) | scout D's note §5 |
| D-7 | D | Two different nouns "key" in one M2 bullet of `docs/STATE.md` (the session's reply key, the service key). | read | queued: one glossary sentence | scout D's note §5.10 |
