# 2026-10-05 seat A401 receipt: the audit of 4.0.1 against the pin, and its vendored source

**The one thing to know before merging:** the branch adds `vendor/effect-4.0.1/` and the seat's
notes under `docs/research/`, and it changes no other tracked file. No gate, generator or census
reads the new folder, and the pin stays at rc.112. The audit's own headline is in
`docs/research/2026-10-05-seat-A401/audit.md`. For this tree the release is a new runtime
revision. It repairs `U-01` on the row's reproduction, and `U-02` stands.

## Base and head

- Branch `seat/audit-401`, worktree `/Users/pooks/Dev/lean4-effect4-audit401`, base `5ebacecc`.
- `1c488570`: the vendored tree, as its own commit.
- `8e9540b1`: the audit note, its scripts, probes and outputs, and two wording repairs of the
  vendored folder's README.
- Head: the commit that adds this receipt. The seat's final message gives its hash.
- Nothing is pushed.

## Changed files

| Path | What |
| --- | --- |
| `vendor/effect-4.0.1/src/` | 496 source files, `package/src` of the registry tarball |
| `vendor/effect-4.0.1/LICENSE` | `package/LICENSE`; its bytes equal the pin's |
| `vendor/effect-4.0.1/README.md` | the provenance, in the pin's layout |
| `vendor/effect-4.0.1/SHA256SUMS` | 496 lines, in the pin's format |
| `docs/research/2026-10-05-seat-A401/audit.md` | the note |
| `docs/research/2026-10-05-seat-A401/scripts/` | 13 scripts and 4 hand tables |
| `docs/research/2026-10-05-seat-A401/probes/` | 3 probes, their outputs on both builds, 1 input |
| `docs/research/2026-10-05-seat-A401/out/` | the tables, the hunks of the 60 cited files, the truth run |
| `docs/research/2026-10-05-seat-A401/provenance/` | the registry record, the attestation, the retrieval facts |
| `docs/research/2026-10-05-seat-A401-receipt.md` | this receipt |

No `.lean` file, no file of `docs/core/`, no register, no generated file, no `package.json` and
no lockfile changed.

## Commands and results

`<S>` is the session's scratchpad folder. `<pin>` is `ts/eff/node_modules/effect` of the main
checkout. `<rel>` is the installed 4.0.1 copy that the brief names.

| Command | Result |
| --- | --- |
| `curl -sS -o effect-4.0.1.meta.json https://registry.npmjs.org/effect/4.0.1` | HTTP 200, 3284 bytes, read 2026-10-05T15:57:57Z |
| `curl -sS -o effect-4.0.1.tgz https://registry.npmjs.org/effect/-/effect-4.0.1.tgz` | 8925614 bytes, 2026-10-05T15:58:13Z; SHA-1 and SHA-512 equal `dist.shasum` and `dist.integrity` |
| `curl -sS -o effect-4.0.1.attestations.json "https://registry.npmjs.org/-/npm/v1/attestations/effect@4.0.1"` | upstream commit `460272d30457f4697d8b8c52cad41caccbcace08`; the subject digest equals the tarball's SHA-512 |
| `tar -xzf <S>/effect-4.0.1.tgz -C vendor/effect-4.0.1 --strip-components=1 package/src package/LICENSE` | 497 files; each equals its tar entry |
| `shasum -a 256 -c SHA256SUMS`, in `vendor/effect-4.0.1` | 496 OK of 496; the same on the committed bytes of `1c488570` |
| `diff -rq <rel>/src vendor/effect-4.0.1/src` | exit 0; the whole installed copy equals the tarball's 2561 files |
| `python3 scripts/check-docs.py` | PASS, 72 documents, before and after each commit |
| `TMPDIR=<S>/tmp ./scripts/generate-effect-runtime-census.sh`, compared with `generated/effect-runtime-census.tsv` | byte-identical |
| `bun scripts/strip.mjs` (four trees) and `bun scripts/units.mjs` (four trees) | 452 and 496 files each; no parse error |
| `python3 scripts/compare_trees.py` | 447 files paired, 267 moved; `out/files.tsv` |
| `python3 scripts/inventory.py` | 3190 rows, 2980 of a pin file; `out/citations.tsv` |
| `python3 scripts/map_citations.py` | 1190 ranges in 60 files; same 2223, changed 550, removed 68; `out/ranges.tsv` |
| `python3 scripts/census_against_release.py` | equal 83, drifted 44, anchor absent 10 |
| `python3 scripts/classify.py` | 618 changed citations, 0 unclassified hunks |
| `python3 scripts/dependents.py` | 287 declarations, 4 registry claims joined directly, 7 register rows |
| `python3 scripts/stale_in_pin.py` | 77 candidates |
| `EFFECT_DIR=<pin> bun probes/backlog.mjs`, then with `<rel>` | exit 0 twice; `probes/backlog.rc112.out`, `probes/backlog.v401.out` |
| `EFFECT_DIR=<pin> bun probes/runtime-changes.mjs`, then with `<rel>` | exit 0 twice |
| `EFFECT_DIR=<pin> PROFILE=probes/profile-heads.input.json bun probes/profile-heads.mjs`, then with `<rel>` | all 58 heads resolve on both; two entry points absent on the release |
| The truth harness's host phase in a copy linked to `<pin>` | `result.json`, `result.md` and six tapes equal the committed files |
| The same copy linked to `<rel>`, two import paths changed in the copy, a stub for the SQLite driver | 30 of 39 programs keep verdict and exit; `out/truth-401/` |
| `python3 scripts/check-language.py --show` on the note, this receipt and the README | no finding |

`out/pipeline.log` holds the result lines of one whole run of the scripts from an empty scratch
folder. That run wrote the same `citations-mapped.tsv` and `changed-citations.tsv` as before.

## Axiom output

No Lean declaration changed. No `lake` command ran.

## Evidence

| Claim | Evidence word | Bound |
| --- | --- | --- |
| The vendored `src/` equals the registry tarball's, and the tarball matches the registry's two hashes | tested | The attestation's signing is not verified |
| The census table is unchanged by the new folder | reproduced | The generator only; the census gate builds Lean and did not run |
| The file comparison, the inventory, the range map | tested | Scripts of the seat; 346 bare line parts are attributed by rule with no confirming name |
| The class of each changed citation | reading | A judgment of the seat, per hunk |
| The release repairs `U-01` on the row's reproduction | reading, then tested | A finite run on bun 1.4.2, host only |
| `U-02` stands in the release, and a forked scope with one finalizer is a new case | reading, then tested | The same |
| Four further changes of behaviour: the race, the await of children, the failing cancel, the uninterruptible close | reading, then tested | Finite runs R1, R2, R3 and one row of the backlog probe |
| The budget's yield lands at another step | tested | Four program shapes at a budget of 64 |
| The memo map's changes, the `Union` node's change, the `Config` evaluation | reading | No probe |
| The truth harness's verdicts on the release | tested | 39 programs, host phase only, the committed manifest; five programs not comparable |

No statement of the note is proved.

## Landed theorems and their placement

None.

## Open obligations

1. **The proof-graph closure.** Which registry claims rest on a changed declaration through
   other theorems needs a Lean build. The seat stopped at the direct join.
2. **The cause of the three schedule differences** of the truth run is read, not tested.
3. **The corpus lane** did not run on the release.
4. **The SQLite driver** `@effect/sql-sqlite-bun@4.0.1` is outside the seat's network grant.
   Five harness programs wait on it.
5. **Two assumptions inside `refactor` classes.** Contexts of one cache root resolve the cached
   keys alike. `Hash` agrees with `Equal` on the reasons of a cause.
6. **Uncited hunks.** 1141 hunks that change compiled code in the cited files meet no cited
   range, and the seat did not read each of them.
7. **The download.** The tarball was fetched on the brief and on decisions row 236, under the
   session's permission system. The seat received no message from the owner.

## Proposed decisions rows (proposals only)

| Proposal | Options | The seat's recommendation |
| --- | --- | --- |
| A. `U-01` after the audit | (a) note in the backlog row that 4.0.1 repairs it, and retire the divergence with the migration's failure-walk slice; (b) adopt the release's whole rule now; (c) no change | (a). The release also adds the interrupt reasons when no handler is skipped. That is a new difference from the tree, and the slice transcribes it |
| B. `U-02` after the audit | (a) note in the row that 4.0.1 keeps it and that a forked scope with one finalizer now answers the finalizer's value; (b) no change | (a). The tree's void stays a divergence. Reporting stays the owner's decision |
| C. The migration ruling of row 232 | The nine slices of the note, in its order; or another cut | Take the note's order: paths and names, the failure walk, scopes, fibers, the budget, the memo map, the data plane, then the census and the harness |
| D. Citations that miss in the pin | A repair lane with no pin move: the 12 rows of `Effect4.Program.arms` and the 77 candidates | Open it; it is independent of the release |
| E. The backlog's candidate table | Add the pin's race leak, masked await of children, lost interrupt of a failing cancel and stranded memo observer, each repaired by the release | Add them as candidates, with the probes R1 to R3 |
| F. The census generator's row `cause.union-first-occurrence` | Its line holds the digest twice, so the generated summary starts with a digest and a bar | Remove the second digest and write the table again |
| G. The architecture role register | A row for `vendor/effect-4.0.1` in `tools/Tools/ArchitectureRoles.lean`, not measured | Add it, so the map lists the folder |
| H. The truth lane on the release | A follow-up lane as the note's F12, with the driver installed | Open it after proposal C is ruled |
| I. The contract lines of row 236 | Cite the Queue at the release's lines of the note's F8, and the posted wake at `vendor/effect-4.0.1/src/Queue.ts:2457-2466` | Use them |
