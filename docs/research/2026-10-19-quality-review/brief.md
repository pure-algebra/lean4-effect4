# Codex brief: a quality audit of the OCaml estate, the next consolidations, and the backlog

You are reviewing `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, at
`292becd3d`. Work in the worktree the coordinator made for you, `/Users/pooks/Dev/wt-quality-review`,
cut from that commit. This is a review: commit nothing, push nothing and merge nothing.

## What we want

Defects with evidence, ranked, each with its fix. Not observations. The owner asks for a quality
audit of the OCaml code: its smells, its improvements and its magic numbers. These are the small
things that set a production estate apart from a pet project, in the OCaml, Jane Street and Lean
pedigree. Then the next consolidations, and a cleanup of the backlog's probes.

Three parts, in this order of weight:
- **Part A, the OCaml audit** (about two thirds of the effort).
- **Part B, consolidation:** where one fact still has two owners.
- **Part C, the backlog:** the probe branches, the research folders and the open follow-ups, each
  with a verdict.

Judge everything by two questions. Does it change behaviour on some input? Does it make the next
reader's or agent's correct step cheaper?

## Read first

1. `AGENTS.md`: the rules and the vocabulary.
2. `ocaml/README.md` and `ocaml/STANDARDS.md`: the estate's map and its nine rules.
3. `docs/core/decisions.md`, rows 391 (the lowering's trust boundary), 414, 415 and 416 (waves 1
   and 2, as landed).
4. The plan: `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-18-slices/README.md`, its §10
   (the hygiene list H1 to H21), and `wave2.md` beside it. The receipts in that folder record what
   each seat left open.
5. `src/OCaml5/Lcnf/Builtins.lean`: how each Lean builtin lowers, with its exactness class.

`docs/research` is not in your worktree; read it at the absolute paths above.

## Part A: the OCaml audit

The hand-written OCaml is 221 files and 51,694 lines; its libraries, without tests and tools, are
69 files and 16,671 lines. The generated OCaml is out of scope except where Part A's first angle
reaches it. Each angle below names the question, our first measurement, and where to start. The
measurements are leads, not findings: confirm or refute each one.

**A1. The numeric exactness of the lowering.** Lean's naturals are unbounded and OCaml's `int`
has 63 bits. `Builtins.lean` has 128 rows: 43 are exact only on a domain and 6 are approximate.
`Nat.add` lowers to `+`, whose row says "OCaml `+` wraps at 2^62 without a trap". `UInt64` is
`int` too, "not exact above 2^62". Row 391 trusts the lowering, but only inside these domains. Find
a path from an outside input to an operation outside its domain. The inputs are wire bytes, a JSON
request, a tape answer, a host reply and a stored node. Bounds exist at the ingress points: `E4_clock.check_nat`,
the JSON profile's limit of 2^53 - 1 and `Eff_frame`'s `max_int`. Is every path through one of them?
Look hardest at digests, hashes and identities that Lean computes over `UInt64`, or over `Nat`
modulo 2^64. Examples are `Canonical.digest` and the closure's catalogue identity. A finding gives
the input, Lean's answer and the OCaml answer.

**A2. Untrusted input refuses; it never raises, hangs or overflows the stack.** Every decoder must
answer a refusal:
- `Eff_wire` and `Eff_frame`;
- the store's `E4_shape`, `E4_node`, `E4_control`, `E4_index`, the pack's segments and the
  write-ahead log's records;
- the MCP framing in `Kit_mcp`;
- the lowered JSON reader and `nat_json_parse`.

Fuzz each with truncated, corrupted and oversized bytes, through qcheck or a byte-flip harness.
Any exception, hang or `Stack_overflow` is a finding. Two inputs to try first:
- a length field near 2^62;
- a deeply nested JSON array sent to `eff mcp`, since the JSON reader now has no budget and
  recurses on the value (decisions row 416 (4)).

**A3. The store's durability.** The store's code holds 15 `Unix.fsync` calls and one `Unix.rename`.
Walk the commit path under a power-loss model:
- the order of writes, syncs and renames;
- the directory's sync after a create or a rename;
- the torn tail of a segment or of the log.

Five sites drop an `Error _` silently: four in `E4_cas` (the recovery and index rebuild paths) and
one in `E4_index`. Say which only lose a cache and which lose data or hide corruption. `E4_lock`
uses `Unix.lockf`. A POSIX record lock belongs to the process and drops when any descriptor of its
file closes. Check that nothing else in the process opens `<dir>/LOCK`. Say what `fork` and a
network file system do to the lock.

**A4. Concurrency beyond the three bugs already fixed.** The model tests found two lock bugs and
one admission race (decisions row 415 (7) and (8)). The hand libraries hold 76 `Mutex` uses, 56
`Atomic` uses and 12 `Domain.spawn` calls. Which shared structures have no model test: the mailbox,
the ring, the log, the cache, the kit's session? `E4_quiescence` waits by polling with a 0.2 ms
sleep. `stm_tool` still passes `~retries:2`, which can hide a race. A finding gives the
interleaving, and a qcheck-stm or lin test that shows it.

**A5. Errors as values.** `ocaml/STANDARDS.md` asks for refusals as values. The hand code holds 86
`failwith`, 89 `invalid_arg`, 7 `Option.get`, 22 `List.hd` and 105 `List.nth`, most of the last
two in tests. Split them:
- a programmer error that the interface documents stays;
- one that outside input can reach is a finding.

Check the CLI's exit codes and its use of stdout and stderr too.

**A6. Magic numbers and configuration.** By count of numeric literals above 2, the library files
lead in this order: `eff_frame.ml`, `e4_index.ml`, `e4_shape.ml`, `e4_cas.ml`, `kit_mcp.ml`,
`e4_control.ml` and `e4_pack.ml`. `e4_sha256.ml`'s constants are the standard's, which is
expected. Three asks:
- an on-disk or wire format has one module that names its constants, with a format version;
- a tuning default has one owner and a reason;
- a test count says why it is that number.

`E4_sched.config_of_env` reads eight `E4_*` environment variables inside a library. It silently
keeps the default when a value is malformed. The recipe's caps, 4000 and 2000 in
`ocaml/gen/roots.json`, need a reason or a measurement.

**A7. Interfaces.** Several hand modules have no `.mli`: `kit_serve.ml`, `api_engine_inst.ml`,
`api_engine_prelude.ml` and `join_escape.ml`, besides test files. Check four more things:
- the 141 `mutable` fields: is each behind an abstract type?
- polymorphic `compare` and `=` on abstract or functional values (54 `compare` sites);
- the 220 `ignore (` sites, where an ignored result may be an error;
- the warning policy: seven flag strings, `-w -33` in `api_gen_inst.ml`, and the kit without the
  engine's `-w @55`.

`dune build @doc` reported 39 warnings or errors at H6; measure them again.

**A8. Idiom, against the pedigree.** Compare with Jane Street's `Base` and `Core`, the compiler's
compiler-libs, and the outside libraries' contracts (`~/Dev/refs/ocaml-tooling/MANIFEST.txt`). Look
at:
- exceptions against results;
- `Printf` inside a library;
- resources without `Fun.protect`;
- hand string building where a `Buffer` or `Format` fits;
- hand derivations where a stock deriver fits a hand type (the sexp probe, `probe/sexp-face`);
- `ppx_expect` where a test compares a golden.

A finding here changes behaviour or reading cost. A style preference is not a finding. ocamlformat
with the Jane Street profile already holds the layout (row 415 (10)).

**A9. Tests that earn their keep.** Find:
- the tests that pin a count or restate a generated output;
- the tests no mutant of the C4 campaign fails
  (`/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-18-slices/w2-engine-mutants/`);
- the slowest tests;
- the tests that fail under load (`stm_load.py` there).

**A10. Hot paths.** Look for list indexing and string concatenation in loops, and `@` in
recursion. Look for structural hashing of large keys, and allocation in the scheduler's loop. Measure before you claim:
a profile or a timing beats a reading.

## Part B: consolidation

**B1. The hand lines that still copy Lean.** `measure.py` in the slices folder counts 567 and lists
them. For each group, name the Lean owner and whether it can be lowered or deleted. If it must stay,
say why.

**B2. OCaml copies of OCaml.** Look for:
- the seven warning flag strings;
- the hex, UTF-8 and digit helpers (`Eff_frame.utf8_valid` against Lean's own check);
- the JSON helpers left in the kit;
- the test helpers that predate `E4_check`.

**B3. Lean copies of Lean.** The jsonexact receipt's J3 (the duplicated `Except` steps) and J4
(`unseenDefs` and `TyDecls.unseen`). Hygiene H11: the 155 `]!`, 12 `head!` and 2 `get!` in `src`,
which the OCaml lowering turns into panics. H13 and H14 too.

**B4. A program's two JSON spellings.** Face 7's `V` array spelling (`OCaml5.Eff.effV.json`,
`ts/eff/json.gen.ts`) and the canonical tagged spelling (`Canonical.print`, the tool's wire) are
related by no theorem. Recommend one spelling, or two with the theorem that relates them, before F1.

**B5. The generated surface's size.** `ocaml/gen/closure_gen.ml` has 69,991 lines.
`ocaml/engine/test/lanes/lanes_gen.mli` grew by 3,774 lines, and `closure_gen.mli` repeats
`api_gen.mli`'s types. What can the generator stop emitting?

## Part C: the backlog

**C1. The probe branches.** Fifteen worktree branches hold commits that `refactor/phase1-phase3`
lacks. Read each with `git log HEAD..<branch>` and `git diff HEAD...<branch>`. Give a verdict: land,
cherry-pick a part, or drop, with the reason.

| Unmerged commits | Branch |
| --- | --- |
| 14 | `codex/vessel-dogfood` |
| 8 | `codex/abstraction-probes` |
| 7 | `codex/vessel-model` |
| 4 | `codex/vessel-fmi` |
| 2 | `codex/vessel-step` |
| 2 | `codex/probe-canonical-image` |
| 2 | `probe/sexp-face` |
| 2 | `claude/laughing-northcutt-cd0311` |
| 2 | `claude/math-d3` |
| 2 | `claude/sad-williamson-6d3b65` |
| 2 | `seat/schema-interop` |
| 1 | `claude/codec-arm-lemmas` |
| 1 | `claude/gracious-shamir-5b34bd` |
| 1 | `codex/probe-pull-dispatch` |
| 1 | `codex/probe-source-resolution` |

Thirteen more worktrees hold no commit that the branch lacks; the coordinator removes them. Read the
other worktrees through `git` only, and change none of them.

**C2. The research folders.** Which folders under `docs/research/` dated 2026-10-15 to 2026-10-18
hold a probe whose result is in neither the tree nor a decisions row? Which can move to an archive
branch (hygiene H16)?

**C3. The open follow-ups, in one order.** These are:
- the hygiene list's H2, H4, H6, H8 (what remains), and H10 to H21;
- wave 3: A4 to A7, F1, E3 and E5;
- the jsonexact receipt's J1 to J5;
- the stale prose: the lanes' docstrings, `Run.Kit`, `Tool.Native` and `scripts/generate.py`'s
  comments;
- the six planned goals.

Order them by what each unblocks. Merge any that are one change, and drop any that no longer apply.

## The finding template

```text
ID          A<n>.<k> | B<n>.<k> | C<n>.<k>
Severity    critical | high | medium | low
Kind        defect | smell | consolidation | cleanup
Where       the files and declarations, by name and path
Evidence    the command, the input and its output; a failing test or counterexample beats an argument
Why         the rule it breaks (STANDARDS rule n, AGENTS.md, a decisions row) or the behaviour at risk
Fix         the change, and the files it touches
Deletes     what goes, with line counts from a command
Test        the red control that fails before the fix and passes after it
Plan        new, or an existing item (H<n>, A<n>, C<n>, F1, E<n>, J<n>)
Size        XS | S | M | L
```

A finding without evidence is not a finding, and "consider" is not one either. Part A gives twenty
findings at most and Part B ten, ranked by severity, then by what they save. Part C is tables.

## Probes

- **OCaml:** build in your worktree's `ocaml/` with `opam exec --switch=effect4 -- dune build`. A
  fuzz harness, a model test or a counterexample input is the best evidence.
- **Lean:** your worktree has no Lean build. Run a check from the main checkout, which is built, as
  `python3 /private/tmp/seams-lean-one.py lake env lean <file>`; it writes nothing there.
- Put every probe under the report folder's `probes/`, with the command that runs it.

## Rules

- Write only `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-19-quality-review/codex-review/`:
  `README.md` and `probes/`.
- Edit no tracked file in any checkout.
- Run none of these: `make`, `lake build Test`, `make gen-semantics`, `tsc`.
- Respect the owner's steers:
  - one owner per fact, and Lean owns meaning;
  - Lean carriers get generated faces, never hand ones;
  - the LCNF lowering owes no proofs (row 391), but a builtin used outside its declared domain is
    a defect;
  - no new program syntax;
  - never argue from rebuild cost;
  - no retired gate lane comes back, and a new check replaces an old one.
- In a Lean probe, write no `simp_all`, `first |` or `try`.
- Cite code by path and declaration name, and literature by authors, title, venue and year.

## Your report

`README.md` opens with the one thing to know. Then:
- a table of the ten findings that matter most;
- the findings of Parts A and B, ranked;
- Part C's tables;
- the decisions only the owner can make.

## Appendix: how the leads were measured

All counts are from `292becd3d`, run in `ocaml/` unless the root is named.

- **Hand files:** `git ls-files '*.ml' '*.mli' | xargs grep -L GENERATED`, without
  `tools/typed_lint/test/`; the libraries are the `.ml` files without `test/`, `tools/`, benches
  and probes.
- **Smells:** `grep -c` over those files for each pattern named above.
- **Numeric literals:** a `grep -o` of literals above 2 over the library files, counted per file.
- **Builtin rows:** `grep -c` of `row … .domain` and `row … .approximate` in
  `src/OCaml5/Lcnf/Builtins.lean`, from the root.
- **Branches:** `git rev-list --count HEAD..<head>` for each entry of `git worktree list`.
