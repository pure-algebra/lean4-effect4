# Codex brief: land the core abstractions, settle the open design questions

You are working in `/Users/pooks/Dev/lean4-effect4` on branch `refactor/phase1-phase3`. Work in a
worktree of your own, cut from the branch head. Commit there, and never push or merge.

## The goal

Effect4 aims to be the best agent-first platform for verified authoring and general computation.
An agent writes a program as first-order data, checks it, runs it, stores it and resumes it.
Every answer it gets is defined once in Lean.

Your job is to make the core abstractions deep and right:
- give each one owner;
- give it a small interface over a lot of function;
- state its laws;
- ground it in the literature and in what the best reference implementations do.

Answer the open design questions below with research and calculation, not taste. Then land the
slices that follow from the answers.

## Read first, in order

1. `AGENTS.md`: the rules. Landing rules are in item 4 under "Rules" below.
2. `docs/research/2026-10-18-agents-md-draft.md`: its table of core abstractions is the frame for
   this brief.
3. `docs/research/2026-10-17-seams/review-2026-10-18.md`: the adversarial review. It covers the
   plan's desires P1–P18, the gap table and the findings.
4. `docs/research/2026-10-18-refinements/README.md`: what already landed overnight, with
   measurements. Do not redo it.
5. `docs/research/2026-10-18-native-exchange/README.md`: the S6b design to test against question 1.
6. The proof seat's branch `worktree-agent-af1c56be5c24596ff`:
   - `combine_deps`, `feed_keeps`, `feed_root` and the fill-set goals are proved there;
   - commit `84f88cf6f` holds kernel-checked counterexamples to some S1 feed goals.

   Read it. Do not redo its proofs.

## Reference shelf

Read these sources directly, and cite each claim by path:
- `~/Dev/refs/ocaml-tooling/`: `hazel`, `rust-analyzer`, `InteractionTrees`, `compcert`,
  `vellvm`, `tezos`, `mcp-spec`, `ocaml-lsp`, `linol`, `merlin`, `bonsai`, `lwd`, `note`, `eio`,
  `dune`, `flow`, `brr`, `ocaml-cohttp`;
- `vendor/effect-4.0.0-rc.112` and `vendor/effect-4.0.1`: the Effect behaviour we transcribe;
- `vendor/refs/`: `Pantograph`, `repl`, `aeneas`, `lean-mlir`, `loom`, `lean4lean`, `veil`,
  `iris-lean`, `cslib`;
- `vendor/papers/`: `gradual-holes`, `program-graphs`.

When a question needs a source that is not on the shelf, such as Irmin, Salsa's book, Adapton or
Jane Street's Incremental, clone it under `~/Dev/refs/`, then record it in
`~/Dev/refs/ocaml-tooling/MANIFEST.txt`.

## The questions

For each question:
- state what the tree has now, by path and declaration;
- state what the literature defines, in a few sentences with citations;
- show what two or three reference implementations do, by path;
- compare the options in one table;
- recommend one, giving its minimal representation, its laws, and what it deletes.

1. **Sessions on disk (S6b): a store port, a snapshot, or something better?**
   - The exchange reads the store through `entryAt`, `root?`, `find` and `commit`.
   - Compare against Irmin's branch and commit store, Tezos' context store, Git's object
     model, and event sourcing.
   - Decide two things: how the generated `Exchange.apply` runs over `E4_disk`, and how resident
     states (a head digest mapped to its loaded state) are proved equal to `load`.
2. **Incremental checking.**
   - Today the design is `Check.Oracle`, `Memo` and `HitRule`, with `combine_deps` splitting a
     module check into parts.
   - Compare against Salsa (rust-analyzer), Adapton, Incremental, Build Systems à la Carte
     (Mokhov, Mitchell, Peyton Jones), and Lean's own elaboration snapshots.
   - Decide the keying, the invalidation rule (early cutoff, red-green), and whether the
     module/part split is the right decomposition.
   - Measured: a native edit costs 0.29 ms, rising to 0.46 ms over 1,000 edits
     (`bench_tool.exe`).
3. **The document, holes and fills.**
   - Today the design is `Doc` (origin plus accepted actions), `FillSet` (fills certified at one
     snapshot), and `SourceSession.feed` under a policy.
   - Compare against Hazelnut, Hazel's live programming with typed holes, total type-error
     localization with holes, and `vendor/papers/gradual-holes`.
   - Some S1 coherence goals are false as stated (`84f88cf6f`). State the true invariant of a
     document under the draft and keep-exact policies, and the law that replaces each false goal.
4. **The agent face.**
   - Today `eff mcp` serves the tool's 19 methods from `Tool.Methods`, a table generated from
     `shape Request`. The kit's `check`, `run` and `explore` stay CLI commands, and `run` also
     cross-checks the call tree against the machine.
   - Compare against the MCP specification, LSP (`ocaml-lsp`, `linol`), Lean's `repl`, and
     Pantograph.
   - Decide four things:
     - whether the kit's commands fold into tool queries, and where the cross-check lives;
     - how a connection names, resumes and forks sessions;
     - structured content versus text in replies;
     - how refusals reach an agent so it can act on them.
5. **The run semantics under the tool.**
   - Today `Eff`, the machine, `Live` and `Run.Tree` transcribe Effect rc.112.
   - Compare against InteractionTrees and algebraic-effect handlers (Plotkin and Pretnar), and
     against OCaml 5 effects (`eio`).
   - Decide whether the machine/tree split is minimal.
   - Decide whether `Program.stepChecked` should take an interpreter built once and sealed: today
     it rebuilds `interpOf` at every step, and the native engine passes it an interpreter it
     ignores.
6. **Trust in generated code.**
   - Today Lean is lowered to OCaml through LCNF (decisions row 391: the lowering is trusted, the
     disk is tested), and Rocq proves the store over exported definitions.
   - Compare against CompCert, Vellvm, Aeneas and lean-mlir.
   - Decide decision D: whether Lean or Rocq owns the store's node laws, given the owner's
     2026-10-16 steer that hard proofs live in Rocq.
   - Decide how to give the native side exact 64-bit numbers, so that `Kit_json`, today a hand
     twin of Lean's shape reader, can be generated.

## Rules

1. **Plain words.** Every Markdown file follows `docs/core/controlled-english.md`: short
   sentences, active voice, one idea per sentence. Draw orders and maps as Mermaid diagrams.
2. **Placement before proof.** A theorem is placed in the theory before it is worked: its concept,
   claim, reach, and consumer (`AGENTS.md`, Trust).
3. **Lean.**
   - Run Lean only through `python3 /private/tmp/seams-lean-one.py lake build <Module>`.
   - Never run `lake build Test`, `make build`, `make check-full` or `make gen-semantics`.
   - Write no `simp_all`, `first |` or `try`; a hand `simp` is `simp only [...]`.
   - Every warning is an error.
4. **Landing.** A landing owes three things and nothing else:
   - the narrow build of the touched modules and batteries;
   - `#axiom_audit` over them, at `[propext, Quot.sound]`;
   - the one behaviour gate it reaches: `make check-ocaml` (now about 2 minutes cold) or
     `make check-ts`.
5. **OCaml.** Run OCaml only through `opam exec --switch=effect4`.
6. **Git.** Commit with an explicit pathspec (`git commit -- <paths>`). Add `docs/research` with
   `-f`.
7. **Files you do not edit.** Leave `docs/core/decisions.md` and the live `AGENTS.md` alone, and
   propose rows instead. Leave the untracked `tools/view/make_videos.py` alone.
8. **Cut as you go.** A new representation lands beside the old one with its agreement theorem;
   then the callers move, and the old one is deleted in the same push. Never leave two owners.

## Deliverables

1. **One research note:** `docs/research/2026-10-18-codex-abstractions/README.md`.
   - It opens with "the one thing to know first".
   - It has one section per question, as described above.
   - It closes with a ranked list of slices: each with its files, what done looks like, and what
     it deletes.
2. **The landed slices:** land those whose answer is clear and whose size is at most a day. Each
   follows the landing rules and gets a receipt line in the note:
   - its commit;
   - the commands run, with their results;
   - its axiom output;
   - what it does not establish.
3. **Your final reply:**
   - your branch and its commits;
   - for each question: the decision, or the open choice and its options, for the owner;
   - the measurements you took, each with its command.
