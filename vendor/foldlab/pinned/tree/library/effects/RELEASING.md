# RELEASING — the gate sequence a release runs

Status: stub, 2026-08-29 (decision 26 seat 2). Deliberately short: a
release is the existing discipline run in order, not a new one. The
posture and what flips at publish time live in
[PACKAGING.md](PACKAGING.md).

A release of `@foldlab/cas` runs, in order, stopping at the first red:

1. **Fresh-clone truth.** `mise run check:ci` green in CI on the
   release commit — every emitter forced, clean tree asserted, every
   gate forced. A local `mise run check` is not a substitute (it may
   skip).
2. **Provenance correspondence.** The `effect` dependency version,
   `package.json`'s `foldlab.effectProvenance`, and the
   `effect-runtime` row of
   `.reference/provenance/sources.lock.json` name each other. If any
   moved since the last release, the correspondence was re-recorded in
   the same change that moved it.
3. **Register audit.** Every dependency in `package.json` is covered
   by a `docs/lab-core/TOOLS.md` row (or a recorded pending-admission
   entry), at the version actually pinned. Drift is a re-admission
   event, handled before, never during, a release.
4. **Version + label.** Bump `version` (0.x honesty — see
   PACKAGING.md), and the CLI's `Command.run` version string in
   `bin/cas.ts` with it. One commit, both files.
5. **Tarball inspection.** `bun pm pack`; confirm the contents are
   exactly the `files` whitelist. The consumer smoke
   (`scripts/check-dist-consumer.ts`, forced by step 1 inside
   `check:effects:ts`) already packed a tarball, installed it with
   only declared dependencies, executed the bin (`--version`, `init`,
   one MCP handshake through the manifest boot gate), and typechecked
   a consumer under node16 and bundler resolution — this step is
   reading the tarball listing with eyes on top of that. (The
   `prepare` hook is pack-safe: `scripts/patch-toolchain.ts` skips
   when `@effect/tsgo` is absent instead of killing the pack.)
6. **The flip.** Remove `"private": true` (publishConfig is staged);
   publish with npm provenance from CI, never from a laptop.
   Provenance requires an OIDC-capable workflow (`permissions:
   id-token: write`) that does not exist yet — writing it is part of
   the first publish, per PACKAGING.md's flip list item 4.
7. **Record.** Tag the commit; the release notes name the rulings the
   surface moved under since the previous tag.

Steps 1–5 run on every release candidate; 6–7 only on an
operator-ordered publish. Until that order exists, a "release" is
steps 1–5 plus the tag.
