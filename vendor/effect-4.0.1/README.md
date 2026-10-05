# Effect 4.0.1 source, vendored for citation

This directory retains exact source bytes from the released Effect package. They are a citation
target only. Effect4 never imports or executes them. No gate, generator or census reads them.

**The pin does not move.** The pinned source is `vendor/effect-4.0.0-rc.112/`, and every proof and
every census row transcribes that tree. This directory exists by decisions rows 232 and 236 of
`docs/core/decisions.md`. The release is audited against the pin, and a contract that follows
the release cites this tree by path. No proof and no census row is relabelled.

- package: `effect@4.0.1`
- tarball: `https://registry.npmjs.org/effect/-/effect-4.0.1.tgz`, 8925614 bytes
- package integrity: `sha512-b1VlQG9g8fwxE5QnIZuPoOP/0MsqHJSRKxUijjoM80E5q95FXrX5yWtY5XI8G+GJsBQAVSDbLS458z9a++uVvw==`
- package shasum (SHA-1): `823e6870716e77902666874a24834ec7cdda50d8`
- tarball SHA-256: `717bd819cd9656eec72df3789031a50610b8617aac9c2611bedae1090b36be91`
- retrieved: 2026-10-05T15:58:13Z, by seat A401
- upstream commit: `460272d30457f4697d8b8c52cad41caccbcace08`, on `refs/heads/main` of
  `https://github.com/Effect-TS/effect` (package directory `packages/effect`)

## Provenance

The registry record of the version (`https://registry.npmjs.org/effect/4.0.1`, read
2026-10-05T15:57:57Z) gives the tarball's address, its integrity and its shasum. The downloaded
tarball matches both hashes. The record names no `gitHead`. The upstream commit above is the one
that the registry's provenance attestation names
(`https://registry.npmjs.org/-/npm/v1/attestations/effect@4.0.1`, SLSA provenance v1, workflow
`.github/workflows/release.yml`). The attestation's subject digest equals the tarball's SHA-512.
Nobody verified the attestation's signing here.

`src/` is `package/src` of that tarball, and `LICENSE` is `package/LICENSE`. Every file was
compared with the tarball's entry after the copy. The retrieval record and the registry's two
documents are in `docs/research/2026-10-05-seat-A401/provenance/`.

An installed copy of the same version (`bun install` of `effect@^4.0.1`, 2026-10-05) holds the
same 2561 files as the tarball, byte for byte. Its `src/` therefore equals this directory's.

## The files that the pin's README names

The pin's README lists the files that the census and the Schema gates read. The table gives the
same files here. No gate reads them in this directory.

| File | SHA-256 | Equal to the pin's bytes |
| --- | --- | --- |
| `src/SchemaRepresentation.ts` | `280ce6db5d31d1254fc5e2ded92601eeac8841eb8c9f8e567db6ddba645d5b85` | no |
| `src/internal/effect.ts` | `e44262d0f2d75afc74ed16b255736fd5074fc74d049d61eff42447328d0e3a73` | no |
| `src/internal/core.ts` | `8657caf09d69df775a0a8b0407a531c6158ca3eef72e7de90eaf830ead1faed3` | no |
| `src/Scheduler.ts` | `c8d81c991fe44824f998ee1ece00fbba9741521de02066a955bf14937adbfca3` | no |
| `src/Scope.ts` | `c378113be62d58db8836ceb3572d458bb4fe1e4c7d88d32b8423199227f88f99` | no |
| `src/Exit.ts` | `f9e4baea6718bd6617069563028710cfaee3ba7b432826f87c405e0ca3513818` | yes |
| `src/Cause.ts` | `b26dd5b0e1982ec25be361916d28d235a73861b5b337369b70e892a33785fda2` | no |
| `src/Array.ts` | `2cf467ff972db2b32556ec95bae4c5d9f1b4292aa89aac1f813ce6693f351e85` | no |
| `src/Context.ts` | `f707a7d486b8da194e3742b419edfd96ccfa25cddf42b911d40694be355b9aa7` | no |
| `src/Result.ts` | `ce118229b4ef376174ccc0b4675c908eee2f22a252c9dabbf01ec8d1af1ad768` | no |
| `src/Ref.ts` | `69dc695dbe042baec090178dcc261f9a171e15a9fe6034d1c479408d6369d8fc` | yes |
| `src/MutableRef.ts` | `0ededd9c6d3f865a9ff804aff3fe7ca7413c22ecd697ae0e7f87d80771ee7a1f` | yes |
| `src/Deferred.ts` | `3cb80cc3c17148d8c6cc264e80f196ca7799c49423497ca7929d98179c797198` | no |
| `src/Layer.ts` | `55349c5c408fed033eacc818a2debf3cc1903129064df06642571a570151431a` | no |
| `src/internal/layer.ts` | `6ad3c8e779bae54dc0b3e57cd99fcd2087354df0c673d6335619d5cd95a74187` | yes |

## Where the pin's files are

The release has no `src/unstable/` folder. Each area of the pin's `src/unstable/` is a top-level
folder here, under the same name, with one exception: `unstable/httpapi/` is `http-api/`. So the
pin's `src/unstable/sql/SqlClient.ts` is `src/sql/SqlClient.ts` here.

Five files of the pin have no counterpart at the same path or at the moved path:
`Encoding.ts`, `internal/schema/schema.ts`, `internal/schema/toArbitrary.ts`,
`testing/FastCheck.ts` and `unstable/encoding/Msgpack.ts`.

The audit note, `docs/research/2026-10-05-seat-A401/audit.md`, compares the two trees file by
file and maps every cited line range of the pin to this tree.

## Full source tree

The manifest is `SHA256SUMS`, in the pin's format: one line per file of `src/`, sorted by byte
order. Check it from this directory with `shasum -a 256 -c SHA256SUMS`.

The included `LICENSE` is the package license. Its bytes equal the pin's `LICENSE`.
