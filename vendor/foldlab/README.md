# Foldlab evidence vendor

This directory is a sealed evidence input for the Effect4 extraction. It is
not a Lean dependency, and no file below `pinned/tree/` or `late/tree/` may be
imported by Effect4.

There are two deliberately separate bundles:

- `pinned/tree/` contains only bytes tracked by Foldlab at the commit recorded
  in `PIN`. The paths selected from that commit are recorded in `SCOPE.txt`.
- `late/tree/` contains the completed, uncommitted S1, S2, and Layer workshop
  evidence that arrived after that pin: 79 Lean probes, three Layer research
  notes, and three final agent reports. These files are evidence only. They
  have no Git-blob claim and must not silently amend the pinned bundle.

`PINNED-MANIFEST.tsv` and `LATE-MANIFEST.tsv` record every source-relative
path, byte count, SHA-256 digest, and (for pinned files) Git blob identity.
The manifests are deterministic and their file sets are closed.

| Bundle | Files | Payload bytes |
| --- | ---: | ---: |
| Pinned tracked evidence | 826 | 9,456,751 |
| Late evidence | 85 | 2,484,232 |
| Total | 911 | 11,940,983 |

From the Effect4 repository root:

```sh
./scripts/check-vendor-foldlab.sh
./scripts/test-vendor-foldlab.sh
./scripts/vendor-foldlab.sh /path/to/foldlab
```

The first command needs no Foldlab checkout. The second runs the check and
then proves, in disposable copies, that one omission, one extra file, and one
byte mutation are each rejected. The refresh command deliberately requires a
Foldlab checkout containing both the pinned Git object and the late working
files; it reads the pinned bundle through `git archive`, never through dirty
working-tree paths.

The upstream license is included inside the pinned tree as `LICENSE`.
