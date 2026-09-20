The added ST9–ST11 arena checks pass, and the OCaml workspace builds. The test output reports zero failures.

The checks cover dense Ref/Deferred keys, preservation of old cells at allocation, and preservation of other keys at replacement. They include empty stores, sizes around 8, 64 and 500, absent keys, negative host indices and max_int. The sparse scope example fails the density predicate as intended. These are finite host checks; the universal arena laws are separate Lean obligations.

Both exact commands, exit codes and source hashes are in manifest.json. No generator ran.
