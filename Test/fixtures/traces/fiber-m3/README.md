# Frozen host traces of the retired M3 `Fibers` family

These nine `.tsv` files are the rc.112 host traces the M3 sequential-projection family
and its runner (`git:606918e:harness/trace/fibers-tail.ts`, retired on
2026-09-04) produced against the pinned install. They are kept because
`src/Effect4/Machine/Stores.lean` and `src/Effect4/Machine/Witnesses.lean` cite the four race traces as
the host evidence behind the race witnesses. They are evidence, frozen: nothing regenerates
them, and `generated/traces/` no longer has a `fiber/` directory.
