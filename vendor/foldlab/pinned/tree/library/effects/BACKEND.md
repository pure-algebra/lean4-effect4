# The local composition — where the bytes actually live

`PROFILE-CAS-HTTP-0.md` is the wire authority. This is the storage one:
what a store IS on a machine, which layers make it, and what backing it
up means. Two layouts are supported, and the CLI's `config.json` is
what says which one a directory is.

Everything here is a composition of layers the library already
publishes. The library names no database and no disk: it speaks
`FileSystem`, `KeyValueStore`, and `SqlClient`, and the concrete
choices below are made by the CLI (`bin/cli/store.ts`), by a test, or
by you.

## The file layout — the default, and the committable one

```
store-root/
  config.json                              {"backend":"file", …}
  objects/<2 hex>/<62 hex>                 canonical bytes
  roots/<64 hex>                           empty file; presence is the publication
  word.jsonl                               one receipt per line, in admission order
```

```ts
Cas.layerWorded(
  Cas.layerFileBackend(storeRoot),
  Cas.layerFileWordLog(storeRoot),
).pipe(
  Layer.provideMerge(Cas.layerAddressSha256Live),
  Layer.provide(myFileSystemLayer),
)
```

`Cas.layerFile(storeRoot)` is the same store WITHOUT receipts — the
word log is an optional service, and a composition that provides none
gets the store law unchanged. `layerWorded` exists because the log has
to stand UNDER the store law's build for the law to see it, and a
composition that merges it beside instead leaves every admission
unreceipted with nothing to say so.

The address is the path, so the filesystem is the index — no manifest,
nothing to rebuild. The directory is the store: rsync it, commit it,
serve it read-only over HTTP and read it back with
`Cas.layerPathReader`, which is why a git-hosted store needs no server
at all.

**`word.jsonl` is the one file in that directory that does not copy.**
Objects and roots are content and names — copying them is the whole
point. Receipts are this device's own record of when it learned
something: the marks are positions in THIS store's history and the
timestamps are THIS host's clock. Copy the directory and both devices
hold receipt 7; append on both and they hold different receipt 8s,
which is a divergence no merge can settle, because the word does not
sync. Copy the store to move the content, and read the copy's history
as the copy's — never as a continuation of the original's. (The
db-backed layout carries the same carve-out one layer down:
`bin/cli/store.ts` states it for Litestream, where a restore restores
this device's word rather than merging two.)

A transient `word.jsonl.lock` may appear beside it: the cross-process
write lock, held only while an append is in flight. Nothing copies it,
and a stale one left by a killed writer is safe to remove — the
refusal that names it says so.

## The database layout — one file, replicable

```
store-root/
  config.json                              {"backend":"sqlite", …}
  cas.db                                   cas_objects + cas_roots + cas_word
```

```ts
Layer.mergeAll(Cas.layerStore, Cas.layerSqlRootStore()).pipe(
  Layer.provideMerge(Layer.mergeAll(
    Cas.layerKvsBackend,
    Cas.layerSqlWordLog(),
  )),
  Layer.provide(KeyValueStore.layerSql({ table: "cas_objects" })),
  Layer.provide(SqliteClient.layer({ filename: `${storeRoot}/cas.db` })),
  Layer.provideMerge(Cas.layerAddressSha256Live),
)
```

That stack is the whole design. Reading it bottom-up:

- **`SqliteClient.layer`** — the only place a driver is named. The
  library never imports it; the CLI does, because a shipped binary has
  to pick a host. Swap this one line for a Postgres or MySQL client and
  nothing above it changes.
- **`KeyValueStore.layerSql`** — the object table, `cas_objects`, keyed
  by the store-root path every path-shaped backend shares
  (`objects/<2 hex>/<62 hex>`). The address is still the key.
- **`Cas.layerKvsBackend`** — the byte plane over that key-value store:
  `ByteReader` and `ByteWriter`, and never `RootStore`, because a
  `KeyValueStore` carries no key enumeration.
- **`Cas.layerSqlRootStore()`** — the naming plane over the SAME
  client: `cas_roots(address TEXT PRIMARY KEY)`, one row per published
  root. This is what SQL adds over the key-value seam beside it, and
  the only thing it adds: enumeration. `publish` is
  `INSERT … ON CONFLICT DO NOTHING` (the set only grows, and
  re-publication is the identity); `list` is `SELECT`.
- **`Cas.layerSqlWordLog()`** — the receipts plane over that same
  client: `cas_word(seq INTEGER PRIMARY KEY, address, tag, size, at)`,
  one row per admission. `append` is one statement — `INSERT … SELECT
  COALESCE(MAX(seq), -1) + 1` — so the mark is assigned under the same
  write lock that lands the row, which is what keeps marks dense with
  no counter held anywhere.
- **`Cas.layerStore`** — the same store law as every other
  composition. Admission at put, re-verification at load, unchanged.
  It reads the word log as an OPTIONAL service, which is why the log
  is provided UNDER it rather than beside it.

Three tables, one file. That is deliberate: the file is the unit
Litestream replicates, so the bytes, the names that name them, and the
history of both are backed up together or not at all. The carve-out is
the same as the file layout's `word.jsonl` — a restore restores THIS
device's word, and a device-sync deployment must exclude `cas_word` or
move it to a local session database.

**WAL is asserted, not configured.** The Bun SQLite client opens the
database in WAL mode by default, which is what Litestream requires.
Nothing in this repo sets that pragma; `test/KvsSqlite.test.ts` reads
`PRAGMA journal_mode` back and asserts `wal`, so a driver default that
changed would turn a gate red instead of silently breaking backups.

**The `ON CONFLICT` clause is the SQLite and PostgreSQL spelling.**
MySQL and SQL Server want their own; the adapter does not pretend to
serve them, and a dialect that refuses the clause fails at its first
publish rather than quietly dropping a root.

**Publication stays fail-closed above the seam.** The Lean side's
`publish_mem` says a published root must be resident; the CLI's
`publish` verb loads the address through the full read law before
calling `RootStore.publish`. The adapter is as dumb as its file
sibling — it grows a set of strings and judges nothing — because a
backend that judged admission would be a second place the store's
invariants could weaken.

## Backup: a Litestream replica of `cas.db`

```sh
litestream replicate -once $STORE/cas.db "file://$BACKUP/replica"
litestream restore -o $STORE/restored.db -integrity-check full "file://$BACKUP/replica"
```

A `file://` replica on another disk is the default backup for a
db-backed store; the same command takes an object-store URL when there
is one. Litestream replicates SQLite pages and knows nothing about
content addressing, so the claim that matters is whether a restored
database still answers every address the model computed.
`scripts/litestream-check.ts` is that check, and it covers both tables:
`seed` replays every Lean conformance vector and publishes each
vector's root, `verify` re-runs the full read law over a DIFFERENT
database file and asserts the restored registry lists exactly what was
published.

Evidence, and only this: run on a Mac against litestream 0.5.16,
`replicate -once` to a `file://` replica and `restore` with
`-integrity-check full` — 29 addresses re-verified and 7/7 roots listed
from the restored database. It is an opt-in script, not part of
`bun run test`, because it needs an external binary.

## Store-to-store transfer is estate-native, not file-level

Moving content between stores does not mean moving files. `Graph`
walks the closure of a root through the read seam and `Store.put`
admits it into the destination — children-first, address-checked at
every step, refusing rather than admitting anything the destination
cannot verify. It works between any two backends in either direction:
file to database, database to a remote over `cas-http/0`, either to
memory. Content addressing makes it idempotent and resumable for free
— re-transferring content already resident is the identity.

That is the transfer story for both layouts, and it is the only one
that carries the store's laws with it.

## Git sync: right for the file layout, wrong for the database

For the FILE layout, git is a legitimate transport. Objects are
immutable files at content-derived paths, so history only ever grows,
merges cannot conflict on a path whose name is its content's digest,
and a published root is an empty file. Push the store root and anyone
can read it with `Cas.layerPathReader` over the raw endpoint, audited
by `Graph.verify`, with no server at all.

For the DATABASE layout it is wrong, and not by a little:

- `cas.db` is a live WAL database. A copy taken while a writer is
  running — which is what `git add` does — can catch a torn page set,
  and the `-wal` and `-shm` sidecars that would explain it are not part
  of the commit.
- Every commit stores a fresh binary blob of the whole file. The
  repository grows by the size of the database per commit, and none of
  it diffs.
- Nothing above the file is content-addressed to git, so a corrupted
  commit is not detectable as anything but a corrupt database.

Back the database up by replicating it. If a committable, diffable,
statically servable store is what is wanted, that is the file layout,
and `cas init` (with no `--backend`) is still what creates it.

## Choosing

Use the **file** layout when the store should be inspectable,
committable, or served off a static host, and when a directory of
small files is a fine shape for the content.

Use the **sqlite** layout when the store should be one file with a
continuous replica behind it, or when many small objects make a
directory tree awkward. It is a single-writer database and the CLI is
a single process; concurrent writers across processes are not a claim
this repo makes for either layout.

Both layouts serve the same seams, so nothing above the byte plane —
no law, no verb, no server — knows which one it is standing on.
