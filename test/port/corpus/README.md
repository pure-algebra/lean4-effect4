# Corpus source inventory

`SOURCES.tsv` is the authored inventory of the external Git checkouts used as
wild-type examples during porting. Each row records only source identity and
provenance. The shared role and disposition deliberately make no claim about
which Effect construct, law, or API a checkout exercises.

The retained fields are:

- `checkout`: one portable, single-component directory name;
- `head_commit`: the exact checked-out commit;
- `root_tree`: the commit's exact root tree;
- `source_url`: the observed `origin` URL, or `-` when none is discoverable;
- `role`: the checkout's source-evidence role; and
- `disposition`: `inventory-only-unclassified` until a separate, reviewed
  classification process assigns narrower evidence.

Run the finite inventory check by supplying the directory that contains the
listed checkouts:

```text
scripts/check-corpus-sources.sh --corpus-root PATH
```

For every pinned commit the checker hashes the canonical byte stream produced
by `git ls-tree -r -z --full-tree COMMIT`. Its per-checkout file count is the
number of recursive tree entries. These compact receipts cover the committed
Git tree without retaining one manifest row per file. Untracked working-tree
files are outside that committed-tree receipt; changes to tracked files are
rejected.
