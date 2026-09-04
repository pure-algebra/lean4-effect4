# vendor/wrangler-3.114.16

Host evidence for `Effect4/Surface/Deploy/Emit.lean`. **Not a model.**

| | |
| --- | --- |
| package | `wrangler` |
| version | `3.114.16` |
| file | `config-schema.json` |
| SHA-256 | `3f7bca5c73d039698e6ffc6f7fa6849c9eef453edf129172e640186b495ea7bb` |
| bytes | 132351 |
| lines | 3341 |
| copied | 2026-09-04 |
| copied from | `/Users/pooks/Dev/mepuka-website/node_modules/wrangler/config-schema.json` |
| licence | `MIT OR Apache-2.0`, as declared by the package; see `LICENSE` |

## What this is, and what it is not

`config-schema.json` is the JSON Schema wrangler publishes for its own
configuration file. It is copied here **byte for byte** so that the estate can
cite a fixed spelling of the wrangler configuration keys and their value shapes
without reading a file outside the repository, and so that a later harness can
validate an emitted `wrangler.generated.json` against the very schema the
pinned wrangler would validate it against.

It is **evidence, not a model**: nothing in `Effect4/` decodes this file, no
Lean theorem is stated about it, and no well-formedness claim rests on it. The
Lean side models a small fragment of the configuration by hand
(`Effect4/Surface/Deploy.lean`'s `Deployment`), and `Deploy/Emit.lean` cites
this file by line for every key it writes. If the two disagree, this file is
right and the Lean side is wrong.

The digest above is the pin. A wrangler upgrade is a new directory
(`vendor/wrangler-<version>/`) with a new digest and a re-read of every cited
line, never an edit of this one.

## The lines that are cited

Read against this copy (`definitions.RawConfig` at line 1256,
`definitions.RawEnvironment` at line 2326):

| key | line in `config-schema.json` | shape |
| --- | --- | --- |
| `RawConfig` | 1256 | `additionalProperties: false`, `type: object` |
| `$schema` | 1259 | string |
| `assets` | 1312 | `$ref: #/definitions/Assets` (definition at line 5) |
| `compatibility_date` | 1376 | string, "a date in the form yyyy-mm-dd" |
| `compatibility_flags` | 1380 | array of string |
| `d1_databases` | 1406 | array of `{ binding*, database_name, database_id, ... }` |
| `durable_objects` | 1494 | `{ bindings: DurableObjectBindings }` (definition at line 252: `{ name*, class_name*, script_name, environment }`) |
| `kv_namespaces` | 1616 | array of `{ binding*, id, preview_id }` |
| `main` | 1729 | string, "the entrypoint/path to the JavaScript file" |
| `name` | 1772 | string, "alphanumeric + dashes only" |
| `pages_build_output_dir` | 1788 | string; "the presence of this field ... indicates a Pages project" |
| `queues` | 1844 | `{ producers: [{ binding*, queue*, delivery_delay }] (1904), consumers: [...] (1852) }` |
| `r2_buckets` | 1933 | array of `{ binding*, bucket_name, jurisdiction, preview_bucket_name }` |
| `routes` | 1967 | array of `Route` (definition at line 3199: a string or one of three objects) |
| `services` | 2014 | array of `{ binding*, service*, entrypoint }` |
| `vars` | 2200 | object whose values are a string or `Json` |

A `*` marks a key the schema lists in the entry's `required` array.
`RawEnvironment` (line 2326) repeats every one of those except
`pages_build_output_dir`, which is a top-level, Pages-only key.
