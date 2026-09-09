import Effect4.Program.Native

/-!
# Packages.KeyValueStoreMemory — the second canonical package table (host rows slice, step 5)

The rows a program may perform against rc.112's in-memory key-value store
(`vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts`: the interface at
`:38-95`, the key at `:208-211`, `layerMemory` at `:331-352`), as a `RowTable` value of
external rows answered by the host.

What is the package's and what is modelled (the scouts of 2026-09-09):

* `get`, `set`, `remove` and `has` are the store's own methods, spelled on the store handle.
  `get` answers `string | undefined` at rc.112; the row types it `.option string` (DB-15) and
  the host adapts the answer with `Option.fromNullable`. `set` takes `string | Uint8Array`;
  the `Uint8Array` half is outside the value alphabet and refused at ingest. `set`, `remove`
  and `clear` answer the underlying `Map`'s results (`{}`, `true`), which the host adapts to
  `void`.
* `size` and `clear` are *properties* of the store, not methods; a `method` row would print a
  call that throws. They are not rows of this table; a receiver-property shape is filed as a
  follow-on (decisions memo A4).
* `make` is the harness's plumbing: the store `layerMemory` builds, spelled as a prelude call
  answering the handle, so a program can obtain the store without a layer.
* Errors cross as `prod string string`: `KeyValueStoreError` is a `Data.TaggedError` with
  `message`, `method` and `key` (`:183-195`).
-/

namespace Effect4.Program.Packages

/-- The rc.112 key string of the store service (`unstable/persistence/KeyValueStore.ts:208`). -/
def kvKey : String := "effect/persistence/KeyValueStore"

/-- The error column: the `_tag` and the message (DB-15). -/
def kvError : Ty := .prod .string .string

def keyValueStoreMemory : RowTable :=
  [ { name := "kvMake", spelling := "Kv.make", shape := .call, kind := .async,
      registration := .external, request := .unit, answer := NativeOp.kvTy, error := .never,
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts:331-352" }
  , { name := "kvGet", spelling := "get", shape := .method, kind := .async,
      registration := .external, request := .prod NativeOp.kvTy .string, answer := .option .string,
      error := kvError,
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts:40-43" }
  , { name := "kvSet", spelling := "set", shape := .method, kind := .async,
      registration := .external, request := .prod NativeOp.kvTy (.prod .string .string),
      answer := .unit, error := kvError,
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts:50-53" }
  , { name := "kvRemove", spelling := "remove", shape := .method, kind := .async,
      registration := .external, request := .prod NativeOp.kvTy .string, answer := .unit,
      error := kvError,
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts:55-58" }
  , { name := "kvHas", spelling := "has", shape := .method, kind := .async,
      registration := .external, request := .prod NativeOp.kvTy .string, answer := .bool,
      error := kvError,
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts:86-89" } ]

end Effect4.Program.Packages
