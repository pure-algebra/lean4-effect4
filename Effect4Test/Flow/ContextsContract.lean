/-
Contract packet: the trace lane (`docs/TRACE-DAG.md`), the `Contexts` family.
Lowering lane L3.

Frozen: the nineteen operation rows of rc.112's `Context` surface and of the
four `Reference`s the runtime reads off a context, the key-table projection the
Lean face runs under, and the traced log of every program the corpus carries.

There is no committed golden under `generated/traces/context/` yet: this family
is new, and generating its goldens belongs to the harness lane. The rows below
are what those goldens must carry.

The family is the first Effect4 carrier for a context at all —
`Effect4/Context/Environment.lean` is an eight-line stub — and it is keyed by
`Effect4.ServiceKey` (`Effect4/Context/Key.lean`), whose identity is the
*pair* of a service name and a type code. `keyConflict` is `ServiceKey.Conflict`
on the wire, and `Key.lean`'s own refusal — "Effect's `Context.Tag` identity is
the tag string alone and cannot express the colliding pair, so no compatibility
with it is claimed" — is exactly what that row does not claim.

Nothing here is a statement about the host: the same rows are compared with
rc.112 by `harness/trace/context-tail.ts`, and that comparison is evidence,
never a theorem. Doc comments cannot precede `#guard`, so the receipts carry
line comments.
-/

import Effect4.Context.ContextFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.ContextsContract

open Effect4.ContextFamily

#check @Effect4.ContextFamily.Contexts
#check (@Effect4.ContextFamily.Contexts.rows : Effect4.Target.EffectV4.ServiceRow)
#check @Effect4.ContextFamily.contextsLive
#check @Effect4.ContextFamily.contextGoldenLog

/-! ## The rows

Fourteen `Context` operations, one key minter, one reference minter, and the
four reference reads. `get` is the only aborting row: `Context.getUnsafe`
throws when the key is missing (`Context.ts:1475-1484`, `:1590`), and the
family spells that as its declared error channel rather than inventing a
value. -/

#guard Contexts.rows.name = "Contexts"

#guard Contexts.rows.ops.map (·.name) =
  [ "empty", "key", "referenceKey", "make", "add", "get", "getOption", "merge", "mergeAll"
  , "pick", "omit", "provideContext", "updateContext", "withContext", "keyConflict"
  , "maxOpsBeforeYield", "preventSchedulerYield", "currentMemoMap", "currentScope" ]

#guard Contexts.rows.ops.map (·.params.length) =
  [0, 2, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 2, 0, 2, 0, 0, 0, 0]

#guard Contexts.rows.ops.map (fun row => (row.name, row.tsAnswer)) =
  [ ("empty", "Context.Context<never>"), ("key", "Context.Key<never, number>")
  , ("referenceKey", "Context.Key<never, number>"), ("make", "Context.Context<never>")
  , ("add", "Context.Context<never>"), ("get", "number")
  , ("getOption", "Option.Option<number>"), ("merge", "Context.Context<never>")
  , ("mergeAll", "Context.Context<never>")
  , ("pick", "Context.Context<never>"), ("omit", "Context.Context<never>")
  , ("provideContext", "Context.Context<never>"), ("updateContext", "Context.Context<never>")
  , ("withContext", "Context.Context<never>"), ("keyConflict", "boolean")
  , ("maxOpsBeforeYield", "number"), ("preventSchedulerYield", "boolean")
  , ("currentMemoMap", "Option.Option<Layer.MemoMap>")
  , ("currentScope", "Option.Option<Scope.Closeable>") ]

#guard Contexts.rows.ops.map (fun row => (row.name, row.tsParams.map Prod.snd)) =
  [ ("empty", []), ("key", ["number", "number"]), ("referenceKey", ["number"])
  , ("make", ["Context.Key<never, number>", "number"])
  , ("add", ["Context.Context<never>", "Context.Key<never, number>", "number"])
  , ("get", ["Context.Context<never>", "Context.Key<never, number>"])
  , ("getOption", ["Context.Context<never>", "Context.Key<never, number>"])
  , ("merge", ["Context.Context<never>", "Context.Context<never>"])
  , ("mergeAll", ["ReadonlyArray<Context.Context<never>>"])
  , ("pick", ["Context.Context<never>", "Context.Key<never, number>"])
  , ("omit", ["Context.Context<never>", "Context.Key<never, number>"])
  , ("provideContext", ["Context.Context<never>"])
  , ("updateContext", ["Context.Key<never, number>", "number"])
  , ("withContext", []),
    ("keyConflict", ["Context.Key<never, number>", "Context.Key<never, number>"])
  , ("maxOpsBeforeYield", []), ("preventSchedulerYield", []), ("currentMemoMap", [])
  , ("currentScope", []) ]

-- `get` is the one aborting row.
#guard Contexts.rows.ops.map (·.error) =
  [none, none, none, none, none, some ("Nat", "number"), none, none, none, none, none, none,
   none, none, none, none, none, none, none]

#guard (Contexts.rows.ops.filter (fun row => row.error.isSome)).map (·.name) = ["get"]

/-! ## The handler is a projection of the key table

The clauses of `Effect4/Context/ContextFamily.lean`, cited here as the shapes
the rows below rest on; their axiom receipts are in
`Effect4Test/Flow/ContextsAxiomReport.lean`. -/

#check @Effect4.ContextFamily.declareKey_is_by_the_pair
#check @Effect4.ContextFamily.minted_keys_conflict
#check @Effect4.ContextFamily.bind_replaces_in_place
#check @Effect4.ContextFamily.lookup_bind_self
#check @Effect4.ContextFamily.lookup_other
#check @Effect4.ContextFamily.maxOps_default
#check @Effect4.ContextFamily.preventYield_default
#check @Effect4.ContextFamily.objectReferences_have_no_default

-- A key's identity is the pair, so two `key` requests with the same name and
-- the same type code answer the same handle …
#guard decide (
  ((contextsLive Contexts.Name.key (0, 0) {}).1.toOption.map Effect4.Meta.Handle.index
    = Option.some 0))
#guard decide (
  ((contextsLive Contexts.Name.key (0, 0)
      (contextsLive Contexts.Name.key (0, 0) {}).2).1.toOption.map Effect4.Meta.Handle.index
    = Option.some 0))

-- … and two with the same name and different codes do not.
#guard decide (
  ((contextsLive Contexts.Name.key (0, 1)
      (contextsLive Contexts.Name.key (0, 0) {}).2).1.toOption.map Effect4.Meta.Handle.index
    = Option.some 1))

-- The four references reserve the first four service names, so a key a program
-- mints can never collide with one: rc.112's own tags are strings like
-- `effect/Scheduler/MaxOpsBeforeYield` and the offset is this alphabet's
-- stand-in for that.
#guard referenceCount == 4
#guard decide ([0, 1, 2, 3].map (fun i => (Reference.ofIndex i).serviceKey.name.value)
  = [0, 1, 2, 3])
#guard decide ((mintedKey 0 0).name.value = 4)

-- `add` binds in place, so a later `add` of the same key wins and the binding
-- keeps its position.
#guard decide (
  Effect4.ContextFamily.ContextStore.bind
      (Effect4.ContextFamily.ContextStore.bind [] (mintedKey 0 0) 7) (mintedKey 0 0) 9
    = [(mintedKey 0 0, 9)])

-- `merge` answers the *other side itself* when one side has no bindings
-- (`Context.ts:1817-1818`), and copies only when both are non-empty;
-- `mergeAll` builds one fresh map whatever its arguments are (`:1864-1870`).
-- The store below holds the empty context (handle 0), a key (handle 1) and a
-- one-binding context (handle 2); a fresh context would be handle 3.
def mergeIdentityStore : ContextStore :=
  (contextsLive Contexts.Name.make (⟨1⟩, 7)
    (contextsLive Contexts.Name.key (0, 0) (contextsLive Contexts.Name.empty () {}).2).2).2

#guard decide (
  (contextsLive Contexts.Name.merge (⟨0⟩, ⟨2⟩) mergeIdentityStore).1.toOption.map
      Effect4.Meta.Handle.index
    = Option.some 2)
#guard decide (
  (contextsLive Contexts.Name.merge (⟨2⟩, ⟨0⟩) mergeIdentityStore).1.toOption.map
      Effect4.Meta.Handle.index
    = Option.some 2)
#guard decide (
  (contextsLive Contexts.Name.merge (⟨2⟩, ⟨2⟩) mergeIdentityStore).1.toOption.map
      Effect4.Meta.Handle.index
    = Option.some 3)
#guard decide (
  (contextsLive Contexts.Name.mergeAll [⟨0⟩, ⟨2⟩] mergeIdentityStore).1.toOption.map
      Effect4.Meta.Handle.index
    = Option.some 3)
#guard decide (
  (contextsLive Contexts.Name.mergeAll [] mergeIdentityStore).1.toOption.map
      Effect4.Meta.Handle.index
    = Option.some 3)

/-! ## The corpus, and the rows each program renders

The wire rows are written inline in each receipt: a `def` rendering rows would
reach `Classical.choice` through the renderer and the axiom gate scans test
declarations too, while a `#guard` is a command, not a declaration. An unknown
name answers a row that no golden can match. -/

#guard contextPrograms.length == 9

#guard contextPrograms.map (·.name) ==
  [ "addGet", "getMissing", "keyConflict", "mergePickOmit", "mergeAllLastWins"
  , "provideThenRead", "referenceDefaults", "updateReference", "memoMapAbsent" ]

-- addGet: a key, a binding, and the read that finds it. Keys and contexts
-- share one handle counter, as `handleIndex` does on the host.
#guard ((contextPrograms.find? (·.name == "addGet")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tempty\t[]"
  , "answer\tempty\t0"
  , "op\tkey\t[0, 0]"
  , "answer\tkey\t1"
  , "op\tadd\t[0, [1, 7]]"
  , "answer\tadd\t2"
  , "op\tget\t[2, 1]"
  , "answer\tget\t7"
  , "done\t{\"success\":7}" ]

-- getMissing: `Context.getUnsafe` throws (`Context.ts:1590`), and the family
-- spells the throw as its declared error channel carrying the key that was not
-- there. On the host it reaches the trace as a defect, which is the one place
-- the two faces disagree and is recorded in the report.
#guard ((contextPrograms.find? (·.name == "getMissing")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tempty\t[]"
  , "answer\tempty\t0"
  , "op\tkey\t[0, 0]"
  , "answer\tkey\t1"
  , "op\tget\t[0, 1]"
  , "failed\tget\t1"
  , "done\t{\"failure\":1}" ]

-- keyConflict: the same service name at two type codes is two keys, they are
-- in conflict, and a binding under one is invisible under the other. This is
-- `Effect4.ServiceKey.Conflict` on the wire.
#guard ((contextPrograms.find? (·.name == "keyConflict")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tkey\t[0, 0]"
  , "answer\tkey\t0"
  , "op\tkey\t[0, 1]"
  , "answer\tkey\t1"
  , "op\tkeyConflict\t[0, 1]"
  , "answer\tkeyConflict\ttrue"
  , "op\tmake\t[0, 7]"
  , "answer\tmake\t2"
  , "op\tgetOption\t[2, 1]"
  , "answer\tgetOption\t{\"none\":true}"
  , "done\t{\"success\":{\"none\":true}}" ]

-- mergePickOmit: `merge` copies the right map over the left, so the shared key
-- answers the right's value; `pick` and `omit` are the two halves of a key's
-- binding.
#guard ((contextPrograms.find? (·.name == "mergePickOmit")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tkey\t[0, 0]"
  , "answer\tkey\t0"
  , "op\tmake\t[0, 7]"
  , "answer\tmake\t1"
  , "op\tmake\t[0, 9]"
  , "answer\tmake\t2"
  , "op\tmerge\t[1, 2]"
  , "answer\tmerge\t3"
  , "op\tpick\t[3, 0]"
  , "answer\tpick\t4"
  , "op\tomit\t[4, 0]"
  , "answer\tomit\t5"
  , "op\tgetOption\t[5, 0]"
  , "answer\tgetOption\t{\"none\":true}"
  , "done\t{\"success\":{\"none\":true}}" ]

-- mergeAllLastWins: `mergeAll` sets every argument's entries into one fresh
-- map in order, so the last context wins the shared key. The list argument is
-- the `twoContexts` atom's answer, spelled on the wire as the cons cells it is.
#guard ((contextPrograms.find? (·.name == "mergeAllLastWins")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tkey\t[0, 0]"
  , "answer\tkey\t0"
  , "op\tmake\t[0, 7]"
  , "answer\tmake\t1"
  , "op\tmake\t[0, 9]"
  , "answer\tmake\t2"
  , "op\tmergeAll\t[1, [2, []]]"
  , "answer\tmergeAll\t3"
  , "op\tgetOption\t[3, 0]"
  , "answer\tgetOption\t{\"some\":9}"
  , "done\t{\"success\":{\"some\":9}}" ]

-- provideThenRead: `provideContext` answers the context it *replaced* — an
-- empty ambient one, created on first use — and `withContext` answers the one
-- it installed. rc.112 restores the previous context when the provided effect
-- finishes; a family whose operations are points cannot see the restore, only
-- the two contexts. counterexample: owed, see the report.
#guard ((contextPrograms.find? (·.name == "provideThenRead")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tkey\t[0, 0]"
  , "answer\tkey\t0"
  , "op\tmake\t[0, 7]"
  , "answer\tmake\t1"
  , "op\tprovideContext\t1"
  , "answer\tprovideContext\t2"
  , "op\twithContext\t[]"
  , "answer\twithContext\t1"
  , "op\tgetOption\t[1, 0]"
  , "answer\tgetOption\t{\"some\":7}"
  , "done\t{\"success\":{\"some\":7}}" ]

-- referenceDefaults: rc.112's `Reference` defaults are *functions* on the host
-- (`defaultValue: () => 2048`, `Scheduler.ts:271`), which DB-02 keeps out of
-- canonical content, so they are values here: `2048` and `false`, read off the
-- pinned source and written down.
#guard ((contextPrograms.find? (·.name == "referenceDefaults")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\tpreventSchedulerYield\t[]"
  , "answer\tpreventSchedulerYield\tfalse"
  , "op\tmaxOpsBeforeYield\t[]"
  , "answer\tmaxOpsBeforeYield\t2048"
  , "done\t{\"success\":2048}" ]

-- updateReference: binding a reference in the fiber's context makes the read
-- after it answer the bound value instead of the default.
#guard ((contextPrograms.find? (·.name == "updateReference")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\treferenceKey\t0"
  , "answer\treferenceKey\t0"
  , "op\tupdateContext\t[0, 3]"
  , "answer\tupdateContext\t1"
  , "op\tmaxOpsBeforeYield\t[]"
  , "answer\tmaxOpsBeforeYield\t3"
  , "done\t{\"success\":3}" ]

-- memoMapAbsent: a reference whose default is an *object* — `CurrentMemoMap`,
-- `Scope` — has no value to write down, so the row answers `Option` and is
-- `none` until a build or a `scoped` binds it, which is
-- `Context.getOrUndefined`'s own answer (`Layer.ts:586`).
#guard ((contextPrograms.find? (·.name == "memoMapAbsent")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown context program"] ==
  [ "op\twithContext\t[]"
  , "answer\twithContext\t0"
  , "op\tcurrentMemoMap\t[]"
  , "answer\tcurrentMemoMap\t{\"none\":true}"
  , "done\t{\"success\":{\"none\":true}}" ]

/-! ## What the family fixes about a handle -/

-- A key and a context each cross the wire as a bare index and as nothing else;
-- what a key *is* is the `ServiceKey` the store binds by, and never the index.
#guard Contexts.encodeAnswer .key ⟨2⟩ = Effects.Trace.Val.nat 2
#guard Contexts.encodeAnswer .empty ⟨0⟩ = Effects.Trace.Val.nat 0
#guard Contexts.encodeParam .add (⟨0⟩, ⟨1⟩, 7) =
  Effects.Trace.Val.pair (.nat 0) (.pair (.nat 1) (.nat 7))

-- Exactly one program of the corpus ends in a failure, and it is `get` on a
-- key the context does not bind.
#guard (contextPrograms.filter (fun entry => entry.log.any (fun event =>
    match event with | .done (.failure _) => true | _ => false))).map (·.name)
  == ["getMissing"]

-- Every log agrees with itself under every registered mask; agreement is a
-- projection equality and never more.
#guard contextPrograms.all (fun entry =>
  Effect4.Trace.maskTable.all (fun mask => Effect4.Trace.agree mask.2 entry.log entry.log))

end Effect4Test.Flow.ContextsContract
