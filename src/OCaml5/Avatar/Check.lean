import OCaml5.Avatar

/-!
# OCaml5.Avatar.Check

**What it is.** The battery of `OCaml5.Avatar` at its interface: the counts, orders and names
pinned on the W1/F2 descriptions, and the **projection guard** — every fact a hand description
states about the *Lean* side (name, field names and types in order, constructor names and
argument names and types) against the twin `Tools/Describe.lean` read off the environment. A
`DIFF` is either an abbreviation in the hand copy or drift of the Machine since the port.

**Depends on.** `OCaml5.Avatar`.

**Properties.**
* **Every guarded description is a row**; a missing twin is a `DIFF`, not a skip — *by construction*.
* **Projection counts are pinned by the guards below**; the report names every disagreement.
  The open rows are the overlay vocabulary recorded in `ocaml/README.md`.
-/

namespace OCaml5.Avatar.Check

open OCaml5.Ml

/-! ## Counts, orders and names

Pinned the way `Fibers`'s are: constructor counts against the Lean file, field order against the
Lean field order, and the mangling round-trip on every field name. -/

-- The keyword escape for type names, and the reason it exists.
#guard typeName "Val" == "val_"
#guard typeName "RunFiber" == "run_fiber"
#guard typeName "SyncOp" == "sync_op"


-- `Stores.lean`'s constructor counts.
#guard Stores.err.ctors.length == 2
#guard Stores.defect.ctors.length == 5
#guard Stores.fnName.ctors.length == 5
#guard Stores.finName.ctors.length == 6
#guard Stores.completion.ctors.length == 2
#guard Stores.syncOp.ctors.length == 23
#guard Stores.raceName.ctors.length == 6
#guard Stores.progName.ctors.length == 24
#guard Stores.name.ctors.length == 21
#guard Stores.actionName.ctors.length == 19
#guard Stores.thunk.ctors.length == 4
#guard Stores.finalizerStrategy.ctors.length == 2
#guard Stores.scopeState.ctors.length == 5

-- `ActionName` is arm for arm with `WithFiberAction` — the same names — but *not* in the
-- same order: `setInterruptible` is `WithFiberAction`'s twelfth and `ActionName`'s sixteenth.
-- A0 §3 lists no such row, so it is seat W1's, and `deep_stores.ml` follows the `Stores.lean`
-- order because that is the file it is the port of.
-- Seat F2: `WithFiberAction` gained `dropObservers` and `cancelRace` in `2f77f7d`; the drift
-- re-diff of 2026-09-04 brought `Ml.Avatar.withFiberAction` up to them, and to
-- `awaitAllFailFast`, which `Stores.lean`'s `ActionName` does not name (only `Layer.lean:348`'s
-- does): every `ActionName` is a `WithFiberAction`, and the one `WithFiberAction` that is no
-- `ActionName` is that arm.
#guard (Stores.actionName.ctors.map (·.leanName)).all
  (fun n => (Fibers.withFiberAction.ctors.map (·.leanName)).contains n)
#guard (Fibers.withFiberAction.ctors.map (·.leanName)).all
  (fun n => (Stores.actionName.ctors.map (·.leanName)).contains n || n == "awaitAllFailFast")
#guard Stores.actionName.ctors.map (·.leanName) !=
  Fibers.withFiberAction.ctors.map (·.leanName)

-- Field order, in the Lean order, mangled.
#guard Stores.stores.fields.map (·.ocaml) == ["refs", "deferreds", "scopes", "next_name"]
#guard Stores.deferredCell.fields.map (·.ocaml) == ["completion", "waiters"]
#guard Stores.deferredStore.fields.map (·.ocaml) == ["cells", "due"]
#guard Stores.scopeEntry.fields.map (·.ocaml) == ["key", "scope"]
#guard Stores.ctx.fields.map (·.ocaml) ==
  ["ambient_scope", "max_ops_before_yield", "prevent_yield"]

-- The mangling is injective on every name this section renders.
#guard (Stores.structs.flatMap (fun d => d.fields.map (·.leanName))).all
  (fun n => unmangleField (mangleField n) == n)

-- No description erases an argument: every `Stores.lean` constructor is arity for arity.
#guard Stores.inductives.all (fun d => d.erasures.isEmpty)
#guard Stores.inductives.all (fun d => d.arities.all (fun a => a.2.1 == a.2.2))

-- The names `deep_stores.ml` uses.
#guard Stores.syncOp.ctors.map (CtorDesc.ocaml "S") ==
  ["SrefMake", "SrefGet", "SrefSet", "SrefGetAndSet", "SrefSetAndGet", "SrefUpdate",
   "SrefGetAndUpdate", "SrefUpdateAndGet", "SrefUpdateSome", "SrefGetAndUpdateSome",
   "SrefUpdateSomeAndGet", "SrefModify", "SrefModifySome", "SdeferredMake", "SdeferredIsDone",
   "SdeferredPoll", "SdeferredCompleteWith", "SdeferredInterruptWith", "SdeferredAwaitCleanup",
   "SscopeMake", "SscopeAdd", "SscopeRemove", "SscopeIsClosed"]
#guard Stores.scopeState.ctors.map (CtorDesc.ocaml "Ss") ==
  ["Ssempty", "SsopenEmpty", "SsopenInline", "SsopenMap", "Ssclosed"]

-- `Layer.lean`'s constructor counts (seat F2, at `2f77f7d`).
#guard Layer.combineMode.ctors.length == 2
#guard Layer.construction.ctors.length == 4
#guard Layer.layerDesc.ctors.length == 6
#guard Layer.finName.ctors.length == 11
#guard Layer.syncOp.ctors.length == 10
#guard Layer.progName.ctors.length == 27
#guard Layer.name.ctors.length == 49
#guard Layer.actionName.ctors.length == 13
#guard Layer.thunk.ctors.length == 3
#guard ForkFlow.fiberOp.ctors.length == 12
#guard ForkFlow.forkRefusal.ctors.length == 6
#guard ForkFlow.forkRequest.fields.map (·.ocaml) == ["root", "args", "daemon", "region"]
#guard Context.contextUpdate.ctors.length == 3
#guard Context.defect.ctors.length == 5
#guard Context.val.ctors.length == 15
#guard Context.err.ctors.length == 2
#guard Context.context.erasures.map (·.1) == ["keysNodup"]
#guard Context.structs.all (fun d => d.holes.isEmpty)
#guard Layer.scopeState.ctors.length == 5
#guard Layer.st.fields.map (·.ocaml) == ["memo", "scopes", "deferreds", "next_name"]
#guard Layer.memoEntry.fields.map (·.ocaml) == ["observers", "effect", "layer_scope", "deferred", "finalizer"]
#guard Layer.inductives.all (fun d => d.erasures.isEmpty)
#guard (Layer.structs.flatMap (fun d => d.fields.map (·.leanName))).all
  (fun n => unmangleField (mangleField n) == n)
-- Layer's `ActionName` is `WithFiberAction` minus the fork-in/run-in/race family plus nothing:
-- every name is a `WithFiberAction` name (`dropObservers` since `2f77f7d`, `awaitAllFailFast`
-- described since the drift re-diff of 2026-09-04).
#guard (Layer.actionName.ctors.map (·.leanName)).all
  (fun n => (Fibers.withFiberAction.ctors.map (·.leanName)).contains n)


/-! ## The projection guard -/

/-- What the renderer consumes of a Lean type under a substitution: a substituted head loses
its arguments (the `Subst` is keyed on the head, so the hand copies abbreviate them), every
other head keeps its arguments, normalised the same way. `leanParams` is not compared: the
avatar's profile fixes the parameters by substitution, so an empty list there is a decision. -/
partial def norm (keys : List String) : LTy → LTy
  | .app h args => if keys.contains h then .app h [] else .app h (args.map (norm keys))

private def projS (d : StructDesc) : String :=
  let keys := d.subst.map (·.1)
  (repr (d.leanName,
    (d.fields.filter fun f => match f.kind with | .substitute => false | _ => true).map
      fun f => (f.leanName, norm keys f.leanTy))).pretty 100000

private def projI (d : InductiveDesc) : String :=
  let keys := d.subst.map (·.1)
  (repr (d.leanName,
    d.ctors.map fun c => (c.leanName, c.args.map fun a => (a.leanName, norm keys a.leanTy)))).pretty 100000

/-- The Lean-side projection of a description. -/
def proj : TypeDesc → String
  | .struct d => projS d
  | .induct d => projI d

/-- The derived twin normalised under the *hand* description's substitution. -/
def projUnder (hand derived : TypeDesc) : String :=
  match hand, derived with
  | .struct h, .struct d => projS { d with subst := h.subst }
  | .induct h, .induct d => projI { d with subst := h.subst }
  | _, d => proj d

private def lowerFirst (s : String) : String :=
  match s.toList with
  | c :: rest => String.ofList (c.toLower :: rest)
  | [] => s

/-- One row per guarded description: the tag the report prints, the hand projection, the derived
one (`<no twin>` when `Describe` produced none). -/
def Part.rows (p : Part) : List (String × String × String) :=
  p.twins.map fun (h, d?) =>
    (p.name.capitalize ++ "." ++ lowerFirst h.leanName, proj h,
     match d? with | some d => projUnder h d | none => "<no twin>")

def report (tag : String) (hand derived : String) : IO Unit :=
  if hand == derived then IO.println s!"OK   {tag}"
  else IO.println s!"DIFF {tag}\n  hand    {hand}\n  derived {derived}"

#guard (parts.map (·.name)).eraseDups.length == parts.length

#guard (parts.flatMap Part.rows).length == 58
#guard ((parts.flatMap Part.rows).filter (fun r => r.2.1 == r.2.2)).length == 48

#eval do
  let rows := parts.flatMap Part.rows
  for (tag, hand, derived) in rows do report tag hand derived
  let n := (rows.filter fun (r : String × String × String) => r.2.1 == r.2.2).length
  IO.println s!"== {n} / {rows.length} agree"

end OCaml5.Avatar.Check
