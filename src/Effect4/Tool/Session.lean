import Effect4.Tool.ToolDerived
import Effect4.Store.Domain.Cas

/-!
# Tool.Session — a session's stored history (seams ST4)

A session persists as a chain of entries at kind `entry`, never as a derived state. The chain
starts at an `origin`, which records the protocol and codec versions and the engine that wrote
it. Each later entry holds its parent, its index in the transcript, one accepted action, and
`after`: the document's program after the action, by reference, `none` exactly when no document
is open. The index makes parent order checkable: an entry at index `n + 1` names one at `n`, and
the entry at `0` names the origin. Refused requests and
queries never enter a chain. `Tool/Exchange.lean` loads chains and appends to them.

The codec is written by hand, as `Annotation`'s is (`src/Effect4/Store/Domain/Traits.lean`): a
reference to the entry's own carrier needs the `Content SessionEntry` being defined. The action is
read through the Tool group's generated exact codec (`Tool/ToolDerived.lean`), and `guarded` makes
the whole reader exact (`SessionEntry.ofVal_exact`, `session-entry-exact`). An entry's parent is
its designated parent field, the one `Node.designatedParent` reads, so a journal root over a
chain moves only along it (`journal_ff`).

Placement: `exact-codecs`, stored carriers, R13. The codec establishes payload identity, not that
an action is accepted.
-/

set_option autoImplicit false

namespace Effect4.Tool

open Effect4 Effect4.Store

/-- The protocol version a chain's origin records; the only one this tool loads. -/
def protocolVersion : Nat := 1

/-- The action codec version a chain's origin records; the only one this tool loads. -/
def codecVersion : Nat := 1

/-- One stored entry of a session's chain. -/
inductive SessionEntry where
  /-- The chain's first entry: the protocol and codec versions, and the writing engine. -/
  | origin (protocol codec : Nat) (engine : Digest)
  /-- One accepted action after its parent, at its transcript index, with the document's program
  after it. -/
  | action (parent : Ref SessionEntry) (index : Nat) (a : Action)
      (after : Option (Ref Program.NativeEff))

namespace SessionEntry

/-- A sum of the two entries, over the action carrier's table. -/
def shapeDoc : ShapeDoc :=
  ⟨.sum "SessionEntry"
    [("origin", 0, [("protocol", .nat), ("codec", .nat), ("engine", .digest)]),
     ("action", 1, [("parent", .ref .entry), ("index", .nat), ("a", (shape Action).root),
       ("after", .option (.ref .program))])],
   (shape Action).defs⟩

/-- The `after` field: `none`, or a reference at kind `program`. -/
def afterToVal : Option (Ref Program.NativeEff) → Val
  | none => .none
  | some r => .some (.ref Kind.program.byte r.digest.bytes)

/-- Constructor `0` or `1`, the fields in declaration order. -/
def write : SessionEntry → Val
  | .origin protocol codec engine => .ctor 0 [.nat protocol, .nat codec, .bytes engine.bytes]
  | .action parent index a after =>
    .ctor 1 [.ref Kind.entry.byte parent.digest.bytes, .nat index, toVal a, afterToVal after]

/-- A reference frame at one kind. -/
def readRef (kind : Kind) : Val → Option Digest
  | .ref byte bytes => if byte = kind.byte then Digest.ofBytes? bytes else none
  | _ => none

/-- The reader of `after`. -/
def afterOfVal : Val → Option (Option (Ref Program.NativeEff))
  | .none => some none
  | .some v => (readRef .program v).map fun d => some ⟨d⟩
  | _ => none

/-- The structural reader; `guarded` makes it exact. -/
def raw : Val → Option SessionEntry
  | .ctor 0 [.nat protocol, .nat codec, .bytes engine] =>
    (Digest.ofBytes? engine).map fun d => .origin protocol codec d
  | .ctor 1 [parent, .nat index, a, after] =>
    match readRef .entry parent, ofVal (α := Action) a, afterOfVal after with
    | some p, some act, some aft => some (.action ⟨p⟩ index act aft)
    | _, _, _ => none
  | _ => none

theorem readRef_ref (kind : Kind) (d : Digest) : readRef kind (.ref kind.byte d.bytes) = some d := by
  simp only [readRef, ↓reduceIte, Digest.ofBytes?_bytes]

theorem afterOfVal_afterToVal (after : Option (Ref Program.NativeEff)) :
    afterOfVal (afterToVal after) = some after := by
  cases after with
  | none => rfl
  | some r =>
    simp only [afterToVal, afterOfVal, readRef_ref, Option.map_some]

theorem raw_write (e : SessionEntry) : raw (write e) = some e := by
  cases e with
  | origin protocol codec engine =>
    simp only [write, raw, Digest.ofBytes?_bytes, Option.map_some]
  | action parent index a after =>
    simp only [write, raw, readRef_ref, ofVal_toVal, afterOfVal_afterToVal]

theorem fits_write (e : SessionEntry) : shapeDoc.accepts (write e) = true := by
  cases e with
  | origin protocol codec engine =>
    refine accepts_sum _ _ _ 0 "origin" _ _ rfl ?_
    refine acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_
      (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_nil _)))
    · rw [acceptsIn_of_not_named _ .nat _ (fun _ h => nomatch h)]
      rfl
    · rw [acceptsIn_of_not_named _ .nat _ (fun _ h => nomatch h)]
      rfl
    · rw [acceptsIn_of_not_named _ .digest _ (fun _ h => nomatch h)]
      simp only [acceptsAt, engine.length_eq, decide_true]
  | action parent index a after =>
    refine accepts_sum _ _ _ 1 "action" _ _ rfl ?_
    refine acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_
      (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_nil _))))
    · rw [acceptsIn_of_not_named _ (.ref .entry) _ (fun _ h => nomatch h)]
      simp only [acceptsAt, parent.digest.length_eq, decide_true, Bool.and_self]
    · rw [acceptsIn_of_not_named _ .nat _ (fun _ h => nomatch h)]
      rfl
    · exact Canonical.fits a
    · cases after with
      | none => exact accepts_option_none _ _
      | some r =>
        apply accepts_option_some
        rw [acceptsIn_of_not_named _ (.ref .program) _ (fun _ h => nomatch h)]
        simp only [acceptsAt, r.digest.length_eq, decide_true, Bool.and_self]

instance instCanonical : Canonical SessionEntry where
  shape := shapeDoc
  toVal := write
  ofVal := guarded write raw
  ofVal_toVal e := guarded_toVal write raw e (raw_write e)
  ofVal_exact := guarded_exact
  fits := fits_write

/-- Entries file at kind `entry`. -/
instance instContent : Content SessionEntry := ⟨.entry⟩

/-- **The entry codec is exact** (`session-entry-exact`): a value tree that reads as an entry is
that entry's own tree. Consumer: `Exchange.load`'s typed reads, through `Cas.get_exact`. -/
theorem ofVal_exact {v : Val} {e : SessionEntry} (h : ofVal v = some e) : v = toVal e :=
  Canonical.ofVal_exact h

end SessionEntry

end Effect4.Tool
