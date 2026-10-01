import Effect4.Api.RunnerDerived

/-! Seat J2, step 3b (reported, not repaired): a shape document names a type by its last name, so two
different types with one last name share a table key. For every codec of the Refusals and Runner
groups, list its document's table; then report (1) a name bound to two different bodies inside one
document (row 8's concern: the dedupe would have to refuse it), and (2) a name bound to different
bodies in different documents (the collision a future document holding both would meet).
Run: `lake env lean docs/research/2026-10-01-landing/seat-J2/probes/ShapeNameCollisions.lean`. -/

open Effect4 Effect4.Store Effect4.Program Effect4.Api Effect4.Machine

/-- One generated codec's document: its type's name and its table. -/
def documents : List (String × ShapeDoc) :=
  [("TableRefusal", Canonical.shape TableRefusal), ("AdmitRefusal", Canonical.shape AdmitRefusal),
   ("Authoring.Reason", Canonical.shape Authoring.Reason), ("Authoring.Refusal", Canonical.shape Authoring.Refusal),
   ("TypeReason", Canonical.shape TypeReason), ("TypeRefusal", Canonical.shape TypeRefusal),
   ("AuthorRefusal", Canonical.shape AuthorRefusal), ("PrintRefusal", Canonical.shape PrintRefusal),
   ("ReadRefusal", Canonical.shape ReadRefusal), ("BuildRefusal", Canonical.shape BuildRefusal),
   ("HostSession.Refusal", Canonical.shape HostSession.Refusal), ("HostSession.Phase", Canonical.shape HostSession.Phase),
   ("Runner.Command", Canonical.shape Runner.Command), ("HostProtocol.State", Canonical.shape HostProtocol.State),
   ("Machine.Stuck", Canonical.shape Machine.Stuck), ("Api.Outcome", Canonical.shape Api.Outcome),
   ("FiberStatus", Canonical.shape FiberStatus), ("Run.Observation", Canonical.shape Run.Observation),
   ("Program.Await", Canonical.shape Program.Await), ("NativeDecision", Canonical.shape NativeDecision)]

/-- Every `(name, body)` binding of a document: the root's own name when it is a named shape, and the
table. Bodies are compared by their rendering. -/
def bindings (doc : ShapeDoc) : List (String × String) :=
  doc.defs.map fun (n, s) => (n, s.render)

/-- Names bound to more than one distinct body within one list of bindings. -/
def conflicts (bs : List (String × String)) : List String :=
  let names := (bs.map (·.1)).eraseDups
  names.filter fun n => ((bs.filter (·.1 == n)).map (·.2)).eraseDups.length > 1

#eval do
  for (ty, doc) in documents do
    let names := (doc.defs.map (·.1))
    IO.println s!"{ty}: {names.length} table entries, {names.eraseDups.length} names; repeated with different bodies: {conflicts (bindings doc)}"
  let all := documents.flatMap fun (_, doc) => bindings doc
  IO.println s!"across documents, names bound to different bodies: {conflicts all}"
