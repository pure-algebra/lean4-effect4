module

public import Effect4.Library.Stream.Source

/-!
# A source assembled from its operation declarations

The pull declaration owns the element and completion columns.
The open answer is the entire state request of pull and close.
The adapter checks those relationships before it constructs the source.
It derives every invocation from the declaration's name.
The module checker still owns argument typing, column formation and body admission.
These relationships concern supplied declarations. Their columns must also match the installed definitions.
The generated declaration record provides that connection on the normal construction path.
Decisions rows 328, 331 and 335 retain stored definitions and the End-value protocol.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Stream
open Effect4.Program Effect4.Program.Authoring

/-- The column relationship that prevents a definition-backed source. -/
inductive Source.DefinitionColumn
  | protocol | openedState | closeState | closeAnswer
  deriving DecidableEq, Repr

/-- The declaration and column that the source adapter refuses. -/
structure Source.DefinitionRefusal where
  definition : String
  column : DefinitionColumn
  deriving DecidableEq, Repr

/-- Assemble a source from declared operations, without repeating element or completion types.
`arguments` are the opening operation's arguments in declaration order.
Pull and close receive the entire opened state as their request.
Acceptance validates column relationships, not the definitions' bodies or batch nonemptiness. -/
def Source.fromDefinitions (opened pull close : DefSrc NativeOp) (arguments : List TermSrc) :
    Except DefinitionRefusal Source :=
  match Ty.payloadTy "Chunk" pull.answer.normalize, Ty.payloadTy "End" pull.answer.normalize with
  | some (.list elem), some done =>
    if pull.answer.normalize = (Program.Stream.pulledTy elem done).normalize then
      if opened.answer.normalize = pull.decl.request.normalize then
        if close.decl.request.normalize = pull.decl.request.normalize then
          if close.answer.normalize = .unit then
            .ok { elem := elem, done := done,
                  opened := Def.invoke opened.name arguments,
                  pull := fun state => Def.invoke pull.name [state],
                  close := fun state => Def.invoke close.name [state] }
          else .error ⟨close.name, .closeAnswer⟩
        else .error ⟨close.name, .closeState⟩
      else .error ⟨opened.name, .openedState⟩
    else .error ⟨pull.name, .protocol⟩
  | _, _ => .error ⟨pull.name, .protocol⟩

end Effect4.Stream
