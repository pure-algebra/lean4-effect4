module

public import Effect4.Program.Authoring
public import Effect4.Program.Stream

@[expose] public section

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- **What a stream's source supplies**: how to open it, how to pull it once, and how to close
it. The three are given where the program is written, so the module stores no code. -/
structure Source where
  /-- The element type. -/
  elem : Ty
  /-- The leftover's type: `unit` for a stream. -/
  done : Ty
  /-- Open the stream. It answers the opened handle. -/
  opened : Src NativeOp
  /-- One pull of the opened stream: it answers `pulledTy elem done`. -/
  pull : TermSrc → Src NativeOp
  /-- Close the opened stream. The consumer registers it as its scope's finalizer. -/
  close : TermSrc → Src NativeOp

/-- A host stream: the kernel's three rows at one request. -/
def Source.host (elem done : Ty) (openRow pullRow closeRow : RowDef) (request : TermSrc) : Source :=
  { elem, done
    opened := Row.call openRow request
    pull := fun h => Row.call pullRow h
    close := fun h => Row.call closeRow h }

end Effect4.Stream
