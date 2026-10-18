import Effect4.Tool.Protocol
import Effect4.Tool.CodecProfile

/-!
# Tool.WireTypes — the connection's framing, outside the tool's state

A request or a reply crosses the wire inside an `Envelope`: the method's name, the version the
connection selected for it, and the payload. A `Connection` holds the selected versions; it lives
with the driver, never in `Tool.State`. A wire `Refusal` is the transport's, kept apart from the
tool's own `Tool.Refusal`: a wire refusal leaves the state unchanged and records nothing.
-/

set_option autoImplicit false
namespace Effect4.Tool.Wire

/-- **A framed message**: connection framing stays outside the semantic tool state. -/
structure Envelope (α : Type) where
  method : String
  version : Nat
  payload : α

/-- **Why the wire refuses a message**, before or after the tool serves it. -/
inductive Refusal where
  | codec (why : CodecProfile.Refusal)
  | unselected (method : String)
  | version (method : String) (selected received : Nat)
  | method (declared actual : String)
  | response
  | connection

/-- **A connection**: the version it selected for each method. -/
structure Connection where
  selected : List (String × Nat)

/-- A connection selects only supported versions, and each method once. -/
def Connection.valid (connection : Connection) : Bool :=
  connection.selected.all (fun (method,version) =>
    ((supportedMethods.lookup method).getD []).contains version) &&
  decide ((connection.selected.map Prod.fst).eraseDups.length = connection.selected.length)

/-- The connection that selects version 1 of every method. -/
def Connection.v1 : Connection :=
  ⟨supportedMethods.map fun entry => (entry.1,1)⟩

end Effect4.Tool.Wire
