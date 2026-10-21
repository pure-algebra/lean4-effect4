import Effect4.Program.Object
import Effect4.Api.ObjectDerived
import Effect4.Api.Author
import Effect4.Program.Check
import Effect4.Program.Services
import Effect4.Store.Domain.Document

/-! Pure operations on program objects. Each operation calls its existing owner.
Admission belongs to `Built.ofProgram`; node bytes belong to the store codec.
The address table belongs to `Check.run`, through source layer references.
Service roles use the target-independent name profile.
No operation here reads files, stores host state or introduces program syntax. -/

set_option autoImplicit false
namespace Effect4.Program
open Effect4 Effect4.Store

namespace Object

/-- Forget the admission certificate. -/
def ofBuilt (b : Api.Built) : Object := ⟨b.app, b.program⟩

/-- Decide admission at the object's signature, retaining its located refusal. -/
def «open» (o : Object) : Except AdmitRefusal Api.Built :=
  Api.Built.ofProgram o.app o.program

/-- Encode the object's versioned store node, including its kind and shape specification. -/
def bytes (o : Object) : Bytes := (nodeOf o).encode

/-- The typed digest of the object's complete store node. -/
def ref (o : Object) : Ref Object := Store.address o

/-- The three owners of a failed load: node framing, typed content, and program admission. -/
inductive LoadRefusal where
  | node (why : Node.ReadRefusal)
  | content (why : Store.ReadRefusal)
  | admission (why : AdmitRefusal)
deriving DecidableEq

/-- Read exact node bytes, then check their kind, specification and canonical payload. -/
def read (bs : Bytes) : Except LoadRefusal Object :=
  match Node.read bs with
  | .error why => .error (.node why)
  | .ok n => (Node.readContent n).mapError .content

/-- Read and admit a saved program, without source elaboration. -/
def load (bs : Bytes) : Except LoadRefusal Api.Built :=
  match read bs with
  | .error why => .error why
  | .ok o => o.open.mapError .admission

/-- Read the checker's source address table, through the program's layer references. -/
def table (o : Object) : List Table.Entry :=
  (Check.run (.module o.app [] o.program)).table

/-- Read service roles after their formation check, without target naming restrictions. -/
def services (o : Object) : Except PrintRefusal (List Service) :=
  match serviceFaultIn anyName o.program.defsOf with
  | some why => .error why
  | none => .ok (servicesOf o.program.defsOf)

end Object

/-- Project the displayed fields. The printed certificate carries no admission evidence. -/
def _root_.Effect4.Api.Built.certificate (b : Api.Built) : Certificate :=
  { answer := b.ty.answer, error := b.ty.error, requires := b.requires, rows := b.table,
    services := (nativeSignature b.table).keyNames, declarations := b.program.defsOf }

end Effect4.Program
