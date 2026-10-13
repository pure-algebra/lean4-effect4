module

public import Effect4.Program.Native

/-!
# Program.RowProtocol — a declared protocol of a host row, as data

Slice PROTOCOL of the claims packet (`docs/research/2026-10-07-packet-application-claims.md`,
§3.5; decisions rows 307 (9) and 336 (9)). A row's types are its first protocol: the request fits
`Row.request`, and a successful answer fits `Row.answer` (the session's reply admission, and
`rowProtocol` in `src/Effect4/Laws/Program/RowProtocol.lean`). A declared protocol refines the
types by two terms of type `bool`:

* `pre` reads the request at level 0: the demand that the program meets at each call;
* `post` reads the request at level 0 and the successful answer at level 1: the promise that the
  host keeps.

A term is first-order data, the term checker types it at the row's columns (`formed`), and
`evalTerm` decides it on values (`admits`, `keeps`). A failure is not read: the error column
types it, and no term reads one. A row with no declared protocol has the protocol of its types.
The meaning of a declared protocol as a protocol of the row signature is
`src/Effect4/Laws/Program/Validated.lean`'s.
-/

@[expose] public section

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- A declared protocol of a host row: a demand on the request and a promise on the request and a
successful answer, each a term of type `bool`. The default asks nothing and promises nothing. -/
structure RowProtocol where
  pre : Term := .lit (.bool true)
  post : Term := .lit (.bool true)
deriving DecidableEq

namespace RowProtocol

/-- **The protocol is formed at a row**: its demand is typed `bool` at the request's column, and
its promise at the request's and the answer's columns. -/
def formed (sig : Signature NativeOp) (row : Row) (p : RowProtocol) : Bool :=
  termTy sig [row.request] p.pre == some .bool &&
    termTy sig [row.request, row.answer] p.post == some .bool

/-- The request meets the protocol's demand. -/
def admits (p : RowProtocol) (request : Val) : Bool :=
  evalTerm [request] p.pre == some (.bool true)

/-- A successful answer keeps the protocol's promise at its request. -/
def keeps (p : RowProtocol) (request answer : Val) : Bool :=
  evalTerm [request, answer] p.post == some (.bool true)

end RowProtocol

/-- The declared protocols of a row table, by the row's spelling. -/
abbrev RowProtocols := List (String × RowProtocol)

namespace RowProtocols

/-- The declared protocol of a table's row at a position, if its spelling has one. -/
def at? (protocols : RowProtocols) (table : RowTable) (i : Nat) : Option RowProtocol :=
  (table[i]?).bind fun row => protocols.lookup row.spelling

/-- **The declared protocols are formed at a table**: each names a row of the table, and its
terms are typed at that row's columns. -/
def formed (protocols : RowProtocols) (table : RowTable) : Bool :=
  protocols.all fun entry =>
    match table.find? (·.spelling == entry.1) with
    | some row => entry.2.formed (nativeSignature table) row
    | none => false

/-- A request meets the demand of its row's declared protocol; a row with none asks nothing. -/
def admits (protocols : RowProtocols) (spelling : String) (request : Val) : Bool :=
  (protocols.lookup spelling).all (·.admits request)

/-- An exit keeps the promise of the declared protocol of the row at a position: a success keeps
it at its request, and a failure is not read. A row with none promises nothing. -/
def keepsAt (protocols : RowProtocols) (table : RowTable) (i : Nat) (request : Val) :
    ExitV → Bool
  | Exit.success answer => (protocols.at? table i).all (·.keeps request answer)
  | Exit.failure _ => true

end RowProtocols

end Effect4.Program
