import Effect4.Store.Domain.Cas

/-!
# Finite disk comparison oracle

The table executes the actual Cas byte entrance, transactions, and checked recovery.
Its observation contains ordered node bytes and complete roots, excluding host file positions.
The native checked image separately checks the durable boundary and frozen snapshots.
This finite table proves no native simulation or filesystem theorem.
-/
namespace OCaml5.Store.DiskOracle
open Effect4.Store

def hexByte (byte : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!]
def hex (bytes : Bytes) : String := String.join (bytes.map hexByte)
def head (value : Head Digest) : String := value.digest.hex ++ ":" ++ toString value.generation
def optionalHead (value : Option (Head Digest)) : String := value.map head |>.getD "none"
def admission : Admission → String
  | .dangling missing => "dangling:" ++ missing.hex
  | .wrongKind reference expected actual => s!"wrongKind:{reference.hex}:{expected.byte.toNat}:{actual.byte.toNat}"
  | .malformedRef => "malformedRef"
  | .handleInContent => "handleInContent"
  | .shortSpec => "shortSpec"
  | .unregisteredKind found => s!"unregisteredKind:{found.toNat}"
  | .badFrame => "badFrame"
  | .trailing => "trailing"
  | .unknownTag found => s!"unknownTag:{found.toNat}"
  | .oversize => "oversize"
  | .badVersion => "badVersion"
  | .conflict address occupant => "conflict:" ++ address.hex ++ ":" ++ hex occupant.encode

def refusal : TxnRefusal → String
  | .node index why => s!"node:{index}:" ++ admission why
  | .noRoot name => "noRoot:" ++ name
  | .staleRoot name expected actual => "staleRoot:" ++ name ++ ":" ++ optionalHead expected ++ ":" ++ optionalHead actual
  | .pinned name => "pinned:" ++ name
  | .target name why => "target:" ++ name ++ ":" ++ admission why
  | .fork name previous target => "fork:" ++ name ++ ":" ++ previous.hex ++ ":" ++ target.hex
  | .restoreNonempty => "restoreNonempty"
  | .duplicateRoot name => "duplicateRoot:" ++ name

def image (store : Store) : String :=
  let nodes := store.nodes.map fun (address, node) => address.hex ++ "=" ++ hex node.encode
  let roots := store.roots.map fun root =>
    s!"{root.name}:{root.policy.byte.toNat}:{root.kind.byte.toNat}:" ++ head root.head
  "n[" ++ ";".intercalate nodes ++ "]r[" ++ ";".intercalate roots ++ "]"

def schema : Node := ⟨0, .schema, zeroDigest, .str "schema"⟩
def schemaAddress : Digest := sha256 schema.encode
def node (payload : Val) : Node := ⟨0, .«export», schemaAddress, payload⟩
def a : Node := node (.str "A")
def b : Node := node (.str "B")
def t : Node := node (.str "T")
def address (node : Node) : Digest := sha256 node.encode
def u : Node := node (.some (.ref Kind.export.byte (address t).bytes))
def target (node : Node) : AnyRef := ⟨.«export», address node⟩
def unknown : Bytes := [0, Kind.export.byte] ++ zeroDigest.bytes ++ framed 253 []
def dangling : Node := ⟨0, .«export», zeroDigest, .str "missing-spec"⟩

def receipt (value : Receipt) : String :=
  let nodes := value.nodes.map fun (digest, outcome) => digest.hex ++ ":" ++ match outcome with
    | .fresh => "fresh" | .duplicate => "duplicate"
  let moves := value.moves.map fun outcome => match outcome with
    | .created generation => "created:" ++ toString generation
    | .advanced generation => "advanced:" ++ toString generation
    | .duplicate generation => "duplicate:" ++ toString generation
  "n[" ++ ";".intercalate nodes ++ "]m[" ++ ";".intercalate moves ++ "]"

def finish (previous : Cas) : Except TxnRefusal (Receipt × Cas) → String × Cas
  | .error why => ("error:" ++ refusal why, previous)
  | .ok (answer, next) => ("ok:" ++ receipt answer, next)

def action (previous : Cas) : Nat → Except String (String × Cas)
  | 0 => .ok (finish previous (previous.commit ⟨[schema, a, b], []⟩))
  | 1 => .ok (finish previous (previous.commit ⟨[], [.create "docs/a" .swap (target a)]⟩))
  | 2 => .ok (finish previous (previous.commit ⟨[], [.advance "docs/a" ⟨address a, 1⟩ (target b)]⟩))
  | 3 => .ok (finish previous (previous.commit ⟨[], [.advance "docs/a" ⟨address b, 2⟩ (target a)]⟩))
  | 4 => .ok (finish previous (previous.commit ⟨[], [.advance "docs/a" ⟨address a, 3⟩ (target a)]⟩))
  | 5 => .ok (finish previous (previous.commit ⟨[], [.advance "docs/a" ⟨address a, 1⟩ ⟨.schema, schemaAddress⟩]⟩))
  | 6 => .ok (finish previous (previous.commit ⟨[t, u], [.advance "missing" ⟨address a, 1⟩ (target u)]⟩))
  | 7 => .ok (finish previous (previous.commit ⟨[t, u], [.create "docs/b" .swap (target u)]⟩))
  | 8 => .ok ("read:" ++ ((previous.store.find (address a)).map fun value => hex value.encode).getD "none", previous)
  | 9 => .ok ("snapshot", previous)
  | 10 => match Cas.restoreBytes (previous.store.nodes.map fun (_, value) => value.encode) previous.store.roots with
    | .error why => .ok ("error:" ++ refusal why, previous)
    | .ok next => .ok ("reopen", next)
  | 11 => .ok (finish previous (previous.commitBytes [unknown] []))
  | 12 => .ok (finish previous (previous.commitBytes [1 :: unknown.drop 1] []))
  | 13 => .ok (finish previous (previous.commitBytes [dangling.encode] []))
  | other => .error s!"unknown oracle action {other}"

structure Graph where
  states : Array Cas
  pending : List Nat
  rows : Array String

def expand (state : Nat) (graph : Graph) : Except String Graph := do
  let some previous := graph.states[state]? | throw s!"unknown oracle state {state}"
  (List.range 14).foldlM (init := graph) fun graph command => do
    let (answer, next) ← action previous command
    let key := image next.store
    let (nextId, states, pending) := match graph.states.toList.findIdx? (fun value => image value.store == key) with
      | some index => (index, graph.states, graph.pending)
      | none => (graph.states.size, graph.states.push next, graph.pending ++ [graph.states.size])
    let row := s!"{state}\t{command}\t{nextId}\t{answer}\t{key}"
    pure ⟨states, pending, graph.rows.push row⟩

def explore : Nat → Graph → Except String Graph
  | 0, graph => if graph.pending.isEmpty then .ok graph else .error "oracle exploration bound exhausted"
  | fuel + 1, graph => match graph.pending with
    | [] => .ok graph
    | state :: rest => do
      let graph ← expand state {graph with pending := rest}
      explore fuel graph

def render : Except String String := do
  let graph ← explore 1000 ⟨#[Cas.empty], [0], #[]⟩
  pure (s!"# actual Cas oracle; states={graph.states.size}; actions=14; command-list-bound=40\n" ++
    "# observation: ordered node bytes and complete roots; durable boundary checked separately\n" ++
    String.intercalate "\n" graph.rows.toList ++ "\n")
end OCaml5.Store.DiskOracle
