module

public import Effect4.Store.Domain.Node

/-!
# Store transaction data

The syntax signature contains node lists, root moves, and interrupted publication points.
Every field is data. No field is a function or a host object.
`Event` is the store's accepted event alphabet from the seams plan.
`src/Effect4/Store/Domain/Cas.lean` owns the transaction interpreter.
This module holds only its event data.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Store

/-- The policy fixed when a root is created. -/
inductive RootPolicy where
  | swap | journal | pin
  deriving DecidableEq, Repr

/-- The registered policy alphabet in wire order. -/
def RootPolicy.all : List RootPolicy := [.swap, .journal, .pin]

/-- The version-2 policy byte; legacy version-1 planes belong to the disk reader. -/
def RootPolicy.byte : RootPolicy → UInt8
  | .swap => 0 | .journal => 1 | .pin => 2

/-- The canonical policy name. -/
def RootPolicy.name : RootPolicy → String
  | .swap => "swap" | .journal => "journal" | .pin => "pin"

/-- The complete expectation for a root move, including repeated digests. -/
structure Head (D : Type) where
  digest : D
  generation : Nat
  deriving DecidableEq, Repr

/-- A root fixes its policy and target kind at creation. -/
structure Root where
  name : String
  policy : RootPolicy
  kind : Kind
  head : Head Digest
  deriving DecidableEq, Repr

/-- A decoded image. Raw bytes must pass Node.read before constructing its nodes. -/
structure RecoveryImage where
  nodes : List Node
  roots : List Root
  deriving DecidableEq, Repr

/-- Create a root, or compare its complete head before advancing it. -/
inductive Move where
  | create (name : String) (policy : RootPolicy) (target : AnyRef)
  | advance (name : String) (expected : Head Digest) (target : AnyRef)
  deriving DecidableEq, Repr

/-- Nodes arrive children first; moves follow all node checks. -/
structure Txn where
  nodes : List Node
  moves : List Move
  deriving DecidableEq, Repr

/-- A transaction never treats an occupied address with another node as success. -/
inductive NodeOutcome where
  | fresh | duplicate
  deriving DecidableEq, Repr

/-- Every accepted move reports its resulting generation. -/
inductive MoveOutcome where
  | created (generation : Nat)
  | advanced (generation : Nat)
  | duplicate (generation : Nat)
  deriving DecidableEq, Repr

/-- Ordered outcomes for the submitted nodes and moves. -/
structure Receipt where
  nodes : List (Digest × NodeOutcome)
  moves : List MoveOutcome
  deriving DecidableEq, Repr

/-- A cut counts fresh nodes, or records complete root publication. -/
inductive Cut where
  | nodes (kept : Nat)
  | published
  deriving DecidableEq, Repr

/-- The store event alphabet; an interruption applies only after full validation. -/
inductive Event where
  | commit (transaction : Txn)
  | interrupt (transaction : Txn) (cut : Cut)
  | restore (image : RecoveryImage)
  deriving DecidableEq, Repr

end Effect4.Store
