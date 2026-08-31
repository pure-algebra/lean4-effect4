import Effects.Server.Free

/-!
# The cas-http/0 server as a tree

The server's per-request semantics denoted into a finite interaction
tree over the storage event signature. The signature mirrors the
implementation's byte-plane backend seam operation for operation
(`src/server/Backend.ts`), and `handle` mirrors the semantic core
(`src/server/Core.ts`) arm by arm, so the correspondence review can
align both files rule by rule.

The upload judgment is a parameter, exactly as the remote client
machine quantifies over `verify`: the judge's own internal law is the
CAS admission core's property, already carried there — the server model
treats it as the abstract decision over the collected resident bytes.
-/

namespace Effects.Server

/-- The storage event signature — the byte-plane seam a server stands
on: load admitted bytes, join admitted bytes in, answer advisory
presence, grow the published-roots set. -/
inductive StoreE (A B : Type) where
  | loadBytes (address : A)
  | putBytes (address : A) (bytes : B)
  | presence (addresses : List A)
  | publishRoot (root : A)

/-- The answer type of each storage event. Reducible so dependent pairs
over the signature compare definitionally in proofs. -/
abbrev StoreAns {A B : Type} : StoreE A B → Type
  | .loadBytes _ => Option B
  | .putBytes _ _ => Unit
  | .presence _ => List Bool
  | .publishRoot _ => Unit

/-- The closed request algebra — one constructor per wire operation. -/
inductive SRequest (A B : Type) where
  | readCapabilities
  | queryPresence (keys : List A)
  | loadNode (id : A)
  | uploadNode (id : A) (bytes : B)
  | publishRoot (root : A) (closure : List A)

/-- The closed outcome vocabulary the status table renders. -/
inductive SOutcome (A B : Type) where
  | capabilities (maxBatchKeys maxNodeBytes : Nat)
  | presence (statuses : List Bool)
  | nodeBytes (bytes : B)
  | nodeAbsent
  | admitted
  | alreadyAdmitted
  | admissionRefused
  | digestMismatch
  | nodeBudgetExceeded
  | batchBudgetExceeded
  | published
  | closureUnverified
  deriving Repr, DecidableEq

/-- The abstract upload judgment's verdict. -/
inductive UploadVerdict where
  | admit
  | alreadyResident
  | refused
  deriving Repr, DecidableEq

/-- The server's semantic parameters: published limits, the address
function, the canonical-decode projection to declared references, and
the admission judgment over the collected facts. -/
structure SParams (A B : Type) where
  maxBatchKeys : Nat
  maxNodeBytes : Nat
  size : B → Nat
  digestOf : B → A
  refsOf : B → Option (List A)
  judge : B → List (Option B) → Option B → UploadVerdict

/-- Load answers render to outcomes. -/
def loadOutcome {A B : Type} : Option B → SOutcome A B
  | some bytes => .nodeBytes bytes
  | none => .nodeAbsent

/-- Issue one load per address, in order, and hand the collected
answers to the continuation. -/
def collect {A B R : Type} (addresses : List A)
    (k : List (Option B) → Prog (StoreE A B) StoreAns R) :
    Prog (StoreE A B) StoreAns R :=
  match addresses with
  | [] => k []
  | address :: rest =>
    .vis (.loadBytes address) fun resident =>
      collect rest fun residents => k (resident :: residents)

/-- The upload arm as a tree: budget, digest equality, canonical
decode, one load per declared reference, one load at the candidate's
own address, then the abstract judgment. -/
def uploadTree {A B : Type} [DecidableEq A] (P : SParams A B)
    (id : A) (bytes : B) : Prog (StoreE A B) StoreAns (SOutcome A B) :=
  if P.size bytes > P.maxNodeBytes then .ret .nodeBudgetExceeded
  else if P.digestOf bytes ≠ id then .ret .digestMismatch
  else
    match P.refsOf bytes with
    | none => .ret .admissionRefused
    | some refs =>
      collect refs fun residents =>
        .vis (.loadBytes id) fun resident =>
          match P.judge bytes residents resident with
          | .admit => .vis (.putBytes id bytes) fun _ => .ret .admitted
          | .alreadyResident => .ret .alreadyAdmitted
          | .refused => .ret .admissionRefused

/-- The server, as a tree: one finite denotation per request. The arms
mirror the implementation core rule by rule. -/
def handle {A B : Type} [DecidableEq A] (P : SParams A B) :
    SRequest A B → Prog (StoreE A B) StoreAns (SOutcome A B)
  | .readCapabilities => .ret (.capabilities P.maxBatchKeys P.maxNodeBytes)
  | .queryPresence keys =>
    if keys.length > P.maxBatchKeys then .ret .batchBudgetExceeded
    else .vis (.presence keys) fun statuses => .ret (.presence statuses)
  | .loadNode id => .vis (.loadBytes id) fun resident => .ret (loadOutcome resident)
  | .uploadNode id bytes => uploadTree P id bytes
  | .publishRoot root closure =>
    .vis (.presence (root :: closure)) fun held =>
      if held.all id then .vis (.publishRoot root) fun _ => .ret .published
      else .ret .closureUnverified

end Effects.Server
