import Effects.Server.Model

/-!
# Reification as interpretation

Tracing is not a second interpreter: `traced` transforms a handler so
it also reifies every event with its answer, and the transcript falls
out of the ordinary `interp` under the transformed handler — the same
move `tiered` makes for topology. The erasure theorem says tracing
changes nothing observable, so every law proved of a handler transports
to its traced form for free.

`runServer` is the server as a program: fold a request script through
the tree denotations and collect the outcomes. `runServerTraced` is the
same fold under the transformation — outcomes plus the reified storage
transcript, which is exactly what a conformance row is.
-/

namespace Effects.Server

/-- Transform a handler to also reify each event with its answer. -/
def traced {E : Type} {Ans : E → Type} {S T : Type}
    (reify : (event : E) → Ans event → T) (h : Handler E Ans S) :
    Handler E Ans (S × List T) := fun event s =>
  ((( h event s.1).1, s.2 ++ [reify event (h event s.1).2]),
    (h event s.1).2)

/-- Erasure: state and result under the traced handler agree with the
untraced interpretation — reification is observationally free. -/
theorem interp_traced_erases {E : Type} {Ans : E → Type} {S T R : Type}
    (reify : (event : E) → Ans event → T) (h : Handler E Ans S)
    (p : Prog E Ans R) : ∀ (s : S) (acc : List T),
    ((interp (traced reify h) p (s, acc)).1.1,
        (interp (traced reify h) p (s, acc)).2)
      = interp h p s := by
  induction p with
  | ret value => intro s acc; rfl
  | vis event resume ih => intro s acc; simp [interp, traced, ih]

/-- The reified storage transcript entry: each event with its answer. -/
inductive StoreEvent (A B : Type) where
  | loadBytes (address : A) (answer : Option B)
  | putBytes (address : A) (bytes : B)
  | presence (addresses : List A) (answer : List Bool)
  | publishRoot (root : A)
  deriving Repr, DecidableEq

/-- Reify one storage event with its answer. -/
def reifyStore {A B : Type} : (event : StoreE A B) → StoreAns event → StoreEvent A B
  | .loadBytes a, answer => .loadBytes a answer
  | .putBytes a b, _ => .putBytes a b
  | .presence keys, answer => .presence keys answer
  | .publishRoot r, _ => .publishRoot r

/-- Query the server: fold a request script through the tree
denotations under any handler, collecting the outcomes in order. -/
def runServer {A B S : Type} [DecidableEq A]
    (h : Handler (StoreE A B) StoreAns S) (P : SParams A B)
    (requests : List (SRequest A B)) (s : S) :
    S × List (SOutcome A B) :=
  requests.foldl
    (fun acc request =>
      let stepped := interp h (handle P request) acc.1
      (stepped.1, acc.2 ++ [stepped.2]))
    (s, [])

/-- The same query with the storage transcript reified alongside:
`runServer` under the tracing transformation, nothing more. -/
def runServerTraced {A B S : Type} [DecidableEq A]
    (h : Handler (StoreE A B) StoreAns S) (P : SParams A B)
    (requests : List (SRequest A B)) (s : S) :
    (S × List (StoreEvent A B)) × List (SOutcome A B) :=
  runServer (traced reifyStore h) P requests (s, [])

end Effects.Server
