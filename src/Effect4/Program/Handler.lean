module

public import Effect4.Program.Services
public import Effect4.Program.LayerView

/-!
# Program.Handler — a service block read by one fold

Plotkin and Pretnar's handlers are algebras for operations. Ahman and Bauer's runners give
clauses that answer directly, without capturing their continuation. This view reads that form
from the existing definitions. It stores no program syntax and states no law of clause meaning.
The design is `docs/research/2026-10-21-handlers/README.md`, sections 2 to 4.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

/-- A service block as a handler. `state` is the state the handler carries.
`requires` records the init's context requirements. `forwards` records the clauses' remaining
context requirements. Each clause records its name, definition position and arity. -/
structure Handler where
  service : String
  state : Ty
  init : Nat
  clauses : List (String × Nat × Nat)
  requires : List ServiceKey
  forwards : List ServiceKey
deriving DecidableEq, Repr

/-- Read one service's handler from its declarations. A missing init refuses the view. -/
def Handler.ofService (decls : List DefDecl) (s : Service) : Option Handler := do
  let init ← decls[s.init]?
  let methods := s.methods.filterMap fun (_, k, _) => decls[k]?
  pure { service := s.name, state := init.answer, init := s.init, clauses := s.methods,
         requires := init.requires, forwards := (methods.flatMap (·.requires)).eraseDups }

/-- The declarations contribute their handlers. Every node joins its children's handlers. -/
def handlerAlgebra {Op : Type} : EffAlgebra Op (fun _ => List Handler) :=
  EffAlgebra.ofLayer fun _ _ args =>
    (args.flatMap fun | .decls ds => (servicesOf ds).filterMap (Handler.ofService ds) | _ => []) ++
    (args.flatMap fun | .child _ hs => hs | _ => [])

/-- The handlers of a program, read by one fold. -/
def handlersOf {Op : Type} : Eff Op → List Handler := cata_eff handlerAlgebra

/-- A method's name, arguments after the state, answer and error. -/
abbrev Clause := String × List Ty × Ty × Ty

/-- Forget the state from each clause's request. A missing or malformed clause refuses the view. -/
def Handler.interface (decls : List DefDecl) (h : Handler) : Option (List Clause) :=
  h.clauses.mapM fun (name, position, arity) => do
    let d ← decls[position]?
    let args ← methodArgs h.state d arity
    pure (name, args, d.answer, d.error)

/-- Handlers of one service fit when both interfaces exist and agree. -/
def Handler.fits (decls : List DefDecl) (h : Handler) (decls' : List DefDecl)
    (h' : Handler) : Bool :=
  h.service == h'.service && match h.interface decls, h'.interface decls' with
    | some i, some i' => i == i'
    | _, _ => false

end Effect4.Program
