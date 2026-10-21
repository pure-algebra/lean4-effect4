import Effect4.Program.Authoring
import Effect4.Program.Authoring.Lifts
import Tools.View.LayerGraph
open Effect4 Effect4.Program Effect4.Program.Authoring Tools.View

/-! G2 taken apart: the elements of the layer hypergraph for a to-do-shaped term, in both merge
orders. The atoms give each `effect` its box and its output wire, and each `service` read a wire
into the box; the combinators are overlay (`LayerGraph.algebra`). The model is computed as lists. -/

/-- A vertex is a box or a wire, named by its tag. -/
def box (k : ServiceKey) : String := s!"box {k.service.value}"
def wire (k : ServiceKey) : String := s!"wire {k.service.value}"

/-- The atoms: an `effect(k, body)` is the body's read wires connected into box k, and box k
connected to wire k. A `service k` read is the vertex `wire k`. Every other constructor is the
overlay of its children. -/
def atoms : EffAlgebra NativeOp (fun _ => AGraph String) :=
  EffAlgebra.ofLayer fun _ ctor args =>
    let children := args.filterMap fun | .child _ g => some g | _ => none
    let keys := args.filterMap fun | .key k => some k | _ => none
    let under := children.foldl AGraph.overlay .empty
    match ctor, keys with
    | "effect", [k] => .overlay (.connect under (.vertex (box k))) (.connect (.vertex (box k)) (.vertex (wire k)))
    | "service", [k] => .vertex (wire k)
    | _, _ => under

/-- The edge-set model, computed: the vertices and the edges a graph denotes. -/
def elems : AGraph String → List String × List (String × String)
  | .empty => ([], [])
  | .vertex a => ([a], [])
  | .overlay x y => let (vx, ex) := elems x; let (vy, ey) := elems y; ((vx ++ vy).eraseDups, (ex ++ ey).eraseDups)
  | .connect x y => let (vx, ex) := elems x; let (vy, ey) := elems y
      ((vx ++ vy).eraseDups, (ex ++ ey ++ vx.flatMap fun a => vy.map fun b => (a, b)).eraseDups)

/-- The term as it was built: the termOf of the graph. -/
def termOf : AGraph String → String
  | .empty => "ε" | .vertex a => s!"⟨{a}⟩"
  | .overlay x y => s!"({termOf x} + {termOf y})"
  | .connect x y => s!"({termOf x} → {termOf y})"

def repo : ServiceKey := ⟨⟨30⟩, ⟨6⟩⟩
def session : ServiceKey := ⟨⟨30⟩, ⟨7⟩⟩
def app : ServiceKey := ⟨⟨30⟩, ⟨8⟩⟩

/-- The hosts as layers, the app's block as a layer over the repo, and main's provision. -/
def hostRepo : LayerSrc NativeOp := Layer.effect repo (succeed unit)
def hostSession : LayerSrc NativeOp := Layer.effect session (succeed unit)
def appBlock : LayerSrc NativeOp := Layer.effect app (service repo)
def ab : LayerSrc NativeOp := Layer.provide appBlock (Layer.merge hostRepo hostSession)
def ba : LayerSrc NativeOp := Layer.provide appBlock (Layer.merge hostSession hostRepo)
/-- Two providers of one wire: the clash the picture shows and evaluation resolves last-wins. -/
def clash : LayerSrc NativeOp := Layer.merge hostRepo (Layer.effect repo (succeed (nat 1)))

def show_ (name : String) (l : LayerSrc NativeOp) : IO Unit := do
  match l {} [2] with
  | .error _ => IO.println s!"{name}: refused"
  | .ok t =>
    let g := LayerGraph.hypergraph atoms t
    let (vs, es) := elems g
    IO.println s!"{name}\n  termOf: {termOf g}\n  vertices: {vs}\n  edges: {es}"

#eval do
  show_ "ab = provide(app, merge(repo, session))" ab
  show_ "ba = provide(app, merge(session, repo))" ba
  let same := match ab {} [2], ba {} [2] with
    | .ok a, .ok b =>
      let (va, ea) := elems (LayerGraph.hypergraph atoms a); let (vb, eb) := elems (LayerGraph.hypergraph atoms b)
      decide (va.toArray.qsort (· < ·) = vb.toArray.qsort (· < ·)) && decide (ea.length = eb.length && ea.all eb.contains)
    | _, _ => false
  IO.println s!"same model: {same}"
  show_ "clash = merge(repo, repo')" clash
