import Effect4.Program.Sketch
import Effect4.Program.Typing.Annotate

/-!
# Program.Typing.PartsTable — a whole program's address table, one traversal per part

**The question.** A sketch's address table (`Sketch.table`, `Program/Sketch.lean`) reads every
address of a whole program in the part that holds it (`Eff.partAt`): each entry asks for the part,
the environment from the part's root, and the checker at the address. That is the table's
specification, and it costs up to one check of a part per entry. This module computes the same
table part by part, with `Annotate.check` (`Program/Typing/Annotate.lean`) once for each part.

## The shape of the table

A program with no block is one part, and its table is `annotate`'s. At a definition block the
table is, in the order of `Node.addresses`:

| Segment | Its entries |
| --- | --- |
| the root `[]` | the module check's answer, in the empty environment |
| the bodies' spine at `[0]` (`Table.bodies`) | each spine node, with no environment and no answer; each body's table at its own base, in its declared request |
| the main program at `[1]` | the main program's table, in the empty environment |

All at the block's signature. The module is not a `module` file: it imports `Program/Sketch.lean`, which is not one. A body with no declaration holds no part, so its entries have no
environment and no answer, as in the specification.

`Sketch.annotate_eq_table` (`Laws/Program/Typing/PartsTable.lean`) proves the two tables equal.
The shape is what lets an edit inside one part splice the whole table (`Sketch.table_fill`).
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- **The entries of a block's bodies' spine**, at the spine's address `base`, at the block's
signature `sig`. A spine node has no environment and no answer. A body with a declaration is a
part: its table at its base, in its declared request. A body past the declarations holds no part. -/
def Table.bodies (sig : Signature Op) : List DefDecl → Effs Op → List Nat → List Table.Entry
  | d :: ds, .cons body rest, base =>
    ⟨base, none, none⟩ :: ((Annotate.check sig [d.request.normalize] (base ++ [0]) body).1 ++
      Table.bodies sig ds rest (base ++ [1]))
  | [], .cons body rest, base =>
    ⟨base, none, none⟩ :: ((Node.addresses (.eff body)).map (fun r => ⟨base ++ 0 :: r, none, none⟩) ++
      Table.bodies sig [] rest (base ++ [1]))
  | _, .nil, base => [⟨base, none, none⟩]

/-- **A whole program's address table, part by part**, with `root` the module check's answer. A
program with no block is one part: its table is `annotate`'s. -/
def annotateModule (s : Signature Op) (root : Except TypeRefusal EffTy) :
    Eff Op → List Table.Entry
  | .defs decls bodies main =>
    ⟨[], some (.env []), some root⟩ :: (Table.bodies (s.withDefs decls) decls bodies [0] ++
      (Annotate.check (s.withDefs decls) [] [1] main).1)
  | p => annotate s [] p

/-- **A sketch's address table, part by part**: its table (`Sketch.annotate_eq_table`,
`Laws/Program/Typing/PartsTable.lean`), with one traversal of each part. -/
def Sketch.annotate (s : Sketch) (app : SigApp := {}) : List Table.Entry :=
  annotateModule (app.withHoles s.holes).signature (s.check app) s.program

end Effect4.Program
