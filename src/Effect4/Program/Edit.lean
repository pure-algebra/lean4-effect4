module

public import Effect4.Program.Typing.Splice
public import Effect4.Program.Typing.Annotate

/-!
# Program.Edit — the edit session: a program, its address table, and edits fed one at a time

**The question.** A tool that edits a program shows its address table after every edit. Checking
the whole program again at each edit costs the whole program. The edit session keeps the table
beside the program, and an edit that keeps its focus's type splices the table instead
(`Table.splice`): it checks the new sub-program and nothing else.

## The face

The face is the session API's (decisions rows 326 and 334): `open`, `feed` and `view`, with an
edit as one kind of event. A run of edits is the fold of `feed` (`run`).

| Operation | It takes | It answers |
| --- | --- | --- |
| `EditSession.open` | a signature, the root's environment, a program | the session, with the program's table |
| `EditSession.feed` | a session and an edit | the next session, and what the edit did to the table (`Edit.Delta`) |
| `EditSession.run` | a session and a list of edits | the session after each edit in turn |
| `EditSession.view` | a session | the table, its refusals, and the program's type |

## What `feed` does

An edit `replace a q` puts `q` in place of the sub-program at the address `a` (`Node.replaceAt`).
The session reads the old focus from its own table (`Table.typedAt`), not from the program:

- **spliced**: the table types the root and the address, and the checker gives `q` the old
  sub-program's type in its environment. The table is spliced, and the new subtree's addresses are
  the addresses to show again.
- **rechecked**: any other edit of a program. The table is computed again from the root
  (`annotate`).
- **unchanged**: the address holds no program. Nothing changes.

The session's invariant is that its table is its program's table (`EditSession.Coherent`). The
open makes it, and each edit keeps it (`EditSession.run_coherent`,
`Laws/Program/Edit.lean`, the claim `edit-session-coherent`). The splice law gives the spliced
case (`table_splice`).

## What this module is not

- It reads no definition block: a program with a block has no table of its own here. A sketch's
  table reads one (`Sketch.table`), and the splice over a whole program's parts is the next
  slice.
- It splices only on a typed program. Holes keep a program typed while it is incomplete
  (`Sketch`), so an edit session over holes stays on the spliced path.
- It runs nothing. Running and editing share the face; one event type for both is open.
- It counts no cost. The cost is read off the definitions, and no theorem counts it.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- **An edit**: one event of an edit session. -/
inductive Edit (Op : Type) where
  /-- put the program in place of the sub-program at the address -/
  | replace (path : List Nat) (program : Eff Op)

/-- **What an edit did to the address table.** -/
inductive Edit.Delta where
  /-- the address holds no program, and nothing changed -/
  | unchanged
  /-- the edit kept its focus's type: the table is spliced, and these addresses are new -/
  | spliced (shown : List (List Nat))
  /-- the table is computed again from the root -/
  | rechecked
  deriving DecidableEq, Repr

/-- **The environment and the type that a table holds at an address**: at the first entry at the
address, where it holds an environment of variables and a type. On a program's table it is the
focus there (`Table.typedAt_table`, `Laws/Program/Edit.lean`). -/
def Table.typedAt (t : List Table.Entry) (a : List Nat) : Option (TyEnv × EffTy) :=
  match t.find? (fun e => decide (e.path = a)) with
  | some ⟨_, some (.env tys), some (.ok ty)⟩ => some (tys, ty)
  | _ => none

/-- **An edit session**: a program, the signature and the root's environment it is checked at,
and its address table. -/
structure EditSession (Op : Type) where
  /-- the signature the program is checked at -/
  sig : Signature Op
  /-- the root's environment -/
  env : TyEnv
  /-- the program -/
  program : Eff Op
  /-- the address table the session keeps; its program's table (`EditSession.Coherent`) -/
  table : List Table.Entry

namespace EditSession

/-- **The session's invariant**: its table is its program's table. -/
def Coherent (l : EditSession Op) : Prop := l.table = Program.table l.sig l.env l.program

/-- **Open** a session on a program: its table in one traversal (`annotate`). -/
def «open» (s : Signature Op) (env : TyEnv) (p : Eff Op) : EditSession Op :=
  ⟨s, env, p, annotate s env p⟩

/-- **Feed** one edit: the next session, and what the edit did to the table. -/
def feed (l : EditSession Op) : Edit Op → EditSession Op × Edit.Delta
  | .replace a q =>
    match (Node.eff l.program).replaceAt a (.eff q) with
    | some (.eff p') =>
      let rechecked : EditSession Op × Edit.Delta :=
        ({ l with program := p', table := annotate l.sig l.env p' }, .rechecked)
      match Table.typedAt l.table [], Table.typedAt l.table a with
      | some _, some (tys, ty) =>
        match Annotate.check l.sig tys a q with
        | (sub, .ok ty') =>
          if ty' = ty then
            ({ l with program := p', table := Table.splice l.table a sub },
              .spliced (sub.map (·.path)))
          else rechecked
        | (_, .error _) => rechecked
      | _, _ => rechecked
    | _ => (l, .unchanged)

/-- **A run of edits**: the fold of `feed`. -/
def run (l : EditSession Op) (edits : List (Edit Op)) : EditSession Op :=
  edits.foldl (fun l e => (l.feed e).1) l

/-- **What a session shows**: its table, the distinct refusals of its entries in the table's
order, and the type its table holds at the root. -/
structure View where
  /-- the address table -/
  table : List Table.Entry
  /-- the distinct refusals of the entries, in the table's order -/
  refusals : List TypeRefusal
  /-- the program's type, where the table holds one at the root -/
  type : Option EffTy

/-- **View** a session. On a coherent session the refusals are the program's (`refusals`), and
the type is the checker's (`EditSession.view_type`, `Laws/Program/Edit.lean`). -/
def view (l : EditSession Op) : View :=
  ⟨l.table, (l.table.filterMap fun e => e.result.bind Checker.refusal).eraseDups,
    (Table.typedAt l.table []).map (·.2)⟩

end EditSession

end Effect4.Program
