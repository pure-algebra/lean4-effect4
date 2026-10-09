module

public import Effect4.Program.Typing.Table

/-!
# Program.Typing.Splice — an edit's table, without checking the program again

An edit replaces the sub-program at an address `a` by another (`Node.replaceAt`). When the new
sub-program has the old one's type in the old one's environment, the edited program's address
table is the old table with one segment replaced: the entries of the subtree at `a`. The table
lists a node before its children, so that subtree is one contiguous segment, and every entry
outside it keeps its environment and its answer. `Table.splice` makes that table from the old
one and the new subtree's table, which costs the new subtree's checks and nothing else.

This is incremental attribute evaluation (Reps, Teitelbaum and Demers, 1983): an edit that keeps
the attributes at the subtree's root changes none outside it. The law is `table_splice`
(`Laws/Program/Typing/Splice.lean`, the claim `edit-splices-table`). Probe LIVE-1
(`docs/research/2026-10-08-live-authoring.md` §4) checked it on three programs first.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

/-- Whether the address `c` is inside the subtree at the address `a`. -/
def Table.under (a c : List Nat) : Bool := a.isPrefixOf c

/-- **The splice at an address**: the old table's entries before the subtree at `a`, then `sub`,
then the old table's entries after the subtree. `sub` is the new subtree's table at its own
addresses (`tableAt` at `a`). -/
def Table.splice (old : List Table.Entry) (a : List Nat) (sub : List Table.Entry) :
    List Table.Entry :=
  old.takeWhile (fun e => !Table.under a e.path) ++ sub ++
    (old.dropWhile fun e => !Table.under a e.path).dropWhile fun e => Table.under a e.path

end Effect4.Program
