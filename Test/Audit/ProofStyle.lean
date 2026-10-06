import ProofGraph.ProofStyle
import Effect4
import Effect4.Laws

/-!
The proof-style ratchet over `src/Effect4` (`tools/ProofGraph/ProofStyle.lean`): no new
`simp_all`, `first`, `try` or `simp` without `only` in a hand-written proof, and no stale entry in
the baseline of the uses written before the rule (`Test/fixtures/proof-style/baseline.tsv`). The
scan parses with this module's environment, which holds every syntax `src/Effect4` uses.
`#proof_style_record "src/Effect4" "Test/fixtures/proof-style/baseline.tsv"` rewrites the
baseline.

The red controls scan a fixture. Against an empty baseline, its four uses are refused by kind,
and so is the command the scan cannot parse (a tactic local to the fixture): an unread command is
a gap the baseline must name. Neither the comment nor the `try … catch` of `do` notation is
counted. Against a baseline with one entry too many, the extra entry is refused as stale.

One control is for a word. `#exhaustive_gate`, `#traversal_census` and `#traversal_class` write
a clause `under Some.Prefix`, and this module's environment holds the three syntaxes. The word
is a keyword in that place only (`&" under "`), so the scan reads a theorem with a hypothesis
named `under`: against the empty baseline it refuses the `first` inside the proof, by kind. With
the word a reserved token, the scan could not parse such a theorem. It reported the theorem as
unread, and it counted no use inside it (seat QTYPES's receipt of 2026-10-05, section 10,
item 5).
-/

/--
error: proof style: 5 finding(s)
new use: first in banned (Test/fixtures/proof-style/red/Sample.lean, lines [6]); 1 > 0 recorded
new use: simp-without-only in banned (Test/fixtures/proof-style/red/Sample.lean, lines [6]); 1 > 0 recorded
new use: simp_all in banned (Test/fixtures/proof-style/red/Sample.lean, lines [5]); 1 > 0 recorded
new use: try in banned (Test/fixtures/proof-style/red/Sample.lean, lines [5]); 1 > 0 recorded
new unread command: localSyntax (Test/fixtures/proof-style/red/Sample.lean, lines [18]): the scan cannot parse it, so banned uses in it go uncounted; 1 > 0 recorded
-/
#guard_msgs (error) in
#proof_style_check "Test/fixtures/proof-style/red" "Test/fixtures/proof-style/red-baseline.tsv"

/--
error: proof style: 1 finding(s)
stale entry: simp_all in plain (Test/fixtures/proof-style/red/Sample.lean): 0 < 1 recorded; rerun #proof_style_record
-/
#guard_msgs (error) in
#proof_style_check "Test/fixtures/proof-style/red" "Test/fixtures/proof-style/red-stale.tsv"

/--
error: proof style: 1 finding(s)
new use: first in named (Test/fixtures/proof-style/under/Sample.lean, lines [6]); 1 > 0 recorded
-/
#guard_msgs (error) in
#proof_style_check "Test/fixtures/proof-style/under" "Test/fixtures/proof-style/red-baseline.tsv"

#proof_style_check "src/Effect4" "Test/fixtures/proof-style/baseline.tsv"
