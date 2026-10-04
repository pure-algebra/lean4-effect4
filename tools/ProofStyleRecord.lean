import ProofGraph.ProofStyle
import Effect4
import Effect4.Laws

/-! `make record-proof-style`: rewrite the proof-style baseline from the tree as it stands
(`tools/ProofGraph/ProofStyle.lean`). Not a library module; run by `lake env lean`. A change to
the baseline is a reviewed diff. -/
#proof_style_record "src/Effect4" "Test/fixtures/proof-style/baseline.tsv"
