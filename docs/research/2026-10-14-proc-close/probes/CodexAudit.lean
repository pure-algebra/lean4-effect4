import CodexRelations
import CodexInline
import CodexObjects
import CodexClosure
import ProofGraph.AxiomAudit

-- Audit the retained review modules themselves, including transitive proof dependencies.
-- Temporary oleans are produced by check-codex-review.py; no library source is changed.
#axiom_audit CodexRelations CodexInline CodexObjects CodexClosure
