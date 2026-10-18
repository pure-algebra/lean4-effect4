# ST1b placement before proof

Every row serves exact-codecs, stored-carrier admission, requirement R13.
These proposed properties extend the seams plan's accepted-history property.
The coordinator registers them during the landing.

| Claim and role | Reach and hypotheses | Exclusions | Consumer |
| --- | --- | --- | --- |
| advance_head; compatibility | Accepted changed advance checks the full expected head and increases generation exactly once. Duplicate targets retain generation. | Host races and persistence. | ST4 compare-and-set. |
| journal_ff; preservation | Accepted changed journal advance follows only designated parents to the previous head. | Arbitrary payload edges and host storage. | ST4 session chains. |
| interrupted_closed; preservation | A closed starting store and fully accepted transaction yield a closed fresh-node prefix. | Universal filesystem correctness and progress. | ST2 recovery. |
| interrupted_roots; compatibility | Every accepted cut has the exact original or published root table. | Host publication atomicity. | ST2 image comparison. |
| commit_grows, bytes_never_change, commit_reads; preservation | Accepted transaction excludes conflict and retains previous node residents and accepted node reads. | Hash injectivity and IO durability. | ST2 and ST4. |
| replay_append; helper | Successful replay extends by the canonical event step. | Admission of arbitrary replay parameters. | Cas.commit and Cas.interrupted reached witnesses. |

Helpers for node prefixes serve interrupted_closed and commit_grows.
Helpers for root moves serve advance_head and journal_ff.
All claims retain the plan's full transaction preflight and stale-first order.

## Proposed registry questions

| Question | Pointer | Required property |
| --- | --- | --- |
| `cas-advance-head` | `Effect4.Store.advance_head` | Changed accepted root moves raise exactly one generation. |
| `cas-advance-stale` | `Effect4.Store.advance_stale` | Full-head staleness precedes all target checks. |
| `cas-advance-duplicate` | `Effect4.Store.advance_duplicate` | Identical targets retain the exact store. |
| `cas-journal-fast-forward` | `Effect4.Store.journal_ff` | Journal advancement uses designated parent chains. |
| `cas-commit-grows` | `Effect4.Store.commit_grows` | Transactions retain earlier residents. |
| `cas-commit-bytes` | `Effect4.Store.bytes_never_change` | Transactions retain each earlier node value. |
| `cas-commit-reads` | `Effect4.Store.commit_reads` | Accepted submitted nodes read back. |
| `cas-interrupted-closed` | `Effect4.Store.interrupted_closed` | Validated cuts retain node closure. |
| `cas-interrupted-roots` | `Effect4.Store.interrupted_roots` | Cuts retain old roots or return the exact published store. |

All pointers live in `src/Effect4/Store/Domain/Cas.lean`.
`replay_append` and the staging decompositions serve these questions and the reached-store constructors.
The checkpoint correction extends designated fields to constructor 0's fourth field at kind checkpoint.
It does not turn incidental references into ancestry.
