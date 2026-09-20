# Agreement searched-proof slice

Agreement now uses the certified plain `by aesop` proof for 80 existing statements.
All 80 headers are byte-identical to the frozen candidates. Reconstructing the
reviewed source from those body spans reproduces the complete intermediate file;
the final file adds exactly the intended origin-gate change from ceiling 1 to 0.
That obligation was already closed in Phase B, so it is not a newly proved claim.

Both requested narrow builds returned 0 and freshly built Agreement. The first
reported 0 open / 1 proved at ceiling 1; the second reported the same at ceiling 0.
The final census returned 0 and closed 82 of 192 statements, unchanged from the
certified Phase B count and population. The exact commands and retained log paths
are in `manifest.json`; raw logs, sources and all 80 comparisons are archived.

The final census uses `Effect4.Stores` and imports `CompletionData`; the baseline
used plain `aesop` in its full-tree scratch environment. These are different search
environments, so this receipt claims no bank improvement caused by the rewrites.
All 82 final searched terms report only `propext` / `Quot.sound` (or no axioms).
This is census dependency evidence, not a new full AxiomGate result over every
stored declaration. Packaging ran no compiler and changed no live source.
