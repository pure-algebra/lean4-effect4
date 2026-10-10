# Row protocol review plan

## Scope and finish criteria

Review `b98d81c33ffa1721fe61b23d38d167b6e0dd9eca` after checkpoint `8a613615`.
Keep production files, owner rulings, and Claude's session unchanged.

- Pin the changed module and its semantics registry links.
- Build the frozen module in the existing isolated artifact overlay.
- Apply its transfer law and H9 to the recorded two-call example.
- Check admitted data, refused data, a checked-instance reply, and a handle allocation request.
- Audit every declaration of the new module with the exact axiom walk.
- Check the semantics registry, import direction, and actual consumers.
- Read the two independent source reviews.
- Record evidence and limits in one review receipt.

## Placement

| Check | Concept and claim | Consumer and reach |
| --- | --- | --- |
| Guarded two-call run | translation-simulation; `rows-denotation-host`, R6 | H9 reader with admitted answers and final host state |
| Row admission controls | host-session-protocol; `reply-at-call-instance`, R6 | next typed-host interface; current template check versus checked-instance admission |
| Allocation control | host-session-protocol; existing handle admission boundary, R6 | description of raw replies; no handle simulation claim |
| Dependency audit | trust of the two named claims | new module declarations and their exact transitive axioms |

These are readers and controls for existing obligations.
They add no production theorem or planned goal.
They establish no progress, physical-host result, or arbitrary session admission guarantee.
