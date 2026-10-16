import Effect4.Laws.Api.SessionRef
import Effect4.Laws.Program.HeapSites

/-!
# Run.CallMap — every host request of a run is performed at a site of its program

The program graph is the address table of a program (`Node.addresses`), and a site census is a
`filterMap` over it. `HeapSites.performSites` lists each `perform` node with its address, row,
request term and level. This module joins that static census to the run: each request a funded,
recorded run holds is the request of a listed site (`request_performed`).

So a generator may compute from the program alone what is written by hand today:

- the call map of a built program (dogfood friction F10): the sites with their checked instance,
  `HostSession.callTable` at each address;
- the rows a host must answer: the rows of the sites, since no run asks another.

Placement (`AGENTS.md`, five points):

1. Concept `host-session-protocol` (concept 9 of `docs/core/semantics.md`), the property that the
   static site census bounds the dynamic calls of a run.
2. Question: the proposed claim `performed-rows`, role preservation, pointer `request_performed`.
3. Reach: every recorded, funded run of every built program and table.
4. Does not establish: that a site is reached, the call's checked instance (the claim
   `reply-at-call-instance` owns it), or that the expansion of layer references keeps a call at
   its address.
5. Unlocks: a generated call map and a host restricted to the program's rows (R6).
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program

/-- **Every host request of a run is performed at a site of its program.** A recorded, funded
run's request, at any fiber and guard token, is the operation of a `perform` node that the site
census lists. Placement: concept `host-session-protocol`, the proposed claim `performed-rows`,
role preservation; requirement R6. Route: the request's frame holds its origin
(`requestOf_current`), the origin addresses a `perform` node of the operation
(`origin_addresses_call`), and the census lists every such node (`performSites_complete`).
Consumer: a generated call map and a host restricted to the program's rows (dogfood friction
F10). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem request_performed (s : Run) (recorded : Run.Reached s) (h : funded s = true)
    (fiber : FiberId) (token : Nat) (op : NativeOp) (request : Val)
    (hreq : requestOf s.machine fiber token = some (op, request)) :
    ∃ path term level, (path, op, term, level) ∈ HeapSites.performSites s.built.program := by
  obtain ⟨f, controller, cancel, o, hf, hp, hcur⟩ := requestOf_current _ _ _ _ _ hreq
  have ho : originOf s.machine fiber token = some o := by
    simp only [originOf, hf, hp, hcur, guard, Option.bind_eq_bind, Option.bind_some, if_true]
    rfl
  obtain ⟨term, hat⟩ :=
    origin_addresses_call s recorded h fiber token op request o hreq ho
  exact ⟨o, term, _, HeapSites.performSites_complete hat⟩

end Effect4.Run
