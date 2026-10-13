# What the evidence means

This guide explains how to interpret formal evidence across Effect4. It covers theorems, planned goals, theorems proved modulo goals, the trust ceiling on axioms, and why claims restrict to explicit fragments and observations.

## The standard of proof {#proof-standard}

Effect4 states its runtime semantics as Lean definitions. Every claim in the semantics registry names the theorem that states it (`tools/ProofGraph/Registry.lean`).

No status is written by hand. The semantics report reads each theorem's proof in the built Lean environment and derives its status: proved, modulo or a planned goal.

## Theorems and verified claims {#theorems}

A theorem is a Lean declaration whose type is a proposition, accepted by the kernel within the trust ceiling.

When a claim points to a theorem whose proof depends on no planned goals, the site marks the claim {proved}.

A proved theorem guarantees its conclusion whenever its hypotheses hold. However, theorems remain conditional on stated premises and do not establish facts outside their formal boundaries.

## Planned goals and open obligations {#planned-goals}

A planned goal is a theorem declared by `proof_goal` with a `sorry` body. It places a question in the theory before its proof exists (decisions row 203).

The site marks a claim that points to such a declaration as a {goal}.

Planned goals allow developers to state and verify downstream theorems before completing upstream proofs. Having no open planned goals does not mean the semantics is finished.

## Proofs modulo planned goals {#proofs-modulo}

A theorem is proved modulo when its proof path reaches one or more planned goals. The site marks claims backed by such theorems as {modulo}.

A theorem proved modulo:
- is checked by the kernel now, with each goal it uses taken as given;
- becomes proved, with no change to its own proof, once every goal it rests on is proved;
- names the goals it rests on, which `#plan_status` lists.

The open work part of the semantics pages lists each planned goal and the theorems that rest on it.

## The trust ceiling on axioms {#trust-ceiling}

The repository enforces a strict trust ceiling on all proof declarations. The allowed axioms are `propext` (propositional extensionality) and `Quot.sound` (quotient soundness).

An automated axiom gate checks every declaration in `Effect4` and `Test`:
- The gate rejects `sorry` outside declared planned goal bodies.
- The gate rejects `partial`, `unsafe`, and `native_decide`.
- The gate rejects undeclared axioms, `extern`, and bodyless `opaque` constants.

So a proved claim rests on Lean's kernel and those two axioms, and on no postulate of the repository.

## Fragments and observations {#fragments-and-observations}

No theorem in Effect4 relates two behaviours without naming the observation it compares. Each such theorem also names the fragment of programs it holds on.

A fragment defines a restricted set of programs or tapes where a theorem applies:
- `Straight` (`src/Effect4/Program/Fragment.lean`) admits sequencing, failures and their handlers, `select`, and synchronous steps and rows. It leaves out loops, fibers, uninterruptible regions, scopes, services and yields.
- `Looped` (`src/Effect4/Laws/Program/FragmentLooped.lean`) is `Straight` with `iterate`.
- `M7Fragment` (`src/Effect4/Laws/Program/Typed/Assembly.lean`) takes a lawful source with an empty row table and a checked program with an empty requirement row. Its tape holds no host answer.

An observation is the part of a run that a theorem compares, such as the exits and the stores. An equal-observation theorem says that two behaviours give the same observation on every program of its fragment.

Equal observations do not imply that underlying runtime states are identical. Restricting claims to explicit fragments and observations prevents unjustified generalizations.

## What evidence does not claim {#evidence-boundaries}

A formal proof establishes exactly what its proposition states, subject to four strict boundaries:
- A conditional theorem leaves its premises open until separate lemmas discharge them.
- An invariant establishes safety, but an invariant does not prove progress or liveness.
- An equal-observation theorem holds only on its stated fragment and leaves unexamined behaviors open.
- The host boundary stays where `docs/core/host-boundary.md` puts it: no theorem says that the host answers, or answers in time.

Readers must inspect the formal proposition to identify the hypotheses, fragment, and observation governing each claim.
