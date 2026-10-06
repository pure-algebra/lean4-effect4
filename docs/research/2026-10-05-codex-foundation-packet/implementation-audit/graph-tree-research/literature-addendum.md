# Execution histories, internal steps and scheduling

These are research connections, not imported theorems. No semantic representation changes.

## Lynch and Vaandrager: use histories when states merge

Source: [Forward and Backward Simulations, Part I](https://ir.cwi.nl/pub/1393), 1995.
Read the local retained paper, section 3.2 and section 6.
Lemma 3.8 lifts a forward simulation along an execution fragment.
Proposition 3.9 composes forward simulations; Theorem 3.10 gives trace inclusion.
Proposition 3.12 states a special result when the source automaton is a forest.
Section 6 allows invariants that restrict the relevant states.

Application: journal histories have a prefix-tree structure even when their resulting machine states merge or revisit earlier states.
Keep the existing `List Command` journal. A cut or fork uses a prefix of that same data.
Use `Run.play_append` to connect a prefix result to the remaining commands.
Do not infer that the machine graph is a forest because `Eff` is a syntax tree.
The paper's hypotheses and observations need an explicit connection before its result can be used here.
This suggests proof organization, not a new execution engine or a proof of fairness.

## Interaction Trees: state relations justify hidden implementation steps

Source: [Xia et al., Interaction Trees](https://arxiv.org/pdf/1906.00046), sections 5 and 7, figures 18 and 20.
The compiler example relates source state to target memory and registers after interpreting their different events.
Its structural proof rests on that relation and the library's behavioral laws.
The trace presentation distinguishes a partial trace, a return and an unanswered event.
Finite prefixes alone do not establish divergence.

Application: a module expansion introduces private cells, hints and cleanup work.
Its public law needs a relation for those states and an observation that explicitly hides only admitted details.
Existing synchronous `Projects` laws can support this connection; they do not supply the scheduled wrapper relation.
The current semantic `Effects.Program` is inductive. It is not the paper's coinductive ITree datatype.
Use the paper's proof technique without replacing `Eff` or claiming its theorems already apply.

## Choice Trees: a scheduler is more than a syntax fold

Source: [Chappe et al., Choice Trees](https://arxiv.org/pdf/2211.06863), sections 3.1, 5.2, 7.1–7.2.
The paper separates internal choice from external events.
Its concurrency example uses a custom interpreter over a thread pool.
Section 7.2 limits some post-scheduling equations to runs without additional concurrent threads.

Application: a shared constructor law does not automatically give a contextual scheduling law.
Queue's posted delivery and Semaphore's live scan need their own policy premises and observations.
Do not erase a yield or posted step merely because it leaves one isolated run's result unchanged.
Keep scheduling choices explicit; a selected scheduler proves no fairness property by association.
No CTree carrier or scheduler rewrite is proposed.
