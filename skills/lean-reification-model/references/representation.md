# Representation decisions

## Content, semantics, and execution

Make the data retained by each carrier explicit. Durable content needs a
declared language for operands, values, code locations, captures, and foreign
references. The proof carrier may use Lean functions even when the content
carrier cannot. The interpreter may use host state even when the content does
not store it. Each boundary needs a relation, not an assumed identity.

For a first-order representation of higher-order programs, choose an explicit
binder/capture strategy: de Bruijn indices, typed variables, named definitions
with checked environments, or another existing project mechanism. State scope,
substitution, capture avoidance, and renaming obligations. A string naming a
closure is insufficient unless its code and capture layout are bound to a
stable, checked definition.

For scoped effects, identify body, handler, exit, cleanup, and continuation
regions. Record which environment is captured and which handler is active at
each continuation. Specify whether resumption is one-shot or multi-shot and
what protects resources if it is duplicated. Named blocks can keep these
children first-order; they still need adequate execution semantics.

## Raw and checked forms

Retain malformed states at ingress when they are needed to explain refusal.
Do not destroy duplicates, order, or missing/empty distinctions before the
checker has applied their policy. Separate field typing, graph reference
closure, profile membership, reachability, and well-foundedness: one does not
imply the others.

Unreachable blocks can still matter to canonical identity, source coverage,
and whole-document reference closure. A reachable-only evaluator does not
provide a complete document validator. Whether dead closed blocks or cycles
are admitted is a contract choice, not an optimization assumption.

Specify `erase`, successful `admit`, and the reconstruction law actually
required. A canonicalizing validator may satisfy a normalized reconstruction
law rather than exact raw equality. State what valid input it can reject.

## Recursion and Lean

An inductive program with continuation functions is well founded but can have
infinitely many branches when answers range over an infinite type. Do not
claim a finite total node count from the word “inductive.”

A finite graph can contain cycles and represent unbounded execution. Describe
its behavior through a suitable step/run relation or a justified semantic
domain. A bounded interpreter can supply observations and counterexamples;
fuel exhaustion leaves a live computation rather than proving divergence.
In a nondeterministic system, arbitrarily long finite runs do not automatically
select one compatible infinite run; state the compatibility and existence
argument needed by the chosen domain.

At the reviewed Lean reference version, coinductive predicates are distinct
from native coinductive data. A library encoding is an additional representation
with its own toolchain, dependencies, productivity, equivalence, and trust
obligations. Do not import a different tree package solely because it has a
similar name. [Lean recursion reference](https://lean-lang.org/doc/reference/4.33.0/Definitions/Recursive-Definitions/).

Check universe levels at the consumer interface. The operation universe,
answer universe, program result, and handler target cannot be independently
changed without checking the full signature. An explicit lift or adapter needs
typing and coherence evidence; a local `Type` abbreviation can conceal a
restriction the intended public API cannot use.

## Worked distinction

A stored workflow says “read a value, then run a callback.” A Lean free program
with a function-valued continuation may prove composition laws. To store that
workflow, represent the continuation's code and environment as data and give
the read instruction a checked successor/capture map. Prove the selected
interpretation agrees on the admitted callback language. Unsupported callbacks
must be explicit refusals or registered host boundaries. The free-program
theorems do not supply that conversion.
