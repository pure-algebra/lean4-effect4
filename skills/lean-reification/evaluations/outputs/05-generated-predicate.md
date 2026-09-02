# Generated admission predicate: verification plan

The deliverable is the entire executable TypeScript admission predicate, generated from the Lean-owned definition and all executable definitions it depends on. Generating twelve examples and maintaining a second recursive implementation by hand does not deliver that counterpart. Keep those examples as possible test inputs; replace the handwritten predicate with the generated artifact.

This is a documentation-only plan. The observations below come from the exercise. No implementation, proof, generator, diagnostic tool, or host case was run for this report. Proposed artifact names and obligation IDs below are planning labels, not claims that those files or theorems exist.

## 1. Freeze the requested correspondence

Let A be the frozen Lean admission predicate and D its raw input domain. D includes inputs A rejects; proving correspondence only for already accepted inputs would leave false acceptance unexamined. Let Rraw(d, x) relate a Lean raw input d to its TypeScript representation x.

Rraw must retain all four root constructors, every recursive child, the document root, and the full ordered reference table. It also retains duplicate entries, reference identities, and missing versus present-empty annotation bags. Use ordered entry data for tables and bags that permit duplicate keys; an ordinary object or Map must not silently replace that representation. Do not normalize away these distinctions before admission. If a transformation needs normalization, it needs a separate declared relation and must not masquerade as exact raw representation.

The main obligation is: for every d in D and every related x, the generated predicate returns exactly A(d), under the declared target execution model. This requires both true-result agreement and false-result agreement. It rules out both accepting an input Lean rejects and rejecting an input Lean accepts. The target observation is the returned Boolean, normal return rather than an unexpected exception, and absence of mutation of the supplied raw data. Record host resource limits separately from mathematical termination.

Copy actual constructor names, field types, aliases, overloads, entry points, and helper declarations from the canonical source before implementing. The case supplies four constructors but not their names; no new names or meanings are being inferred here. Preserve the whole requested domain. An extraction failure must name the unsupported source construct and stop generation; it must not silently narrow the predicate to the twelve examples.

Any adapter for JavaScript values outside Rraw has a separate input policy. Its parse or representation rejection is not automatically the Lean predicate's refusal. Likewise, a finite table containing reference cycles must be treated according to the Lean profile, rather than accidentally rejected or traversed forever because the target follows host pointers.

## 2. Required artifacts and generation route

| Proposed artifact | Required contents and owner |
| --- | --- |
| Source binding record | Exact Lean declaration and transitive executable dependencies, source revision or dirty-source digest, toolchain, admitted profile, and the source-owned raw representation. The Lean admission owner controls this record. |
| Checked predicate description | First-order executable description derived from the canonical Lean definition, with all branch equations, recursive fields, and primitive operations accounted for. No separately handwritten semantic recursion. The source-to-description relation is an explicit obligation. |
| Typed target description | Inspectable target syntax for the generated predicate and its helpers. Unchecked text escapes are forbidden on this generation route or proved unreachable from it. |
| Generated TypeScript module | The callable whole predicate, required input bindings and helpers, and the promised exports. No fixture lookup implementation, placeholder branch, or manually maintained duplicate predicate. |
| Independent source census and join report | Each in-scope source constructor, field, helper, public alias or overload, and foreign-reference route joined to its target disposition and verification obligations. Construct this inventory independently of the generator's recursive walk. |
| Verification record | Exact source and target identities, regeneration entry point and arguments, certificates or proof receipts, analyzed file list, case list, versions, observations, and open assumptions. |

The implementation must provide one documented regeneration entry point. It takes the frozen source binding and declared configuration and produces the executable module plus deterministic descriptions and manifests. Regenerate in a clean temporary destination and compare bytes with the delivered artifacts. Record every input affecting those bytes. Regeneration establishes reproducibility; it is not the source-to-target correctness argument.

Use the following assurance route: prove the source-to-description relation, then perform per-artifact translation validation against the exact generated target. The translation validator must have an acceptance-implies-relation theorem. Its accepted certificate binds this source description to this parsed target and establishes predicate agreement for every related raw input, not just the tested examples. Rejected, timed-out, or incomplete validation leaves the obligation open. The generator remains automatic even though its outputs are independently validated.

This choice avoids claiming a universal verified compiler. A validator that checks only branch names, signatures, or byte determinism is insufficient: its acceptance theorem must cover the operations and recursive computation that determine A's result.

## 3. Transformation obligations

| ID and boundary | Required direction and evidence |
| --- | --- |
| GP-RAW: raw Lean data to target input | Establish Rraw over the entire chosen carrier, retaining the raw distinctions above. Check conversion in both directions where a round trip is claimed. Keep malformed external representation outcomes separate. |
| GP-SOURCE: A to first-order description | For every raw input, interpreting the emitted description produces A's Boolean. Bind the relation to the exact definitions and dependencies, not only A's signature. Extraction is allowed to fail explicitly, but successful generation of this entire promised predicate is required. |
| GP-TARGET: description to parsed target | Validator acceptance implies equality of predicate observations for all related inputs under the declared target semantics. Account for all reachable helpers, control paths, and primitive operations. Save the exact accepted pair and certificate. |
| GP-TEXT: target description to rendered bytes to parsed target | Relate the actual emitted text to the target validated by GP-TARGET. Establish correct parsing, quoting, binding names, and escaping in the admitted target grammar. A trusted or proved parser/renderer boundary must be named; an external parser's output is not automatically a proof about the bytes. |
| GP-HOST: emitted module to observed host execution | Typecheck and execute the exact generated file set at the pinned host, using an independently accounted-for corpus and observer. This is bounded host evidence unless a separate host implementation relation is supplied. |

For GP-TARGET, equality of the deterministic Boolean result is the intended observation. If target behavior is modeled as a set of possible runs, require every permitted target run to correspond to the source result; merely showing that one target run can return the right answer permits additional wrong behavior. Do not add scheduler or fairness obligations when this pure predicate has no such behavior.

Record permitted transitive logical dependencies for the Lean relations and validator theorem separately from compiler, parser, and runtime trust. A proof of the description's meaning does not prove that an unchecked renderer or JavaScript engine implements it.

## 4. Independently account for the whole recursive surface

The coverage inventory must be obtained without reusing the generator's traversal. Join exact source rows to target rows; fail on missing, duplicate, or unexplained extra rows. The source census is the closure check; a test count is not.

| Source route | Required accounting and distinguishing cases |
| --- | --- |
| Four root constructors | One exact inventory row for each source constructor and all its fields. Exercise an inhabited accepted form and applicable rejected boundary for each. A count of target switch statements is not a substitute for this join. |
| Check containing a list of checks | Visit every list element, recursively. Include empty and multi-element lists; put a rejecting child after an accepting child and at deeper positions so a first-child-only walk is exposed. |
| Check's separate optional annotation | Account for this field independently of the list of checks. Distinguish absent, present-empty, and present-with-nested-schema data. Place the decisive nested schema here while the checks list is otherwise harmless. |
| Filter's required annotation | Account for the required field and every contained nested schema. Test its valid empty or nonempty forms as the source permits, malformed absence, and nested refusal cases independently of check annotations. |
| Document root | Evaluate the root through every applicable constructor and nested route. |
| Ordered reference table | Account for every stored row, including rows unreachable from the root. Put decisive nested data in later and unreachable rows. Exercise forward, missing, or cyclic references only as admitted by the frozen source rules; do not replace the whole table with a root-reachability projection. |
| Duplicate keys and order | Retain both copies of duplicate entries and their order in the target input and observers. Use entries with different nested contents to expose accidental deduplication or first/last-entry substitution. |
| Missing versus present-empty bags | Retain and observe the distinction even if some inputs happen to receive the same Boolean. Do not invent a rejection rule merely because the representations differ. |
| Aliases, overloads, helpers, and admitted foreign references | Inventory the actual reachable source declarations and public surface. Foreign identities must bind to stated types, capabilities, and behavior assumptions; an unexplained target callback is an open boundary. |

Expected acceptance comes from the frozen Lean predicate, not an assumption that every duplicate, empty bag, or unreachable entry is invalid. The generated counterpart must reproduce the source rule over that data. Raw preservation and traversal accounting remain necessary even where two cases receive the same Boolean.

Use direct evaluation of A on independently constructed inputs as the source oracle, together with explicit witnesses tied to individual contract rules. The TypeScript observer must call the generated predicate on the corresponding raw inputs, rather than a generated list of expected answers. Check exact case identities and counts on both sides. The current common traversal for cases and expectations can omit the same field twice and still agree.

Future mutation checks should independently try a constant-false predicate, a constant-true predicate, an omitted root branch, skipping the second check, ignoring optional annotations, ignoring filter annotations, dropping an unreachable reference row, and merging duplicate entries. Where a mutation changes only raw identity rather than a Boolean, the raw observer or structural relation must catch it. Each mutation must reach the intended detector, fail there for the intended reason, and be followed by an accepted restored control. Do not credit an earlier parse or build failure as a later detector's success.

## 5. Repair the annotation update claim

The supplied codec establishes decoding after encoding returns the value. It does not establish encoding after decoding returns the original raw spelling.

The counterexample is already decisive: decoding `long` gives the same value as decoding `short`; encoding that value gives `short`. Thus encoding the decoding of `long` changes the raw input. The law “put back the value just read and retain the original entry” fails if put is implemented as decode followed by encode. This is a consequence of the supplied equations, not a newly executed test.

For the requested unchanged-value behavior, retain the original raw entry and its spelling alongside the decoded view. When an update supplies the same value under the declared value equality, return the original entry unchanged. Preserve surrounding entry order, duplicates, annotation presence, and untouched fields. For changed values, define the permitted reconstruction policy separately; canonical encoding can be appropriate there only within that declared policy.

The codec/view owner must discharge these distinct obligations:

- Decoding an encoding returns the intended value on the codec's value domain; retain the supplied proof and its exact scope.
- Encoding an accepted decoding yields the declared canonical form, if that is the codec claim. Prove normalization idempotence on its stated domain. Do not call this raw identity.
- Putting back the value read from an accepted raw entry returns that exact entry, including `long`.
- Reading after a permitted changed-value update returns the requested value, while the agreed surrounding raw content remains unchanged.
- If the API advertises further update laws, such as equality of sequential and final updates, state and prove them separately. Preserving an unchanged value alone does not establish all such laws.

Keep both spellings in the directional test corpus. Test unchanged updates starting from each spelling. Restricting the raw domain to `short` would evade the requested preservation of accepted `long` entries; it is not the repair chosen here.

## 6. Make diagnostics and host acceptance observable

The reported language-service run analyzed zero input files. Its zero diagnostics do not establish anything about the generated module. Treat this as an evidence failure, not a successful validation.

Before accepting a future diagnostics result, require a nonempty analyzed program whose exact file list and digests match the expected generated entry points and helper files. Check actual inclusion, not merely the existence of files on disk. Record the diagnostic provider, configuration, detected version, and result. A deliberately incorrect generated-file control must trigger the intended diagnostic provider; restoring the file must return to the expected clean result. If both compiler diagnostics and another language-service provider are required, validate their inclusion and controls independently.

Pin the Lean source and toolchain, generated bytes, TypeScript compiler and relevant options, runtime, effective installed host package bytes, diagnostic provider, profile, and oracle inputs separately. An upstream tag alone does not identify the package bytes actually loaded by the harness. Record the exact executed case set and observations against the emitted module. Include nested and resource-boundary inputs appropriate to the admitted carrier; finite successful runs do not prove freedom from host stack or memory limits on every input.

The reference example needs two explicit acceptance records:

| Layer | Supplied observation | Legitimate description |
| --- | --- | --- |
| Document codec | Accepts the reference | Document-codec acceptance for that input. |
| Revival API | Rejects the reference | Revival rejection for that input under the chosen host profile and registry. |

Replace the release note's shared “host accepted” label with those separate observations. Test the accepted and rejected reference cases at each actual API. Codec acceptance is not evidence of revival, parsing, validation, or application success. Do not silently shrink the Lean predicate's domain to the host revival domain to make a comparison pass. If correspondence with revival is separately promised, define that relation and close the reference mismatch under the relevant authority.

## 7. Completion and claim limits

The target owner can close the generated-counterpart work only when the executable module is generated from the exact canonical definition, the independent source census accounts for the whole requested surface, required source/target relations have receipts, and the documented regeneration reproduces the delivered bytes. The host owner separately closes the exact file/case checks, nonempty diagnostics, and bounded runtime comparisons. The annotation owner closes the requested raw-update laws. Release wording must reflect those separate results.

After those obligations close, an appropriate report would say which generated predicate agrees with which Lean definition over which raw domain, identify the exact relation and its proof or accepted validation certificate, and state the pinned host cases that matched. It must also name any unproved parser, transpiler, runtime, or foreign-reference connection. Per-artifact validation does not prove correctness of every future compiler output; a checked artifact can nevertheless have a universally quantified relation over its modeled input domain. Host tests remain bounded by their cases, observations, versions, and resource conditions.

This work does not, by itself, reify arbitrary TypeScript programs, establish agreement with every host API, or authorize retirement of a source owner. The requested automatic whole-predicate scope remains intact.

The source declaration names, revisions, installed hashes, and executable command names were not supplied. They must be bound in the implementation record before running the gates; none is invented here. This missing execution context does not block the documentation plan.

## Skill and reference files used

- `/Users/pooks/Dev/lean4-effect4/skills/lean-reification-target/SKILL.md`
- `/Users/pooks/Dev/lean4-effect4/skills/lean-reification-target/references/boundaries.md`

Applicable `/Users/pooks/Dev/lean4-effect4/AGENTS.md` and `/Users/pooks/Dev/lean4-effect4/COORDINATION.md` were also read. The exercise's explicit documentation-only authorization controls the work performed. No workflow ambiguity prevented producing this plan.
