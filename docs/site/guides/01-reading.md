# How to read the site

This guide explains how to read the documentation site. It describes what each page holds, how status marks work, how keys connect parts, and how tools inspect JSON artifacts.

## What a page holds {#page-structure}

Every page presents one topic with structured text. A page belongs to a site category such as guides, semantics, or the specimen.

Each page provides three formats:
- An HTML view rendered through a typed content shell.
- A Markdown file named `index.md` for text readers.
- A JSON document named `document.json` for machine tools.

The site derives pages from the loaded Lean environment and written Markdown sources. Generated pages show evidence from the repository, while written guides explain design principles.

## Status words and marks {#status-marks}

The site uses status words to communicate evidence. Each status word renders with a distinct visual mark in the interface:
- {proved}: A theorem accepted by the Lean kernel within the trust ceiling.
- {modulo}: A theorem whose proof reaches one or more planned goals.
- {goal}: A planned goal whose proof is admitted with `sorry`.
- {open}: A requirement or task with unfinished obligations.
- {refuted}: A statement that a registered counterexample refutes.
- {absent}: A property with no declaration or goal, accompanied by a stated reason.
- {assumed}: A condition taken as an external assumption.

These words keep evidence kinds distinct. A reader inspects the assigned mark to determine whether a claim rests on verified proofs or pending goals.

## Keys and cross references {#keys}

A part of a page carries a unique anchor key. Headings define keys either from explicit attributes or from normalized title text.

A link refers to a key on the same page or across pages:
- An anchor link points to a key using a hash prefix.
- A relative link points to another page directory.
- A claim key references a specific semantics claim in the registry.

These keys allow readers and tools to cite exact parts without relying on line numbers.

## The open work {#open-work}

The open work part of the semantics pages lists every open planned goal and every theorem proved modulo goals.

Each entry gives three things:
- The declared goal statement in Lean.
- The module and requirement that own the obligation.
- The docstring explaining why the proof waits and which consumer needs it.

Dependency chains show how higher milestones depend on open goals. Readers trace these chains to see the remaining verification steps.

## Figures and code blocks {#figures}

A figure draws a requirement's open work as a graph (decisions row 365). Its nodes are the planned goals and the theorems proved modulo them. An arrow goes from a node to a node its proof reaches first. Each node links to its claim or goal, and its mark gives its status.

Below each figure, the figure in words lists every node with its status and the nodes it points to. It serves a reader who does not see the picture, and a screen reader names the figure by its caption.

A code block shows a Lean statement or a definition. A statement longer than eight lines folds under its first line, and opens on demand (decisions row 366).

## Navigation and the margin {#navigation}

The site provides navigation elements across every page. The top header displays major areas and breadcrumbs for the current path.

The margin presents the parts list of the current page under the heading On this page. Readers select an entry in the margin to jump directly to that subsection.

The bottom of each page links to the previous and next pages in the sequence. A dedicated contents page indexes every document across the site.

## Reading the site as JSON {#json-records}

Machine agents read the site through structured JSON files. Every page directory contains a `document.json` file conforming to the `effect4-document/1` format.

The root provides two additional JSON resources:
- `site.json`: An index containing page paths, titles, group memberships, and part keys.
- `semantics/report.json`: The whole semantics report data emitted by the semantics driver.

An automated agent parses these JSON files directly to verify claims, inspect dependency graphs, and follow part references.
