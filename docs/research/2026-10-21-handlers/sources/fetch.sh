#!/bin/sh
# Fetch the open-access sources of the handlers note into pdf/. Never committed; the index is.
# Two copies are shared with the view-graph note (`docs/research/2026-10-21-view-graph/sources/`).
set -e
cd "$(dirname "$0")/pdf"
get() { [ -f "$2" ] || curl -sSL --max-time 90 -o "$2" "$1"; }
get https://arxiv.org/pdf/1312.1399 plotkin-pretnar-2013-handling-algebraic-effects.pdf
get https://arxiv.org/pdf/1910.11629 ahman-bauer-2020-runners-in-action.pdf
get https://homepages.inf.ed.ac.uk/gdp/publications/Combining_Effects.pdf hyland-plotkin-power-2006-combining-effects.pdf
get https://homepages.inf.ed.ac.uk/gdp/publications/tensors_of_comodels.pdf plotkin-power-2008-tensors-of-comodels.pdf
get https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf wu-schrijvers-hinze-2014-effect-handlers-in-scope.pdf
