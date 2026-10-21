#!/bin/sh
# Fetch the open-access sources of the view-graph note into pdf/. Never committed; the index is.
set -e
cd "$(dirname "$0")/pdf"
get() { [ -f "$2" ] || curl -sSL -o "$2" "$1"; }
get https://arxiv.org/pdf/0908.3347 selinger-2010-string-diagrams-survey.pdf
get https://arxiv.org/pdf/1502.00872 fong-2015-decorated-cospans.pdf
get https://arxiv.org/pdf/1504.05625 baez-fong-2015-passive-linear-networks.pdf
get https://arxiv.org/pdf/1602.06771 bonchi-sobocinski-zanasi-2016-rewriting-modulo-smc.pdf
get https://www.lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-360/ECS-LFCS-97-360.pdf hasegawa-1997-models-of-sharing-graphs.pdf
get https://raw.githubusercontent.com/snowleopard/alga-paper/master/paper.pdf mokhov-2017-algebraic-graphs-with-class.pdf
get https://arxiv.org/pdf/1312.1399 plotkin-pretnar-2013-handling-algebraic-effects.pdf
get https://arxiv.org/pdf/1910.11629 ahman-bauer-2020-runners-in-action.pdf
