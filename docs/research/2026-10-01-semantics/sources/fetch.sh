#!/bin/sh
# Refetch the new downloads of seat A (2026-10-01). Run from this folder; then
# `shasum -a 256 -c SHA256SUMS`. Every URL is an author's page, an institutional
# repository, arXiv, or the book's own site. See README.md for each file's terms.
set -e
curl -fL -o tapl-contents.pdf https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf
curl -fL -o attapl-frontmatter.pdf https://www.cis.upenn.edu/~bcpierce/attapl/frontmatter.pdf
curl -fL -o pfpl-2nded-abbrev.pdf https://www.cs.cmu.edu/~rwh/pfpl/abbrev.pdf
curl -fL -o plf.tgz https://softwarefoundations.cis.upenn.edu/plf-current/plf.tgz
curl -fL -o plotkin-pretnar-2009-handlers-of-algebraic-effects.pdf https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf
curl -fL -o pretnar-2015-introduction-to-algebraic-effects-and-handlers.pdf https://www.eff-lang.org/handlers-tutorial.pdf
curl -fL -o bauer-pretnar-2015-programming-with-algebraic-effects-and-handlers.pdf https://arxiv.org/pdf/1203.1539
curl -fL -o castagna-2024-programming-with-union-intersection-negation-types.pdf https://arxiv.org/pdf/2111.03354
curl -fL -o leroy-2009-formal-verification-of-a-realistic-compiler.pdf https://xavierleroy.org/publi/compcert-CACM.pdf
curl -fL -o ahmed-2004-semantics-of-types-for-mutable-state.pdf https://www.ccs.neu.edu/home/amal/ahmedsthesis.pdf
curl -fL -o ahmed-dreyer-rossberg-2009-state-dependent-representation-independence.pdf https://www.ccs.neu.edu/home/amal/papers/sdri.pdf
curl -fL -o jung-et-al-2015-iris.pdf https://iris-project.org/pdfs/2015-popl-iris1-final.pdf
curl -fL -o meijer-fokkinga-paterson-1991-bananas-lenses.pdf https://maartenfokkinga.github.io/utwente/mmf91m.pdf
curl -fL -o rendel-ostermann-2010-invertible-syntax-descriptions.pdf https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf
curl -fL -o lynch-vaandrager-1995-forward-and-backward-simulations.pdf https://ir.cwi.nl/pub/1393/1393D.pdf
curl -fL -o de-vilhena-pottier-2021-separation-logic-for-effect-handlers.pdf https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf
curl -fL -o wadler-2012-propositions-as-sessions-icfp.pdf https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf
curl -fL -o wadler-2014-propositions-as-sessions-jfp.pdf https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions-jfp.pdf
curl -fL -o mcbride-2008-clowns-to-the-left-of-me.pdf https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf
curl -fL -o petricek-orchard-mycroft-2014-coeffects.pdf https://www.doc.ic.ac.uk/~dorchard/publ/coeffects-icfp14.pdf
curl -fL -o pickering-gibbons-wu-2017-profunctor-optics.pdf https://arxiv.org/pdf/1703.10857
curl -fL -o gibbons-2002-calculating-functional-programs.pdf https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/acmmpc-calcfp.pdf
