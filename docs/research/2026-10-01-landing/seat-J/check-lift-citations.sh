#!/usr/bin/env bash
# Seat J, step 1: every Machine/Fibers.lean range Lift.lean cited at 75ee115c (where the citations
# were written) against the range 27 lines lower in the working tree. Run from the worktree root.
set -euo pipefail
old=$(mktemp)
git show 75ee115c:src/Effect4/Machine/Fibers.lean > "$old"
new=src/Effect4/Machine/Fibers.lean
same=0; differ=0
for pair in 1798-1799:1825-1826 1838-1851:1865-1878 2003-2003:2030-2030 2009-2016:2036-2043 \
            2015-2016:2042-2043 2045-2048:2072-2075 2076-2076:2103-2103 2090-2091:2117-2118 \
            2096-2097:2123-2124 2098-2106:2125-2133 2108-2108:2135-2135 2161-2173:2188-2200; do
  o=${pair%%:*}; n=${pair##*:}
  if diff <(sed -n "${o%-*},${o#*-}p" "$old") <(sed -n "${n%-*},${n#*-}p" "$new") > /dev/null; then
    echo "same    75ee115c :$o    now :$n"; same=$((same + 1))
  else
    echo "DIFFER  75ee115c :$o    now :$n"; differ=$((differ + 1))
  fi
done
for f in src/Effect4/Laws/Program/Guard/AnswerDecision.lean:94-112 src/Effect4/Laws/Program/RuntimeR.lean:51-54; do
  p=${f%%:*}; r=${f##*:}
  if diff <(git show "75ee115c:$p" | sed -n "${r%-*},${r#*-}p") <(sed -n "${r%-*},${r#*-}p" "$p") > /dev/null; then
    echo "same    $p:$r (unmoved)"; same=$((same + 1))
  else
    echo "DIFFER  $p:$r"; differ=$((differ + 1))
  fi
done
rm -f "$old"
echo "same=$same differ=$differ"
test "$differ" -eq 0
