"""Record the inspected source versions; no proof status is inferred."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('upstream', type=Path)
parser.add_argument('--effect4', type=Path, required=True)
args = parser.parse_args()
root = args.upstream.resolve()
repo = args.effect4.resolve()

def git(path, *argv):
    return subprocess.check_output(['git', '-C', str(path), *argv], text=True).strip()

def pin(path, base):
    raw = path.read_bytes()
    return {'path': str(path.relative_to(base)), 'bytes': len(raw),
            'sha256': hashlib.sha256(raw).hexdigest()}

notes = []
for path in sorted((root / 'lean/docs').glob('*.md')):
    text = path.read_text()
    title = next((line[2:] for line in text.splitlines() if line.startswith('# ')), path.stem)
    specs = re.findall(r'\]\(\.\./ComparatorChallenges/([^\s)]+\.lean)\)', text)
    notes.append({'id': path.stem, 'title': title, 'comparators': specs, **pin(path, root)})
configs = []
for path in sorted((root / 'lean/ComparatorChallenges').glob('*.json')):
    data = json.loads(path.read_text())
    configs.append({'path': str(path.relative_to(root)),
                    **{k: data.get(k) for k in ('challenge_module', 'solution_module', 'theorem_names',
                                               'permitted_axioms', 'enable_nanoda')}})
selected = [
 'lean/README.md', 'lean/lean-toolchain', 'lean/lakefile.lean', 'lean/formalization.yaml', 'LICENSE',
 'lean/ComparatorChallenges/README.md',
 'lean/OAI/Combinatorics/SnakyCertificate/Lists.lean',
 'lean/OAI/Combinatorics/SnakyCertificate/Invariants.lean',
 'lean/OAI/Combinatorics/SnakyCertificate/Equations00.lean',
 'lean/OAI/Combinatorics/SnakyCertificate/Main.lean',
 'lean/OAI/Combinatorics/ThinTrees/Encoding/GreedyTree.lean',
 'lean/OAI/Combinatorics/ThinTrees/Encoding/AlgorithmicMain.lean',
 'lean/OAI/Combinatorics/ParityLifts/GraphIso.lean',
 'lean/OAI/Combinatorics/ParityLifts/Model.lean',
 'lean/OAI/Combinatorics/PlanarL1/Embedding.lean',
 'lean/OAI/Combinatorics/TreewidthL1/Main.lean',
 'lean/OAI/Computability/Scheduling/RegisterMachine.lean',
 'lean/OAI/Computability/Scheduling/Main.lean',
 'lean/OAI/Combinatorics/UniformKServer/Main.lean',
 'lean/ComparatorChallenges/RandomizedMeanPayoff.lean',
 'lean/ComparatorChallenges/LogspaceEquality.lean',
 'lean/OAI/Optimization/Tropical/TruffetCounterexample.lean',
]
# Keep missing path reporting explicit rather than manufacturing a source pin.
present = [p for p in selected if (root / p).is_file()]
effect4 = [
 'lean-toolchain', 'src/Effect4/Program/TyFoldExtras.lean',
 'tools/Tools/View/AlgGraph.lean', 'tools/Tools/View/Flow.lean',
 'tools/Tools/View/FlowLaws.lean', 'tools/Tools/View/Graph.lean', 'tools/Tools/View/Run.lean',
 'tools/ProofGraph/Proof.lean', 'tools/ProofGraph/Axioms.lean', 'tools/ProofGraph/Plan.lean',
 'tools/ProofGraph/AxiomAudit.lean', 'docs/core/semantics.md',
 'docs/research/2026-10-09-program-graph-design.md',
]
output = {
 'upstream': {'remote': 'https://github.com/openai/math', 'commit': git(root, 'rev-parse', 'HEAD'),
              'toolchain': (root / 'lean/lean-toolchain').read_text().strip()},
 'effect4': {'commit': git(repo, 'rev-parse', 'HEAD'),
             'toolchain': (repo / 'lean-toolchain').read_text().strip(),
             'working_tree_sources': [pin(repo / p, repo) for p in effect4 if (repo / p).is_file()]},
 'review_base': git(Path.cwd(), 'rev-parse', 'HEAD'),
 'counts': {'scope_notes': len(notes), 'comparison_configs': len(configs),
            'configs_permitting_choice': sum('Classical.choice' in (c['permitted_axioms'] or []) for c in configs),
            'configs_enabling_nanoda': sum(c['enable_nanoda'] is True for c in configs)},
 'selected_sources': [pin(root / p, root) for p in present],
 'missing_selected_sources': [p for p in selected if p not in present],
 'notes': notes, 'comparators': configs,
 'evidence_limit': 'Inventory and source inspection only; no upstream build or comparator run.',
}
print(json.dumps(output, indent=2, ensure_ascii=False))
