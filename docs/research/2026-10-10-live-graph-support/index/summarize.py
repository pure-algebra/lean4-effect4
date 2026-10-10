"""Derive benchmark medians from retained Lean output."""
import csv
import json
from pathlib import Path
import statistics

HERE = Path(__file__).resolve().parent
rows = list(csv.DictReader((HERE / 'benchmark.log').read_text().splitlines(), delimiter='\t'))
results = []
for mode in sorted({r['mode'] for r in rows}):
    for n in sorted({int(r['items']) for r in rows}):
        values = {}
        for implementation in ['reference', 'indexed']:
            samples = [int(r['nanoseconds']) for r in rows
                       if r['mode'] == mode and int(r['items']) == n
                       and r['implementation'] == implementation]
            assert len(samples) == 3
            values[implementation] = statistics.median(samples)
        results.append({'mode': mode, 'items': n,
                        'reference_median_ms': round(values['reference'] / 1e6, 3),
                        'indexed_median_ms': round(values['indexed'] / 1e6, 3),
                        'ratio': round(values['reference'] / values['indexed'], 2)})
report = {'samples_per_pair': 3,
          'includes': 'Actual Lean assignment, index construction, checksum, one IO.Ref write',
          'excludes': 'Layout, waits, Kahn, JSON, MCP, rendering, native executable timing',
          'remaining_costs': 'hAt and heightAt retain list lookup; sparse trie follows key bits',
          'results': results}
(HERE / 'benchmark-summary.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
