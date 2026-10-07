#!/usr/bin/env python3
"""check-lock-install: each package of ts/eff/bun.lock against ts/eff/node_modules, by version.

Read-only: nothing is installed, and nothing is written. A package whose `os` or `cpu` names
another platform is not installed here, and is counted apart. It exits 1 when a package of this
platform is absent or stands at another version. `scripts/check-ingest.sh` runs it in place of
an install (decisions row 295): the Makefile's rule `ts/eff/node_modules` is the one place that
installs. Usage: check-lock-install.py <repository>."""
import json, pathlib, platform, re, sys

root = pathlib.Path(sys.argv[1])
lock = json.loads(re.sub(r',(\s*[}\]])', r'\1', (root / 'ts/eff/bun.lock').read_text()))
host = {'os': {'Darwin': 'darwin', 'Linux': 'linux'}[platform.system()],
        'cpu': {'arm64': 'arm64', 'aarch64': 'arm64', 'x86_64': 'x64'}[platform.machine()]}


def for_this_host(meta):
    for key, value in host.items():
        named = meta.get(key)
        if named is not None and value not in (named if isinstance(named, list) else [named]):
            return False
    return True


same, other, absent, elsewhere = 0, [], [], 0
for name, entry in sorted(lock['packages'].items()):
    version = entry[0].rsplit('@', 1)[1]
    meta = next((part for part in entry[1:] if isinstance(part, dict)), {})
    manifest = root / 'ts/eff/node_modules' / name / 'package.json'
    if not manifest.is_file():
        if for_this_host(meta):
            absent.append(entry[0])
        else:
            elsewhere += 1
    elif json.loads(manifest.read_text())['version'] == version:
        same += 1
    else:
        other.append(f'{entry[0]} (installed {json.loads(manifest.read_text())["version"]})')
print(f'bun.lock names {len(lock["packages"])} packages: {same} installed at the locked version, '
      f'{len(other)} at another version, {len(absent)} absent, {elsewhere} of another platform')
for line in other + absent:
    print('  ' + line)
sys.exit(1 if other or absent else 0)
