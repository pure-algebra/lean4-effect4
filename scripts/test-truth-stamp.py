#!/usr/bin/env python3
"""The truth gate's stamp must miss when a host package or the install manifest moves.

Host rows step 6 widened the digest from `effect/**` to every host package the harness can
import (`effect/**` and `@effect/**`) and made `ts/eff/package.json` and `bun.lock` direct
inputs. This test builds a temporary host tree and manifest, and checks that a driver version
bump and a manifest edit each change the digest while nothing else does. No bun, no Lean, no
network: pure Python over a temporary directory, against the real repository inputs.

    python3 scripts/test-truth-stamp.py
"""
import sys
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / 'scripts'))
import importlib.util
spec = importlib.util.spec_from_file_location('check_truth', root / 'scripts/check-truth.py')
check_truth = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_truth)

truth = root / 'harness/truth'
bun_version = b'1.3.14\n'


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


with tempfile.TemporaryDirectory(prefix='truth-stamp-') as temporary:
    tmp = Path(temporary)
    modules = tmp / 'node_modules'
    write(modules / 'effect/package.json', '{"version":"4.0.0-rc.112"}\n')
    write(modules / 'effect/dist/index.js', 'export {}\n')
    write(modules / '@effect/sql-sqlite-bun/package.json', '{"version":"4.0.0-rc.112"}\n')
    write(modules / '@effect/sql-sqlite-bun/dist/index.js', 'export {}\n')
    write(modules / 'oxc-parser/package.json', '{"version":"0.147.0"}\n')
    manifest = [tmp / 'package.json', tmp / 'bun.lock']
    write(manifest[0], '{"dependencies":{"effect":"4.0.0-rc.112","@effect/sql-sqlite-bun":"4.0.0-rc.112"}}\n')
    write(manifest[1], 'lock\n')

    digest = lambda: check_truth.truth_digest(root, truth, modules, manifest, bun_version)
    d0 = digest()
    assert digest() == d0, 'the digest is not deterministic'

    # A driver bump under @effect/ is seen (the widening).
    write(modules / '@effect/sql-sqlite-bun/package.json', '{"version":"4.0.0-rc.113"}\n')
    assert digest() != d0, 'a driver version bump under @effect/ did not move the stamp'
    write(modules / '@effect/sql-sqlite-bun/package.json', '{"version":"4.0.0-rc.112"}\n')
    assert digest() == d0, 'restoring the driver did not restore the digest'

    # A change to the install manifest is seen directly (a direct input).
    write(manifest[0], '{"dependencies":{"effect":"4.0.0-rc.112","@effect/sql-sqlite-bun":"4.0.0-rc.113"}}\n')
    assert digest() != d0, 'a manifest edit did not move the stamp'
    write(manifest[0], '{"dependencies":{"effect":"4.0.0-rc.112","@effect/sql-sqlite-bun":"4.0.0-rc.112"}}\n')
    assert digest() == d0

    # A platform-specific binding outside the host packages is not an input (machine-stable).
    write(modules / 'oxc-parser/package.json', '{"version":"0.147.1"}\n')
    assert digest() == d0, 'a change outside effect/** and @effect/** moved the stamp'

    print('PASS test-truth-stamp: a driver bump and a manifest edit miss the stamp; other packages do not move it')
