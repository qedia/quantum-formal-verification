#!/usr/bin/env python3
"""Build and audit all principal source examples and registered integration derivations.

The registry in source_rule_audit.lean is deliberately separate from the retained
backend example audit. Passing this gate does not certify an unregistered example
or establish correspondence for unregistered proof dependencies.
"""
import hashlib
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def source_digest():
    files = list((ROOT / 'Qhl').rglob('*.lean')) + [
        ROOT / 'Qhl.lean', ROOT / 'lakefile.toml', ROOT / 'lean-toolchain',
        ROOT / 'lake-manifest.json', ROOT / 'scripts/prover_check.py',
        ROOT / 'scripts/source_rule_check.py', ROOT / 'scripts/source_rule_audit.lean',
        ROOT / 'scripts/source_example_endpoints.lean',
        ROOT / 'scripts/measurement_mask_check.lean', ROOT / 'scripts/rus_classical_check.lean',
    ]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(files)}


snapshot = source_digest()
for mode, target, log in [
    ('build', None, 'source-rule-gate-build.log'),
    ('lean', 'scripts/source_rule_audit.lean', 'source-rule-audit.log'),
    ('lean', 'scripts/source_example_endpoints.lean', 'source-example-endpoints.log'),
    ('lean', 'scripts/measurement_mask_check.lean', 'measurement-mask-check.log'),
    ('lean', 'scripts/rus_classical_check.lean', 'rus-classical-check.log'),
]:
    command = [sys.executable, str(ROOT / 'scripts/prover_check.py'),
               '--log', str(ROOT / '.lake/prover-logs' / log), mode]
    if target:
        command.append(target)
    result = subprocess.run(command, cwd=ROOT)
    if result.returncode:
        sys.exit(result.returncode)
    if source_digest() != snapshot:
        sys.exit('FAIL: source changed during verification; rerun on the integrated revision.')
