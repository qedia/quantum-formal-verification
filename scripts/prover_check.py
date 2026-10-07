#!/usr/bin/env python3
"""Quiet Lean feedback; only reviewed maintenance/style warnings are non-blocking.

Usage: python3 scripts/prover_check.py [--verbose] [--log FILE] build [TARGET]
       python3 scripts/prover_check.py [--verbose] [--log FILE] lean FILE

This command checks compilation/diagnostics, not the other acceptance categories.
The complete output is always saved. Unknown warnings require review.
"""
from pathlib import Path
import argparse
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
HEADER = re.compile(
    r'^(?:(?P<lake>warning|error|info):\s*'
    r'(?:[^\n]*?\.lean:\d+:\d+:\s*)?'
    r'|[^\n]*?\.lean:\d+:\d+:\s*(?P<lean>warning|error|info):\s*)'
    r'(?P<message>[^\n]*)', re.MULTILINE)

REVIEWED = [
    r'This simp argument is unused:',
    r'The `show` tactic should only be used to indicate intermediate goal states for readability\.',
    r'Variable name `[^`]+` is not explicitly referenced\.',
    r'`EuclideanSpace\.single_apply` has been deprecated: Use `PiLp\.single_apply` instead',
    r'`List\.take_succ` has been deprecated: Use `List\.take_add_one` instead',
    r'this tactic is never executed',
    r"'(?:ring|push_cast)' tactic does nothing",
    r'`[^`]+` is a flexible tactic modifying `[^`]+`\. Try `simp\?`.*',
]

def diagnostics(output):
    matches = list(HEADER.finditer(output))
    result = []
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        result.append({
            'severity': match['lake'] or match['lean'],
            'message': match['message'].strip(),
            'block': output[match.start():end].strip(),
        })
    return result

def classify_output(output):
    suppressed, unresolved, errors = [], [], []
    for item in diagnostics(output):
        if item['severity'] == 'error':
            errors.append(item)
        elif item['severity'] == 'warning':
            reviewed = any(re.fullmatch(pattern, item['message']) for pattern in REVIEWED)
            (suppressed if reviewed else unresolved).append(item)
    return {'suppressed': suppressed, 'unresolved': unresolved, 'errors': errors}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--log', type=Path)
    parser.add_argument('mode', choices=['build', 'lean'])
    parser.add_argument('target', nargs='?')
    args = parser.parse_args()
    if args.mode == 'lean' and not args.target:
        parser.error('lean requires a source file')
    command = ['lake', 'build', args.target or 'Qhl'] if args.mode == 'build' else [
        'lake', 'env', 'lean', str(Path(args.target).resolve())]
    log = args.log or ROOT / '.lake/prover-logs' / f'{args.mode}.log'
    log.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    output = result.stdout
    log.write_text(output)
    classified = classify_output(output)
    passed = result.returncode == 0 and not classified['unresolved'] and not classified['errors']
    if args.verbose:
        print(output, end='' if output.endswith('\n') else '\n')
    elif not passed:
        actionable = classified['errors'] + classified['unresolved']
        print('\n\n'.join(item['block'] for item in actionable) if actionable
              else '\n'.join(output.splitlines()[-20:]))
    print(f"{'PASS' if passed else 'FAIL'}: {args.mode}; "
          f"{len(classified['suppressed'])} reviewed style/maintenance warnings suppressed; "
          f"{len(classified['unresolved'])} warnings need review; "
          f"{len(classified['errors'])} errors.")
    if not passed:
        print(f'Full log: {log}')
    return 0 if passed else (result.returncode or 1)

if __name__ == '__main__':
    sys.exit(main())
