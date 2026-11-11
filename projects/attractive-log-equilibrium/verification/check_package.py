#!/usr/bin/env python3
"""Check source identity only; this never certifies a Lean proof."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(root=ROOT):
    manifest = json.loads((root/'verification/source-manifest.json').read_text())
    errors = []
    for name, expected in manifest['files'].items():
        p = root/name
        if not p.is_file() or p.is_symlink() or digest(p) != expected:
            errors.append('Source mismatch: '+name)
    tracked_lean = {n for n in manifest['files'] if n.startswith('lean/') and n.endswith('.lean')}
    actual_lean = {str(p.relative_to(root)) for p in (root/'lean').rglob('*.lean') if '.lake' not in p.relative_to(root/'lean').parts}
    if tracked_lean != actual_lean:
        errors.append('Lean file inventory differs from manifest')
    for name in ['frozen_statements.sha256','domain_statements.sha256']:
        for line in (root/'verification'/name).read_text().splitlines():
            expected, file = line.split(maxsplit=1)
            if digest(root/'lean'/file) != expected:
                errors.append('Statement freeze mismatch: '+file)
    return manifest, errors

if __name__ == '__main__':
    manifest, errors = check()
    print(json.dumps({'status':'PASS' if not errors else 'FAIL', 'files':len(manifest['files']),
                      'errors':errors, 'scope':'Source integrity only; no compilation or replay.'}, indent=2))
    raise SystemExit(bool(errors))
