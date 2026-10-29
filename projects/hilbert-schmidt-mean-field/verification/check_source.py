#!/usr/bin/env python3
"""Check packaged source bytes against the recorded accepted-snapshot manifest.
This does not run Lean or establish theorem correctness.
"""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'source-manifest.json').read_text())
source = root.parent / 'lean'
failures = []
for name, record in manifest['files'].items():
    path = source / name
    if not path.is_file() or path.is_symlink():
        failures.append(f'missing or non-regular: {name}')
        continue
    data = path.read_bytes()
    if len(data) != record['bytes'] or hashlib.sha256(data).hexdigest() != record['sha256']:
        failures.append(f'content mismatch: {name}')
    git_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    if git_blob != record['git_blob']:
        failures.append(f'Git blob mismatch: {name}')
extra = sorted(str(p.relative_to(source)) for p in source.rglob('*.lean')
               if '.lake' not in p.relative_to(source).parts
               and str(p.relative_to(source)) not in manifest['files'])
failures.extend(f'unmanifested Lean file: {name}' for name in extra)
if failures:
    raise SystemExit('\n'.join(failures))
print(f"PASS: {len(manifest['files'])} source/config files match the manifest")
print('This is an integrity check, not Lean compilation or proof verification.')
