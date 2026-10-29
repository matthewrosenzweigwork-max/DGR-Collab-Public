#!/usr/bin/env python3
"""Check public package bytes and local import closure, without executing Lean."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
manifest=json.loads((root/'verification/solution-source-manifest.json').read_text())
errors=[]
for name,want in manifest.items():
 p=root/'lean'/name
 if not p.is_file(): errors.append('missing: '+name)
 elif hashlib.sha256(p.read_bytes()).hexdigest()!=want: errors.append('hash mismatch: '+name)
for p in (root/'lean').rglob('*.lean'):
 for line in p.read_text().splitlines():
  m=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
  if not m: continue
  for module in m.group(1).split('--')[0].split():
   if module.startswith('LeanResearch') and not (root/'lean'/Path(*module.split('.'))).with_suffix('.lean').is_file():errors.append('missing local import: '+module+' in '+str(p.relative_to(root)))
result={'status':'PASS' if not errors else 'FAIL','manifest_files_checked':len(manifest),'local_proof_modules':sum(k.startswith('LeanResearch/') and k.endswith('.lean') for k in manifest),'errors':errors,'lean_compilation_performed':False,'scope':'Exact hashes and local import closure only; not kernel replay.'}
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
