#!/usr/bin/env python3
"""Validate a recorded machine run and two current AI/human review receipts.

This is evidence validation, not a new kernel replay. Publication approval is separate.
"""
import argparse
import hashlib
import json
from pathlib import Path
from check_package import ROOT, check

TARGETS={'LogGasPaper.main','LogGasPaper.kernel_exists','LogGasChallenge.principal',
         'LogGasChallenge.bulk','LogGasPaper.main_with_domain'}
ROLES={'mathematical-fidelity','lean-verification'}

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for part in iter(lambda:f.read(1024*1024),b''):h.update(part)
    return h.hexdigest()

def validate(root, evidence):
    manifest, errors=check(root)
    machine_path=evidence/'receipt.json'
    machine=json.loads(machine_path.read_text())
    if machine.get('status')!='machine_checks_passed':errors.append('Machine checks not passed')
    if machine.get('source_manifest_sha256')!=sha(root/'verification/source-manifest.json'):errors.append('Machine receipt belongs to another source manifest')
    if set(machine.get('targets',[]))!=TARGETS:errors.append('Target inventory mismatch')
    if set(machine.get('permitted_axioms',[]))!={'propext','Classical.choice','Quot.sound'}:errors.append('Axiom policy mismatch')
    if machine.get('inputs_unchanged') is not True:errors.append('Missing final input-integrity check')
    required={'project-build','compile-ReleaseChallenge','compile-ReleaseSolution','compile-WrongStatement','compile-ForbiddenAxiom',
              'export-ReleaseChallenge','export-ReleaseSolution','export-WrongStatement','export-ForbiddenAxiom',
              'reject-missing-target','reject-changed-statement','reject-forbidden-axiom','official-comparator-nanoda','strict-nanoda'}
    checks=machine.get('checks',[])
    if len({c['name'] for c in checks})!=len(checks):errors.append('Duplicate machine check names')
    if not required <= {c['name'] for c in checks}:errors.append('Required machine checks missing')
    for c in checks:
        expected=1 if c['name'].startswith('reject-') else 0
        if c.get('expected_exit_code')!=expected or c.get('exit_code')!=expected or c.get('stop_reason'):
            errors.append('Unexpected machine outcome: '+c['name'])
        p=evidence/'logs'/(c['name']+'.log')
        if not p.exists() or sha(p)!=c['log_sha256']:errors.append('Machine log missing/changed: '+c['name'])
        if 'export' in c:
            p=evidence/c['export']
            if not p.is_file() or p.stat().st_size!=c['export_bytes'] or sha(p)!=c['export_sha256']:
                errors.append('Proof export missing/changed: '+c['export'])
    artifacts=machine.get('evidence_artifacts',{})
    required_artifacts={'fresh-object-bindings.json','control-object-bindings.json','build-config.toml','source-manifest.json',
                        'official-comparator-nanoda.json','strict-nanoda.json','ReleaseChallenge.ndjson','ReleaseSolution.ndjson',
                        'WrongStatement.ndjson','ForbiddenAxiom.ndjson'}
    if not required_artifacts<=artifacts.keys():errors.append('Evidence artifact bindings missing')
    for name,record in artifacts.items():
        p=evidence/name
        if not p.is_file() or p.stat().st_size!=record['bytes'] or sha(p)!=record['sha256']:
            errors.append('Bound evidence artifact missing/changed: '+name)
    reviewers=[]
    for role in sorted(ROLES):
        p=root/'verification/reviews'/(role+'.json')
        if not p.exists():errors.append('Missing current review: '+role);continue
        review=json.loads(p.read_text())
        if review.get('role')!=role or review.get('verdict')!='passed':errors.append('Review not passed: '+role)
        if review.get('blocking_findings'):errors.append('Blocking review findings: '+role)
        identity=review.get('reviewer_id')
        if not identity:errors.append('Reviewer identity missing: '+role)
        reviewers.append(identity)
        hashes=review.get('reviewed_package_files',{})
        required_files={'lean/PaperChallenge.lean','lean/PaperDomainChallenge.lean','lean/PaperDomainSolution.lean','verification/SCOPE.md'} if role=='mathematical-fidelity' else {'verification/verify_release.py','verification/check_package.py','verification/check_release.py','verification/source-manifest.json'}
        if not required_files <= hashes.keys():errors.append('Required review coverage missing: '+role)
        for name,h in hashes.items():
            if not (root/name).is_file() or sha(root/name)!=h:errors.append('Reviewed file changed: '+role+': '+name)
        if role=='lean-verification' and review.get('machine_receipt_sha256')!=sha(machine_path):errors.append('Verification review does not bind this machine receipt')
    if len(reviewers)!=2 or len(set(reviewers))!=2:errors.append('Two distinct current reviewers required')
    return {'status':'release_checks_passed' if not errors else 'incomplete','errors':errors,
            'scope':'Recorded machine evidence and source-bound reviews; not a new replay or publication approval.',
            'reviewer_ids':reviewers,'machine_receipt_sha256':sha(machine_path)}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--evidence',type=Path,required=True)
    args=ap.parse_args()
    try:result=validate(ROOT,args.evidence.resolve())
    except (OSError,ValueError,KeyError,TypeError) as exc:result={'status':'incomplete','errors':[str(exc)]}
    print(json.dumps(result,indent=2))
    raise SystemExit(result['status']!='release_checks_passed')
