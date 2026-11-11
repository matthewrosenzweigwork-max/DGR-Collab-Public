#!/usr/bin/env python3
"""Fresh project compilation, same-run object binding, Comparator and strict Nanoda.

Run on Linux with the pinned Lean toolchain, bwrap, and already-installed pinned
dependencies (lake exe cache get). No previous project outputs are reused.
Human approval and AI review are separate from this machine-checking receipt.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
from check_package import check

ROOT=Path(__file__).resolve().parent.parent
LEAN=ROOT/'lean'
TARGETS=['LogGasPaper.main','LogGasPaper.kernel_exists','LogGasChallenge.principal',
         'LogGasChallenge.bulk','LogGasPaper.main_with_domain']
TYPES=['LogGasPaper.PaperTheorem','LogGasPaper.LogKernelExists','LogGasChallenge.principalStatement',
       'LogGasChallenge.bulkStatement','LogGasPaper.PaperTheoremWithDomain']
AXIOMS=['propext','Classical.choice','Quot.sound']
PRIMITIVES=['Quot','Quot.mk','Quot.lift','Quot.ind','Nat.add','Nat.sub','Nat.mul','Nat.pow',
 'Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft',
 'Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk',
 'Char','optParam','autoParam','semiOutParam','outParam']

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for part in iter(lambda:f.read(1024*1024),b''):h.update(part)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    out=args.output.resolve()
    out.mkdir(parents=True,exist_ok=False)
    logs=out/'logs';logs.mkdir()
    inputs=out/'inputs';inputs.mkdir()
    objects=out/'control-objects';objects.mkdir()
    receipt={'status':'running','checks':[],'targets':TARGETS,'permitted_axioms':AXIOMS,
             'scope':'Fresh packaged project build with pinned dependency artifacts reused; same-run source/object bindings; selected-target Comparator and strict Nanoda replay. No whole-Mathlib rebuild, independent OS administration, or human certification.',
             'started_utc':datetime.now(timezone.utc).isoformat(),'pid':os.getpid()}
    def save():
        receipt['updated_utc']=datetime.now(timezone.utc).isoformat()
        temp=out/'receipt.tmp';temp.write_text(json.dumps(receipt,indent=2)+'\n');temp.replace(out/'receipt.json')
    def resource_ok():
        memory=next(int(s.split()[1]) for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
        return memory>=4*1024**2 and shutil.disk_usage(out).free>=3*1024**3
    def run(name,argv,expected=0,export=None,timeout=7200,cwd=LEAN):
        receipt['stage']=name;save();print(receipt['updated_utc'],name,flush=True)
        start=time.monotonic();reason=None
        with (logs/(name+'.log')).open('wb') as log:
            stdout=export.open('wb') if export else log
            try:
                proc=subprocess.Popen(argv,cwd=cwd,stdout=stdout,stderr=log,start_new_session=True)
                while proc.poll() is None:
                    if time.monotonic()-start>timeout:reason='timeout'
                    elif not resource_ok():reason='resource_guard'
                    if reason:
                        os.killpg(proc.pid,signal.SIGTERM)
                        try:proc.wait(timeout=10)
                        except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL)
                        break
                    time.sleep(2)
                code=proc.wait()
            finally:
                if export:stdout.close()
        record={'name':name,'command':argv,'exit_code':code,'expected_exit_code':expected,
                'seconds':round(time.monotonic()-start,2),'stop_reason':reason,
                'log_sha256':sha(logs/(name+'.log'))}
        if export:record.update(export=export.name,export_sha256=sha(export),export_bytes=export.stat().st_size)
        receipt['checks'].append(record);save()
        if reason or code!=expected:raise RuntimeError(f'{name}: expected {expected}, got {code}, {reason}')
        return (logs/(name+'.log')).read_text()
    def box(argv,writable=(),cwd=LEAN):
        command=['bwrap','--die-with-parent','--unshare-net','--ro-bind','/','/','--dev','/dev','--proc','/proc']
        for path in writable:command+=['--bind',str(path),str(path)]
        return command+['--chdir',str(cwd),'--',*map(str,argv)]
    try:
        assert os.name=='posix' and Path('/proc/meminfo').exists(),'Linux required'
        os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);os.nice(15)
        os.environ['LEAN_NUM_THREADS']='2';os.environ['LEAN_ABORT_ON_PANIC']='1'
        manifest,errors=check();assert not errors,errors
        receipt['source_manifest_sha256']=sha(ROOT/'verification/source-manifest.json')
        (out/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
        assert (LEAN/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.36.0-rc1'
        lock=json.loads((LEAN/'lake-manifest.json').read_text())
        dependency_checks=[]
        for dep in lock['packages']:
            path=LEAN/'.lake/packages'/dep['name']
            actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
            assert actual==dep['rev'],dep['name']+' revision mismatch'
            subprocess.run(['git','-C',str(path),'diff','--quiet','HEAD','--'],check=True)
            dependency_checks.append({'name':dep['name'],'revision':actual})
        receipt['dependencies']=dependency_checks
        lean_exe=Path(subprocess.check_output(['elan','which','lean'],cwd=LEAN,text=True).strip())
        tc=lean_exe.parent
        receipt['tool_hashes']={n:sha(tc/n) for n in ['lean','lake','leanexport','leanchecker','nanoda_bin']}
        receipt['sandbox_binary_sha256']=sha(Path(shutil.which('bwrap')))
        stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+str(os.getpid())
        buildrel='.lake/build-release-'+stamp
        build=LEAN/buildrel
        assert not build.exists(),'Fresh build directory already exists'
        config=(LEAN/'lakefile.toml').read_text()
        assert not re.search(r'^buildDir\s*=',config,re.M)
        config=config.replace('defaultTargets = ["LogGas"]','defaultTargets = ["LogGas"]\nbuildDir = "'+buildrel+'"')
        assert 'buildDir = "'+buildrel+'"' in config
        configfile=LEAN/('lakefile.release-'+stamp+'.toml');configfile.write_text(config)
        (out/'build-config.toml').write_text(config)
        lake=[str(tc/'lake'),'-f',str(configfile)]
        run('lean-version',box([str(lean_exe),'--version']))
        run('project-build',box(lake+['build','LogGas','Challenge','Solution','PaperChallenge','PaperSolution',
                                     'PaperDomainChallenge','PaperDomainSolution','VerificationAudit'],[LEAN/'.lake']))
        # Bind objects immediately after the fresh build, before any export.
        built={str(p.relative_to(build)):sha(p) for p in sorted(build.rglob('*.olean'))}
        assert built and all((build/'lib/lean'/(n+'.olean')).exists() for n in ['PaperDomainChallenge','PaperDomainSolution','Solution','PaperSolution'])
        (out/'fresh-object-bindings.json').write_text(json.dumps(built,indent=2)+'\n')
        receipt['project_object_count']=len(built);receipt['build_directory']=buildrel
        assert not check()[1],'Source changed during build'
        paths=run('lean-path',lake+['env','printenv','LEAN_PATH']).strip()
        resolved=[(Path(v) if Path(v).is_absolute() else LEAN/v).resolve() for v in paths.split(':') if v]
        allowed=[(build/'lib/lean').resolve(),(tc.parent/'lib/lean').resolve()]+[(LEAN/'.lake/packages'/d['name']/'.lake/build/lib/lean').resolve() for d in lock['packages']]
        assert resolved and all(v in allowed for v in resolved),'Unexpected artifact search path'
        os.environ['LEAN_PATH']=str(objects)+':'+':'.join(map(str,resolved))
        scaffold='import PaperDomainChallenge\nimport Challenge\n\n'
        challenge=scaffold+'\n'.join(f'theorem {n} : {t} := by sorry' for n,t in zip(TARGETS,TYPES))+'\n'
        (inputs/'ReleaseChallenge.lean').write_text(challenge)
        (inputs/'ReleaseSolution.lean').write_text('import PaperDomainSolution\nimport Solution\n')
        (inputs/'WrongStatement.lean').write_text(challenge.replace('theorem LogGasPaper.main_with_domain : LogGasPaper.PaperTheoremWithDomain := by sorry','theorem LogGasPaper.main_with_domain : True := by trivial'))
        (inputs/'ForbiddenAxiom.lean').write_text(scaffold+'axiom ReleaseControl.forbidden : False\n'+
             '\n'.join(f'theorem {n} : {t} := False.elim ReleaseControl.forbidden' for n,t in zip(TARGETS,TYPES))+'\n')
        receipt['challenge_and_control_sources']={p.name:sha(p) for p in inputs.glob('*.lean')}
        exports={}
        generated_hashes={}
        control_hashes={}
        for module in ['ReleaseChallenge','ReleaseSolution','WrongStatement','ForbiddenAxiom']:
            run('compile-'+module,box([lean_exe,'-o',objects/(module+'.olean'),inputs/(module+'.lean')],[objects],inputs),cwd=inputs)
            control_hashes[module+'.olean']=sha(objects/(module+'.olean'))
            export=out/(module+'.ndjson')
            run('export-'+module,box([tc/'leanexport',module,'--',*TARGETS,*AXIOMS,*PRIMITIVES],cwd=inputs),export=export,cwd=inputs)
            exports[module]=export
        comparator={'challenge_module':'ReleaseChallenge','solution_module':'ReleaseSolution','theorem_names':TARGETS,
                    'definition_names':[],'permitted_axioms':AXIOMS,'external_kernels':{'nanoda':[str(tc/'nanoda_bin')]}}
        def compare(name,left,right,cfg,expected):
            p=out/(name+'.json');p.write_text(json.dumps(cfg,indent=2)+'\n')
            generated_hashes[p.name]=sha(p)
            # The trusted Comparator frontend parses exports; its external kernels
            # are sandboxed by the official toolchain. No candidate Lake config is loaded.
            return run(name,[str(tc/'lake'),'comparator','--config',str(p),'--challenge-from-export',str(left),
                             '--solution-from-export',str(right)],expected=expected)
        c=exports['ReleaseChallenge'];s=exports['ReleaseSolution']
        missing=dict(comparator,theorem_names=TARGETS+['ReleaseControl.missing'])
        negative=compare('reject-missing-target',c,s,missing,1)
        assert 'Const not found' in negative and 'ReleaseControl.missing' in negative
        negative=compare('reject-changed-statement',exports['WrongStatement'],s,comparator,1)
        assert 'theorem statement do not match' in negative and 'main_with_domain' in negative
        negative=compare('reject-forbidden-axiom',c,exports['ForbiddenAxiom'],comparator,1)
        assert 'Illegal axiom' in negative and 'ReleaseControl.forbidden' in negative
        positive=compare('official-comparator-nanoda',c,s,comparator,0)
        assert all(m in positive for m in ['nanoda kernel accepts the solution','Lean default kernel accepts the solution','Your solution is okay!'])
        strict={'export_file_path':str(s),'use_stdin':False,'permitted_axioms':AXIOMS,'unpermitted_axiom_hard_error':True,
                'unsafe_permit_all_axioms':False,'nat_extension':True,'string_extension':True,'num_threads':2,
                'print_success_message':True,'pp_to_stdout':True,'pp_declars':TARGETS}
        strictfile=out/'strict-nanoda.json';strictfile.write_text(json.dumps(strict,indent=2)+'\n')
        generated_hashes[strictfile.name]=sha(strictfile)
        strictlog=run('strict-nanoda',box([tc/'nanoda_bin',strictfile]))
        match=re.search(r'Checked (\d+) declarations with no errors',strictlog)
        assert match,'Strict Nanoda did not report clean success'
        receipt['strict_nanoda_declarations']=int(match.group(1))
        assert not check()[1],'Final source integrity failed'
        assert sha(ROOT/'verification/source-manifest.json')==receipt['source_manifest_sha256'],'Source manifest changed'
        assert all(sha(build/p)==h for p,h in built.items()),'Project objects changed'
        assert json.loads((out/'fresh-object-bindings.json').read_text())==built,'Object binding record changed'
        assert configfile.read_text()==config and (out/'build-config.toml').read_text()==config,'Build configuration changed'
        assert all(sha(objects/n)==h for n,h in control_hashes.items()),'Control objects changed'
        assert all(sha(out/n)==h for n,h in generated_hashes.items()),'Checker configuration changed'
        for c in receipt['checks']:
            if 'export' in c:
                assert sha(out/c['export'])==c['export_sha256'] and (out/c['export']).stat().st_size==c['export_bytes'],'Proof export changed'
        assert all(sha(tc/n)==h for n,h in receipt['tool_hashes'].items()),'Checker binaries changed'
        assert sha(Path(shutil.which('bwrap')))==receipt['sandbox_binary_sha256'],'Sandbox binary changed'
        assert all(sha(inputs/n)==h for n,h in receipt['challenge_and_control_sources'].items()),'Challenge changed'
        (out/'control-object-bindings.json').write_text(json.dumps(control_hashes,indent=2)+'\n')
        receipt['evidence_artifacts']={str(p.relative_to(out)):{'sha256':sha(p),'bytes':p.stat().st_size}
            for p in sorted(out.rglob('*')) if p.is_file() and p.name not in {'receipt.json','receipt.tmp'}}
        receipt['inputs_unchanged']=True
        receipt['status']='machine_checks_passed'
    except Exception as exc:
        receipt['status']='failed';receipt['error']=repr(exc)
    finally:
        receipt['finished_utc']=datetime.now(timezone.utc).isoformat();save()
        print(json.dumps(receipt,indent=2),flush=True)
    return 0 if receipt['status']=='machine_checks_passed' else 1

if __name__=='__main__':
    raise SystemExit(main())
