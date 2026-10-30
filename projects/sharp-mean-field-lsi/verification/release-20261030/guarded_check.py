#!/usr/bin/env python3
"""One isolated, evidence-preserving verification, never a dependency builder."""
import argparse, datetime, fcntl, hashlib, json, os, pathlib, shutil, signal, subprocess, time

HERE = pathlib.Path(__file__).resolve().parent
LEAN = pathlib.Path('/workspace/shared/dgr-build-tools/lean-4.35.0-rc3-linux/bin/lean')

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def memory():
    return int(next(x for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])

def resource_snapshot():
    return {'mem_available_kib': memory(), 'disk_free_bytes': shutil.disk_usage(HERE).free,
            'pressure': {n: pathlib.Path('/proc/pressure', n).read_text() for n in ('memory', 'io') if pathlib.Path('/proc/pressure', n).exists()}}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('label')
    ap.add_argument('source')
    ap.add_argument('source_root')
    ap.add_argument('output')
    ap.add_argument('--lean-path', required=True)
    a = ap.parse_args()
    src, source_root, out = map(pathlib.Path, (a.source, a.source_root, a.output))
    assert src.is_file() and source_root.is_dir()
    assert out.is_relative_to(HERE) and not out.exists() and not out.is_symlink(), str(out)
    receipts = HERE / 'receipts'
    receipts.mkdir(exist_ok=True)
    rec, log = receipts / (a.label + '.json'), receipts / (a.label + '.log')
    assert not rec.exists() and not log.exists(), 'Use a new label; preserve old evidence.'
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(LEAN), '--threads=1', '--trust=0', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
           '--root=' + str(source_root), '-o', str(out), str(src)]
    env = dict(os.environ, LEAN_PATH=a.lean_path, LEAN_NUM_THREADS='1', LAKE='/nonexistent/no-dependency-build')
    evidence = {'label': a.label, 'command': cmd, 'lean_path': a.lean_path,
                'source_sha256': digest(src), 'source_root': str(source_root),
                'compiler_wrapper_sha256': digest(LEAN), 'compiler_binary_sha256': digest(LEAN.with_name('lean.real')),
                'limits': {'deadline_seconds': 300, 'rss_kib': 6291456, 'memory_floor_kib': 2097152, 'disk_floor_bytes': 838860800},
                'psi_available': pathlib.Path('/proc/pressure/memory').exists()}
    with (HERE / 'lane.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        evidence['preflight'] = resource_snapshot()
        if memory() < 2097152 or shutil.disk_usage(HERE).free < 838860800:
            evidence['exit_code'] = 'DEFERRED_RESOURCE_FLOOR'
        else:
            evidence['started_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
            start, peak, reason, next_progress = time.monotonic(), 0, None, 0
            with log.open('xb') as stream:
                proc = subprocess.Popen(cmd, cwd=source_root, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                evidence['pid'] = proc.pid
                while proc.poll() is None:
                    try:
                        rss = int(next(x for x in pathlib.Path('/proc', str(proc.pid), 'status').read_text().splitlines() if x.startswith('VmRSS:')).split()[1])
                        peak = max(peak, rss)
                    except (OSError, StopIteration):
                        pass
                    if time.monotonic() >= next_progress:
                        progress = {'label': a.label, 'pid': proc.pid, 'elapsed_seconds': time.monotonic()-start, 'peak_rss_kib': peak, 'resources': resource_snapshot()}
                        try:
                            progress['process_status'] = pathlib.Path('/proc', str(proc.pid), 'status').read_text()
                            progress['process_stat'] = pathlib.Path('/proc', str(proc.pid), 'stat').read_text()
                            progress['process_wchan'] = pathlib.Path('/proc', str(proc.pid), 'wchan').read_text()
                        except OSError: pass
                        (receipts / (a.label + '.progress.json')).write_text(json.dumps(progress, indent=2)+'\n')
                        next_progress = time.monotonic() + 5
                    if peak > 6291456: reason = 'RSS_LIMIT_6GIB'
                    elif memory() < 2097152: reason = 'MEM_AVAILABLE_BELOW_2GIB'
                    elif shutil.disk_usage(HERE).free < 838860800: reason = 'DISK_BELOW_800MIB'
                    elif time.monotonic() - start > 300: reason = 'TIMEOUT_300S'
                    if reason:
                        os.killpg(proc.pid, signal.SIGTERM)
                        try: proc.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            os.killpg(proc.pid, signal.SIGKILL)
                            proc.wait()
                        break
                    time.sleep(.25)
                evidence.update(exit_code=reason or proc.returncode, duration_seconds=time.monotonic()-start, peak_rss_kib=peak)
            evidence['log_sha256'] = digest(log)
            if out.is_file(): evidence['output_sha256'] = digest(out)
        evidence['source_unchanged'] = digest(src) == evidence['source_sha256']
        evidence['postflight'] = resource_snapshot()
        if not evidence['source_unchanged']:
            evidence['prior_exit_code'] = evidence['exit_code']
            evidence['exit_code'] = 'INVALIDATED_SOURCE_CHANGED'
        rec.write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps(evidence, indent=2), flush=True)

if __name__ == '__main__':
    main()
