#!/usr/bin/env python3
"""Capture a *real* pinned Stacks Lean --json compiler process with atomic receipt.

Must run inside the checked-out GitHub Actions research fork. Does not build
missing dependencies or modify Git history; it consumes the restored build cache.
On runner kill the completed receipt will be absent. Native gate remains UNKNOWN.
"""
from __future__ import annotations
import argparse,hashlib,json,os,pathlib,signal,subprocess,tempfile,time
from mathgraph_0dsb_gate_v3 import CONSUMER,CONSUMER_BLOB,UPSTREAM,REPAIR,ORIGINAL_SOURCE_BLOBS,REQUIRED_IMPORT_BUILD

# Permitted changes in the original-source *research branch* relative to Axiom's
# complete pinned upstream commit. No production source modifications allowed.
RESEARCH_FILES = frozenset({
    '.github/workflows/mathgraph-0dsb-baseline-negative.yml',
    'StacksFrontier/AlgebraicGeometry/Stacks/MathGraph0DSBCanonicalSmoke.lean',
    '.github/scripts/mathgraph_0dsb_capture_v3.py',
    '.github/scripts/mathgraph_0dsb_gate_v3.py',
})
LEAN_COMMAND = ['lake','env','lean','--json',CONSUMER]


def git(*args):
    p=subprocess.run(['git',*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    return p.stdout.decode().strip()


def preflight(source):
    head=git('rev-parse','HEAD')
    actual=git('hash-object','--',CONSUMER)
    if actual != CONSUMER_BLOB:
        raise ValueError('consumer blob not pinned')
    toolchain=pathlib.Path('lean-toolchain').read_text().strip()
    if toolchain != 'leanprover/lean4:v4.35.0':
        raise ValueError('lean-toolchain not 4.35.0')
    if source=='original':
        subprocess.run(['git','merge-base','--is-ancestor',UPSTREAM,'HEAD'],check=True)
        changed=set(git('diff','--name-only',UPSTREAM,'HEAD').splitlines())
        if not changed<=RESEARCH_FILES:
            raise ValueError('upstream source differs beyond permitted research files: '+repr(sorted(changed-RESEARCH_FILES)))
        if git('diff','--name-only') or git('diff','--cached','--name-only'):
            raise ValueError('uncommitted tracked changes present')
        observed={p:git('hash-object','--',p) for p in ORIGINAL_SOURCE_BLOBS}
        if observed!=ORIGINAL_SOURCE_BLOBS:
            raise ValueError('original pinned source/toolchain blob mismatch')
        return {'source_commit':head,'original_upstream':UPSTREAM,'source_blob_checks':observed,
                'consumer_blob':actual,'toolchain':toolchain}
    if source=='repaired':
        if head!=REPAIR:
            raise ValueError('repair source commit not pinned')
        if git('diff','--name-only') or git('diff','--cached','--name-only'):
            raise ValueError('uncommitted tracked changes present')
        return {'source_commit':head,'consumer_blob':actual,'toolchain':toolchain}
    raise ValueError('unrecognized source')


def atomic_json(path: pathlib.Path, data):
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp = path.with_suffix(path.suffix+'.partial')
    with tmp.open('w',encoding='utf8') as f:
        json.dump(data,f,indent=2,sort_keys=True)
        f.write('\n')
        f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)


def record(source, pin, exit_code, outpath, errpath, completed):
    out=outpath.read_bytes(); err=errpath.read_bytes()
    return {'source':source,**pin,'command':LEAN_COMMAND,
            'completed':completed,'exit_code':exit_code,
            'stdout_sha256':hashlib.sha256(out).hexdigest(),
            'stderr_sha256':hashlib.sha256(err).hexdigest(),
            'stdout_length':len(out),'stderr_length':len(err)}


def run_capture(source,outdir: pathlib.Path,timeout_seconds=1200):
    pin=preflight(source)
    ver=subprocess.run(['lake','env','lean','--version'],capture_output=True,text=True,check=True)
    if '4.35.0' not in ver.stdout+ver.stderr:
        raise ValueError('runtime Lean toolchain version mismatch')
    outdir.mkdir(parents=True,exist_ok=True)
    out,err,receipt=(outdir/'consumer.ndjson',outdir/'consumer.stderr',outdir/'receipt.json')
    if receipt.exists():
        receipt.unlink()  # prevents a stale complete receipt being reused after an interrupted process
    # Direct Lean consumes imported .olean files. A successful, source-relative
    # Lake build of BOTH imports is necessary before interpreting diagnostics.
    # This short guard should run AFTER checkpointed dependency build segments.
    depout=outdir/'imports.build.stdout'
    deperr=outdir/'imports.build.stderr'
    with depout.open('wb') as o, deperr.open('wb') as e:
        dep = subprocess.Popen(REQUIRED_IMPORT_BUILD,stdout=o,stderr=e,start_new_session=True)
        try:
            dep_status=dep.wait(timeout=180)
        except subprocess.TimeoutExpired:
            try: os.killpg(dep.pid,signal.SIGINT)
            except ProcessLookupError: pass
            try: dep.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try: os.killpg(dep.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                dep.wait()
            raise RuntimeError('import dependency build did not finish within 180 seconds')
    if dep_status != 0:
        raise RuntimeError('import dependency build returned nonzero; cannot verify source-relative olean imports')
    pin.update(dependencies_verified=True,dependencies_command=REQUIRED_IMPORT_BUILD,
               dependencies_build_stdout_sha256=hashlib.sha256(depout.read_bytes()).hexdigest(),
               dependencies_build_stderr_sha256=hashlib.sha256(deperr.read_bytes()).hexdigest())
    timeout_hit=False
    with out.open('wb') as stdout, err.open('wb') as stderr:
        proc=subprocess.Popen(LEAN_COMMAND,stdout=stdout,stderr=stderr,start_new_session=True)
        try:
            status=proc.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            timeout_hit=True
            try:os.killpg(proc.pid,signal.SIGINT)
            except ProcessLookupError:pass
            try:status=proc.wait(timeout=15)
            except subprocess.TimeoutExpired:
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                status=proc.wait()
    data=record(source,pin,status,out,err,completed=not timeout_hit)
    if timeout_hit:
        data['timed_out']=True
        # A timed-out process is not a complete diagnostic stream; always UNKNOWN.
        # Still write an explicit incomplete receipt for postmortem provenance.
    atomic_json(receipt,data)
    return data


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--source',required=True,choices=['original','repaired'])
    p.add_argument('--outdir',required=True,type=pathlib.Path)
    p.add_argument('--timeout-seconds',type=int,default=1200)
    a=p.parse_args()
    if a.timeout_seconds < 30 or a.timeout_seconds>1800:
        p.error('timeout-seconds must be 30..1800')
    result=run_capture(a.source,a.outdir,a.timeout_seconds)
    print(json.dumps({k:result[k] for k in ('completed','exit_code','stdout_sha256','stderr_sha256')},sort_keys=True))
    return 0 if result['completed'] else 2

if __name__=='__main__':
    raise SystemExit(main())
