#!/usr/bin/env python3
"""MathGraph Stacks 0DSB native gate v3 — local candidate, no native qualification yet.

Intentionally fail-closed: structured compiler stream + completed capture receipt +
source/consumer identities + exact semantic diagnostic/axiom evidence.
Synthetic unit tests do NOT establish a native RED/GREEN result.
"""
from __future__ import annotations
import hashlib, json, pathlib, re, argparse, sys

CONSUMER = 'StacksFrontier/AlgebraicGeometry/Stacks/MathGraph0DSBCanonicalSmoke.lean'
CONSUMER_BLOB = '6f6c582bc7843d814dfaba26424d50af0a59a006'
UPSTREAM = '5ed82d14634e8d9576bb844c7bd4e3da66d450e7'
REPAIR = 'e1199c53e4822beaaaca1bf801f66448b5e69e7f'
ORIGINAL_SOURCE_BLOBS = {
    'StacksFrontier/AlgebraicGeometry/Stacks/LocalRingDimensionChartIndependence.lean': '78460946e7a2ac77734e8da5f9bb4c451257899b',
    'StacksFrontier/AlgebraicGeometry/Stacks/LocalRingDimensionVersal.lean': '25679380a0181cdc51bdab762cce0c1f4678c2c2',
    'StacksFrontier/AlgebraicGeometry/Stacks/SmoothPresentationLocalRingDimension.lean': 'a06907008ed4350bc4e81902b0fb78c94dd7258e',
    'lean-toolchain': 'a6aff065db2882c535684f8c5bcd4f16e9a23915',
    'lakefile.toml': 'ed2417d0fb730fb086fa520872b4e56cc604c052',
}
EXPECTED_SITE = {53: 'mathGraph_0DSB_canonical_contract', 87: 'mathGraph_0DSB_versal_dimension_agrees'}
AXIOM_SITE = {94: 'AlgebraicGeometry.Stack.mathGraph_0DSB_canonical_contract',
              95: 'AlgebraicGeometry.Stack.mathGraph_0DSB_versal_dimension_agrees'}
ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
REQUIRED_IMPORT_BUILD = [
    'lake','build',
    'StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionVersal',
    'StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartComparison',
]
MISMATCH = re.compile(r'\b(?:application\s+)?type mismatch\b', re.IGNORECASE)
# Format pinned at leanprover/lean4 v4.35.0: src/Lean/Elab/Print.lean:293-298
AXIOMS_PRESENT = re.compile(r"^'([^']+)' depends on axioms: \[([^\]\r\n]*)\]$")
AXIOMS_EMPTY = re.compile(r"^'([^']+)' does not depend on any axioms$")


def unknown(reason, **details):
    return {'state': 'UNKNOWN', 'reason': reason, **details}


def path_matches(value):
    return isinstance(value, str) and (value == CONSUMER or value.endswith('/' + CONSUMER))


def strict_messages(raw: bytes):
    try:
        text = raw.decode('utf-8', errors='strict')
    except UnicodeError as exc:
        raise ValueError('non-UTF8 diagnostic capture') from exc
    if not text.strip():
        raise ValueError('empty diagnostic stream')
    messages = []
    for no, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            m = json.loads(line)
        except (ValueError, TypeError) as exc:
            raise ValueError(f'invalid NDJSON at line {no}') from exc
        if not isinstance(m, dict) or not {'fileName','pos','severity','data'}.issubset(m):
            raise ValueError(f'bad SerialMessage schema at line {no}')
        p = m['pos']
        if (not isinstance(m['fileName'], str) or not isinstance(m['data'], str)
            or not isinstance(p, dict) or type(p.get('line')) is not int
            or type(p.get('column')) is not int or p['line'] < 1 or p['column'] < 0
            or m['severity'] not in ('error','warning','information')):
            raise ValueError(f'bad SerialMessage value at line {no}')
        if 'maximum number of errors' in m['data'].lower():
            raise ValueError('Lean reached maxErrors; diagnostic coverage truncated')
        messages.append(m)
    if not messages:
        raise ValueError('empty messages')
    return messages


def classify_axiom(m):
    """Parse the pinned Lean 4.35 print-axioms format without conflating messages."""
    data = m['data'].strip()
    empty = AXIOMS_EMPTY.fullmatch(data)
    listed = AXIOMS_PRESENT.fullmatch(data)
    if empty:
        return empty.group(1), frozenset()
    if listed:
        names = [x.strip() for x in listed.group(2).split(',')]
        if not all(names) or len(names) != len(set(names)):
            raise ValueError('empty or duplicate axiom')
        return listed.group(1), frozenset(names)
    raise ValueError('not a print-axioms record')


def classify(source: str, receipt: dict, stdout: bytes, stderr: bytes):
    if source not in ('original','repaired'):
        raise ValueError(source)
    if not isinstance(receipt, dict) or receipt.get('completed') is not True:
        return unknown('missing completed compiler-capture receipt')
    if receipt.get('source') != source or receipt.get('consumer_blob') != CONSUMER_BLOB:
        return unknown('capture source or consumer identity mismatch')
    if receipt.get('dependencies_verified') is not True or receipt.get('dependencies_command') != REQUIRED_IMPORT_BUILD:
        return unknown('no completed source-relative native build of BOTH imported modules')
    if receipt.get('toolchain') != 'leanprover/lean4:v4.35.0':
        return unknown('unverified compiler toolchain')
    if source == 'original':
        if receipt.get('original_upstream') != UPSTREAM or receipt.get('source_blob_checks') != ORIGINAL_SOURCE_BLOBS:
            return unknown('original source production-file pins not verified')
    else:
        if receipt.get('source_commit') != REPAIR:
            return unknown('repaired commit identity mismatch')
    if (receipt.get('stdout_sha256') != hashlib.sha256(stdout).hexdigest()
        or receipt.get('stderr_sha256') != hashlib.sha256(stderr).hexdigest()
        or receipt.get('stdout_length') != len(stdout)
        or receipt.get('stderr_length') != len(stderr)):
        return unknown('capture receipt digest/length mismatch (truncated or switched log)')
    if stderr:
        return unknown('non-empty unparsed compiler stderr')
    status = receipt.get('exit_code')
    if type(status) is not int or status < 0 or status in (124,137,143):
        return unknown('missing or interrupted compiler exit')
    try:
        messages = strict_messages(stdout)
    except ValueError as exc:
        return unknown(str(exc))
    errors = [m for m in messages if m['severity']=='error']
    if source=='original':
        if status==0 or not errors:
            return unknown('original is not an observed native negative')
        # A single exact semantic mismatch in the FIRST theorem's direct `exact`
        # application is enough to refute the ORIGINAL public contract required
        # by the unchanged consumer. The second numerical test may emit cascade
        # errors after the first failed theorem; never infer its own error site
        # from this first witness. The repaired side must elaborate BOTH.
        if any(not path_matches(e['fileName']) for e in errors):
            return unknown('error outside consumer, dependencies not independently qualified',errors=len(errors))
        direct=[]; numeric=[]
        for e in errors:
            data=e['data']; line=e['pos']['line']
            semantic=bool(MISMATCH.search(data) and 'HasLocalRingDimensionAtSomeChart' in data
                          and re.search(r'\bHasLocalRingDimension\b',data))
            if semantic and line==53: direct.append(e)
            if semantic and line==87: numeric.append(e)
        if not direct:
            return unknown('no direct legacy-versus-canonical type mismatch at first consumer',errors=len(errors))
        return {'state':'ORIGINAL_DIRECT_CONTRACT_RED_CANDIDATE','errors':len(errors),
                'direct_site':53,'numeric_site_independently_witnessed':bool(numeric),
                'reason':'pinned source fails direct consumer on same-record legacy/canonical type difference; repaired GREEN must still pass both'}
    if status != 0 or errors:
        return unknown('repaired native compilation did not exit zero without errors', errors=len(errors))
    found={}
    for m in messages:
        if m['severity'] != 'information':
            continue
        if not path_matches(m['fileName']) or m['pos']['line'] not in AXIOM_SITE:
            continue
        site=m['pos']['line']
        try:
            name, axioms = classify_axiom(m)
        except ValueError:
            return unknown('unparseable axiom information at pinned line', line=site)
        if name != AXIOM_SITE[site]:
            return unknown('axiom output refers to wrong theorem', line=site)
        if site in found:
            return unknown('duplicate axiom report', line=site)
        if not axioms <= ALLOWED_AXIOMS:
            return unknown('unapproved axiom dependency', line=site, unapproved=sorted(axioms-ALLOWED_AXIOMS))
        found[site]=sorted(axioms)
    if set(found)!=set(AXIOM_SITE):
        return unknown('missing exact axiom output for both declarations', found=sorted(found))
    return {'state':'REPAIRED_BOTH_CONSUMERS_GREEN_AXIOMS_CANDIDATE',
            'axioms':found,'reason':'zero native compiler errors; exact printed axioms use permitted set'}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source',required=True,choices=['original','repaired'])
    ap.add_argument('--receipt',required=True,type=pathlib.Path)
    ap.add_argument('--stdout',required=True,type=pathlib.Path)
    ap.add_argument('--stderr',required=True,type=pathlib.Path)
    a=ap.parse_args()
    try:
        result=classify(a.source,json.loads(a.receipt.read_text()),a.stdout.read_bytes(),a.stderr.read_bytes())
    except (OSError,ValueError) as exc:
        result=unknown('cannot read candidate receipts or logs: '+str(exc))
    print(json.dumps(result,sort_keys=True))
    return 0 if result['state'].endswith('_CANDIDATE') else 2

if __name__=='__main__':
    sys.exit(main())
