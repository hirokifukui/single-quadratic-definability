#!/usr/bin/env python3
"""cited_name_census.py - Gate-8 M03: who is inside the trust boundary, counted by machine.

Section 11 tells the reader, by hand, how many declarations the paper names are outside the
frozen-statement set, and which of those are still roots of the axiom report.  A hand-kept census
drifts: at r29 it said nineteen when the true figure was larger, it placed one frozen name among
the unfrozen, and nobody noticed for several rounds because nothing recompiled it.  This script
recomputes the census and fails if the paper's stated numbers disagree with the development.

A name counts as OURS if it is backticked in the body (Appendix F excluded, which carries its own
prose proofs) and is declared somewhere under DiophCompression/ or MPUP/.  Mathlib names and file
names are therefore not counted.

NOTE on the axiom report: root names are fully qualified and namespaces NEST
(DiophCompression.SemanticQuadraticSingular.foo).  Matching only one component silently reports
real roots as missing -- that happened while writing this file, and would have put a false erratum
into the paper.  Compare on the LAST dotted component.

Usage: python3 scripts/cited_name_census.py <MANUSCRIPT.md> [--write-json out.json]
Anchors: CITED_NAMES, CITED_OURS, OUTSIDE_FROZEN, OUTSIDE_BUT_ROOT, COVERED_BY_NEITHER,
         MANUSCRIPT_SAYS_OUTSIDE, MANUSCRIPT_SAYS_ROOTS, MANUSCRIPT_SAYS_NEITHER, CENSUS_EXIT
"""
import glob, io, json, os, re, sys

DECL = re.compile(r'^(?:noncomputable |private |protected )*(theorem|def|abbrev)\s+'
                  r'([A-Za-z0-9_.\u00C0-\U0010FFFF\']+)', re.M)
NAME = re.compile(r"`([A-Za-z_][A-Za-z0-9_.\u2080-\u2089\u2032']*)`")
WORDS = {'one': 1, 'two': 2, 'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7, 'eight': 8,  # s40: the count fell below nine
         'nine': 9, 'ten': 10, 'eleven': 11, 'twelve': 12, 'thirteen': 13, 'fourteen': 14,
         'fifteen': 15, 'sixteen': 16, 'seventeen': 17, 'eighteen': 18, 'nineteen': 19,
         'twenty': 20, 'twenty-one': 21, 'twenty-two': 22, 'twenty-three': 23,
         'twenty-four': 24, 'twenty-five': 25, 'twenty-six': 26}

def decls(paths, kinds=('theorem', 'def', 'abbrev')):
    out = {}
    for p in paths:
        for m in DECL.finditer(io.open(p, encoding='utf-8').read()):
            if m.group(1) in kinds:
                out.setdefault(m.group(2), p)
    return out

def main(ms, lean_root, out_json=None):
    body = io.open(ms, encoding='utf-8').read().split('## Appendix F')[0]
    prod_paths = [p for d in ('DiophCompression', 'MPUP')
                  for p in glob.glob(os.path.join(lean_root, d, '**', '*.lean'), recursive=True)
                  if '/probe' not in p and '/audit_smoke' not in p]
    prod = decls(prod_paths)
    frozen = decls(glob.glob(os.path.join(lean_root, 'frozen_statements', '*_STATEMENTS.lean')))
    far_src = io.open(os.path.join(lean_root, 'scripts', 'FinalAxiomReport.lean'),
                      encoding='utf-8').read()
    far = {q.split('.')[-1] for q in re.findall(r'^#print axioms (\S+)$', far_src, re.M)}

    cited = {m.group(1) for m in NAME.finditer(body) if not m.group(1).endswith('.lean')}
    ours = sorted(n for n in cited if n in prod)
    outside = sorted(n for n in ours if n not in frozen)
    roots = sorted(n for n in outside if n in far)
    neither = sorted(n for n in outside if n not in far)

    said = {}
    # s36 (Gate-10 M01): the three figures left section 11 for release/TRUST_BOUNDARY_APAL.md, which
    # is passed with --says; without it the manuscript body is read as before.
    says_src = body
    if '--says' in sys.argv:
        says_src = open(sys.argv[sys.argv.index('--says') + 1], encoding='utf-8').read()
        print('STATEMENT_SOURCE=%s' % sys.argv[sys.argv.index('--says') + 1])
    else:
        print('STATEMENT_SOURCE=manuscript')
    body = says_src
    m = re.search(r'([A-Za-z-]+) are outside the frozen-statement set: ([A-Za-z-]+) of those',
                  body)
    if m:
        said['outside'] = WORDS.get(m.group(1).lower())
        said['roots'] = WORDS.get(m.group(2).lower())
    m2 = re.search(r'The remaining ([A-Za-z-]+) —', body) or \
         re.search(r'The remaining ([A-Za-z-]+) --', body)
    if m2:
        said['neither'] = WORDS.get(m2.group(1).lower())

    print('CITED_NAMES=%d' % len(cited))
    print('CITED_OURS=%d' % len(ours))
    print('OUTSIDE_FROZEN=%d' % len(outside))
    print('OUTSIDE_BUT_ROOT=%d' % len(roots))
    print('COVERED_BY_NEITHER=%d' % len(neither))
    print('MANUSCRIPT_SAYS_OUTSIDE=%s' % said.get('outside'))
    print('MANUSCRIPT_SAYS_ROOTS=%s' % said.get('roots'))
    print('MANUSCRIPT_SAYS_NEITHER=%s' % said.get('neither'))
    print('ROOT_NAMES=%s' % ', '.join(roots))
    print('NEITHER_NAMES=%s' % ', '.join(neither))

    rc = 0
    for key, got in (('outside', len(outside)), ('roots', len(roots)), ('neither', len(neither))):
        if said.get(key) != got:
            print('FAIL census %s: manuscript says %s, development has %d' % (key, said.get(key), got))
            rc = 1
    if out_json:
        io.open(out_json, 'w', encoding='utf-8').write(json.dumps(
            {'outside': outside, 'roots': roots, 'neither': neither}, indent=1, ensure_ascii=False))
    print('CENSUS_EXIT=%d' % rc)
    return rc

if __name__ == '__main__':
    if len(sys.argv) < 2:
        sys.stderr.write(__doc__); sys.exit(2)
    if '--lean-root' in sys.argv:
        root = sys.argv[sys.argv.index('--lean-root') + 1]
    else:
        root = os.environ.get('MPUP_WORK', os.path.expanduser('~/lean/mpup-lean'))
    oj = sys.argv[3] if len(sys.argv) > 3 and sys.argv[2] == '--write-json' else None
    sys.exit(main(sys.argv[1], root, oj))
