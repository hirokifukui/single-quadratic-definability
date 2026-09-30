"""s58: planted defects on Propositions A.9-A.12 in temp copies of <root> (default pkg_r40) (submission/native, tools, certificates,
frozen_statements); each must make paper_claims_check exit 1."""
import os, re, shutil, subprocess, sys, tempfile
P = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.expanduser('~/lean/mpup-lean/pkg_r40'); TEX = 'submission/native/sections/15_appa_open_problems.tex'
def tex_sub(a, b):
    def f(r):
        p = os.path.join(r, TEX); s = open(p).read(); assert s.count(a) >= 1, a; open(p, 'w').write(s.replace(a, b, 1))
    return f
def tsv_sub(label, col, val):
    def f(r):
        p = os.path.join(r, 'submission/native/PAPER_CLAIMS.tsv'); L = open(p).read().split('\n')
        for i, l in enumerate(L):
            c = l.split('\t')
            if c[0] == label: c[col] = val; L[i] = '\t'.join(c)
        open(p, 'w').write('\n'.join(L))
    return f
C = [("P1 A.9 hypothesis deleted", tex_sub(r'Assume $\mathrm{TCER}$ and let $m ≥ 2$.', r'Let $m ≥ 2$.')),
     ("P2 A.9 m >= 2 deleted", tex_sub(r'Assume $\mathrm{TCER}$ and let $m ≥ 2$. A function', r'Assume $\mathrm{TCER}$. A function')),
     ("P3 A.10 'unconditionally' inserted", tex_sub(r'Assume $\mathrm{TCER}$. The map', r'Assume $\mathrm{TCER}$. Then, unconditionally, the map')),
     ("P4 A.11 root swapped to parityFn_not_commonSlope", tsv_sub('Proposition A.11', 1, 'parityFn_not_commonSlope')),
     ("P5 A.12 forged type hash", tsv_sub('Proposition A.12', 11, '0' * 64)),
     ("P6 A.11 TCER inserted", tex_sub('It is not the case that every function', r'Assume $\mathrm{TCER}$. It is not the case that every function'))]
caught = 0
for name, plant in C:
    r = tempfile.mkdtemp(prefix='s58plant_')
    for d in ('submission', 'tools', 'certificates', 'frozen_statements'): shutil.copytree(os.path.join(P, d), os.path.join(r, d))
    plant(r)
    q = subprocess.run([sys.executable, 'tools/paper_claims_check.py', '.'], cwd=r, capture_output=True, text=True)
    fl = [l for l in q.stdout.split('\n') if l.startswith('FAIL')][:1]
    ok = q.returncode == 1; caught += ok
    print('CAUGHT' if ok else 'MISSED', name, 'exit=%d' % q.returncode, fl)
    shutil.rmtree(r)
print('A9A12_PLANTS_CAUGHT=%d/%d' % (caught, len(C)))
sys.exit(0 if caught == len(C) else 1)
