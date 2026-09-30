"""s59: planted defects on Lemma A.13 and Propositions A.14, A.15 in temp copies of <root> (default pkg_r40) (submission/native, tools, certificates,
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
C = [("P1 A.14 hypothesis deleted", tex_sub(r'Assume $\mathrm{TCER}$. A function $f : ℤ^{n} → ℤ$', r'A function $f : ℤ^{n} → ℤ$')),
     ("P2 A.14 'odd coordinate' clause deleted", tex_sub(r', $p$ having an odd coordinate', r'')),
     ("P3 A.15 'unconditionally' inserted", tex_sub(r'Assume $\mathrm{TCER}$. For every', r'Assume $\mathrm{TCER}$. Unconditionally, for every')),
     ("P4 A.15 m >= 1 inserted", tex_sub(r'For every $f : ℤ^{n} → ℤ^{m}$', r'For every $f : ℤ^{n} → ℤ^{m}$ with $m ≥ 1$')),
     ("P5 A.13 root swapped to affine_eq_of_eq_on_coset", tsv_sub('Lemma A.13', 1, 'affine_eq_of_eq_on_coset')),
     ("P6 A.14 forged type hash", tsv_sub('Proposition A.14', 11, '0' * 64)),
     ("P7 A.13 'finite group' inserted", tex_sub(r'of an additive commutative group $G$', r'of a finite group $G$'))]
caught = 0
for name, plant in C:
    r = tempfile.mkdtemp(prefix='s59plant_')
    for d in ('submission', 'tools', 'certificates', 'frozen_statements'): shutil.copytree(os.path.join(P, d), os.path.join(r, d))
    plant(r)
    q = subprocess.run([sys.executable, 'tools/paper_claims_check.py', '.'], cwd=r, capture_output=True, text=True)
    fl = [l for l in q.stdout.split('\n') if l.startswith('FAIL')][:1]
    ok = q.returncode == 1; caught += ok
    print('CAUGHT' if ok else 'MISSED', name, 'exit=%d' % q.returncode, fl)
    shutil.rmtree(r)
print('A13A15_PLANTS_CAUGHT=%d/%d' % (caught, len(C)))
sys.exit(0 if caught == len(C) else 1)
