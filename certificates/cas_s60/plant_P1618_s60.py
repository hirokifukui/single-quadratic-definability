"""s60: planted defects on Propositions 10.16, 10.17, 10.18 in temp copies of <root> (default pkg_r40) (submission/native, tools, certificates,
frozen_statements); each must make paper_claims_check exit 1."""
import os, re, shutil, subprocess, sys, tempfile
P = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.expanduser('~/lean/mpup-lean/pkg_r40'); TEX = 'submission/native/sections/10_s10_definable_functions.tex'
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
C = [("P1 10.17 hypothesis deleted", tex_sub(r'Assume $\mathrm{TCER}$. A function $f : ℤ^{n} → ℤ^{m}$ is defined by a single quadratic equation over ℤ if and only if', r'A function $f : ℤ^{n} → ℤ^{m}$ is defined by a single quadratic equation over ℤ if and only if')),
     ("P2 10.16 'without' -> 'with'", tex_sub(r'over ℤ without unknowns if and only if', r'over ℤ with unknowns if and only if')),
     ("P3 10.16 TCER inserted", tex_sub(r'A function $f : ℤ^{n} → ℤ$ is defined by a single quadratic equation over ℤ without unknowns', r'Assume $\mathrm{TCER}$. A function $f : ℤ^{n} → ℤ$ is defined by a single quadratic equation over ℤ without unknowns')),
     ("P4 10.18 'no' -> 'some'", tex_sub(r'and by no single quadratic equation over ℤ without unknowns', r'and by some single quadratic equation over ℤ without unknowns')),
     ("P5 10.18 root swapped to floorThird_oneWitness", tsv_sub('Proposition 10.18', 1, 'floorThird_oneWitness')),
     ("P6 10.17 forged type hash", tsv_sub('Proposition 10.17', 11, '0' * 64)),
     ("P7 10.17 uniqueness weakened", tex_sub(r'whose solutions in the unknowns coincide whenever', r'whose solutions in the unknowns are few whenever'))]
caught = 0
for name, plant in C:
    r = tempfile.mkdtemp(prefix='s60plant_')
    for d in ('submission', 'tools', 'certificates', 'frozen_statements'): shutil.copytree(os.path.join(P, d), os.path.join(r, d))
    plant(r)
    q = subprocess.run([sys.executable, 'tools/paper_claims_check.py', '.'], cwd=r, capture_output=True, text=True)
    fl = [l for l in q.stdout.split('\n') if l.startswith('FAIL')][:1]
    ok = q.returncode == 1; caught += ok
    print('CAUGHT' if ok else 'MISSED', name, 'exit=%d' % q.returncode, fl)
    shutil.rmtree(r)
print('P1618_PLANTS_CAUGHT=%d/%d' % (caught, len(C)))
sys.exit(0 if caught == len(C) else 1)
