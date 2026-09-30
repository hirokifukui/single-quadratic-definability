#!/usr/bin/env python3
"""s56: verify GPT R44 SOURCE_EVIDENCE excerpts against the sealed r44 BASE tree (read-only).
usage: check_source_evidence.py EVIDENCE.md BASE_DIR [--plant]"""
import sys, re, hashlib, os
ev, base = sys.argv[1], sys.argv[2]; plant = '--plant' in sys.argv
txt = open(ev, encoding='utf-8').read().split('\n')
secs=[]; i=0
while i < len(txt):
    m = re.match(r'^## (\S+) : (\d+)–(\d+)$', txt[i])
    if m:
        path, a, b = m.group(1), int(m.group(2)), int(m.group(3))
        sha = re.match(r'^SHA256 `([0-9a-f]{64})`$', txt[i+1]).group(1)
        assert txt[i+2].startswith('```'); j=i+3; body=[]
        while not txt[j].startswith('```'): body.append(txt[j]); j+=1
        secs.append((path,a,b,sha,body)); i=j
    i+=1
ok=bad=0
for k,(path,a,b,sha,body) in enumerate(secs):
    fp=os.path.join(base,path)
    if not os.path.exists(fp): print('MISSING',path); bad+=1; continue
    raw=open(fp,'rb').read(); h=hashlib.sha256(raw).hexdigest()
    lines=raw.decode('utf-8').split('\n')
    if plant and k==0: lines=list(lines); lines[a-1]=lines[a-1]+' PLANT'
    errs=[]
    if h!=sha: errs.append('sha')
    if len(body)!=b-a+1: errs.append(f'count {len(body)} vs {b-a+1}')
    for ln in body:
        m=re.match(r'^(\d+): ?(.*)$',ln)
        if not m: errs.append('fmt'); continue
        n=int(m.group(1)); s=m.group(2)
        if not (a<=n<=b) or lines[n-1].rstrip()!=s.rstrip(): errs.append(f'L{n}')
    if errs: bad+=1; print('FAIL',path,a,b,errs[:5])
    else: ok+=1
print(f'SECTIONS={len(secs)} OK={ok} FAIL={bad}')
