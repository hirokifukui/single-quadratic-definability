"""s56: measure the blind spot of native_statement_check.norm on the registered paper claims (+ Lemmas A.3-A.5).
Read-only: imports the shipped tools; writes nothing into the package.
For every statement: count ASCII '-' in math, and TeX relation/logic macros that norm() deletes by name.
Then plant, per statement, (a) deletion of the first ASCII minus, (b) \\le<->\\ge swap, (c) '-' -> '+',
and report whether the normalized text (hence claim_hash) changes.  A control that MUST change: insert a digit."""
import csv, os, re, sys, glob
T = os.path.expanduser('~/lean/mpup-lean/pkg_r40/tools'); sys.path.insert(0, T)
from native_statement_check import norm, ENV2KIND
NAT = os.path.expanduser('~/lean/mpup-lean/pkg_r40/submission/native')
RX = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|example|conjecture|notation|question)(Part|\*)?\}(?:\[(.*?)\])?(?:\\label(?:\[[^\]]*\])?\{[^}]*:([^}]*)\})?(.*?)\\end\{\1\2?\}", re.S)
raw = {}
for f in sorted(glob.glob(os.path.join(NAT, 'sections', '*.tex'))):
    for m in RX.finditer(open(f, encoding='utf-8').read()):
        if m.group(4): raw[(ENV2KIND[m.group(1)], m.group(4))] = ((m.group(3) or ''), m.group(5).split('\\begin{proof}')[0])
rows = list(csv.DictReader(open(os.path.join(NAT, 'PAPER_CLAIMS.tsv'), encoding='utf-8'), delimiter='\t'))
labels = [tuple(r['paper_label'].split(' ', 1)) for r in rows] + [('Lemma', 'A.3'), ('Lemma', 'A.4'), ('Lemma', 'A.5')]
MAC = re.compile(r"\\(le|ge|leq|geq|lt|gt|neq|ne|subset|subseteq|subsetneq|supset|supseteq|pm|mp|in|notin|forall|exists|to|iff|implies|land|lor|neg|cap|cup|times|cdot|mid|nmid)\b")
def txt(note, body): return ('(' + note + ').' if note else '') + body
n_minus = n_mac = blind_del = blind_swap = vis_plus = ctl = 0
for k in labels:
    if k not in raw: print('NOT_FOUND', k); continue
    note, body = raw[k]; base = norm(txt(note, body))
    mins = len(re.findall(r'(?<![a-zA-Z])-', body)); macs = MAC.findall(body)
    n_minus += mins > 0; n_mac += bool(macs)
    if mins:
        i = re.search(r'(?<![a-zA-Z])-', body).start()
        blind_del += norm(txt(note, body[:i] + body[i+1:])) == base
        vis_plus += norm(txt(note, body[:i] + '+' + body[i+1:])) != base
    if re.search(r'\\le\b|\\ge\b|\\leq\b|\\geq\b', body):
        sw = re.sub(r'\\(le|ge|leq|geq)\b', lambda m: {'le':'\\ge','ge':'\\le','leq':'\\geq','geq':'\\leq'}[m.group(1)], body)
        blind_swap += norm(txt(note, sw)) == base
    ctl += norm(txt(note, body + '7')) != base
    print('%-16s minus=%d macros=%s' % (' '.join(k), mins, ','.join(sorted(set(macs)))[:80]))
print('STATEMENTS=%d WITH_ASCII_MINUS=%d WITH_DELETED_MACROS=%d' % (len(labels), n_minus, n_mac))
print('MINUS_DELETION_INVISIBLE=%d  MINUS_TO_PLUS_VISIBLE=%d  LE_GE_SWAP_INVISIBLE=%d' % (blind_del, vis_plus, blind_swap))
print('CONTROL_DIGIT_VISIBLE=%d/%d' % (ctl, len(labels)))
