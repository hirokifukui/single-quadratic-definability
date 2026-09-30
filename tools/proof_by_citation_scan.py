#!/usr/bin/env python3
"""proof_by_citation_scan.py - where does the paper discharge a claim with a Lean name?

Referee 3 (blank-slate, s31) rejected the paper in part because Theorem 6.4 is stated with no
proof: its six clauses are each discharged by a Lean declaration name, while the paper elsewhere
says it does not ask a referee to read Lean in place of a proof. That is a judgement about one
theorem; before deciding what to do about it, the whole body should be measured the same way.

For every numbered statement of the body (Appendix F excluded: it carries its own proofs and is
scanned separately by the same rule) the block from the statement to the next statement or heading
is classified:

    PROVED     the block contains a proof paragraph
    CITED      no proof paragraph, and the block cites at least one Lean declaration name
    NEITHER    no proof paragraph and no Lean name (definitions, remarks, statements proved later)

CITED is the category the referee objected to. NEITHER is not by itself a defect - a definition
needs no proof - so the report prints the kind, and the reader decides.

Usage: python3 scripts/proof_by_citation_scan.py <MANUSCRIPT.md> [out.tsv]
"""
# s34 (Gate-8 M02): statement labels may be lettered.  Theorem C.1 was invisible to every
# scanner because this pattern required a leading digit.  [A-Z]+ not [A-Z]: a single letter
# cannot match AA.1, which Gate-8 itself named as a required positive control.
import csv, io, re, sys

KINDS = r'Theorem|Definition|Lemma|Corollary|Proposition|Remark|Examples?|Fact'
# the paper writes '*Proof.*', '**Proof.**' and also '*Proof of 2.1.*'; the first version of
# this scanner missed the third form and reported Theorems 2.1 and 2.2 as unproved. A false
# alarm is a defect in the probe, not in the paper.
PROOF = re.compile(r'\*{1,2}Proof[^*\n]{0,40}\*{1,2}', re.M)
NAME  = re.compile(r'`([A-Za-z_][A-Za-z0-9_.\u2080-\u2089\u2032\']*)`')

def blocks(text):
    starts = [(m.start(), m.group(1), m.group(2))
              for m in re.finditer(r'^\*\*(' + KINDS + r')\s+((?:[0-9]+|[A-Z]+)\.[0-9]+)\*\*', text, re.M)]
    for i, (pos, kind, num) in enumerate(starts):
        nxt = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        cut = re.search(r'\n## ', text[pos:nxt])
        end = pos + cut.start() if cut else nxt
        yield kind, num, text[pos:end]

def main(path, out=None):
    src = io.open(path, encoding='utf-8').read()
    body = src.split('## Appendix F')[0]
    # a proof may be placed after the NEXT statement and named by number ('*Proof of 2.1.*'),
    # which the block model would miss; collect those numbers separately. Found by a positive
    # control: Theorem 2.1 is proved and the first two versions of this scanner said it was not.
    named = set(re.findall(r'\*{1,2}Proof of ((?:[0-9]+|[A-Z]+)\.[0-9]+)', body))
    rows = []
    for kind, num, blk in blocks(body):
        names = [n for n in NAME.findall(blk) if not n.endswith('.lean')]
        proved = bool(PROOF.search(blk)) or num in named
        verdict = 'PROVED' if proved else ('CITED' if names else 'NEITHER')
        rows.append([num, kind, verdict, str(len(names)), ', '.join(names[:4])])
    from collections import Counter
    c = Counter(r[2] for r in rows)
    print("STATEMENTS=%d  PROVED=%d  CITED=%d  NEITHER=%d"
          % (len(rows), c['PROVED'], c['CITED'], c['NEITHER']))
    print()
    print("  CITED - a claim whose only support in the paper is a Lean name:")
    for r in rows:
        if r[2] == 'CITED':
            print("    %-5s %-12s %s names: %s" % (r[0], r[1], r[3], r[4]))
    print()
    print("  NEITHER - no proof and no Lean name (check each: a definition needs none):")
    print("    " + ", ".join("%s %s" % (r[1], r[0]) for r in rows if r[2] == 'NEITHER'))
    # s35 (Gate-9 G10).  A definition or a remark may stand without a proof; a THEOREM may not.
    # At r30 Theorem 6.2 sat in NEITHER, and the only thing that noticed was a reviewer reading
    # the list by eye.  The verdict is now a number with an anchor, and a nonzero one fails.
    CLAIMS = ('Theorem', 'Lemma', 'Corollary', 'Proposition', 'Fact')
    bare = [r for r in rows if r[2] == 'NEITHER' and r[1] in CLAIMS]
    print()
    print("UNPROVED_OR_UNCITED_THEOREMS=%d" % len(bare))
    for r in bare:
        print("    BARE %s %s" % (r[1], r[0]))
    print("PROOF_CITATION_EXIT=%d" % (1 if bare else 0))
    if out:
        with io.open(out, 'w', newline='', encoding='utf-8') as fh:
            w = csv.writer(fh, delimiter='\t')
            w.writerow(['number', 'kind', 'verdict', 'n_lean_names', 'names'])
            w.writerows(rows)
        print("\nTSV=" + out)
    return 1 if bare else 0

if __name__ == '__main__':
    if len(sys.argv) < 2:
        sys.stderr.write(__doc__); sys.exit(2)
    sys.exit(main(*sys.argv[1:3]))
