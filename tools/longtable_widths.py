#!/usr/bin/env python3
"""longtable_widths.py -- recompute longtable column widths from CONTENT, not from the header.

Why (s37, Gate-11 N17).  The one-time Markdown->TeX migrator sized every column from the width of
its header cell.  Where a table's header is short and its body long -- "claim" over
"saturation/splitting/block", "#" over a Lean name -- the column was set to 0.06\\linewidth and the
body ran past it.  73 of the 73 overfull boxes over 5pt in the r32 build were of this kind or of the
neighbouring kind (no break point inside a CamelCase identifier).  This tool is the repair, and it
is a tool rather than a hand edit so that the next table added to the paper is measured the same way.

Method.  For each column: measure, over every row, (a) the plain-text length of the cell and (b) the
longest run with no break opportunity in it (spaces and \\allowbreak{} are break opportunities).  A
column is never narrower than its longest unbreakable run; the slack left over is shared out in
proportion to average cell length.  Character width is calibrated at 0.0105\\linewidth, measured from
the r32 log (an 11-character word overflowed a 0.060\\linewidth column by 25.2pt).

Usage:  python3 tools/longtable_widths.py <dir-of-sections> [--apply]
Prints one line per table; exit 0.  Without --apply nothing is written.
"""
import glob, os, re, sys

CHAR = 0.0105          # linewidth fraction per character, calibrated from the r32 log
PAD   = 0.012          # inter-column padding allowance
# The p-widths must leave room for \tabcolsep, which LaTeX puts on BOTH sides of every
# inter-column gap: (n-1) x 2 x 6pt.  The r32 six-column table overflowed by exactly
# 13.02pt, which pins the text width at 469.8pt and this allowance at 0.0256 per gap.
GAP  = 0.0256
def total(ncol):
    return min(0.900, 1.0 - (ncol - 1)*GAP - 0.030)

def plain(cell):
    s = re.sub(r"\\allowbreak\{\}", " ", cell)
    s = re.sub(r"\\[a-zA-Z]+\*?", "", s)
    s = re.sub(r"[{}\\]", "", s)
    return s.strip()

def cells(row):
    row = re.sub(r"\\\\\s*$", "", row.strip())
    return [c.strip() for c in re.split(r"(?<!\\)&", row)]

def widths(rows, ncol):
    avg = [0.0]*ncol; mx = [1]*ncol
    for r in rows:
        cs = cells(r)
        for i in range(min(ncol, len(cs))):
            p = plain(cs[i])
            avg[i] += len(p)
            for tok in p.split():
                mx[i] = max(mx[i], len(tok))
    n = max(1, len(rows))
    avg = [a/n for a in avg]
    floor = [t*CHAR + PAD for t in mx]
    TOT = total(ncol)
    slack = TOT - sum(floor)
    if slack <= 0:                      # cannot fit: scale the floors down proportionally
        k = TOT/sum(floor)
        return [f*k for f in floor], False
    tot = sum(avg) or 1.0
    return [floor[i] + slack*avg[i]/tot for i in range(ncol)], True

def main():
    root = sys.argv[1]; apply = "--apply" in sys.argv
    pat = re.compile(r"(\\begin\{longtable\}\{)([^\n]*?)(\}\n)(.*?)(\\end\{longtable\})", re.S)
    for f in sorted(glob.glob(os.path.join(root, "*.tex"))):
        t = open(f, encoding="utf-8").read(); out = []; last = 0; changed = 0
        for m in pat.finditer(t):
            spec = m.group(2); body = m.group(4)
            old = [float(x) for x in re.findall(r"p\{([0-9.]+)\\linewidth\}", spec)]
            if not old: continue
            rows = [r for r in body.splitlines() if "&" in r]
            new, ok = widths(rows, len(old))
            newspec = spec
            it = iter(new)
            newspec = re.sub(r"p\{[0-9.]+\\linewidth\}",
                             lambda _m: "p{%.3f\\linewidth}" % next(it), newspec)
            print("%-44s cols=%d rows=%2d  %s -> %s%s" % (
                os.path.basename(f)[:44], len(old), len(rows),
                ",".join("%.3f" % w for w in old), ",".join("%.3f" % w for w in new),
                "" if ok else "   [floors exceed the line: scaled down]"))
            out.append(t[last:m.start(2)]); out.append(newspec); last = m.end(2); changed += 1
        if changed and apply:
            out.append(t[last:]); open(f, "w", encoding="utf-8").write("".join(out))

if __name__ == "__main__":
    main()
