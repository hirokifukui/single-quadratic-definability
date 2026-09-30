#!/usr/bin/env python3
"""manuscript_index.py - the structural index of the paper, from either markup.

S05 moves the source of truth from Markdown to LaTeX. The nine *computed* Gate-5 checks read
Markdown syntax directly and cannot survive that move. Rather than write them twice, both markups
emit ONE structural index and the checks read the index.

Every field is something the migration must not change:

    title            one line
    abstract         running text, canonicalised, with its word count
    keywords         the keyword list, in order
    headings         top-level headings, in document order
    statements       (kind, number) of every numbered statement, in document order
    refs_defined     reference keys the bibliography defines, sorted
    refs_cited       reference keys the body cites, sorted

Typography is markup, not content: emphasis markers and the two spellings of the dashes are
canonicalised away before comparison. Anything else that differs is a real difference.

The tex front end accepts BOTH the run-in form a converter produces (\\textbf{Theorem 2.1}) and the
amsthm form the migration introduces (\\begin{theorem}...\\label{...:2.1}), so a half-migrated
document still indexes. Which form was seen is reported but is NOT part of the index.

Usage:
    python3 scripts/manuscript_index.py md   <MANUSCRIPT.md>  [out.json]
    python3 scripts/manuscript_index.py tex  <MANUSCRIPT.tex> [out.json]
    python3 scripts/manuscript_index.py compare <a.json> <b.json>       exit 1 if they differ
"""
# s34 (Gate-8 M02): statement labels may be lettered.  Theorem C.1 was invisible to every
# scanner because this pattern required a leading digit.  [A-Z]+ not [A-Z]: a single letter
# cannot match AA.1, which Gate-8 itself named as a required positive control.
import io, json, os, re, sys

KINDS = r'Theorem|Definition|Lemma|Corollary|Proposition|Remark|Examples?|Fact'
WORD = r"[A-Za-z\u2082\u2084\u2124\u2115][A-Za-z0-9'\u2019\-\u2082\u2084]*"   # identical to gate5_verify

def canon(s):
    s = s.replace('---', '\u2014').replace('--', '\u2013')
    s = s.replace('*', '').replace('`', '').replace('\u2019', "'")
    return re.sub(r'\s+', ' ', s).strip()

def words(s):
    return len(re.findall(WORD, s))

def detex(s):
    for a, b in ((r'\_', '_'), (r'\&', '&'), (r'\%', '%'), (r'\#', '#'),
                 (r'\{', '{'), (r'\}', '}'), ('{[}', '['), ('{]}', ']'), ('~', ' ')):
        s = s.replace(a, b)
    for _ in range(5):
        t = re.sub(r'\\(?:textbf|textit|emph|texttt|text|mathrm|hypertarget)\*?\{([^{}]*)\}', r'\1', s)
        if t == s:
            break
        s = t
    s = re.sub(r'\\[A-Za-z@]+\*?(\[[^\]]*\])?', ' ', s)
    return s.replace('$', ' ').replace('{', ' ').replace('}', ' ')

def index(title, abstract, keywords, headings, statements, refs_defined, refs_cited, form):
    return dict(title=canon(title), abstract=canon(abstract), abstract_words=words(canon(abstract)),
                keywords=[canon(k) for k in keywords], headings=[canon(h) for h in headings],
                statements=[[k, n] for k, n in statements],
                refs_defined=sorted(set(refs_defined)), refs_cited=sorted(set(refs_cited)),
                _form=form)

def from_md(src):
    lines = src.split('\n')
    title = lines[0][2:] if lines[0].startswith('# ') else ''
    abstract = src.split('**Abstract.**', 1)[1].split('\n---\n', 1)[0] if '**Abstract.**' in src else ''
    kw = src.split('**Keywords.**', 1)[1].split('\n')[0] if '**Keywords.**' in src else ''
    keywords = [k.strip().rstrip('.') for k in kw.split(';') if k.strip()]
    headings = [l[3:] for l in lines if l.startswith('## ')]
    statements = [(m.group(1).rstrip('s'), m.group(2))
                  for m in re.finditer(r'\*\*(' + KINDS + r')\s+((?:[0-9]+|[A-Z]+)\.[0-9]+)\*\*', src)]
    body, _, refsec = src.partition('## References')
    return index(title, abstract, keywords, headings, statements,
                 re.findall(r'^\[([A-Za-z0-9+]+)\]', refsec, flags=re.M),
                 re.findall(r'\[([A-Z][A-Za-z]{1,6}\d{0,2})\]', body), 'markdown')

def expand_inputs(src, base, depth=0):
    """s32: resolve \\input / \\include relative to the master file's directory.
    Found by planting three amsthm statements in sections/s01.tex and watching the reader
    report zero: it was reading the master only. A native LaTeX manuscript IS a master plus
    section files, so without this the index sees an empty document and stays green on it
    for the whole migration."""
    if depth > 8:
        sys.stderr.write('INPUT_DEPTH_EXCEEDED: refusing to recurse further\n'); return src
    def sub(m):
        rel = m.group(1).strip()
        if not rel.endswith('.tex'): rel += '.tex'
        q = os.path.join(base, rel)
        if not os.path.exists(q):
            sys.stderr.write('INPUT_NOT_FOUND: %s\n' % q); return ''
        return expand_inputs(io.open(q, encoding='utf-8').read(), os.path.dirname(q) or base, depth+1)
    return re.sub(r'\\(?:input|include)\{([^}]*)\}', sub, src)

def from_tex(src, base='.', auxsrc=None):
    src = expand_inputs(src, base)
    src = re.sub(r'(?<!\\)%.*', '', src)
    m = re.search(r'\\title\{(.*?)\}\s*\n', src, re.S)
    title = detex(m.group(1)) if m else ''
    # s32: the reader used to look ONLY for pandoc's \textbf{Abstract.}. A native LaTeX file
    # writes \begin{abstract} and the reader returned '' with no error -- silently, and in
    # exactly the direction of the migration this tool exists to guard. Both forms are read
    # now, and a document with neither is reported rather than scored as an empty abstract.
    m_env = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', src, re.S)
    if m_env:
        abstract = detex(m_env.group(1))
    else:
        a = re.split(r'\\textbf\{Abstract\.\}', src, maxsplit=1)
        abstract = detex(re.split(r'\\(?:sub)?section|\\begin\{center\}', a[1], maxsplit=1)[0]) if len(a) > 1 else ''
    if not abstract.strip():
        sys.stderr.write('ABSTRACT_NOT_FOUND: neither \\begin{abstract} nor \\textbf{Abstract.} '
                         'matched. A silently empty field is how a gate goes green on nothing.\n')
    k = re.split(r'\\textbf\{Keywords\.\}', src, maxsplit=1)
    kw = detex(k[1].split('\n\n')[0]) if len(k) > 1 else ''
    keywords = [x.strip().rstrip('.') for x in kw.split(';') if x.strip()]
    headings = [detex(x) for x in
                re.findall(r'\\(?:sub)?section\*?\{((?:[^{}]|\{[^{}]*\})*)\}', src, re.S)]
    run_in = [(m.group(1).rstrip('s'), m.group(2))
              for m in re.finditer(r'\\textbf\{(' + KINDS + r')\s+((?:[0-9]+|[A-Z]+)\.[0-9]+)\}', src)]
    # s32: statement numbers are NOT in a native LaTeX source. `\begin{theorem}` is lowercase and
    # the number 1.1 is assigned by LaTeX at compile time; an ordinary label reads
    # \label{thm:fragments}. The old regex wanted a capitalised environment whose label literally
    # contained the number, which is a pandoc-shaped expectation and reads zero statements on any
    # real amsthm document -- silently. Numbers are now read from the .aux, i.e. from what LaTeX
    # actually assigned, not from what the source claims. If the .aux is absent or a label is
    # missing from it, that is reported and the statement is not silently dropped.
    aux = {}
    auxpath = os.path.splitext(os.path.abspath(auxsrc))[0] + '.aux' if auxsrc else None
    if auxpath and os.path.exists(auxpath):
        for m in re.finditer(r'\\newlabel\{([^{}]+)\}\{\{([^{}]*)\}', io.open(auxpath, encoding='utf-8', errors='ignore').read()):
            aux[m.group(1)] = m.group(2)
    envs = []
    for m in re.finditer(r'\\begin\{(' + KINDS + r')\}\s*(?:\[[^\]]*\])?\s*(?:\\label\{([^{}]+)\})?',
                         src, re.I):
        kind = m.group(1).capitalize().rstrip('s')
        key = m.group(2)
        if key is None:
            sys.stderr.write('STATEMENT_WITHOUT_LABEL: a %s environment carries no \\label; '
                             'it cannot be matched across the two markups\n' % kind)
            continue
        num = aux.get(key)
        if num is None:
            if not auxpath or not os.path.exists(auxpath):
                sys.stderr.write('AUX_NOT_FOUND: %s -- statement numbers cannot be read until the '
                                 'document has been compiled once\n' % auxpath)
            else:
                sys.stderr.write('LABEL_NOT_IN_AUX: %s\n' % key)
            continue
        if re.fullmatch(r'(?:[0-9]+|[A-Z]+)\.[0-9]+', num or ''):
            envs.append((kind, num))
    # legacy path: labels that carry the number in the key itself (pandoc-era documents)
    envs += [(m.group(1).capitalize().rstrip('s'), m.group(2))
             for m in re.finditer(r'\\begin\{(' + KINDS + r')\}.{0,200}?\\label\{[^{}]*?((?:[0-9]+|[A-Z]+)\.[0-9]+)\}',
                                  src, re.S)]
    envs = sorted(set(envs))
    bib = re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}', src)
    # split on the References HEADING COMMAND, before detex flattens it into prose
    rp = re.split(r'\\(?:sub)?section\*?\{\s*References\s*\}', src, maxsplit=1)
    body, refsec = (detex(rp[0]), detex(rp[1])) if len(rp) == 2 else (detex(src), '')
    defined = bib if bib else re.findall(r'^\s*\[([A-Za-z0-9+]+)\]', refsec, flags=re.M)
    return index(title, abstract, keywords, headings, run_in + envs, defined,
                 re.findall(r'\[([A-Z][A-Za-z]{1,6}\d{0,2})\]', body),
                 'latex (run-in %d, amsthm %d)' % (len(run_in), len(envs)))

def restrict(idx, secs):
    """s32, defect 1. The comparison was whole-document, so every intermediate state of a
    section-by-section migration was red and the gate could not tell a bad step from an unfinished
    one. In partial mode the caller states which sections it CLAIMS to have migrated; the
    statement list is restricted to those sections on both sides, and the fields that cannot be
    meaningful until the end are skipped BY NAME rather than quietly passing."""
    out = dict(idx)
    keep = set(secs)
    def sec_of(num):
        return num.split('.')[0]
    out['statements'] = sorted(
        tuple(x) for x in idx.get('statements', [])
        if sec_of((tuple(x))[1]) in keep)
    for f in ('refs_cited', 'refs_defined', 'headings'):
        out.pop(f, None)
    return out


def compare(a, b, secs=None):
    bad = 0
    if secs:
        a, b = restrict(a, secs), restrict(b, secs)
        print("PARTIAL_MODE sections=%s" % ",".join(secs))
        print("SKIPPED_FIELDS refs_cited, refs_defined, headings "
              "-- not meaningful until the bibliography and all sections have moved")
    for k in [x for x in sorted(a) if not x.startswith('_')]:
        va, vb = a[k], b.get(k)
        if va == vb:
            print("SAME %-16s (%s)" % (k, len(va) if isinstance(va, list) else 1))
            continue
        bad += 1
        print("DIFF %s" % k)
        if isinstance(va, list):
            ta = [tuple(x) if isinstance(x, list) else x for x in va]
            tb = [tuple(x) if isinstance(x, list) else x for x in (vb or [])]
            print("   len %d vs %d" % (len(ta), len(tb)))
            print("   only in A: %s" % [x for x in ta if x not in tb][:8])
            print("   only in B: %s" % [x for x in tb if x not in ta][:8])
        else:
            sa, sb = str(va), str(vb)
            i = next((j for j in range(min(len(sa), len(sb))) if sa[j] != sb[j]), min(len(sa), len(sb)))
            print("   first difference at char %d" % i)
            print("   A: ...%s..." % sa[max(0, i - 40):i + 40])
            print("   B: ...%s..." % sb[max(0, i - 40):i + 40])
    print("INDEX_FIELDS=%d  DIFFERING=%d  INDEX_EQUAL=%s" %
          (len([x for x in a if not x.startswith('_')]), bad, bad == 0))
    return 1 if bad else 0

if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.stderr.write(__doc__)
        sys.exit(2)
    if sys.argv[1] == 'compare':
        secs = None
        for _i, _x in enumerate(sys.argv):
            if _x == '--sections' and _i + 1 < len(sys.argv):
                secs = [t.strip() for t in sys.argv[_i+1].split(',') if t.strip()]
        sys.exit(compare(json.load(open(sys.argv[2], encoding='utf-8')),
                         json.load(open(sys.argv[3], encoding='utf-8')), secs))
    src = open(sys.argv[2], encoding='utf-8').read()
    idx = from_md(src) if sys.argv[1] == 'md' else from_tex(src, os.path.dirname(os.path.abspath(sys.argv[2])), sys.argv[2])
    if len(sys.argv) > 3:
        json.dump(idx, open(sys.argv[3], 'w', encoding='utf-8'),
                  ensure_ascii=False, indent=1, sort_keys=True)
    print("FORM=%s" % idx['_form'])
    for k in sorted(idx):
        if k.startswith('_'):
            continue
        v = idx[k]
        print("  %-16s %s" % (k, len(v) if isinstance(v, list) else
                              (v if not isinstance(v, str) or len(v) < 55 else v[:52] + '...')))
