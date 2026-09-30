#!/usr/bin/env python3
"""build_appendix_e_tex.py — the Appendix E generation, stand-alone.

Session 32 origin: the pandoc build inlined the table by substituting the <!--APPENDIX_E_TABLE-->
placeholder; pandoc drops HTML comments, so the native path had a paragraph promising a table and
no table -- the defect a blank-slate reviewer rejected the paper for at r27.

s54 (R42-A3-6).  This tool used to take a vault root and edit <vault>/submission/tex/sections/appE.tex
in place.  That path stopped existing when the build moved to submission/native, whose section 19
does \\input{appendix_e_table}; the write branch therefore failed on every package and had not run
since.  The shipped build (papers/apal_build/build.sh, step 1) calls
manuscript/gen_appendix_e_numbered.py with five arguments and converts the printed table with
tools/md_to_native_tex.table.  This tool now does exactly that, into a directory the caller names,
and edits no manuscript source.  Its STATEMENT_MAP_FULL.md must equal release/STATEMENT_MAP_FULL.md
of the same package (the build gates the same equality).

Two artifacts, both generated, neither maintained by hand:
  <out_dir>/STATEMENT_MAP_FULL.md   every numbered statement of the indexed region
  <out_dir>/appendix_e_table.tex    the printed table (one row per PAPER_CLAIMS statement)
  (<out_dir>/appendix_e_table.md is the intermediate the build also keeps.)

Gates: exit 1 if the generator fails, if either table is empty, or if a numbered Theorem of the
indexed region has no row in the full map.

Usage: build_appendix_e_tex.py <MANUSCRIPT.md> <frozen_statements_dir> <PAPER_CLAIMS.tsv> <out_dir>
"""
# s34 (Gate-8 M02): statement labels may be lettered.  Theorem C.1 was invisible to every
# scanner because this pattern required a leading digit.  [A-Z]+ not [A-Z]: a single letter
# cannot match AA.1, which Gate-8 itself named as a required positive control.
import io, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main(md_path, frozen, claims, out_dir):
    gen = os.path.join(os.path.dirname(os.path.abspath(md_path)), 'gen_appendix_e_numbered.py')
    os.makedirs(out_dir, exist_ok=True)
    short_md = os.path.join(out_dir, 'appendix_e_table.md')
    full_md = os.path.join(out_dir, 'STATEMENT_MAP_FULL.md')
    r = subprocess.run(['python3', gen, md_path, frozen, short_md, full_md, claims],
                       capture_output=True)
    if r.returncode != 0:
        sys.stderr.write('GEN_FAILED\n' + r.stderr.decode('utf-8', 'replace')); sys.exit(1)

    full_rows = [l for l in io.open(full_md, encoding='utf-8').read().splitlines() if l.startswith('| ')]
    short_lines = [l for l in io.open(short_md, encoding='utf-8').read().split('\n') if l.startswith('|')]
    if len(full_rows) < 3:
        sys.stderr.write('FULL_MAP_EMPTY: %d rows\n' % len(full_rows)); sys.exit(1)
    if len(short_lines) < 3:
        sys.stderr.write('PRINTED_TABLE_EMPTY: %d rows\n' % len(short_lines)); sys.exit(1)

    # every numbered Theorem the generator INDEXES must have a row.  s52: the generator builds its
    # rows from src.split('## Appendix F')[0], and the paper says Appendix F "is not indexed in
    # either" table -- so the scope here is the same split expression, on purpose.
    # APPENDIX_E_GATE_SCOPED_S52
    src = io.open(md_path, encoding='utf-8').read()
    indexed = src.split('## Appendix F')[0]
    want = set(re.findall(r'^\*\*Theorem\s+((?:[0-9]+|[A-Z]+)\.[0-9]+)\*\*', indexed, re.M))
    thm = [l for l in full_rows[2:] if re.search(r'\|\s*Theorem\b', l)]
    have = set(re.findall(r'\|\s*((?:[0-9]+|[A-Z]+)\.[0-9]+)\s*\|', '\n'.join(thm)))
    if want - have:
        sys.stderr.write('THEOREM_WITHOUT_ROW: %s\n' % sorted(want - have)); sys.exit(1)

    # the same conversion as build.sh step 1 (md_to_native_tex.table)
    tools_dir = HERE if os.path.exists(os.path.join(HERE, 'md_to_native_tex.py')) else \
        os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(md_path))), 'tools')
    sys.path.insert(0, tools_dir)
    from md_to_native_tex import table
    io.open(os.path.join(out_dir, 'appendix_e_table.tex'), 'w', encoding='utf-8').write(
        '\n'.join(table(short_lines)) + '\n')
    print('APPENDIX_E_TEX_OK  full_rows=%d  printed_rows=%d  theorems_covered=%d/%d'
          % (len(full_rows) - 2, len(short_lines) - 2, len(want & have), len(want)))


if __name__ == '__main__':
    if len(sys.argv) != 5:
        sys.stderr.write(__doc__); sys.exit(2)
    main(*sys.argv[1:5])
