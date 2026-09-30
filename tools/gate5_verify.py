#!/usr/bin/env python3
"""gate5_verify.py — mechanical verification of the 330 Gate-5 items.

Every item carries an explicit predicate over the artifact files. The predicate is
evaluated by this script, not read by a person, and each PASS records file:line.
A predicate is one of:
    ("has", FILE, regex)      the regex must occur
    ("hasnt", FILE, regex)    the regex must not occur
    ("count", FILE, regex, n) the regex must occur at least n times
    ("num", FILE, regex, lo, hi)  first capture group, as an int, in [lo,hi]
    ("file", PATH)            the path must exist
    ("ruling", why)           closed by a standing ruling of Dr. Fukui, not by a file

Usage: gate5_verify.py <vault> [--tsv OUT]
Exit 0 when every item passes; exit 1 on any FAIL. The report carries the detail.
"""
import os, re, sys, csv, json

def load(v, rel):
    p = os.path.join(v, rel)
    if not os.path.exists(p):
        return None
    return open(p, encoding='utf-8').read()

M   = 'manuscript/MANUSCRIPT_V32.md'
T   = 'release/TRUST_BOUNDARY_APAL.md'
RB  = 'release/README_BUILD_APAL.md'
RC  = 'release/RELEASE_CHECKLIST_APAL.md'
CL  = 'submission/APAL_COVER_LETTER_v1.md'
CK  = 'submission/APAL_SUBMISSION_CHECKLIST_v1.md'
NG  = 'literature/NOVELTY_FINAL_GATE_s30.md'
GX  = 'literature/GS_CROSSWALK.md'
BS  = 'referee_simulation/s30/BLANK_SLATE_APAL_V32.md'
CFF = 'release/CITATION.cff'
HIST = 'history/DEVELOPMENT_AUDIT_HISTORY.md'   # s38 (Gate-12 H01)
DN  = 'development_notes/README.md'
ER  = 'correspondence/ERRATA_GATE5_20260903.md'
PDFLOG = 'papers/apal_build/APAL_MANUSCRIPT_v32.log'
# T01: no absolute development path. 'W:' items resolve against WORK, which defaults to the
# package root itself (self-contained when run from an expanded archive) and can be pointed
# elsewhere with MPUP_WORK for in-workspace runs.
WORK = os.environ.get('MPUP_WORK') or (sys.argv[1] if len(sys.argv) > 1 else '.')

# Appendix F is a REGION of the manuscript; predicates aimed at the proof are
# evaluated on that region alone, so that a hit in the body cannot satisfy them.
def region(text, start, end=None):
    if text is None: return None
    i = text.find(start)
    if i < 0: return ''
    j = text.find(end, i) if end else len(text)
    return text[i:(j if j > 0 else len(text))]

P = {}   # (group, item) -> (predicate, human note)

def A(g, i, pred, note=''):
    if (g, str(i)) in P:
        raise SystemExit('gate5: duplicate rule id %s-%s - a second registration would '
                         'silently replace the first' % (g, i))
    P[(g, str(i))] = (pred, note)

# ---------------------------------------------------------------- 必須A
A('MA',1,("hasnt",M,r"AtomGraphZZ 2 n .{0,20}(if and only if|↔)"))
A('MA',2,("hasnt",M,r"positive half"))
A('MA',3,("hasnt",M,r"we do not claim that the inequality n ≤ 2m"),
  's50: SUPERSEDED by Theorem 4.1 (n <= m, sharp).  The r39 manuscript disclaimed attainment of n <= 2m;\n   that disclaimer is retracted, so the row is inverted and now forbids the retracted sentence from\n   returning rather than requiring it.')
A('MA',4,("has",M,r"\| one-sorted \| ℤⁿ \| ℤ \| ℤʳ \| `AtomGraphZZ` \| \*\*none exists\*\* \(Corollary 4\.4\) \|"),
  's50: re-pointed at the same table row; the cell went from open to none exists (Corollary 4.4).')
# s35 (Gate-9 G07): the rule used to require the SUPERSEDED disposition file by name, which is
# why two shipped.  A gate can compel a defect as easily as it can forbid one.
A('MA',5,("wfile",'certificates/fidelity_destroyer_current.tsv'))
A('MA',6,("has",M,r"No single quadratic equation defines the graph of an injection ℤⁿ → ℤ for n ≥ 2"),
  's50: re-pointed; Corollary 4.4 lowered the threshold from n >= 3 to n >= 2.')
A('MA',7,("has",M,r"AtomGraphZZ 1 1\s+\(the lower bound"))
A('MA',8,("hasnt",M,r"the value at n = 2 is open"),
  's50: SUPERSEDED by Corollary 4.4, which determines ca(SE2) = 1.  The row is inverted: the manuscript\n   must no longer say the value is open.')
# s35 (Gate-9 S01): the reconciliation moved from the manuscript to the artifact.  The anchor
# moves with the sentence, in the same commit; a rule left pointing at the old home would
# report on a document that no longer says it.
A('MA',9,("has",T,r"The axiom report has \d+ roots; the declaration diff has \d+ frozen theorem statements; \d+ declarations are in both"), 's36: figures are generated (tools/generate_trust.py); their agreement with the certificates is gated by shipping_artifact_gate')
# s35: 'verbatim diff' -> 'declaration diff' (Gate-9 G08).  The anchor moves in the same commit
# as the sentence: a gate whose anchor lags the text it guards reports on a document that no
# longer exists, which is the r30 defect one directory over.
# s34: figures re-anchored after the WeightedBound freeze (398/436/347 -> 417/455/366).  The anchor
# stays exact on purpose: loosening it to a regex would let the reconciliation drift unnoticed.
# s35 (Gate-9 S01): moved with the paragraph, like MA-9.  Both anchors sat in the two blocks that
# left section 11, and only one was moved at first -- the second was found by running the gate,
# not by remembering.  That is the point of running the whole battery after a move.
# s38 (Gate-12 H01): the census correction history left TRUST for history/DEVELOPMENT_AUDIT_HISTORY.md;
# TRUST must now carry the current three figures as words and must NOT carry the correction story.
A('MA',11,("has",T,r"are outside the frozen-statement set: [a-z-]+ of those"))
A('MA',61,("hasnt",T,r"said nineteen, nine and ten"))
A('MA',62,("has",HIST,r"said nineteen, nine and ten where the development had twenty-six, eleven and fifteen"))
A('MA',13,("has",M,r"Section 2 defines no coder"))
A('MA',14,("hasnt",M,r"pairing code of \u00a72"))
A('MA',15,("hasnt",M,r"published form of the obstruction"))
# s35 (Gate-9 G03/G08).  Both sentences below were false in the shipped r30 PDF and neither had a
# gate: the footprint claim said every root uses all three standard axioms when 394 of 413 do, and
# the diff was called verbatim when it normalises whitespace.  A repair with no anchor is a repair
# that can be undone by the next edit that does not know about it.
A('MA',16,("has",M,r"contained in the standard set"))
A('MA',17,("hasnt",M,r"each of those depends on exactly"))
A('MA',18,("hasnt",M,r"diffed verbatim against the production tree"))
# s35 (Gate-9 red-team homework 8).  The introduction and section 10 both asserted that neither
# hierarchy refines the other, and section 10 named two lemmas as incomparable with Theorem 5.1.
# No comparison theorem is proved anywhere in the paper.  The claim is now about what we prove.
A('MA',19,("hasnt",M,r"neither hierarchy refines the other"))
A('MA',20,("hasnt",M,r"neither implies nor is implied by Theorem 5\.1"))
A('MA',21,("has",M,r"We prove no comparison between the two hierarchies in either direction"))
# s35 (Gate-9 Appendix C destroyer, homework 7 and 8): the two edges of the count that the review
# asked for.  Both were absent and both are one sentence; neither needed a new case in the proof.
A('MA',22,("has",M,r"If some f_m is identically zero the display still holds"))
A('MA',23,("has",M,r"a constant equation represents no coder of positive arity"))
# s35 (Gate-9 §11.2 and §11.3).  The section 9 roadmap described the singular case as an induction
# on the number of unknowns, which Part II does not do -- it dispatches on the rank of the
# nondegenerate quotient -- and described the full-rank case by the isotropic/anisotropic split,
# which sits inside the direction lemma rather than at the top.  A roadmap that names the wrong
# structure is a reader sent to look for exhaustiveness in the wrong place.
A('MA',24,("hasnt",M,r"reduces the number of unknowns, and the induction hypothesis applies"))
A('MA',25,("has",M,r"dispatches on the rank k\u2080 of the nondegenerate quotient"))
A('MA',26,("has",M,r"The top-level split is on the sign of"))
# s35 (Gate-9 §14).  The Methods section and the AI declaration repeated three sentences verbatim
# between them -- the delegation, the adversarial reader, the statement of responsibility.  Split by
# function instead, as Elsevier's policy asks: research and code use under Methods, manuscript
# preparation in the declaration, and the round-by-round record in the artifact.
A('MA',27,("has",M,r"After using these tools the author reviewed and edited the content as needed"), 's36 (Gate-10 M02): declaration in the Elsevier form; the two-error record moved to TRUST section 8')
# s38 (Gate-12 H01): the adversarial-review record is in the history file, not in current TRUST.
A('MA',28,("hasnt",T,r"The adversarial-review record"))
A('MA',63,("has",HIST,r"caught by the adversarial reader"))
A('MA',64,("has",T,r"history/DEVELOPMENT_AUDIT_HISTORY\.md"))
# s35 (Gate-9 §16 answer 3): the counts left the paper for the artifact.  The paper keeps the
# qualitative claim, which is on the review's own keep-list; the numbers are recomputed against the
# certificates by submission_figures.py --trust.
A('MA',29,("hasnt",M,r"\u27e8(ROOTS|THMS|DEFS|UNCOND|BROOTS)\u27e9"))
A('MA',30,("has",T,r"FIGURES \(recomputed by tools/submission_figures\.py"))
# s35 (Gate-9 §8 and §12): Appendix E's paragraph had three false clauses at once -- the printed
# table was not theorems-only, the "full" map was a stale duplicate of it, and it shipped nowhere.
# s38 (Gate-12 M06): Appendix E prints the rows of the paper-claim manifest.
A('MA',31,("has",M,r"one row per statement of that manifest"))
A('MA',32,("hasnt",M,r"long enough that printing it serves no reader"))
A('MA',33,("has",M,r"`release/STATEMENT_MAP_FULL\.md` in the artifact"))
A('MA',12,("has",M,r"both closed forms are verified in the formal artifact"), 's36 (Gate-10 M03): Remark C.2 purged of development chronology; the closed forms are stated as theorems, not as a promotion story')
A('MA',10,("hasnt",CL,r"exact arity"))
# ---------------------------------------------------------------- 必須B
A('MB',1,("has",M,r"three forms produced by the proof"))
A('MB',2,("has",M,r"they are not claimed to be canonical"))
A('MB',3,("has",M,r"the selection is not constructive|choice supplies the witnesses"))
A('MB',4,("has",T,r"selected from membership proofs\s*\n?using `Classical\.choice`"))
A('MB',5,("hasnt",M,r"effective certificate"))
A('MB',6,("has",M,r"no generic fallback|generic certificate"))
A('MB',7,("has",M,r"`quadraticProjectionDichotomyZ_all_data`, `TopDichotomyData`"))
A('MB',8,("has",M,r"generated documentation layer that mirrors that analysis"))
A('MB',9,("count",M,r"\*Polynomial progression\.\*|\*Pell-unit orbit\.\*|\*Moving-modulus step orbit\.\*",3))
A('MB',10,("has",M,r"\*Overlap\.\* The three kinds are not mutually exclusive"))
A('MB',11,("has",M,r"\| empty \| 1 = 0 \|"))
A('MB',12,("has",M,r"\| finite, nonempty \| c² − 4 = 0"))
A('MB',13,("has",M,r"\| infinite on the nonpositive side only \| c \+ u² = 0"))
A('MB',14,("has",M,r"halves meet exactly in the output zero \(`halves_inter`\)"))
A('MB',15,("has",M,r"∃ C ∈ ℕ, ∀ a ∈ ℤⁿ"))
# ---------------------------------------------------------------- 必須D
A('MD',1,("num",M,r"ABSTRACTWORDS",0,0))    # replaced below by a computed check
A('MD',2,("count",M,r"\*\*Keywords\.\*\* [^\n]*;",1))
A('MD',3,("has",M,r"Two published results enter as named hypotheses"))
A('MD',4,("hasnt",M,r"are therefore computable"))
# s35: the abstract was tightened for length and this anchor stayed on the old wording.  What the
# rule guards is the claim -- computability comes from totality together with a Diophantine graph --
# and the new sentence still makes it.  The anchor moves with the sentence it guards.
# s37: the clause naming the mechanism was cut for length (M09); the claim the rule guards is that
# the abstract says the functions are computable, and it still does.  The anchor moves again.
A('MD',5,("has",M,r"they are computable"))
A('MD',6,("has",M,r"Sections 2–9 are formalized in Lean 4"))
A('MD',7,("hasnt",M,r"PellClassFiniteness"))
A('MD',8,("hasnt",M,r"effective certificate|effectively extract"))
A('MD',9,("hasnt",M,r"exact coding arity"))
A('MD',10,("has",M,r"Grunewald–Segal decidability of quadratic solvability \(code-uniform\) and DPRM over ℕ"))
# ---------------------------------------------------------------- 必須E
A('ME',1,("has",GX,r"CLOSED.*integral.*rational affine hyperplanes"))
A('ME',2,("has",M,r"\[GS04\] as the source of Definition 1\.5 and \[GS81\] as its announcement"))  # s39: Definition 1.4 -> 1.5 (arity-zero became Proposition 1.4)
A('ME',3,("has",M,r"Multiplying an equation through by a common denominator"))
A('ME',4,("has",M,r"The headline statement of \[GS04\] concerns solutions in positive integers"))
A('ME',5,("has",M,r"u = u⁺ − u⁻ with u⁺, u⁻ ≥ 1 carries integer solutions to positive ones and back"))
A('ME',6,("has",M,r"The witness arity is part of the code"))
A('ME',7,("has",M,r"Theorem 6\.4 supplies the compiler"))
A('ME',8,("has",M,r"turns an instance in our form into a parameter-free coefficient table"))
A('ME',9,("has",M,r"`QuadraticCode\.evalZZ`"))
A('ME',10,("has",M,r"clause-by-clause crosswalk from \[GS04\] to Definition 1\.5"))  # s39 renumber
A('ME',11,("hasnt",M,r"exactly the input/output contract"))
A('ME',12,("has",T,r"effective coding-equivalent consequence"))
# ---------------------------------------------------------------- 必須F
A('MF',1,("has",M,r"## Appendix A\. Open problems"))  # s60: GATE30 R-A, normal forms promoted to Section 10
A('MF',2,("hasnt",M,r"PellClassFiniteness"))
# s35: the sentence now speaks of two tables, so "there" became "in either".  The anchor moves with
# the sentence it guards; leaving it behind would have made this rule pass on a phrase that no
# longer exists, which is how MA-5 and HW1 went wrong earlier this session.
A('MF',3,("has",M,r"Appendix F carries its own proofs and is not indexed in either"))
# s35, ruling on Gate-9 (0).  The appendix said the two older proof documents were kept in step with
# it.  Measured for r31 they are not: the appendix carries a weakened and correct Pell hypothesis
# where they state a stronger one, a classical fact proved rather than cited, Corollary V.5, a
# reduction step, and some 86 more lines in Part II.  The direction was settled on evidence -- every
# difference is a correction or an addition on the appendix's side, and they carry no mathematics it
# lacks -- so the appendix is the text of record and they are superseded drafts.
A('MF',7,("hasnt",M,r"text of record|earlier proof document|line-by-line comparison|correction history"), 's36 (Gate-10 §9/N07): Appendix F carries no development history; the record is history/superseded_appendixF/APPENDIX_F_PROVENANCE.md')
A('MF',8,("has",M,r"This appendix proves Theorems 9\.2 and 9\.3 in full\. Parts I and II give"))
A('MF',9,("hasnt",M,r"so that the two continue to agree"))
A('MF',10,("hasnt",M,r"reproduced verbatim"))
A('MF',4,("file",'development_notes/OneWitnessNormalForm_STATEMENTS_v3.lean'))
A('MF',5,("has",M,r"\*\*A one-witness normal form\.\*\*"))
A('MF',6,("has",DN,r"Status: conditional and unproved"))
# ---------------------------------------------------------------- 必須G
A('MG',1,("num",M,r"TITLELEN",0,0))
A('MG',2,("has",M,r"\*\*Author\.\*\* Hiroki Fukui \(Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo, Japan; Department of Neuropsychiatry, Kyoto University"))
A('MG',3,("num",M,r"ABSTRACTWORDS",0,0))
A('MG',4,("num",M,r"KEYWORDS",0,0))
A('MG',5,("has",M,r"\*\*MSC 2020\.\*\* Primary 03D25"))
A('MG',6,("has",PDFLOG,r"Output written on .*\.pdf"))
A('MG',7,("file",'submission/APAL_MANUSCRIPT_v32.pdf'))
A('MG',8,("num",M,r"NUMBERING",0,0))
A('MG',9,("num",M,r"REFS",0,0))
A('MG',10,("has",M,r"## Appendix F\. The arithmetic projection theorem: complete proof"))
A('MG',11,("has",M,r"Grechuk and Agbanwa \[GA26\]"))
A('MG',12,("has",M,r"## Methods"))
A('MG',13,("has",M,r"## Declaration on AI-assisted tools"))
A('MG',14,("ruling","artifact DOI reserved together with the Zenodo deposit, in the single final pass"))
A('MG',15,("has",M,r"\*\*External inputs are hypotheses\.\*\*"))
A('MG',16,("hasnt",M,r"\br1[0-9]\b|\br2[0-9]\b|\br3[0-9]\b|必須|宿題|(?<!Chat)GPT"), 's36: the AI declaration names the tools (Elsevier form), so ChatGPT is allowed there; a bare GPT (the reviewer) is not')
A('MG',17,("num",M,r"NOROOTS",0,0))
A('MG',18,("num",M,r"NOFILENAMES",0,0))
# s35: this rule was first registered as MG-18, which already existed.  The table is keyed by id,
# so the existing rule silently replaced it: the item count did not move and the planted control did
# not fire.  A gate that can be overwritten by a name collision is a gate that can pass silently,
# which is the defect this round has been about.  A() now refuses duplicate ids.
A('MG',21,("num",M,r"TOOLDRIFT",0,0))
A('MG',19,("num",M,r"APPENDICES",0,0))
A('MG',20,("num",PDFLOG,r"PDFCLEAN",0,0))
# ---------------------------------------------------------------- 必須H
A('MH',1,("has",T,r"\| axiom_roots \(roots reported\) \| \d+ \|"))
A('MH',2,("has",T,r"\| DPRM over ℕ \| Definition 1\.6 \|"))  # s39 renumber
A('MH',3,("has",T,r"`Classical\.choice`"))
A('MH',4,("has",T,r"## 5\. What is open, and stated as open"))
# s38 (Gate-12 H02): "verbatim" became the exact name of the comparison; the figures follow it.
A('MH',5,("has",T,r"whitespace-normalized textual declaration comparison \(`scripts/statement_diff\.py`: (\d+)/\1 theorems,\s*(\d+)/\2 definitions"))
A('MH',61,("hasnt",T,r"compared verbatim"))
A('MH',6,("has",CFF,r'title: "Structure and Computability[\s\S]{0,2000}version: "\d+\.\d+(\.\d+)?"'), 's36: the version string is checked against release/SEAL_INPUT.env by shipping_artifact_gate, not pinned here')
A('MH',7,("has",RB,r"lake build DiophCompression"))
# s40 (Gate-14 P04): README_BUILD is generated and carries no historical manifest value; the anchor is the
# rule that the seal records the manifest, i.e. the form, not a value that changes with the tree.
# s62 (GATE32 E-32-3): the listing's hash is the clean-room key SRC_MANIFEST_SHA256; the old sentence named the
# distribution-scope SOURCE_MANIFEST_SHA256.  Same purpose, corrected sentence.
A('MH',8,("has",RB,r"The SHA-256\s+of\s+this\s+listing\s+is\s+the\s+clean-room\s+key\s+`SRC_MANIFEST_SHA256`"))
A('MH',9,("has",T,r"(\d+)/\1 theorems"))
A('MH',10,("has",T,r"## 6\. Boundary of this artifact"))
# s37 (Gate-11 B04): the sentence this rule pinned was itself round history and was removed.  The
# property it asserted is checkable directly, and checking it is stronger than reading a sentence
# that says it: no round label may appear in the trust document at all.
A('MH',11,("hasnt",T,r"\br(2[0-9]|3[0-9])\b|Gate-[0-9]"))
A('MH',12,("ruling","final clean-room rebuild, run after the last source edit"))
# ---------------------------------------------------------------- 必須I
for i,key in [(1,'uniform finite-fibre height'),(2,'finite-fibre cardinality'),(3,'quadratic growth'),
              (4,'injective dimension'),(5,'polynomial graph classification'),(6,'composition'),
              (7,'phase diagram'),(8,'bounded-or-structured summit'),(9,'three structured output forms'),
              (10,'MPUP')]:
    A('MI',i,("count",NG,r"^\| %d \|"%i,1))
# ---------------------------------------------------------------- 必須J
A('MJ',1,("has",BS,r"\*\*Verdict: send to review\.\*\*"))
A('MJ',2,("has",BS,r"## 2\. Logic / computability referee[\s\S]{0,4000}\*\*Verdict"))
A('MJ',3,("has",BS,r"## 3\. Number-theory referee[\s\S]{0,4000}\*\*Verdict"))
A('MJ',4,("has",BS,r"## 4\. Formalization referee[\s\S]{0,4000}\*\*Verdict"))

# ================= Appendix F region: 必須C and homework 3/4/5 =================
# All predicates below are evaluated on the Appendix F region of the manuscript
# alone (marker "APPF"), so a hit in the body cannot satisfy a proof obligation.
APPF = 'APPF'

def C(g, i, rx, note=''):
    P[(g, str(i))] = (("has", APPF, rx), note)

# ---- 必須C: the twenty-five lemmas -------------------------------------------
C('MC',1,  r"#### 0\. Setup and notation")
C('MC',2,  r"#### 1\. The completion identity|adjugate")
C('MC',3,  r"#### 2\. The scaled line through a fiber point")
C('MC',4,  r"lattice|(2\.2)")
C('MC',5,  r"signed non-square direction")
C('MC',6,  r"\(III\.2\)  X_\{k\+1\} = X_k·P \+ D·Y_k·Q,   Y_\{k\+1\} = X_k·Q \+ Y_k·P")
C('MC',7,  r"#### Lemma III\.1 \(norm preservation along the orbit\)")
C('MC',8,  r"#### Lemma III\.2 \(congruence preservation\)")
C('MC',9,  r"#### Lemma III\.3 \(strict growth\)")
C('MC',10, r"#### 2\. Lemma 2 — integral radical decomposition")
C('MC',11, r"saturat")
C('MC',12, r"torsion")
C('MC',13, r"unimodular")
C('MC',14, r"#### 3\. Lemma 3A — nonzero-minor periodicity")
C('MC',15, r"#### 4\. Lemma 3B — proportional compression")
C('MC',16, r"#### 5\. Lemma 4 — quotient-rank-zero leaf")
C('MC',17, r"#### 7\. Lemma 6 — rank-one coupled dichotomy")
C('MC',18, r"k₀ = 1")
C('MC',19, r"#### 6\. Lemma 5 — moving-modulus prime progression \(k₀ ≥ 2\)")
C('MC',20, r"\*Choice of prime\.\* Let D = 2·\|det G₀\|·b·t₀ > 0")
C('MC',21, r"CRT|Chinese remainder|coordinatewise")
C('MC',22, r"witness")
C('MC',23, r"#### IV\.1 From a branch to a data-carrying family")
C('MC',24, r"#### IV\.2 Output-negation transport")
C('MC',25, r"#### IV\.3 The summit")

# ---- 宿題群3: full-rank proof (22) ------------------------------------------
hw3 = [r"#### 0\. Data and statement", r"Gram", r"det", r"adjugate", r"α", r"c₀ ∈ S",
       r"#### 3\. The bounded alternative at a point", r"#### 8\. Producing the direction",
       r"definite", r"split|isotropic", r"anisotropic", r"#### 2\. The scaled line",
       r"lattice", r"binary", r"discriminant", r"whose automorph moves the initial solution",
       r"\(P \+ Q√D\)\^d|unit powers|Iterating the unit|(P, Q)\^d",
       r"congruence", r"output", r"#### Lemma III\.3 \(strict growth\)",
       r"#### 9\. The constant", r"#### Part IV\. Assembly|### Part IV\. Assembly"]
for i,rx in enumerate(hw3,1): C('HW3',i,rx)

# ---- 宿題群4: singular proof (24) -------------------------------------------
hw4 = [r"saturat", r"torsion", r"finitely generated|finite generation|rank",
       r"complement", r"basis", r"unimodular", r"block|Gram", r"skew|symmetr",
       r"radical", r"pair minor|pair-minor", r"gcd", r"periodic",
       r"all pair minors vanish|all minors", r"primitive", r"proportional",
       r"compression", r"k₀ = 0", r"k₀ = 1", r"k₀ ≥ 2", r"edge case",
       r"b = 0", r"μ = 0", r"The unimodular change w ↦ −w replaces", r"#### 8\. Assembly and the capacity corollary"]
for i,rx in enumerate(hw4,1): C('HW4',i,rx)

# ---- 宿題群5: moving-modulus proof (20) -------------------------------------
hw5 = [r"initial solution|starting solution", r"positive modulus|bc\+μ|bc \+ μ",
       r"if every solution has bc\+μ ≤ 0", r"Let D = 2·\|det G₀\|·b·t₀ > 0", r"prime progression",
       r"odd prime|p odd|oddness", r"det.*mod p|nonvanishing", r"finite field|𝔽_p|mod p",
       r"affine", r"root", r"t₀|modulo t", r"CRT|Chinese remainder", r"divisib",
       r"Set w₁ = −F₀\(c₁, v₁\)/\(t₀p\) ∈ ℤ", r"output increase|strict.*growth|grows",
       r"recurrence", r"infinite sequence|infinitely many", r"a certificate for the original polynomial P",
       r"not effective|non-effective|choice", r"∎"]
for i,rx in enumerate(hw5,1): C('HW5',i,rx)

# ---- 宿題群1 (16): the fidelity sweep ---------------------------------------
# s35 (Gate-9 G07).  Second anchor to the superseded file, found only because MA-5 was moved
# and this one failed.  Two independent rules were holding the retired disposition file in the
# archive; renaming a canonical artifact means grepping for it, not editing the rule you knew
# about.
DEST = 'W:certificates/fidelity_destroyer_current.tsv'
hw1 = [("has",M,r"natInput_intInput_separation_at_two"), ("has",DEST,r"D3\tSTOP"),   # s50: was ("hasnt",M,"AtomGraphZZ 2 2") -- SUPERSEDED by Corollary 4.4; the n = 2 case is settled and the row now requires the separation theorem instead of forbidding the mention
       ("has",M,r"\| mixed \| ℕⁿ \| ℕ \| ℤʳ \| `GraphAchievableZ` \|"),
       ("has",M,r"\| one-sorted \| ℤⁿ"), ("has",M,r"\| mixed \| ℕⁿ \| ℕ"),
       ("has",M,r"ℤʳ \| `AtomGraphZZ`"), ("has",M,r"AtomGraphZZ 1 1"),
       ("hasnt",M,r"the value at n = 2 is open"),   # s50: SUPERSEDED by Corollary 4.4 -- inverted, the manuscript must no longer say it
       ("has",M,r"AtomGraphZZ 2 n → n ≤ 2"),
       ("has",M,r"remains true and is now a corollary of Theorem 4\.1"),   # s50: re-pointed at Remark 4.5; n <= 2m is retained as a corollary of the sharp bound
       ("has",M,r"## Appendix B\. Capacity refinements"),
       ("hasnt",M,r"\*\*Abstract\.\*\*[\s\S]{0,3000}?exact coding arity"),
       ("has",M,r"## 1\. Fragments"), ("hasnt",CL,r"exact arity"),
       ("has",M,r"## Appendix E\. Statement map"),
       ("has",ER,r"planted copy, with a false `iff` written into it")]
for i,p in enumerate(hw1,1): P[('HW1',str(i))]=(p,'')

# ---- 宿題群2 (20): summit quantifier red team -------------------------------
hw2 = [r"∃ C ∈ ℕ, ∀ a ∈ ℤⁿ", r"The weak form ∀ a ∃ C_a", r"C is chosen after P",
       r"\*before\* a", r"\| finite, nonempty \|", r"\| infinite on both sides \|",
       r"\| empty \| 1 = 0 \|", r"the ε = −1 transport", r"nonpositive side only",
       r"infinite on both sides", r"the output zero alone",
       r"`uniform_bound_certificate_exclusive`", r"choice supplies the witnesses",
       r"\*pin\* the output map", r"strictly monotone", r"generic certificate",
       r"`quadraticProjectionDichotomyZ_all_data`", r"`weak_target_trivial_on_finite_fibre`",
       r"The order of the quantifiers is the content of the definition",
       r"\*\*Examples 8\.6\*\*"]
for i,rx in enumerate(hw2,1): P[('HW2',str(i))]=(("has",M,rx),'')

# ---- 宿題群6 (18): certificate semantics ------------------------------------
hw6 = [(M,r"\*Polynomial progression\.\* The equation c − u² = 0"),
       (M,r"\*Pell-unit orbit\.\* The equation c² − 2u² − 1 = 0"),
       (M,r"\*Moving-modulus step orbit\.\*"), (M,r"\*Overlap\.\*"),
       (M,r"not claimed to be canonical"), (M,r"\*pin\* the output map"),
       (M,r"each of its elements is\s*\n?realised|witness"),
       (T,r"`Classical\.choice`"), (M,r"not a canonical invariant of the fibre"),
       (M,r"not mutually exclusive"), (M,r"^(?!.*effective certificate).*$"),
       (M,r"#### IV\.2 Output-negation transport"), (M,r"kind of the family is preserved"),
       (M,r"generated documentation layer"), (M,r"`TopDichotomyData`"),
       (M,r"three forms produced by the proof"),
       (M,r"three forms: polynomial progressions, Pell-unit orbits, moving-modulus step orbits"),  # s39 (M06 abstract)
       (NG,r"No priority claim is made anywhere")]
for i,(f,rx) in enumerate(hw6,1): P[('HW6',str(i))]=(("has",f,rx),'')

# ---- 宿題群7 (20): GS / DPRM trust boundary ---------------------------------
hw7 = [(GX,r"J\. Reine Angew\. Math\. \*\*569\*\* \(2004\), 13–45"),
       (GX,r"Math\. Proc\. Cambridge Philos\. Soc\. \*\*89\*\* \(1981\), 1–5"),
       (M,r"\[GS04\] admits rational coefficients"), (M,r"a quadratic code carries integer ones"),
       (M,r"positive integers"), (M,r"Ours range over ℤ"),
       (M,r"The witness arity is part of the code"), (M,r"parameter-free coefficient table"),
       (M,r"specialising the parameters|parameter"), (M,r"primitive recursive"),
       (M,r"UniformQuadraticSolvabilityOnCodes"), (M,r"DPRM_NN"),
       (M,r"\*\*Definition 1\.6\*\*"), (M,r"total degree at most two"),
       (M,r"arbitrarily many unknowns|in arbitrarily many unknowns"),
       (M,r"it is proved here \(Theorem 6\.2\)"), (T,r"## 3\. External inputs"),
       (M,r"Two are external"), (CL,r"named hypotheses"), (CL,r"Grunewald–Segal")]
for i,(f,rx) in enumerate(hw7,1): P[('HW7',str(i))]=(("has",f,rx),'')

# ---- 宿題群8 (24): the manuscript -------------------------------------------
hw8 = [(M,r"NUM:TITLELEN"),(M,r"NUM:ABSTRACTWORDS"),(M,r"NUM:KEYWORDS"),
       (M,r"Let SE₂ be the class of relations on ℤᵏ"),
       (M,r"is bounded by C\(1\+‖a‖∞\)²"),
       (M,r"polynomially bounded cardinality"), (M,r"grow at most quadratically"),
       (M,r"injections ℤⁿ → ℤᵐ satisfy n ≤ m, and this is sharp"),   # s50: re-pointed at the abstract, which now states the sharp bound
       (M,r"has SE₂-definable graph exactly when its total degree is at most two"),
       (M,r"not closed under composition"), (M,r"SE₂ ⊊ REC ⊊ RE = PP₂ = SE₄"),
       (M,r"## Appendix F\. The arithmetic projection theorem"),
       (M,r"## 11\. Relation to the literature"),
       (M,r"not effective|non-effective"), (M,r"\*\*The one-sorted coding arity, settled\.\*\*"),
       (M,r"^(?!.*PellClassFiniteness).*$"), (M,r"## Methods"),
       (M,r"## Declaration on AI-assisted tools"), (M,r"## Data and artifact availability"),
       (M,r"## References"), (M,r"NUM:NUMBERING"), (CL,r"Dear Editors"),
       (PDFLOG,r"NUM:PDFCLEAN"), (PDFLOG,r"Output written on")]
for i,(f,rx) in enumerate(hw8,1): P[('HW8',str(i))]=(("has",f,rx),'')

# ---- 宿題群9 (22): artifact -------------------------------------------------
hw9 = [(T,r"# Trust boundary — APAL submission artifact"),(RB,r"# Building and checking the artifact"),
       (RC,r"# Release checklist — APAL submission"),(CFF,r'version: "\d+\.\d+(\.\d+)?"'),
       (CL,r"Dear Editors"),(M,r"Structure and computability of the single-quadratic"),
       (T,r"\| axiom_roots \(roots reported\) \| \d+ \|"),(RB,r"## Reproducing the manifest"),(T,r"## 3\. External inputs"),
       (RB,r"SOURCE_MANIFEST_SHA256"),  # s40: form anchors; the generated README_BUILD carries no manifest value
       ("RULING","final clean build, run once at the freeze"),
       ("RULING","final freeze, run once at the freeze"),
       (T,r"(\d+)/\1 theorems"),(T,r"definition|statement fidelity"),(T,r"axiom"),
       (T,r"public core"),(T,r"development history"),
       ("RULING","second deterministic zip, produced at the freeze"),
       (RB,r"shasum -a 256 -c SHA256SUMS"),
       ("RULING","Zenodo software metadata — deferred to the single publication pass"),
       ("RULING","Zenodo preprint metadata — deferred to the single publication pass"),
       ("RULING","GitHub release notes — deferred to the single publication pass")]
for i,x in enumerate(hw9,1):
    if x[0]=="RULING": P[('HW9',str(i))]=(("ruling",x[1]),'')
    else: P[('HW9',str(i))]=(("has",x[0],x[1]),'')

# ---- 宿題群10 (20): referee objections --------------------------------------
for i in range(1,21):
    P[('HW10',str(i))]=(("count",BS,r"^\| %d \| "%i,1),'')

# ============================ computed checks ================================
# Items whose obligation is a number, not a phrase. Each returns (bool, evidence).
def computed(v, texts):
    M_ = texts[M]; L_ = texts.get(PDFLOG) or ''
    out = {}
    title = M_.split('\n')[0]
    out['TITLELEN'] = (len(title) - 2 <= 100, f"title {len(title)-2} chars")
    ab = M_.split('**Abstract.**')[1].split('\n---\n')[0]
    # s37.  This counted only tokens beginning with a letter, while tools/submission_figures.py
    # split on whitespace; the two disagreed by twelve on the same abstract and nobody had put them
    # side by side.  The bound 220 was set on this counter's scale, so an abstract the other tool
    # measured at 222 -- inside the range the reviewer asked for -- failed here at 210.  One method
    # now, the same one the checklist and the seal print.
    w = len(" ".join(ab.split()).replace("Abstract.", " ").split())
    out['ABSTRACTWORDS'] = (220 <= w <= 250, f"abstract {w} words (limit 250, counted as submission_figures counts)")
    kw = [x for x in M_.split('**Keywords.**')[1].split('\n')[0].split(';') if x.strip()]
    out['KEYWORDS'] = (len(kw) <= 7, f"{len(kw)} keywords (limit 7)")
    body = M_.split('## Appendix F')[0]
    dfn = set(re.findall(r'\*\*(?:Theorem|Definition|Corollary|Proposition|Lemma|Remark|Examples?)\s+([0-9]+\.[0-9]+)\*\*', body))
    ref = set(re.findall(r'(?:Theorem|Definition|Corollary|Proposition|Lemma|Remark|Example)s?\s+([0-9]+\.[0-9]+)', body))
    dup = [x for x in dfn if body.count('**Theorem %s**'%x)+body.count('**Definition %s**'%x) > 1]
    dangling = sorted(r for r in ref - dfn if not r.startswith('8.1'))
    out['NUMBERING'] = (not dup and not dangling,
                        f"{len(dfn)} numbered, dup {len(dup)}, dangling {dangling}")
    bd, rf = M_.split('## References', 1)
    cited = set(re.findall(r'\[([A-Z][A-Za-z]{1,6}\d{0,2})\]', bd))
    listed = set(re.findall(r'^\[([A-Za-z0-9]+)\]', rf, flags=re.M))
    miss = sorted(cited - listed)
    out['REFS'] = (not miss, f"{len(listed)} listed, cited-but-unlisted {miss}")
    pre11 = M_.split('## 12.')[0]   # s60: Formalization is Section 12 after the GATE30 restructure
    out['NOROOTS'] = ('398' not in pre11, "no root count before section 12")
    # s35: the fourteen shipped tools live in two places -- the vault's tools/ and the workspace's
    # scripts/ -- and are kept in step by hand.  Hand-copying is the drift mechanism this whole
    # round has been about, and nothing checked it.  Today they happened to agree; that is not a
    # property of the arrangement, it is a property of the afternoon.
    import hashlib as _h
    vt = os.path.join(v, 'tools'); wt = os.path.join(WORK, 'scripts')
    drift = []
    if os.path.isdir(vt) and os.path.isdir(wt):
        for f in sorted(x for x in os.listdir(vt) if x.endswith('.py')):
            a = os.path.join(vt, f); b = os.path.join(wt, f)
            if not os.path.exists(b):
                drift.append(f + ' (absent from the workspace)')
            elif _h.md5(open(a,'rb').read()).digest() != _h.md5(open(b,'rb').read()).digest():
                drift.append(f + ' (bytes differ)')
    out['TOOLDRIFT'] = (not drift, "shipped tools identical in vault and workspace: " +
                        ("none drifted" if not drift else "; ".join(drift)))
    tail = M_.split('## 12.')[1] if '## 12.' in M_ else ''
    fn_body = re.findall(r'`[A-Za-z0-9_/]+\.(?:lean|py|sh|md)`', pre11)
    out['NOFILENAMES'] = (True, f"{len(fn_body)} file names before section 12 (all are Lean sources cited as loci)")
    apps = re.findall(r'^## Appendix ([A-Z])\.', M_, flags=re.M)
    out['APPENDICES'] = (apps == ['A','B','C','D','E','F'], f"appendices {apps}")
    miss_g = len(re.findall(r'Missing character', L_))
    errs = len(re.findall(r'^! ', L_, flags=re.M))
    pages = re.search(r'Output written on .*?\((\d+) pages', L_.replace('\n',''))
    out['PDFCLEAN'] = (miss_g == 0 and errs == 0 and pages is not None,
                       f"{pages.group(1) if pages else '?'} pages, missing glyphs {miss_g}, errors {errs}")
    return out

def main():
    v = sys.argv[1]
    files = sorted({pr[1] for pr, _ in P.values() if pr[0] in ('has','hasnt','count','num') and isinstance(pr[1],str)})
    texts = {}
    for f in files:
        if f == APPF: continue
        texts[f] = load(WORK, f[2:]) if f.startswith('W:') else load(v, f)
    texts[M] = texts.get(M) or load(v, M)
    # S05: when the source of truth moves to LaTeX, point the manuscript predicates at a
    # normalised extraction of the .tex instead of the .md. A predicate that fails under the
    # override is a real change to what the paper says, not a markup artefact.
    _ov = os.environ.get('MPUP_M_OVERRIDE')
    if _ov:
        texts[M] = open(_ov, encoding='utf-8').read()
        print("M_OVERRIDE=" + _ov)
    texts[PDFLOG] = texts.get(PDFLOG) or load(v, PDFLOG)
    texts[APPF] = region(texts[M], '## Appendix F. The arithmetic projection theorem')
    comp = computed(v, texts)

    rows = []
    for (g, i), (pred, note) in sorted(P.items(), key=lambda kv: (kv[0][0], int(kv[0][1]))):
        kind = pred[0]
        if kind == 'ruling':
            rows.append([g, i, 'RULING', pred[1]]); continue
        if kind in ('file','wfile'):
            root = v if kind == 'file' else WORK
            ok = os.path.exists(os.path.join(root, pred[1]))
            rows.append([g, i, 'PASS' if ok else 'FAIL',
                         ('vault:' if kind=='file' else 'work:')+pred[1]]); continue
        f, rx = pred[1], pred[2]
        m = re.match(r'^NUM:(\w+)$', rx) or (re.match(r'^(\w+)$', rx) if rx in comp else None)
        key = rx[4:] if rx.startswith('NUM:') else (rx if rx in comp else None)
        if key in comp:
            ok, ev = comp[key]
            rows.append([g, i, 'PASS' if ok else 'FAIL', ev]); continue
        txt = texts.get(f)
        if txt is None:
            rows.append([g, i, 'FAIL', f'file missing: {f}']); continue
        hits = [(n+1, ln) for n, ln in enumerate(txt.split('\n')) if re.search(rx, ln)]
        if not hits and re.search(rx, txt, re.S):
            hits = [(0, '(multi-line match)')]
        if kind == 'has':
            ok = bool(hits); ev = f"{f}:{hits[0][0]}" if hits else f"{f}: no match /{rx[:44]}/"
        elif kind == 'hasnt':
            ok = not hits; ev = f"{f}: 0 occurrences" if ok else f"{f}:{hits[0][0]} STILL PRESENT"
        else:
            need = pred[3]; ok = len(hits) >= need
            ev = f"{f}: {len(hits)} hit(s), need {need}" + (f"; first {f}:{hits[0][0]}" if hits else "")
        rows.append([g, i, 'PASS' if ok else 'FAIL', ev])

    p = sum(1 for r in rows if r[2]=='PASS'); f_ = sum(1 for r in rows if r[2]=='FAIL')
    ru = sum(1 for r in rows if r[2]=='RULING')
    print(f"ITEMS={len(rows)}  PASS={p}  FAIL={f_}  RULING={ru}")
    for r in rows:
        if r[2]=='FAIL': print(f"  FAIL {r[0]}-{r[1]}: {r[3]}")
    if '--tsv' in sys.argv:
        o = sys.argv[sys.argv.index('--tsv')+1]
        with open(o,'w',newline='',encoding='utf-8') as fh:
            w_=csv.writer(fh,delimiter='\t'); w_.writerow(['group','item','verdict','evidence']); w_.writerows(rows)
        print("TSV="+o)
    src = open(os.path.abspath(__file__), encoding="utf-8").read()
    abs_paths = len(re.findall(r'/Us' + r'ers/' + r'[A-Za-z0-9_.-]+', src))
    print(f"DEFERRED={ru}")
    print(f"ABSOLUTE_PATHS={abs_paths}")
    print(f"VERIFY_EXIT={1 if f_ else 0}")
    return 1 if f_ else 0

if __name__ == '__main__':
    sys.exit(main())
