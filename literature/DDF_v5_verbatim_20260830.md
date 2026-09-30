# DDF verbatim audit — arXiv:2102.06941v5 (19 Nov 2025), fetched 2026-08-30 via fetch_pdf (36 pages, saved fetch_pdf/DDF_2102.06941v5_1.pdf)
Phase −1 record. Lemma numbers below are those of v5; earlier versions number the ring lemmas 8.18–8.19 (web snippet seen earlier).

Definition 1.3 (field K, diophantine D ⊆ Kⁿ): rk∃_K(D) = min{m : some existential formula with at most m existential quantifiers defines D}.
Definition 1.6: rk∃(K) = sup_D rk∃_K(D) over all diophantine D ⊆ Kⁿ, all n.
Definition 2.12: rk∃,n_L(Σ) = sup over ∃-formulas in at most n free variables; rk∃_L(Σ) = sup_n.
§8, before Lemma 8.19: "In the following we view a ring R (always assumed commutative and with 1) as an L_ring-structure and apply the definitions from Section 2."
Lemma 8.19 (verbatim): "Let R be a ring. If there exists f ∈ R[X,Y] such that f : R × R → R is injective, then rk∃(R) = rk∃,1(R)."
  Proof idea (verbatim core): f_n iterated injection Rⁿ → R; {f_n(a) : a ∈ φ(R)} defined by φ′ with ≤ d = rk∃,1(R) quantifiers; φ equivalent to φ′(f_n(X)).
Lemma 8.20 (verbatim): "Let R = Z or let R be an integral domain such that Frac(R) is imperfect. There exists f ∈ R[X,Y] such that f : R×R → R is injective. Furthermore, if R = Z, we may assume that f(R × R) ⊆ Z≥0."
  Proof for Z (verbatim): "The map Z → Z≥0 : X ↦ 2X² − X is easily seen to be injective. Furthermore, also the map Z≥0 × Z≥0 → Z≥0 : (X,Y) ↦ (X+Y)(X+Y+1)+2Y is known to be injective (f/2 is the Cantor pairing function). We may thus take the polynomial f = (2X²−X+2Y²−Y)(2X²−X+2Y²−Y+1)+4Y²−2Y."
Remark 8.23: N in Lemma 8.21 can be rk∃(Z) = rk∃,1(Z) (Lemmas 8.19, 8.20); rk∃,1(Z) ≤ 10 from [Sun21, Thm 1.1(ii)]; rk∃,1(Z≥0) ≤ 9 from Jones [Jon82] (9 unknowns).
Remark 8.28 (verbatim): "Recall from Remark 8.23 that rk∃(Z) = rk∃,1(Z) ≤ 10. On the other hand, rk∃(Z) > 1: any ∃1-L_ring-definable subset of Z is recursive, but there exist recursively enumerable subsets of Z (hence ∃-L_ring-definable by Matijasevič' theorem) which are not recursive."
Consequences for the manuscript: (i) cite Lemma 8.19 / 8.20 (v5), not 8.18/8.19; (ii) our π = cantorScaledPair IS the Z≥0-pairing of DDF's proof — say so; (iii) DDF work one-sorted over Z (all variables in Z) — our inputs are in N: state the trace/mixed semantics; (iv) 1 < rk∃(Z) ≤ 10 is a standard, published quantity — a degree-bounded analogue rk∃_{≤d}(Z) is the natural bridge candidate (UNDERFLOW s19 'desk bridge').
